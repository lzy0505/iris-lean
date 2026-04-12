#!/usr/bin/env python3
"""
Iris-Lean Porting Completeness Checker

Compares Iris-Rocq definitions against Iris-Lean's @[rocq_alias] annotations
to track porting progress.

Usage:
  python3 scripts/check_porting.py [options]

Options:
  --format summary|csv|html   Output format (default: summary)
  --output PATH               Output file path (default: stdout for summary/csv,
                               report.html for html)
  --rocq-commit SHA           Iris-Rocq commit to check against
  --no-build                  Skip running lake exe dumpRocqAliases
  --cache-dir DIR             Cache directory (default: .lake/iris-rocq-cache)
"""

import argparse
import csv
import io
import json
import os
import re
import subprocess
import sys
import tarfile
import tomllib
import urllib.request
from collections import defaultdict
from pathlib import Path

# ============================================================================
# Configuration
# ============================================================================

DEFAULT_ROCQ_COMMIT = "master"
GITLAB_PROJECT_ID = "iris%2Firis"  # URL-encoded iris/iris
GITLAB_API_BASE = "https://gitlab.mpi-sws.org/api/v4"
GITLAB_WEB_BASE = "https://gitlab.mpi-sws.org/iris/iris"

# Subdirectory within the Iris-Rocq repo containing the source
ROCQ_SRC_PREFIX = "iris/"


# ============================================================================
# Rocq Definition Parsing
# ============================================================================

# Regex for definition keywords
_DEF_KW = (
    r"Definition|Lemma|Theorem|Instance|Class|Record|Structure|"
    r"Inductive|Fixpoint|CoFixpoint|Variant|Corollary|Proposition|"
    r"Fact|Remark|Example"
)

# Match a definition line, optionally prefixed by Global/Program/#[export]/#[global]
DEF_RE = re.compile(
    rf"^\s*(?:(?:Global|Local|Program|#\[(?:export|global)\])\s+)*"
    rf"({_DEF_KW})\s+"
    rf"(\w[\w']*)",
    re.MULTILINE,
)

# Module start/end (affects name qualification)
MODULE_START_RE = re.compile(r"^\s*Module\s+(\w+)", re.MULTILINE)
MODULE_END_RE = re.compile(r"^\s*End\s+(\w+)\s*\.", re.MULTILINE)

# Section start/end (tracked for scope but does NOT qualify names)
SECTION_START_RE = re.compile(r"^\s*Section\s+(\w+)", re.MULTILINE)
SECTION_END_RE = re.compile(r"^\s*End\s+(\w+)\s*\.", re.MULTILINE)

# Skip local definitions
# Lines to skip entirely
SKIP_LINE_RE = re.compile(
    r"^\s*(?:Notation|Ltac|Ltac2|Tactic\s+Notation|Hint|Arguments|"
    r"Typeclasses\s+Opaque|Typeclasses\s+Transparent|"
    r"Existing\s+Instance|Params|Canonical|"
    r"Declare\s+Scope|Delimit\s+Scope|Bind\s+Scope|"
    r"Open\s+Scope|Close\s+Scope|"
    r"Coercion|Import|Export|Require|From|Set|Unset)\b"
)


def strip_comments(text: str) -> str:
    """Remove Rocq (* ... *) comments (nested)."""
    result = []
    depth = 0
    i = 0
    while i < len(text):
        if text[i:i+2] == "(*":
            depth += 1
            i += 2
        elif text[i:i+2] == "*)" and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0:
            result.append(text[i])
            i += 1
        else:
            i += 1
    return "".join(result)


def parse_rocq_file(text: str) -> list[str]:
    """Extract all definition names from a Rocq .v file.

    Returns fully-qualified names (with Module prefixes, but not Section prefixes).
    """
    text = strip_comments(text)

    names = []
    module_stack = []  # Stack of module names for qualification
    section_names = set()  # Track section names to distinguish from modules on End

    for line in text.split("\n"):
        # Track module boundaries
        m = MODULE_START_RE.match(line)
        if m and not re.match(r"^\s*Module\s+Type\b", line):
            module_stack.append(m.group(1))
            continue

        # Track section names
        m = SECTION_START_RE.match(line)
        if m:
            section_names.add(m.group(1))
            continue

        # Handle End
        m = MODULE_END_RE.match(line)
        if m:
            end_name = m.group(1)
            if end_name in section_names:
                section_names.discard(end_name)
            elif module_stack and module_stack[-1] == end_name:
                module_stack.pop()
            continue

        # Skip non-definition lines
        if SKIP_LINE_RE.match(line):
            continue

        # Match definitions
        m = DEF_RE.match(line)
        if m:
            _kind = m.group(1)
            name = m.group(2)
            # Qualify with module prefix
            if module_stack:
                qualified = ".".join(module_stack) + "." + name
            else:
                qualified = name
            names.append(qualified)

    return names


# ============================================================================
# Iris-Rocq Download and Cache
# ============================================================================

def resolve_commit(ref: str) -> str:
    """Resolve a Git ref (branch name, tag, or SHA) to a full commit SHA."""
    url = (
        f"{GITLAB_API_BASE}/projects/{GITLAB_PROJECT_ID}"
        f"/repository/commits/{ref}"
    )
    try:
        with urllib.request.urlopen(url, timeout=30) as resp:
            data = json.loads(resp.read())
            return data["id"]
    except Exception as e:
        print(f"Warning: could not resolve ref '{ref}': {e}", file=sys.stderr)
        return ref


def download_iris_rocq(
    commit: str, cache_dir: Path
) -> tuple[dict[str, list[str]], str]:
    """Download Iris-Rocq at the given commit, parse definitions, cache as JSON,
    and delete the source tree.

    Returns: (definitions dict, resolved commit SHA).
    """
    # Resolve branch/tag names to a concrete SHA
    resolved = resolve_commit(commit)
    if resolved != commit:
        print(f"Resolved '{commit}' -> {resolved}", file=sys.stderr)

    cache_file = cache_dir / resolved / "rocq_definitions.json"

    if cache_file.exists():
        print(f"Using cached Rocq definitions from {cache_file}", file=sys.stderr)
        with open(cache_file) as f:
            return json.load(f), resolved

    print(f"Downloading Iris-Rocq at {resolved}...", file=sys.stderr)
    url = (
        f"{GITLAB_API_BASE}/projects/{GITLAB_PROJECT_ID}"
        f"/repository/archive.tar.gz?sha={resolved}"
    )

    req = urllib.request.Request(url)
    with urllib.request.urlopen(req, timeout=120) as resp:
        tarball_data = resp.read()

    print(f"Downloaded {len(tarball_data) / 1024:.0f} KB, parsing...", file=sys.stderr)

    definitions: dict[str, list[str]] = {}

    with tarfile.open(fileobj=io.BytesIO(tarball_data), mode="r:gz") as tf:
        for member in tf.getmembers():
            if not member.isfile() or not member.name.endswith(".v"):
                continue

            # Strip the top-level archive directory (e.g., "iris-master-SHA/")
            parts = member.name.split("/", 1)
            if len(parts) < 2:
                continue
            rel_path = parts[1]

            # Only process files under iris/ (the source directory)
            if not rel_path.startswith(ROCQ_SRC_PREFIX):
                continue

            f = tf.extractfile(member)
            if f is None:
                continue

            text = f.read().decode("utf-8", errors="replace")
            defs = parse_rocq_file(text)

            if defs:
                definitions[rel_path] = defs

    # Cache the definitions
    cache_file.parent.mkdir(parents=True, exist_ok=True)
    with open(cache_file, "w") as f:
        json.dump(definitions, f, indent=2)
    print(
        f"Parsed {sum(len(v) for v in definitions.values())} definitions "
        f"from {len(definitions)} files",
        file=sys.stderr,
    )

    return definitions, resolved


# ============================================================================
# Lean Data Loading
# ============================================================================

def run_lake_dump(output_path: str = ".lake/rocq_aliases.json") -> None:
    """Run lake exe dumpRocqAliases to generate the JSON dump."""
    print("Running lake exe dumpRocqAliases...", file=sys.stderr)
    result = subprocess.run(
        ["lake", "exe", "dumpRocqAliases", output_path],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(f"Error running lake exe dumpRocqAliases:", file=sys.stderr)
        print(result.stderr, file=sys.stderr)
        sys.exit(1)
    print(result.stdout.strip(), file=sys.stderr)


def load_lean_data(
    json_path: str = ".lake/rocq_aliases.json",
) -> tuple[dict[str, str], dict[str, str]]:
    """Load the Lean alias and ignore data.

    Returns:
        aliases: dict mapping rocq_name -> lean_name
        ignores: dict mapping rocq_name -> reason
    """
    with open(json_path) as f:
        data = json.load(f)

    aliases = {a["rocq"]: a["lean"] for a in data["aliases"]}
    ignores = {i["rocq"]: i["reason"] for i in data["ignores"]}
    return aliases, ignores


def load_config(
    path: str = "rocq_ignore.toml",
) -> tuple[str, set[str], set[str]]:
    """Load the TOML configuration.

    Returns:
        rocq_commit: the Rocq commit/ref to track (or "" to use default)
        ignored_paths: set of file paths and directory prefixes to skip
        ignored_names: set of individual definition names to skip
    """
    ignored_paths: set[str] = set()
    ignored_names: set[str] = set()
    rocq_commit = ""

    if not os.path.exists(path):
        return rocq_commit, ignored_paths, ignored_names

    with open(path, "rb") as f:
        data = tomllib.load(f)

    rocq_commit = data.get("rocq", {}).get("commit", "")
    for p in data.get("files", {}).get("ignore", []):
        ignored_paths.add(p)
    for p in data.get("directories", {}).get("ignore", []):
        ignored_paths.add(p)
    for n in data.get("names", {}).get("ignore", []):
        ignored_names.add(n)

    return rocq_commit, ignored_paths, ignored_names


# ============================================================================
# Report Computation
# ============================================================================

class ReportEntry:
    __slots__ = ("rocq_file", "rocq_name", "status", "lean_name", "reason")

    def __init__(self, rocq_file, rocq_name, status, lean_name="", reason=""):
        self.rocq_file = rocq_file
        self.rocq_name = rocq_name
        self.status = status
        self.lean_name = lean_name
        self.reason = reason


class Report:
    def __init__(self):
        self.entries: list[ReportEntry] = []
        self.rocq_commit: str = ""
        self.total_rocq: int = 0

    @property
    def ported(self):
        return [e for e in self.entries if e.status == "ported"]

    @property
    def ignored(self):
        return [e for e in self.entries if e.status == "ignored"]

    @property
    def missing(self):
        return [e for e in self.entries if e.status == "missing"]

    @property
    def stale_alias(self):
        return [e for e in self.entries if e.status == "stale_alias"]

    @property
    def stale_ignore(self):
        return [e for e in self.entries if e.status == "stale_ignore"]


def compute_report(
    rocq_defs: dict[str, list[str]],
    aliases: dict[str, str],
    ignores: dict[str, str],
    ignored_paths: set[str],
    ignored_names: set[str],
    rocq_commit: str,
) -> Report:
    """Compare Rocq definitions against Lean aliases and ignores."""
    report = Report()
    report.rocq_commit = rocq_commit

    # Build flat set of all Rocq definition names -> file
    rocq_name_to_file: dict[str, str] = {}
    for filepath, names in rocq_defs.items():
        for name in names:
            rocq_name_to_file[name] = filepath

    report.total_rocq = len(rocq_name_to_file)

    # Classify each Rocq definition
    for name, filepath in sorted(rocq_name_to_file.items()):
        # Check file-level ignores (from rocq_ignore.txt)
        file_ignored = any(filepath.startswith(p) for p in ignored_paths)
        if name in aliases:
            report.entries.append(
                ReportEntry(filepath, name, "ported", lean_name=aliases[name])
            )
        elif name in ignores or name in ignored_names or file_ignored:
            reason = ignores.get(name, "")
            if not reason and file_ignored:
                reason = f"file ignored ({filepath})"
            elif not reason:
                reason = "ignored via rocq_ignore.txt"
            report.entries.append(
                ReportEntry(filepath, name, "ignored", reason=reason)
            )
        else:
            report.entries.append(ReportEntry(filepath, name, "missing"))

    # Find stale aliases (in Lean but not in Rocq)
    rocq_names = set(rocq_name_to_file.keys())
    for name, lean_name in sorted(aliases.items()):
        if name not in rocq_names:
            report.entries.append(
                ReportEntry("", name, "stale_alias", lean_name=lean_name)
            )

    # Find stale ignores
    for name, reason in sorted(ignores.items()):
        if name not in rocq_names:
            report.entries.append(
                ReportEntry("", name, "stale_ignore", reason=reason)
            )

    return report


# ============================================================================
# Output Formatters
# ============================================================================

def output_summary(report: Report, out=sys.stdout) -> None:
    """Print a human-readable summary."""
    print("=" * 60, file=out)
    print("Iris Porting Completeness Report", file=out)
    print("=" * 60, file=out)
    print(f"Rocq commit: {report.rocq_commit}", file=out)
    print(f"Total Rocq definitions: {report.total_rocq}", file=out)
    print(f"Ported (with rocq_alias): {len(report.ported)}", file=out)
    print(f"Ignored: {len(report.ignored)}", file=out)
    print(f"Missing: {len(report.missing)}", file=out)
    if report.stale_alias:
        print(f"Stale aliases: {len(report.stale_alias)}", file=out)
    if report.stale_ignore:
        print(f"Stale ignores: {len(report.stale_ignore)}", file=out)

    if report.total_rocq > 0:
        pct = len(report.ported) / report.total_rocq * 100
        print(f"\nProgress: {pct:.1f}%", file=out)

    # Per-file breakdown
    files: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))
    for e in report.entries:
        if e.rocq_file:
            files[e.rocq_file][e.status] += 1

    print(f"\nPer-file breakdown:", file=out)
    print("-" * 60, file=out)

    for filepath in sorted(files.keys()):
        counts = files[filepath]
        total = sum(counts.values())
        ported = counts.get("ported", 0)
        ignored = counts.get("ignored", 0)
        missing = counts.get("missing", 0)
        done = ported + ignored
        pct = done / total * 100 if total > 0 else 0
        status_parts = []
        if ported:
            status_parts.append(f"{ported} ported")
        if ignored:
            status_parts.append(f"{ignored} ignored")
        if missing:
            status_parts.append(f"{missing} missing")
        status_str = ", ".join(status_parts)
        # Shorten path for display
        display = filepath.removeprefix(ROCQ_SRC_PREFIX)
        print(f"  {display:40s} {done:3d}/{total:<3d} ({pct:5.1f}%) [{status_str}]", file=out)


def output_csv(report: Report, path: str) -> None:
    """Write a CSV report."""
    f = open(path, "w", newline="") if path != "-" else sys.stdout
    writer = csv.writer(f)
    writer.writerow(["rocq_file", "rocq_name", "status", "lean_name", "reason"])
    for e in report.entries:
        writer.writerow([e.rocq_file, e.rocq_name, e.status, e.lean_name, e.reason])
    if path != "-":
        f.close()
        print(f"Wrote CSV to {path}", file=sys.stderr)


def output_html(report: Report, path: str) -> None:
    """Generate a self-contained HTML report."""
    # Per-file data
    files_data: dict[str, list[ReportEntry]] = defaultdict(list)
    stale_entries: list[ReportEntry] = []
    for e in report.entries:
        if e.status in ("stale_alias", "stale_ignore"):
            stale_entries.append(e)
        elif e.rocq_file:
            files_data[e.rocq_file].append(e)

    total = report.total_rocq
    ported = len(report.ported)
    ignored = len(report.ignored)
    missing = len(report.missing)
    pct = ported / total * 100 if total > 0 else 0

    # Collect top-level folders for the folder filter
    folders: set[str] = set()
    for filepath in files_data:
        display = filepath.removeprefix(ROCQ_SRC_PREFIX)
        folder = display.split("/")[0]
        folders.add(folder)

    # Compute per-folder summary
    folder_stats: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))
    for filepath, entries in files_data.items():
        display = filepath.removeprefix(ROCQ_SRC_PREFIX)
        folder = display.split("/")[0]
        for e in entries:
            folder_stats[folder][e.status] += 1
            folder_stats[folder]["total"] += 1

    folder_buttons = ""
    for folder in sorted(folders):
        fs = folder_stats[folder]
        f_total = fs["total"]
        f_done = fs.get("ported", 0) + fs.get("ignored", 0)
        f_pct = f_done / f_total * 100 if f_total > 0 else 0
        folder_buttons += (
            f'<button class="folder-btn" onclick="setFolder(\'{folder}\')">'
            f'{folder}/ <small>{f_done}/{f_total}</small></button>\n'
        )

    file_rows = []
    for filepath in sorted(files_data.keys()):
        entries = files_data[filepath]
        display = filepath.removeprefix(ROCQ_SRC_PREFIX)
        folder = display.split("/")[0]
        n_ported = sum(1 for e in entries if e.status == "ported")
        n_ignored = sum(1 for e in entries if e.status == "ignored")
        n_missing = sum(1 for e in entries if e.status == "missing")
        n_total = len(entries)
        n_done = n_ported + n_ignored
        file_pct = n_done / n_total * 100 if n_total > 0 else 0

        rows_html = []
        for e in sorted(entries, key=lambda x: (x.status != "missing", x.rocq_name)):
            badge_cls = {
                "ported": "badge-ported",
                "ignored": "badge-ignored",
                "missing": "badge-missing",
            }.get(e.status, "")
            detail = e.lean_name if e.status == "ported" else e.reason
            rows_html.append(
                f'<tr class="entry {e.status}" data-name="{e.rocq_name}">'
                f'<td>{e.rocq_name}</td>'
                f'<td><span class="badge {badge_cls}"></span></td>'
                f"<td>{detail}</td>"
                f"</tr>"
            )

        bar_w = file_pct

        rocq_link = f"{GITLAB_WEB_BASE}/-/blob/{report.rocq_commit}/{filepath}"

        file_rows.append(f"""
        <div class="file-section" data-file="{display}" data-folder="{folder}">
          <div class="file-header" onclick="this.parentElement.classList.toggle('open')">
            <span class="arrow">&#9654;</span>
            <code class="file-name">{display}</code>
            <a class="file-link" href="{rocq_link}" target="_blank" onclick="event.stopPropagation()">[src]</a>
            <span class="file-stats">{n_done}/{n_total} ({file_pct:.0f}%)</span>
            <span class="mini-bar"><span class="mini-bar-fill" style="width:{bar_w:.1f}%"></span></span>
          </div>
          <table class="file-table">
            <thead><tr><th>Rocq Name</th><th>Status</th><th>Details</th></tr></thead>
            <tbody>{"".join(rows_html)}</tbody>
          </table>
        </div>""")

    stale_html = ""
    if stale_entries:
        stale_rows = []
        for e in stale_entries:
            badge_cls = "badge-stale"
            detail = e.lean_name if e.status == "stale_alias" else e.reason
            stale_rows.append(
                f'<tr class="entry stale_alias" data-name="{e.rocq_name}">'
                f'<td>{e.rocq_name}</td>'
                f'<td><span class="badge {badge_cls}"></span></td>'
                f"<td>{detail}</td></tr>"
            )
        stale_html = f"""
        <div class="file-section open" data-file="stale" data-folder="_stale">
          <div class="file-header" onclick="this.parentElement.classList.toggle('open')">
            <span class="arrow">&#9654;</span>
            <code class="file-name">Stale Entries</code>
            <span class="file-stats">{len(stale_entries)} entries</span>
          </div>
          <table class="file-table">
            <thead><tr><th>Name</th><th>Status</th><th>Details</th></tr></thead>
            <tbody>{"".join(stale_rows)}</tbody>
          </table>
        </div>"""

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Iris Porting Status</title>
<style>
  * {{ box-sizing: border-box; margin: 0; padding: 0; }}
  body {{ font-family: "Georgia", "Times New Roman", serif;
         max-width: 960px; margin: 0 auto; padding: 24px;
         background: #fff; color: #222; line-height: 1.5; }}
  h1 {{ font-size: 1.6em; margin-bottom: 4px; font-weight: normal; }}
  h2 {{ font-size: 1.1em; font-weight: normal; margin: 18px 0 8px; border-bottom: 1px solid #ccc; padding-bottom: 4px; }}
  .meta {{ font-size: 0.85em; color: #666; margin-bottom: 16px; }}
  .meta a {{ color: #555; }}

  /* Summary table */
  .summary {{ border-collapse: collapse; margin: 12px 0 20px; width: 100%; }}
  .summary td {{ padding: 6px 0; text-align: center; font-size: 0.85em; color: #666;
                 border-right: 1px solid #ddd; }}
  .summary td:last-child {{ border-right: none; }}
  .summary .num {{ display: block; font-family: "SF Mono", "Menlo", "Consolas", monospace;
                   font-size: 1.6em; font-weight: bold; color: #222; }}

  /* Progress */
  .progress-bar {{ height: 14px; background: #ddd; margin: 0 0 20px; }}
  .progress-fill {{ height: 100%; background: #4a4; }}

  /* Search + filters */
  .controls {{ margin: 16px 0; }}
  .search {{ width: 100%; padding: 6px 8px; font-size: 0.95em;
             border: 1px solid #999; font-family: inherit; margin-bottom: 8px; }}
  .filter-row {{ display: flex; gap: 6px; flex-wrap: wrap; margin-bottom: 6px; }}
  .filter-btn, .folder-btn {{
    padding: 3px 10px; border: 1px solid #aaa; background: #f8f8f8;
    cursor: pointer; font-size: 0.82em; font-family: inherit; }}
  .filter-btn:hover, .folder-btn:hover {{ background: #eee; }}
  .filter-btn.active {{ background: #333; color: #fff; border-color: #333; }}
  .folder-btn.active {{ background: #555; color: #fff; border-color: #555; }}
  .folder-btn small {{ color: inherit; opacity: 0.7; }}

  /* File sections */
  .file-section {{ border-top: 1px solid #ddd; }}
  .file-section:last-child {{ border-bottom: 1px solid #ddd; }}
  .file-header {{ padding: 6px 0; cursor: pointer; display: flex;
                  align-items: center; gap: 8px; user-select: none; }}
  .file-header:hover {{ background: #fafafa; }}
  .arrow {{ font-size: 0.65em; width: 1em; text-align: center; }}
  .file-section.open .arrow {{ transform: rotate(90deg); }}
  .file-name {{ font-size: 0.92em; font-family: "SF Mono", "Menlo", "Consolas", monospace; }}
  .file-link {{ font-size: 0.75em; color: #888; text-decoration: none; }}
  .file-link:hover {{ color: #24a; }}
  .file-stats {{ color: #666; font-size: 0.82em; margin-left: auto; white-space: nowrap; font-family: "SF Mono", "Menlo", "Consolas", monospace; }}
  .mini-bar {{ display: inline-block; width: 80px; height: 4px; background: #ddd; vertical-align: middle; margin-left: 8px; }}
  .mini-bar-fill {{ display: block; height: 100%; background: #4a4; }}

  /* Tables */
  .file-table {{ width: 100%; border-collapse: collapse; display: none; margin-bottom: 8px; }}
  .file-section.open .file-table {{ display: table; }}
  .file-table th {{ text-align: left; padding: 4px 8px; font-weight: normal;
                    font-size: 0.8em; color: #888; border-bottom: 1px solid #eee; }}
  .file-table td {{ padding: 3px 8px; border-bottom: 1px solid #f0f0f0;
                    font-size: 0.85em; font-family: "SF Mono", "Menlo", "Consolas", monospace; }}
  .file-table td:nth-child(2) {{ font-family: inherit; }}

  /* Badges */
  .badge {{ font-size: 0.75em; font-family: "SF Mono", "Menlo", "Consolas", monospace;
            letter-spacing: 0.03em; text-transform: uppercase; }}
  .badge-ported {{ color: #2a6e2a; }}
  .badge-ported::before {{ content: "ported"; }}
  .badge-ignored {{ color: #888; }}
  .badge-ignored::before {{ content: "ignored"; }}
  .badge-missing {{ color: #b33; }}
  .badge-missing::before {{ content: "missing"; }}
  .badge-stale {{ color: #96600a; }}
  .badge-stale::before {{ content: "stale"; }}

  a {{ color: #24a; }}
  a:hover {{ color: #126; }}
  .hidden {{ display: none !important; }}
</style>
</head>
<body>
<h1>Iris Porting Status</h1>
<p class="meta">Tracking against Rocq
  <a href="{GITLAB_WEB_BASE}/-/commit/{report.rocq_commit}">{report.rocq_commit[:12]}</a>
</p>

<table class="summary">
  <tr>
    <td>Total<br><span class="num">{total}</span></td>
    <td>Ported<br><span class="num">{ported}</span></td>
    <td>Ignored<br><span class="num">{ignored}</span></td>
    <td>Missing<br><span class="num">{missing}</span></td>
    <td>Stale<br><span class="num">{len(report.stale_alias)}</span></td>
    <td>Progress<br><span class="num">{pct:.1f}%</span></td>
  </tr>
</table>

<div class="progress-bar"><div class="progress-fill" style="width:{pct:.1f}%"></div></div>

<div class="controls">
  <input type="text" class="search" placeholder="Search definitions..." oninput="applyFilters()">

  <div class="filter-row">
    <b style="font-size:0.85em;line-height:2">Status:</b>
    <button class="filter-btn active" onclick="setFilter('all')">all</button>
    <button class="filter-btn" onclick="setFilter('ported')">ported</button>
    <button class="filter-btn" onclick="setFilter('missing')">missing</button>
    <button class="filter-btn" onclick="setFilter('ignored')">ignored</button>
    <button class="filter-btn" onclick="setFilter('stale_alias')">stale</button>
  </div>

  <div class="filter-row">
    <b style="font-size:0.85em;line-height:2">Folder:</b>
    <button class="folder-btn active" onclick="setFolder('all')">all/</button>
    {folder_buttons}
  </div>
</div>

<div id="files">
{"".join(file_rows)}
{stale_html}
</div>

<script>
let currentFilter = 'all';
let currentFolder = 'all';

function setFilter(f) {{
  currentFilter = f;
  document.querySelectorAll('.filter-btn').forEach(b => b.classList.remove('active'));
  event.target.classList.add('active');
  applyFilters();
}}

function setFolder(f) {{
  currentFolder = f;
  document.querySelectorAll('.folder-btn').forEach(b => b.classList.remove('active'));
  event.target.classList.add('active');
  applyFilters();
}}

function applyFilters() {{
  const q = document.querySelector('.search').value.toLowerCase();
  document.querySelectorAll('.file-section').forEach(section => {{
    const folder = section.dataset.folder;
    if (currentFolder !== 'all' && folder !== currentFolder) {{
      section.classList.add('hidden');
      return;
    }}
    let anyVisible = false;
    section.querySelectorAll('.entry').forEach(row => {{
      const name = row.dataset.name.toLowerCase();
      const matchesSearch = !q || name.includes(q);
      const matchesFilter = currentFilter === 'all' || row.classList.contains(currentFilter);
      const visible = matchesSearch && matchesFilter;
      row.classList.toggle('hidden', !visible);
      if (visible) anyVisible = true;
    }});
    // For stale section, always show if folder matches
    if (!section.querySelectorAll('.entry').length) anyVisible = true;
    section.classList.toggle('hidden', !anyVisible);
  }});
}}
</script>
</body>
</html>"""

    with open(path, "w") as f:
        f.write(html)
    print(f"Wrote HTML report to {path}", file=sys.stderr)


# ============================================================================
# Main
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Iris-Lean porting completeness checker"
    )
    parser.add_argument(
        "--format",
        choices=["summary", "csv", "html"],
        default="summary",
        help="Output format (default: summary)",
    )
    parser.add_argument("--output", "-o", help="Output file path")
    parser.add_argument(
        "--rocq-commit",
        default=DEFAULT_ROCQ_COMMIT,
        help=f"Iris-Rocq commit SHA or branch (default: {DEFAULT_ROCQ_COMMIT})",
    )
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="Skip running lake exe dumpRocqAliases",
    )
    parser.add_argument(
        "--cache-dir",
        default=".lake/iris-rocq-cache",
        help="Cache directory for downloaded Rocq sources",
    )
    parser.add_argument(
        "--lean-json",
        default=".lake/rocq_aliases.json",
        help="Path to the Lean alias JSON dump",
    )

    args = parser.parse_args()

    # Step 0: Load config
    config_commit, ignored_paths, ignored_names = load_config()
    if ignored_paths or ignored_names:
        print(
            f"Loaded {len(ignored_paths)} ignored paths and "
            f"{len(ignored_names)} ignored names from rocq_ignore.toml",
            file=sys.stderr,
        )

    # CLI --rocq-commit overrides the TOML config
    rocq_ref = args.rocq_commit
    if rocq_ref == DEFAULT_ROCQ_COMMIT and config_commit:
        rocq_ref = config_commit

    # Step 1: Get Lean data
    if not args.no_build:
        run_lake_dump(args.lean_json)
    elif not os.path.exists(args.lean_json):
        print(
            f"Error: {args.lean_json} not found. Run without --no-build first.",
            file=sys.stderr,
        )
        sys.exit(1)

    aliases, ignores = load_lean_data(args.lean_json)
    print(
        f"Loaded {len(aliases)} aliases and {len(ignores)} ignores from Lean",
        file=sys.stderr,
    )

    # Step 2: Get Rocq definitions
    cache_dir = Path(args.cache_dir)
    rocq_defs, rocq_commit = download_iris_rocq(rocq_ref, cache_dir)

    # Step 3: Compute report
    report = compute_report(
        rocq_defs, aliases, ignores, ignored_paths, ignored_names, rocq_commit
    )

    # Step 4: Output
    if args.format == "summary":
        output_summary(report, out=open(args.output, "w") if args.output else sys.stdout)
    elif args.format == "csv":
        output_csv(report, args.output or "-")
    elif args.format == "html":
        output_html(report, args.output or "report.html")


if __name__ == "__main__":
    main()
