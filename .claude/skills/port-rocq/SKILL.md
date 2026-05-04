---
name: port-rocq
description: Port one Iris-Rocq .v file to iris-lean using a four-stage agent pipeline. Use when the user asks to port a Rocq Iris file to Lean (e.g. "port iris/algebra/frac.v"), or invokes /port-rocq. Spawns rocq-port-defs (Stage 1), two parallel rocq-review-defs runs (Stage 2 crosscheck), rocq-port-proofs (Stage 3), and rocq-review-proofs (Stage 4 final gate). Enforces every ported decl has @[rocq_alias], no sorries/axioms in the final output, lake build clean, and zero stale aliases via scripts/check_porting.py.
---

# Port one Iris-Rocq file to iris-lean

This skill orchestrates a four-stage agent pipeline to port a single Rocq `.v` file from `iris-rocq` to `iris-lean`. It enforces the user's invariants:

1. The project always builds (`lake build` is a hard gate at every stage that allows it).
2. Every ported decl carries `@[rocq_alias <fully.qualified.rocq.name>]`.
3. `python3 scripts/check_porting.py` shows no stale aliases for this file.
4. **`#rocq_ignore` is reserved for "the Rocq concept is not needed in iris-lean"** (Rocq-specific tactic/notation, redundant with iris-lean facility, subsumed by an existing lemma). Decls that *would* be ported except they depend on something not yet ported elsewhere are **left unmarked** — the tracking system reports them as `missing` and a future port pass picks them up.
5. Statements are semantically equivalent to the Rocq originals, expressed in iris-lean syntax/IPM tactics/named lemmas — not literal Rocq translation.
6. Lean names match local mathlib-style conventions.
7. Proofs prefer iris-lean IPM tactics from https://raw.githubusercontent.com/leanprover-community/iris-lean/refs/heads/master/Iris/tactics.md (lowercase-leading: `iintro`, `iapply`, `icases`, `imod`, `imodintro`, `inext`, `isplit`, `iexists`, `ihave`, `ispecialize`, `ileft`, `iright`, `iclear`, `irevert`, `irename`, `ipure`, `ipure_intro`, `iintuitionistic`, `ispatial`, `iexact`, `iassumption`, `iex_falso`, `iemp_intro`, `istart`, `istop`).
8. Every ported file is reviewed by **two independent reviewer runs** (Stage 2 crosscheck) and a final-gate reviewer (Stage 4).
9. No sorries, no new axioms in the final output.

## Inputs

The user invokes `/port-rocq <relative-rocq-path>`, e.g.

```
/port-rocq iris/algebra/frac.v
```

The path is relative to the iris-rocq root (`/Users/zongyuan/code/iris-rocq/`). Valid top-level folders: `algebra`, `base_logic`, `bi`, `program_logic`, `proofmode`, `si_logic`.

## Pipeline

```
       Stage 1: rocq-port-defs
                │
                ▼ build must succeed (sorries OK)
       Stage 2: rocq-review-defs ‖ rocq-review-defs   (PARALLEL — same prompt, twice)
                │
                ▼ orchestrator merges reports (union of issues)
                │ pass → continue;  fail → loop to Stage 1 (cap 3 rounds)
       Stage 3: rocq-port-proofs
                │
                ▼ build must succeed; no sorry; no new axiom
       Stage 3.5: /lean4:golf <LEAN_FILE>           (auto-golf the proofs)
                │
                ▼ build must still succeed (golf reverts on failure)
       Stage 4: rocq-review-proofs ‖ rocq-review-style   (PARALLEL — orthogonal axes)
                │
                ▼ orchestrator merges reports (union of issues)
                │ both approve → done
                │ either revise → loop to Stage 3 (cap 3 rounds)
                ▼ either escalate → hand to user
```

**Stage 4 is two orthogonal reviewers running in parallel:**
- `rocq-review-proofs` — build/axioms/stale-aliases/tactic-name-correctness/proof-discipline-against-laziness.
- `rocq-review-style` — proof concision and stylistic match (length ratios, term-vs-tactic, redundant `show`/`have`, inline comments, docstring register, header authors, architectural taste).

Both must `approve` for the pipeline to finish. Issues from either go into the merged feedback.

## Step-by-step orchestration

### 0. Resolve paths and pre-flight

**iris-loogle (local server, accessed via the Lean MCP).** Agents query Loogle through `mcp__lean-lsp__lean_loogle`. The MCP server is configured (via `LOOGLE_URL=http://localhost:8088` in the user's MCP config) to route Loogle queries to the local iris-loogle instance, whose index is built with the `Iris` module loaded — so the MCP transparently covers iris-lean + Mathlib + Batteries, unrate-limited. Before Stage 1, check that the server is up:
```
curl -sf http://localhost:8088/json?q=true >/dev/null || echo "loogle down"
```
If it's down, start it (in the background) from `/Users/zongyuan/code/iris-loogle/`:
```
cd /Users/zongyuan/code/iris-loogle && uv run server.py
```
Agents are told to **always go through the MCP** (`mcp__lean-lsp__lean_loogle`), never via raw `curl`. They are also told that **`mcp__lean-lsp__lean_local_search` replaces `Grep` for any Lean-side lookup** — `Grep` is reserved for non-Lean files (Rocq `.v`, configs, scripts).

```
ROCQ_ROOT="/Users/zongyuan/code/iris-rocq"
LEAN_REPO_ROOT="/Users/zongyuan/code/iris-lean"
ROCQ_FILE="$ROCQ_ROOT/$1"     # e.g. /Users/zongyuan/code/iris-rocq/iris/algebra/frac.v
```

Validate:
- `ROCQ_FILE` exists.
- It lives under `$ROCQ_ROOT/iris/{algebra,base_logic,bi,program_logic,proofmode,si_logic}/`.

Compute `LEAN_FILE`:
- Drop the `.v` extension; replace `iris/<folder>/<name>.v` with `Iris/Iris/<Folder>/<Name>.lean` where `<Folder>` is the PascalCase form of `<folder>` (e.g. `algebra` → `Algebra`, `base_logic` → `BaseLogic`, `program_logic` → `ProgramLogic`, `si_logic` → `SiLogic`, `proofmode` → `ProofMode`, `bi` → `BI`) and `<Name>` is the PascalCase form of the file basename (e.g. `frac` → `Frac`, `internal_eq` → `InternalEq`, `derived_laws_later` → `DerivedLawsLater`).

If `LEAN_FILE` already exists, ask the user whether to overwrite.

### 1. Worktree

Per the iris-lean repo convention, work in a worktree:

```bash
WORKTREE="$LEAN_REPO_ROOT/.claude/worktrees/port-$BASE"
git -C "$LEAN_REPO_ROOT" worktree add "$WORKTREE" -b "claude/port-$BASE"
```

Where `$BASE` is the basename of the Rocq file without extension (e.g. `frac`). All subsequent paths used by the agents reference `$WORKTREE` as `LEAN_REPO_ROOT`.

Also create a progress doc per the local CLAUDE.md convention (if iris-lean has one): `$WORKTREE/docs/port-$BASE.md` capturing the plan and status.

### 2. Baseline build

Capture the pre-port build state so Stage 4 can compare:

```bash
cd "$WORKTREE/Iris" && lake build 2>&1 | tee /tmp/port-rocq-baseline-$BASE.log
```

Record any pre-existing warnings in `BASELINE_BUILD` for Stage 4.

If `lake build` fails on master before any porting, abort and tell the user — we can't port on top of a broken tree.

### 3. Stage 1 — Spawn `rocq-port-defs`

Invoke the agent with these exact inputs:

```
Agent(subagent_type=rocq-port-defs, prompt=<below>)
```

Prompt body (substitute the variables; the agent has its own detailed instructions in its definition file):

```
ROCQ_FILE: <absolute path>
LEAN_FILE: <absolute path>
LEAN_REPO_ROOT: <WORKTREE absolute path>

[If REVISION_FEEDBACK is non-empty, paste it here verbatim under a "Previous review issues to address:" heading.]

Follow your full instructions. Return the structured JSON report.
```

Wait for the report. Verify `"build": "pass"`. If it's `"fail"`, escalate to user — Stage 1 is the cheapest stage to debug, but if the agent can't even build a sorry-stub file, something is structurally wrong (wrong import path, missing folder, etc.).

### 4. Stage 2 — Two parallel `rocq-review-defs`

**Spawn two `rocq-review-defs` agents in a single message** (true parallelism, fresh context each):

```
Agent(subagent_type=rocq-review-defs, prompt=<reviewer prompt>)   # call A
Agent(subagent_type=rocq-review-defs, prompt=<reviewer prompt>)   # call B  (same prompt)
```

Reviewer prompt body:

```
ROCQ_FILE: <absolute path>
LEAN_FILE: <absolute path>
LEAN_REPO_ROOT: <WORKTREE absolute path>
STAGE1_REPORT: <paste Stage 1's JSON report verbatim>

Follow your full instructions. Return the structured JSON report.
```

Both reports come back. **Merge them**:

- For each headline field (`alias_coverage`, `alias_qualified`, `alias_dupes`, `stale`, `ignore_justified`, `stmt_equivalence`, `binder_shape`, `instance_args`, `notation`, `def_extensional`, `naming`, `tactic_names`):
  - If both report `pass` → merged is `pass`.
  - If either reports `fail` → merged is `fail`.
  - If one reports `pass` and the other `warn` → merged is `warn`.
  - If both `warn` → merged is `warn`.
- For `issues`: take the **union**. If both reviewers flagged the same `decl + check`, deduplicate by keeping the more specific message.
- **Surface disagreements**: if the two reviewers disagree on whether a particular check passes, include both verdicts in the consolidated feedback so the Stage-1 porter sees both perspectives. Add a synthetic issue: `{"decl": "<scope>", "check": "<check>", "msg": "DISAGREEMENT: reviewer A says <X>, reviewer B says <Y>. Treating as fail. Apply the stricter interpretation."}`.

If the merged headline contains any `fail`, **loop back to Stage 1** with the merged issue list as `REVISION_FEEDBACK`. Cap at 3 revision rounds. After the third failure, escalate to the user with the merged report.

If the merged report is all `pass` (and at most a handful of `warn`s), proceed to Stage 3.

### 5. Stage 3 — Spawn `rocq-port-proofs`

```
Agent(subagent_type=rocq-port-proofs, prompt=<below>)
```

Prompt body:

```
LEAN_FILE: <absolute path>
ROCQ_FILE: <absolute path>
LEAN_REPO_ROOT: <WORKTREE absolute path>
STAGE2_REPORT: <merged Stage 2 report JSON>

[If REVISION_FEEDBACK from a previous Stage 4 iteration is non-empty, paste it.]

Follow your full instructions. Return the structured JSON report.
```

Wait for the report.
- If `"verdict": "blocked"`, escalate to the user with `blocked_proofs` content. Do not proceed to Stage 4.
- If `"verdict": "ready"`, proceed.

### 5.5. Stage 3.5 — Auto-golf the proofs via `/lean4:golf`

Before sending the file to the Stage-4 reviewers, run the lean4-skills golfer on it. This uses well-tested compression patterns (term-mode collapse, instant-win rewrites, optional lemma-replacement search) that would catch most of the verbosity issues a style reviewer would otherwise flag.

Invoke the slash command on the file (use the `Skill` tool with `lean4:golf`):

```
Skill(skill="lean4:golf", args="<LEAN_FILE absolute path>")
```

The golf command:
- Verifies the file builds first (it must — Stage 3 already ensured this).
- Detects golfable patterns and applies them with per-edit revert-on-failure.
- Returns a savings summary.

After it finishes:
1. Run `cd "$WORKTREE/Iris" && lake build` once more to confirm the file is still clean (golf reverts on failure, but cross-file effects deserve a check).
2. If the build *did* break, that's an internal golf bug — abort the pipeline and report to the user with the golf output. Do not retry blindly.
3. Capture the golf summary (lines saved, patterns applied, skipped patterns) in a `STAGE3_5_REPORT` to pass to the Stage-4 reviewers. They use it to recalibrate: if golf already reduced 30 lines, the style reviewer should not over-flag the remaining length.

This stage is **non-optional**. If the user invokes the pipeline with `--no-golf` (or some equivalent), refuse with a clear explanation: golf is the cheapest, safest concision improvement available, and skipping it shifts more work onto the style reviewer (which can only flag, not fix).

### 6. Stage 4 — Spawn `rocq-review-proofs` AND `rocq-review-style` in parallel

**Single message, two `Agent` calls** (true parallelism, fresh context each):

```
Agent(subagent_type=rocq-review-proofs, prompt=<below>)
Agent(subagent_type=rocq-review-style,  prompt=<below>)
```

Both prompts have the same body:

```
LEAN_FILE: <absolute path>
ROCQ_FILE: <absolute path>
LEAN_REPO_ROOT: <WORKTREE absolute path>
STAGE1_REPORT: <verbatim>
STAGE2_REPORT: <merged>
STAGE3_REPORT: <verbatim>
STAGE3_5_REPORT: <golf summary verbatim>
BASELINE_BUILD: <pre-port build log excerpt>

Follow your full instructions. Return the structured JSON report.
```

The two reviewers cover **orthogonal axes**:
- `rocq-review-proofs` — correctness gates: build, axioms, ignore-set unchanged, stale aliases, tactic-name correctness, anti-laziness style.
- `rocq-review-style` — concision/aesthetic gates: length ratio vs Rocq, term-vs-tactic mode, intermediate `have`s, redundant `show`s, inline-comment policy, docstring register, header authors, architectural taste.

**Merging the two reports:**

- For each headline check field, take the per-reviewer verdict as-is (the two reviewers' fields don't overlap).
- For `issues`, take the **union**.
- Compute the merged `verdict`:
  - **`approve`** — both reviewers return `approve`.
  - **`revise`** — either returns `revise` and neither returns `escalate`. Loop back to Stage 3 with the merged issue list as `REVISION_FEEDBACK`. Cap at 3 rounds.
  - **`escalate`** — either returns `escalate`. Hand to the user with both reports. Do not retry.

Stage 4 caps at 3 Stage-3↔Stage-4 loops total, regardless of which reviewer triggered the loop. After the third failure, escalate to the user.

### 7. Finalize

On a clean `approve`:

1. Update `$WORKTREE/docs/port-$BASE.md` with:
   - Final list of ported decls (from Stage 3's `filled` array).
   - Final list of ignored decls (from Stage 1's `ignored` array, possibly trimmed).
   - Reviewer warnings that didn't block but are worth surfacing.
   - The Stage 4 report verdict.

2. Print a summary to the user:
   ```
   ✅ Ported: <N> decls
   ⏭ Ignored (not needed in iris-lean): <M> decls
   ⏳ Left missing (deferred — depends on unported items): <P> decls
   ⚠ Warnings (review at leisure): <K>
   📁 File: <LEAN_FILE relative path>
   🔀 Worktree: <WORKTREE>
   🌱 Branch: claude/port-<BASE>

   Next steps:
   - Inspect the diff: `git -C <WORKTREE> diff master`
   - Run the full porting checker: `cd <WORKTREE> && python3 scripts/check_porting.py --format html -o /tmp/port-<BASE>.html && open /tmp/port-<BASE>.html`
   - The <P> "left missing" decls will appear under `missing` in the report — they get picked up automatically once their dependencies are ported.
   - When happy, merge: `cd <LEAN_REPO_ROOT> && git merge --squash claude/port-<BASE>` (or open a PR).
   ```

3. Do **not** commit, push, open a PR, or remove the worktree without explicit user approval. The orchestrator stops at "ready to commit".

## Failure modes & escalation

| Stage | Failure | Action |
|---|---|---|
| 0 | path validation fails | Error to user, suggest correction |
| 0 | `LEAN_FILE` exists | Ask user whether to overwrite |
| 0 | baseline `lake build` fails | Abort, tell user the tree is broken pre-port |
| 1 | agent returns `"build": "fail"` after 1 attempt | Escalate to user with the error |
| 2 | merged report has `fail` after 3 revision rounds | Escalate to user with the consolidated issue list |
| 3 | agent returns `"verdict": "blocked"` | Escalate to user with `blocked_proofs` |
| 3.5 | `/lean4:golf` breaks the build (internal golf bug, not Stage 3's fault) | Abort pipeline with the golf log; user investigates |
| 4 | either reviewer returns `"revise"` after 3 rounds | Escalate to user |
| 4 | either reviewer returns `"escalate"` | Escalate to user immediately |

Escalation = stop the pipeline, write the current state to `$WORKTREE/docs/port-$BASE.md`, and report to the user with concrete next-step suggestions.

## Constraints on the orchestrator (you, when running this skill)

- **Never** modify the agent definition files mid-run. They're versioned.
- **Never** suppress agent output stderr (`2>/dev/null` etc).
- **Never** auto-merge, auto-push, or auto-PR. Stop at "ready to commit".
- **Never** skip Stage 2 even if Stage 1 looks obviously correct. The crosscheck is the user's redundancy guarantee.
- **Never** spawn the two Stage-2 reviewers sequentially. They must run in parallel (single message, two `Agent` calls) so each has fresh context.
- **Never** spawn the two Stage-4 reviewers sequentially. They cover orthogonal axes (correctness vs concision); both must run in parallel so each has fresh context.
- **Always** invoke `/lean4:golf` via the `Skill` tool at Stage 3.5 — never delegate it to one of the porter agents. The porter agents' Edit budget should not be spent on what the golf skill already does mechanically and safely.
- **Always** include the `STAGE1_REPORT` / `STAGE2_REPORT` / `STAGE3_REPORT` / `STAGE3_5_REPORT` verbatim in downstream agent prompts. They're the agents' only window into prior stages.
- If the user asks to "skip Stage 2", "skip Stage 3.5", or "skip Stage 4", refuse and explain why these gates exist.
