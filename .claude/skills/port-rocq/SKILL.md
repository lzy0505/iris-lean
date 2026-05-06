---
name: port-rocq
description: Port one Iris-Rocq .v file to iris-lean using a four-stage agent pipeline. Use when the user asks to port a Rocq Iris file to Lean (e.g. "port iris/algebra/frac.v"), or invokes /port-rocq. Spawns rocq-port-defs (Stage 1), two parallel rocq-review-defs runs (Stage 2 crosscheck), rocq-port-proofs (Stage 3), and rocq-review-proofs (Stage 4 final gate). Enforces every ported decl has @[rocq_alias], no sorries/axioms in the final output, lake build clean, and zero stale aliases via scripts/check_porting.py.
---

# Port one Iris-Rocq file to iris-lean

> **Code quality is paramount.** A port is not "done" when it compiles — it is done when both correctness and style reviewers approve. **Every suggestion from the proof and def reviewers must be addressed.** None are advisory; none are skipped. A `warn` and a `fail` are both feedback the porter has to handle.
>
> Address feedback in two passes when natural:
> 1. **Correctness first.** Loop until the def-reviewer (Stage 2) and proof-reviewer's correctness checks (Stage 4a — build, axioms, ignores, stale aliases, tactic-name correctness) all pass.
> 2. **Style second.** Then loop until *every* style-reviewer suggestion (Stage 4b — length ratio, term-vs-tactic, intermediate `have`s, oversized terms, one idea per line, case-split inflation, redundant `show`, inline comments, docstring register, architectural taste, naming, header authors) is also addressed.
>
> Do not declare the pipeline successful until both rounds reach `approve`. The final reviewer's verdict on a `warn`-laden output is `revise`, not `approve` — `warn`s have to be cleaned up just like `fail`s, even if the orchestrator's loop budget would otherwise let them slide.

> **Self-improvement directive.** The user is keenly interested in improving this workflow. If you encounter commands that are repeatedly difficult or repeatedly need approval, sub-agents that behave contrary to your expectations, prompts that are misleading or contradict observed behaviour, or you find yourself wishing for an additional tool that's not on the allowlist, **present the user with a self-improvement suggestion** at a natural pause in the work (typically: at the end of a stage, in the final summary, or immediately when the friction blocks progress). Surface the friction concretely — what command/agent/prompt failed, what you tried, what would have been easier — so the user can fix the root cause rather than guess. This applies to every agent and every stage; reviewers can also surface meta-suggestions about porter behaviour, and porters can surface them about reviewers.

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
                │ STRICT: both `approve` AND both issues arrays empty → continue
                ▼ ANY issue from EITHER reviewer → loop back to Stage 1 (cap 5 rounds)
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

**Search tools.** Agents use `mcp__lean-lsp__lean_loogle` for type-pattern queries (covers iris-lean + Mathlib + Batteries, unrate-limited) and `mcp__lean-lsp__lean_local_search` in place of `Grep` for any Lean-side lookup. `Grep` is reserved for non-Lean files (Rocq `.v`, configs, scripts). If `mcp__lean-lsp__lean_loogle` returns an error indicating the underlying Loogle service is unreachable, surface that to the user — the orchestrator does not own that infrastructure.

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

- For each headline field (`alias_coverage`, `alias_qualified`, `alias_dupes`, `stale`, `ignore_justified`, `instance_kind`, `stmt_equivalence`, `binder_shape`, `instance_args`, `notation`, `def_extensional`, `naming`, `tactic_names`):
  - If both report `pass` → merged is `pass`.
  - If either reports `fail` → merged is `fail`.
  - If one reports `pass` and the other `warn` → merged is `warn`.
  - If both `warn` → merged is `warn`.
- For `issues`: take the **union**. If both reviewers flagged the same `decl + check`, deduplicate by keeping the more specific message.
- **Surface disagreements**: if the two reviewers disagree on whether a particular check passes, include both verdicts in the consolidated feedback so the Stage-1 porter sees both perspectives. Add a synthetic issue: `{"decl": "<scope>", "check": "<check>", "msg": "DISAGREEMENT: reviewer A says <X>, reviewer B says <Y>. Treating as fail. Apply the stricter interpretation."}`.

**Gate to Stage 3 — strict.** Proceed to Stage 3 **only if both reviewers returned `approve` AND the merged `issues` array is empty**. There is no "good enough" state at this gate:

- Either reviewer reports `revise` → loop back to Stage 1 with the merged issues as `REVISION_FEEDBACK`.
- Either reviewer reports `approve` but with non-empty `issues` (i.e. `warn`-level findings) → loop back to Stage 1 with those issues as `REVISION_FEEDBACK`. A `warn` is still a suggestion the porter must address.
- Any merged headline is `fail` or `warn` → loop back to Stage 1.
- Any disagreement between the two reviewers (one says OK, the other flags) → loop back to Stage 1 (apply the stricter interpretation).

Only when **both reviewers' verdicts are `approve` AND both reviewers' `issues` arrays are empty AND every merged headline is `pass`** does the orchestrator proceed to Stage 3.

Cap at 5 revision rounds at this gate. After the fifth failure, escalate to the user with the merged report and the full revision history. The bar is intentionally high: definitions and lemma statements are the leverage point — a wrong statement at this stage cascades into wasted Stage-3 effort and a likely re-port. Better to spend the rounds here.

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

**Coverage pre-check (style reviewer only).** Before merging, validate that `rocq-review-style`'s report includes a `coverage` block with `rules_checked == rules_total` (i.e. it walked every HOUSE_STYLE.md rule, including `N/A` rows). If `rules_checked < rules_total`, **the report is incomplete** — re-run the style reviewer once with explicit feedback that under-coverage was detected. If the second run is also under-covered, escalate to the user (the agent prompt is broken or the model is short-circuiting; either way the orchestrator can't paper over it). Do not merge an incomplete report; doing so would let style violations slip through.

**Merging the two reports** (after coverage validation passes):

- For each headline check field, take the per-reviewer verdict as-is (the two reviewers' fields don't overlap).
- For `issues`, take the **union**. Both `fail` and `warn` issues count — both must be addressed.
- Compute the merged `verdict`:
  - **`approve`** — both reviewers return `approve` AND the union of `issues` is empty. A reviewer that returns `approve` with non-empty issues is reporting `warn`-level findings; those still need to be addressed before the pipeline finishes.
  - **`revise`** — either returns `revise`, OR either returns `approve` with non-empty `issues` (warn-only), and neither returns `escalate`. Loop back to Stage 3 with the merged issue list as `REVISION_FEEDBACK`. The first revise round should focus on **correctness** issues (any from `rocq-review-proofs`); subsequent rounds clean up the **style** issues (from `rocq-review-style`). The Stage-3 porter should prioritize accordingly.
  - **`escalate`** — either returns `escalate`. Hand to the user with both reports. Do not retry.

**Two-pass loop policy:**
- **Pass 1 (correctness):** Loop until `rocq-review-proofs` returns `approve` with empty issues. Cap at 3 rounds. Style issues from `rocq-review-style` are *carried forward* — not lost — but not the primary target of this pass.
- **Pass 2 (style):** Once correctness is settled, loop until `rocq-review-style` returns `approve` with empty issues. Cap at 3 rounds. Each Stage-3 invocation in this pass focuses purely on the style feedback; the porter must not regress any correctness check.
- If pass 2's revisions break a correctness check (regression), drop back to pass 1 once, then resume pass 2.
- If after 6 total rounds (3 + 3) any reviewer still has open issues, escalate to the user with both reports and the full revision history.

This is non-negotiable: a port with unaddressed `warn` findings is not finished. The user's quality bar is "address every reviewer suggestion" — the orchestrator enforces it, not the agents on their own.

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

3. **Aggregate self-improvement suggestions.** Collect every `self_improvement` entry from the porter reports (Stage 1, Stage 3) and every `issues` entry with `"check": "meta"` from the reviewer reports (Stage 2 ×2, Stage 4 ×2). If the aggregate is non-empty, append a section to the user summary:
   ```
   🔧 Workflow suggestions (from agents):
   - <stage>: <suggestion>
   - ...
   ```
   These are friction reports — concrete pain points the agents hit during the run. Do not edit, condense, or filter them; the user will read them directly and tune the prompts / settings / tools accordingly. If the aggregate is empty, omit the section entirely (don't print "no suggestions" — that's noise).

4. Do **not** commit, push, open a PR, or remove the worktree without explicit user approval. The orchestrator stops at "ready to commit".

## Failure modes & escalation

| Stage | Failure | Action |
|---|---|---|
| 0 | path validation fails | Error to user, suggest correction |
| 0 | `LEAN_FILE` exists | Ask user whether to overwrite |
| 0 | baseline `lake build` fails | Abort, tell user the tree is broken pre-port |
| 1 | agent returns `"build": "fail"` after 1 attempt | Escalate to user with the error |
| 2 | gate not met after 5 revision rounds (any issue from either reviewer, not just `fail`) | Escalate to user with the consolidated issue list |
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
