# `/port-rocq` — Agentic Rocq → iris-lean porting

Four-stage pipeline that takes one Iris-Rocq `.v` file and produces a corresponding `.lean` file in iris-lean, with `@[rocq_alias]` annotations, no sorries, no new axioms, and a clean `lake build` + `scripts/check_porting.py`.

## Usage

```
/port-rocq <relative-path-under-iris-rocq>
```

For example:

```
/port-rocq iris/algebra/frac.v
/port-rocq iris/proofmode/ident_name.v
/port-rocq iris/bi/internal_eq.v
```

The path must live under `iris/{algebra,base_logic,bi,program_logic,proofmode,si_logic}/` in the local clone of iris-rocq (`/Users/zongyuan/code/iris-rocq/`).

## What it does

```
Stage 1 — rocq-port-defs
    ↓ (writes Lean file with sorry-stub theorems and rocq_alias annotations; lake build must pass)
Stage 2 — rocq-review-defs ‖ rocq-review-defs   (two parallel runs, same prompt)
    ↓ (orchestrator merges reports; loop to Stage 1 if any fail; cap 3 rounds)
Stage 3 — rocq-port-proofs
    ↓ (fills every sorry; no axioms; uses iris-lean IPM tactics)
Stage 3.5 — /lean4:golf <file>
    ↓ (auto-applies safe compressions: `apply f; exact h` → `exact f h`, `by exact t` → `t`, etc.)
Stage 4 — rocq-review-proofs ‖ rocq-review-style   (two parallel reviewers, orthogonal axes)
    ↓ (correctness gate + concision/style gate; loop to Stage 3 if either fails; cap 3 rounds)
✅ Done — file ready for human review and commit
```

## Files involved

```
.claude/
├── agents/
│   ├── rocq-port-defs.md       # Stage 1
│   ├── rocq-review-defs.md     # Stage 2 (run twice — same prompt, crosscheck)
│   ├── rocq-port-proofs.md     # Stage 3
│   ├── rocq-review-proofs.md   # Stage 4a — correctness gate
│   └── rocq-review-style.md    # Stage 4b — concision/style gate (parallel with 4a)
└── skills/
    └── port-rocq/
        ├── SKILL.md            # Orchestrator
        └── README.md           # This file
```

The skill is the entry point. The orchestrator (the main agent reading the skill) spawns the four agents in turn, merges Stage-2 reports for crosscheck, and surfaces the result to the user.

## Invariants enforced

1. `lake build` clean at every stage that allows it (after Stage 1: sorries OK; after Stage 3: zero sorries).
2. Every ported `def`/`theorem`/`instance` carries `@[rocq_alias <fully-qualified-rocq-name>]` (Module prefixes included, Section prefixes excluded — see `Iris/Iris/Std/RocqPorting.lean`).
3. **`#rocq_ignore` only for "not needed in iris-lean"** — Rocq-specific tactic/notation, redundant with iris-lean facility, subsumed by an existing lemma. Decls that depend on unported items are **left unmarked**; `scripts/check_porting.py` reports them as `missing` for later passes.
4. `python3 scripts/check_porting.py --format stale` shows zero stale aliases for the touched file.
5. **Zero `axiom` declarations introduced by the new file** (foundation axioms like `Classical.choice`, `Quot.sound`, `propext` transitively imported from elsewhere are fine; new ones are not).
6. Statements semantically equivalent to the Rocq originals, in iris-lean syntax.
7. Proofs use **iris-lean IPM tactic names** (lowercase-leading: `iintro`, `iapply`, `icases`, `imod`, `imodintro`, `inext`, `isplit`, `iexists`, `ihave`, `ispecialize`, `ileft`, `iright`, `iclear`, `irevert`, `irename`, `ipure`, `ipure_intro`, `iintuitionistic`, `ispatial`, `iexact`, `iassumption`, `iex_falso`, `iemp_intro`, `istart`, `istop`). Rocq-style PascalCase (`iIntros`, `iApply`, `iSplit`, `iModIntro`, `iDestruct`, ...) is a hard fail.
8. Two independent reviewer agents (Stage 2) crosscheck the alias correctness and statement equivalence; the orchestrator surfaces disagreements.
9. Stage 3.5 runs `/lean4:golf <file>` automatically — applies safe compression patterns (term-mode collapse, instant-win rewrites, optional lemma-replacement search) before reviewers see the file. Reverts on build failure.
10. Two parallel Stage-4 reviewers run on orthogonal axes:
    - `rocq-review-proofs` — correctness gate (build, axioms, stale aliases, anti-laziness).
    - `rocq-review-style` — concision/aesthetic gate (length ratio vs Rocq, term-vs-tactic mode, redundant `show`/`have`, inline comments, docstring register, header authors). Catches over-engineered or verbose proofs that compile but read worse than the original.

## Outputs

On success, the skill leaves you with:

- A new branch `claude/port-<basename>` in the iris-lean worktree.
- The ported `.lean` file.
- A summary doc at `docs/port-<basename>.md` listing what was ported, ignored, and any warnings.

The skill **does not** auto-commit, auto-push, or auto-merge. Inspect the diff, run any extra checks you want (`python3 scripts/check_porting.py --format html`), and merge / open a PR yourself.

## When things go wrong

| Symptom | Likely cause | What the orchestrator does |
|---|---|---|
| Stage 1 returns `"build": "fail"` | Wrong import path, missing folder, or new BI notation that the porter mis-handled | Stops; surfaces the build error |
| Stage 2 disagreement | One reviewer caught something subtle the other missed (e.g. Module prefix when nested) | Routes to Stage 1 with both perspectives in the feedback |
| Stage 2 fails 3 rounds | The porter can't satisfy the reviewers — usually means a genuine semantic difference between Rocq and iris-lean | Escalates to user |
| Stage 3 returns `"blocked"` | A specific proof can't be ported because the Rocq feature has no iris-lean analog | Escalates with the porter's notes — user decides between "redo with help" or "demote to `#rocq_ignore`" |
| Stage 4 returns `"escalate"` | Build broke, or `sorryAx` showed up in a transitive dep, or check_porting.py revealed an upstream regression | Stops; user investigates |

## Manual override

If you want to re-run only Stage 3+4 (because Stage 2 already approved the signatures and you only want to re-do the proofs), the agents can be invoked individually via the `Agent` tool — but this is not the supported path. The skill is the entry point; the agents are not standalone.

## Prerequisites

- **iris-loogle (local server)**: the agents' canonical type-pattern search. Index covers iris-lean + Mathlib + Batteries (built with the `Iris` module loaded), unrate-limited. Start it once with `cd /Users/zongyuan/code/iris-loogle && uv run server.py`. The orchestrator checks for it at pre-flight. If it's down, agents fall back to `Grep` over `Iris/Iris/`. Agents' tools allowlists deliberately exclude `mcp__lean-lsp__lean_loogle` (its index lacks iris-lean — wrong index for this workflow). `mcp__lean-lsp__lean_leansearch` and `mcp__lean-lsp__lean_leanfinder` remain available as rate-limited fallbacks for natural-language / semantic queries.

## Mathlib policy

iris-lean is intentionally light on Mathlib dependencies. Agents are told to **avoid Mathlib results when possible** and only reach for it when there's no iris-lean equivalent and the missing piece is genuinely necessary. When a self-contained Mathlib/Batteries lemma is necessary and importing the upstream module would be too heavy, it's acceptable to copy the lemma into `Iris/Iris/Std/` with a credit comment.

## See also

- `Iris/Iris/Std/RocqPorting.lean` — definitive docstring on `@[rocq_alias]`, `#rocq_ignore`, and Module-vs-Section name qualification.
- `scripts/README.md` — how `check_porting.py` works.
- `scripts/ROCQ_REVISION` — pinned upstream commit; agents validate against this.
- https://raw.githubusercontent.com/leanprover-community/iris-lean/refs/heads/master/Iris/tactics.md — canonical iris-lean IPM tactics doc. **Required reading for every agent.**
