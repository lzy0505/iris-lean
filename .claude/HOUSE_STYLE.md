---
name: House style rules
description: Complete house style rules for iris-lean, organized by category — naming, implicits, scoping, class design, proof style, formatting, documentation.
---

# House Style Rules

## Naming

1. **Mathlib casing convention.** Types/Props/classes: `UpperCamelCase` (`structure Foo`, `class Bar`). Theorems (terms of `Prop`): `snake_case` (`op_congr_left`, `later_true`). Other terms of `Type` (functions, defs): `lowerCamelCase` (`toFun`, `transpAp`). When an `UpperCamelCase` name appears inside a `snake_case` name, use `lowerCamelCase` (`map_natCast` not `map_NatCast`).

2. **Mathlib naming conventions.** `_left`/`_right` not `_l`/`_r`. `map_` prefix for morphism fields (`f_ne` → `map_ne`, `homomorphism` → `map_op`). Rearrangement lemmas: `op_op_op_comm`, `op_left_comm`.

3. **Suffix conventions.** `_equiv` for `≡`, `_dist` for `≡{n}≡`, `_of_forall_equiv` or `_pointwise` for pointwise variants.

4. **Theorems named per mathlib conventions.** The theorem name should describe what it proves, with the primary subject as a namespace or prefix.

5. **Short constructor names — drop type prefix.** `Excl.exclInvalid` → `Excl.invalid`. The namespace provides context.

7. **Names reflect the abstraction.** `HeapOF` → `PartialMapOF` when it works for any `PartialMap`.

8. **Unambiguous theorem names.** `singleton_map_ne` → `singleton_map_none` (it returns `none`, not "not equal").

9. **Greek letters for type variables.** `α`, `β`, `γ` not `A`, `B`, `C`. Domain-specific names (`PROP`, `M`, `K`, `V`) are fine.

10. **Type names in theorem names are lowercase.** `later_True` → `later_true`. Theorems are fully snake_case.

## Implicit Arguments

11. **Implicit binders in class fields** when arguments are inferrable. `op_assoc : ∀ {a b c}, ...` not `∀ a b c, ...`.

12. **Implicit binders in hypothesis parameters.** `(h : ∀ {i x}, l[i]? = some x → ...)` not `(h : ∀ i x, ...)`.

13. **Function arguments implicit when inferrable.** `{Φ Ψ : K → V → M}` not `(Φ Ψ : K → V → M)` when determined by other args.

14. **Don't re-bind variables already in scope.** If `{p : Bool}` is in a `variable` block, don't repeat `{p}` in theorem signatures.

15. **Remove inferrable named arguments from type ascriptions.** When `ExclAuthR (F := F) (A := A)` has inferrable named args, drop them: `ExclAuthR (F := F)`. Extends rule 13 to ascriptions in expression bodies.

16. **Narrow type ascription scope.** Ascribe the minimal subexpression needed for inference. `(●E a : ExclAuthR (F := F)) • ◯E b` not `((●E a : ExclAuthR (F := F)) • ◯E b : ...)`.

## Variable & Scope Management

15. **Consolidate `variable` declarations.** Merge adjacent `variable` lines into one when they share scope.

16. **Merge `open` statements.** `open OFE Iris.Std` not separate lines.

17. **Open namespaces to eliminate qualified names.** Then remove all now-redundant qualifiers.

18. **`section` vs `namespace`.** Use `namespace` when definitions should be namespaced (`Foo.bar`). Use `section` only for scoping variables without a namespace.

19. **Sections to scope variables.** `section Hom` / `end Hom` for variable blocks that apply to a subset of theorems.

20. **Notation inside namespaces.** Don't leave notation floating between `end Foo` and a new section.

21. **Never use `omit`.** Restructure variable scoping so `omit` is unnecessary.

22. **Explicit function parameters over `variable (x)`.** `variable` is for shared context; actual function arguments belong in signatures.

## Class & Instance Design

23. **Eliminate `haveI`/`letI` for inferrable instances.** Use `attribute [instance]`, `variable`, or restructure so typeclass resolution handles it.

24. **Instance arguments for structures.** `[H : MonoidHomomorphism ...]` enables dot notation: `H.map_unit`, `H.map_op`.

25. **Element-level predicates as `class`, not `def`.** `class DiscreteE ... : Prop where discrete : ...` enables `[DiscreteE x]` and `.discrete`.

26. **`instance ... where` for typeclass derivations.** Not `theorem ... : Foo := ...`.

27. **`where` syntax for simple instances.** Not `⟨...⟩` or `by refine { ... }`.

28. **Inline CMRA/typeclass field definitions.** Don't define separate `@[simp] def Foo.pcore` just to plug into an instance. Exception: `Valid`, `Equiv`, `Dist` that need `@[simp]` independently.

29. **Drop redundant binders in instance fields.** `assoc := by simp` not `assoc {x y z} := by simp`.

30. **Extract base classes — don't duplicate.** Shared definitions belong in the base class. Remove duplicates from subclasses.

31. **Remove duplicate notation/instances** inherited from parent classes.

## Proof Style

32. **Term-mode over tactic-mode** when branches are short. `match l with | .nil => .rfl | .cons _ _ => ...`.

33. **Dot notation.** `.rfl`, `.symm`, `.trans`, `.nil`, `.cons`. Also `H.dist` over `equiv_dist.mp H _`, `(IH H).le` over `Dist.le (IH ...) ...`.

34. **Pipe chains.** `op_congr_right (..) |>.trans op_assoc.symm`.

35. **`simpa` and `grind`** over multi-step simp+closer patterns.

36. **Prefer `suffices` over `rw [show ... from ...]`.** Use `suffices H : goal by rwa [...]` instead of `rw [show X = Y from proof, ...]`. Separates the rewrite from the proof of the simplified statement.

36. **`[DecidableEq K]` over `open Classical in`** when branching on equality.

37. **Reduce `have` bindings — prefer backwards reasoning.** Inline single-use `have`s. Use `apply`/`refine` chains over forward `have` chains.

38. **No unnecessary parentheses in tactic arguments.** `rcases get? a x` not `rcases (get? a x)`.

39. **Remove redundant outer parentheses in theorem signatures.** `✓{n} (●E a : T) • ◯E a` not `(✓{n} ((●E a : T) • ◯E a))` when precedence makes grouping clear.

39. **`refine .trans ?_ rhs`** over `apply flip Dist.trans rhs`.

40. **Compress `intro`/`apply`/`intro`.** `refine fun n => f fun k => ?_`.

41. **`exact` not `apply` when no goals remain.**

42. **Prefer `..` for inferrable arguments.** `exact (foo ..)` not `exact (foo f g _ _)`.

43. **`next` over `rename_i`.** `next h => ...` not `· rename_i h; ...`.

44. **Structured `induction ... with`** over bare `induction` + `rename_i`.

45. **`rintro` to combine intro and case split.** `rintro (_|i)` not `intro i; cases i`.

46. **`rintro ⟨a, rfl⟩`** to substitute equalities immediately.

47. **`·.casesOn` over `Bool.rec`.** `p.casesOn .rfl foo` not `Bool.rec .rfl foo p`.

48. **`.symm` on arguments over `_mpr` lemmas.** `foo_mp h.symm` not separate `foo_mpr`.

49. **Collapse identical branches with `<;>`.** DRY within proofs.

50. **`obtain` over `rcases` for simple destructuring.** `obtain _|x' := expr` not `rcases expr with _|x'`.

51. **`Option.map` over `<$>`** in algebraic contexts. `(pcore x).map f` not `f <$> pcore x`.

52. **Convert trivial tactic proofs to term.** `by exact H` → `H`. `by rfl` → `rfl`.

53. **`have` not `let` for proof bindings in tactic mode.** In term-mode, `let` is fine for binding shared subexpressions (see STYLE_EXTENSIONS §9).

54. **Hoist shared computations out of case splits.** Same `have` in multiple branches → move before `cases`.

55. **`@[elab_as_elim]`** on custom induction principles.

56. **No `@[simp]` on predicates/type definitions** that shouldn't auto-unfold.

57. **Delete trivial extensionality/congruence lemmas** that just wrap `congrArg`/`funext`.

58. **Unicode `→` over ASCII `->`.** Always.

59. **Named hypotheses before the colon.** `theorem foo (h : H) : P` not `theorem foo : H → P := fun h =>`. This applies to explicit (especially `Prop`-valued) hypotheses — use judgment. Inferrable implicit arguments should be deleted per STYLE_EXTENSIONS §8.

60. **`:=` at end of signature line.** Proof body indented below.

3. Multiple rewrites in a single `rw`
`rw [foo, bar]` is preferred over separate `rw` calls.

5. Open namespaces to shorten proofs
Open relevant namespaces to eliminate verbose qualified names. After opening, remove all newly-redundant qualifiers. A qualified name should only remain when the unqualified form would shadow or cause ambiguity.

6. Eliminate `haveI`
Restructure proofs to avoid `haveI := ha` — use instance arguments, `@`, or reorganize.

8. Delete inferrable implicit arguments
Prefer `theorem foo : ...` over `theorem foo {a b : A} : ...` when `a` and `b` can be inferred. We differ from mathlib here.

9. Term-mode vs tactic proofs
Prefer term-mode for clean one-liners. Use tactic mode when destructuring or rewriting is needed. Do not force term-mode if it duplicates subexpressions — use `let` to bind shared terms.

10. Drop `inferInstance` instances
Do not port Rocq instances whose Lean proof would be just `inferInstance`.
Create a `rocq_ignore` for them.

## Formatting

61. **No double blank lines.** At most one blank line between definitions.

62. **No stray whitespace.** No double spaces within code, no trailing whitespace.

63. **Space before `:=`.** `def foo : T :=` not `def foo : T:=`.

64. **No leading space after `⟨`.** `⟨foo, bar⟩` not `⟨ foo, bar⟩`.

65. **Line width ~100 chars.** Wrap signatures with 4-space continuation indent.

66. **Declaration ordering.** Within a namespace: definitions, notation/syntax, law classes, theorems.

## Documentation

67. **No "Corresponds to Rocq's ..." in docstrings.** Describe behavior in Lean terms. Use `rocq_alias` for Rocq name mapping.

68. **No `abbrev` aliases for Rocq names.** Use `rocq_alias`.

69. **Delete commented-out code.** Version control preserves history.

71. **No `set_option` warning suppressions.** 

72. **No stale comments** — abandoned design notes, restated code, empty section labels.

73. **Docstrings on notation-enabling instances.** Short docstring explaining what `∅`, `⊆`, `∪`, `\`, `∈` etc. they enable.

74. **Section headers use `/-! ## Title -/`** not plain `/- Title -/`.

75. **Wrap docstrings at ~100 chars.** Same line width as code.

## Guiding principles (apply to every rule)

These four overarching principles inform the rubrics below; when a borderline call needs adjudication, fall back to whichever applies most directly.

P1. **Match existing repository style.** The ideal code is indistinguishable from neighbour files in the same folder. iris-lean has its own register that supersedes generic mathlib conventions; calibrate to what's already there before judging the new file.

P2. **One line, one idea.** Each line expresses one rewrite, one application, one case split, or one named intermediate. Don't splice tactics together with semicolons artificially. Acceptable chaining: parallel branches under `<;>` (`cases x <;> rfl`), short term-mode compositions where each piece is a named lemma, or a `simp only [<short list>]`.

P3. **Every tactic's outcome should be easily predictable.** Prefer `refine` to `apply`. `refine` makes the resulting goal-shape explicit at the call site; `apply` leaves the reader to mentally reconstruct what unification produced. Same goes for `simp only` over broad mid-proof `simp`, and named lemmas over `omega`/`decide`/`grind` for goals that aren't genuinely arithmetic / decidable / large.

P4. **Minimize `have`s; prefer backwards reasoning.** Lead with `refine` / `calc` / `exact <named lemma>` so each line states what we're trying to prove next. Use `have` only when an intermediate is reused two or more times, or when its name aids readability of a structurally complex term.

## Stage-3 (porter) review rubrics

These are the rules a reviewer applies during Stage-4b style review of a freshly-ported file. They quantify (where possible) the principles and earlier rules so reviews are reproducible. Each rule has a `pass` / `warn` / `fail` split — `warn` is "the porter should fix this in the next round", `fail` is "the porter must fix this".

### R1. Length ratio

Per ported theorem/instance, count `R` = Rocq proof line count (between `Proof.` and `Qed.`/`Defined.`, exclusive), `L` = Lean proof line count. Compute `L / R`.

| Ratio | Verdict |
|---|---|
| `L ≤ R` | `pass` |
| `R < L ≤ 2R` | `pass` (some structural translation overhead is fine) |
| `2R < L ≤ 3R` | `warn` — flag as "verbose, consider compressing" |
| `L > 3R` | `fail` — flag with concrete suggestions |

Trivial Rocq proofs (`Proof. done. Qed.`, `Proof. by simpl. Qed.`, single-tactic): the Lean side should be a term-mode `:= rfl` / `:= Iff.rfl` / `:= ⟨...⟩` etc. — not a `by simp` block. `R = 1` with multi-line Lean `by` block is a `fail` regardless of ratio.

### R2. Term-mode vs tactic-mode

For Rocq proofs that are pure term-mode (`Proof. apply foo, lem. Qed.`, `Proof. exact foo. Qed.`, `Proof. done. Qed.`), the Lean port should be term-mode `:= ...` not `:= by exact ...` / `:= by apply ...`. Each `:= by exact|apply|trivial|simp <single arg>` whose Rocq counterpart was term-mode is a `warn`.

### R3. Predictable outcome (operationalizes P3)

Scan for tactics whose effect is opaque without running the elaborator:

- **`apply` vs `refine`.** `apply` is acceptable when the residual is a single straightforward goal. Flag `apply` whose use produces multiple residuals or where signature-load is required to predict residuals. Heuristic: `apply f` followed by ≥ 2 separate tactic blocks at the same nesting level is suspect — `refine`-territory.
- **Broad `simp` mid-proof.** `simp [<long list>]` mid-proof is opaque about which lemma did the work. Acceptable: `simp only [<list>]` (narrower), terminal `simp`, `simp` after a clearly-named structural step.
- **`omega` / `decide` / `grind` on non-numeric / non-decidable / non-large goals.**

Each unjustified `apply` is a `warn`; ≥ 3 in one proof escalates to `fail`. Mid-proof broad `simp` is a `warn`. Misapplied `omega`/`decide`/`grind` is a `warn`.

### R4. Intermediate `have`s (operationalizes P4)

**4.1 — gratuitous single-use `have`s.** A `have` whose body is short (≤ ~30 chars), uneventful (no nested dot-chain or function-application chain), and used exactly once is a candidate for inlining. Each such trivially-inlineable single-use `have` is a `warn`. Multiple in one proof escalate to `fail`. Single-use `have`s with longer or structurally non-trivial expressions are fine.

**4.2 — forwards-heavy proofs.** A proof with ≥ 3 `have h_i := …` lines feeding into a single closing tactic is forwards reasoning — reads bottom-up. Restructure as `calc` / `refine` with holes. `warn` even when each individual `have` is locally justified — the *shape* is wrong. Don't flag if the underlying lemmas genuinely need to be assembled forwards (e.g. matching against a concrete data structure layer by layer).

### R5. Oversized term

Per proof body:
- **Max single-line term width.**
- **Max dot-chain depth.** (Length of the longest `a.foo.bar.baz` or `(...).trans (...).mp (...).symm` chain.)

| Metric | Threshold | Verdict |
|---|---|---|
| Line ≤ 80 chars | | `pass` |
| Line 81–120 chars | | `warn` |
| Line > 120 chars | | `fail` |
| Dot-chain ≤ 2 | | `pass` |
| Dot-chain = 3 | | `warn` |
| Dot-chain ≥ 4 | | `fail` |

Suggestion: name an intermediate with `have`, switch to `calc` for entailment chains, or hoist a recurring sub-proof to `private theorem`.

### R6. One idea per line (operationalizes P2)

Scan for lines that pack multiple distinct steps:
- Two or more semicolon-separated tactics that are *not* under a `<;>` parallel branch and where the tactics are different operations (e.g. `simp [foo]; rw [bar]; exact baz` is three ideas).
- A `simp`/`rw` rewrite chained with a closing tactic (`simp; exact foo`) where `simp` is doing real work. One-liners like `cases x <;> rfl` or `(lem.mp h).symm` are fine.
- Long term-mode chains where one `.trans`/`.mp`/`.mpr` step is composed with two or more transformations (`(h.symm.trans foo.mp).bar` — three ideas pretending to be one).

Each violation is a `warn`. ≥ 3 violations in a single proof body escalate to `fail`.

### R7. Case-split inflation

A Lean port should not perform substantially more case analysis than its Rocq counterpart.
- `R_splits` = count of `destruct`, `case`, `induction`, `inversion`, `discriminate` in Rocq.
- `L_splits` = count of `cases`, `rcases`, `obtain`, `match … with`, `induction`, `split`, `icases` in Lean. (Don't count `<;> cases` parallel bursts as separate splits if they share an arm.)

| Ratio | Verdict |
|---|---|
| `L_splits ≤ R_splits + 1` | `pass` (one extra is fine — Lean often case-analyses an `Option` where Rocq used a tactic) |
| `R_splits + 1 < L_splits ≤ 2 · max(R_splits, 1) + 1` | `warn` |
| more | `fail` — "look for an iris-lean lemma that packages this case analysis; the Rocq proof discharged it with `apply foo` instead of splitting" |

### R8. Redundant `show`

For each `show <type>`:
- **Acceptable**: the goal is a non-trivial reduction of the term that follows, and `show` performs the reduction so the next tactic can see it.
- **Not acceptable**: `show <type>` immediately before `exact <term>` where `<term>` already has type `<type>`. Pure padding.
- **Not acceptable**: a sequence of two or more `show` lines giving different views of the same goal.

Each unjustified `show` is a `warn`; ≥ 2 in one proof escalate to `fail`.

### R9. Inline comments in proofs

Iris-lean proof bodies are nearly comment-free. Inline comments inside a `:= by` block are a code smell — they suggest the proof is opaque enough to need explanation, which is itself the problem. Threshold: zero inline proof comments in a typical algebra/BI port. Acceptable: `--` directly above a `theorem`/`def` declaration as a docstring-like blurb. Anything inside a `by` block or between `:=` and the term body is a `warn`.

### R10. Module docstring register

The module `/-! ... -/` docstring should describe the *concept* the file formalizes, not the porting story. **Fail** if it contains:

- "Port of …", "alternative port", "parallel port", "ported from".
- "We deviate from / differ from / depart from the Rocq version".
- Justifications like "iris-lean does not currently provide X, so we abstract over Y".
- Self-explaining commentary on Stage-1 ignore decisions.

**Pass** if the docstring talks about the mathematical / logical concept (what a *user* of the file needs to know).

### R11. Architectural taste (soft check — `warn` only)

- File introduced a typeclass named after itself (e.g. `Frac2.Param`) when neighbours use abstraction-named typeclasses (e.g. `Fraction`)? `warn`: "consider renaming the abstraction class to reflect the concept, not the file".
- File hand-rolled a wrapper `structure` + `instance : COFE ...` when `LeibnizO` (or another existing primitive) would have done it? Check with `mcp__lean-lsp__lean_local_search` for `LeibnizO`. `warn`: "consider replacing the custom carrier with `LeibnizO α`".
- File ships an abstract typeclass with no concrete instance? `warn`: "consider providing at least one concrete instance to demonstrate inhabitation".

These are *judgement* warnings — don't block on them, but surface so the user can re-evaluate.

### R12. Local naming conventions

Local hypothesis names (`have`, `let`, `intro` patterns) should match neighbour-file convention. iris-lean tends to use lowercase `h…` (`hP`, `hPQ`, `hΨ`) rather than `H1`, `H2`, `Hk`. Inconsistent prefix is a `warn`. (This is separate from the def-stage theorem-name check.)

### R13. Header authors

The `Authors:` line in the copyright block:
- **Pass** if it contains a real name or the literal placeholder `TODO: fill in author`.
- **Fail** if it contains: `iris-lean contributors`, `Anonymous`, `Claude`, `AI`, or any other generic / made-up author. The porter must not invent authorship — the human owner of the PR fills it in.
