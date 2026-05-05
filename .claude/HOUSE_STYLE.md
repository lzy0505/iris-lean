# House Style Rules

Style rules for iris-lean. The Stage-4b style reviewer (and, by extension, every porter agent) checks code against every entry below. The structure is:

- **Principles P1–P4** — overarching guidance. When a numbered rule is silent or ambiguous, fall back to whichever principle most directly applies.
- **Numbered rules** — concrete style decisions, organized by category.
- **Stage-3 review rubrics R1–R13** — quantified acceptance criteria for ported proofs.

Within each category, rules are intended to be exhaustive, not illustrative. The reviewer maintains a worksheet enumerating every entry and visits each one for every file.

## Guiding principles

P1. **Match existing repository style.** The ideal code is indistinguishable from neighbour files in the same folder. iris-lean has its own register that supersedes generic mathlib conventions; calibrate to what's already there before judging the new file. Cosmetic rules below can be softened by a clear local pattern; principles P1–P4 and rubrics R1–R13 cannot.

P2. **One line, one idea.** Each line expresses one rewrite, one application, one case split, or one named intermediate. Don't splice tactics together with semicolons artificially. Acceptable chaining: parallel branches under `<;>` (`cases x <;> rfl`), short term-mode compositions where each piece is a named lemma, or a `simp only [<short list>]`.

P3. **Every tactic's outcome should be easily predictable.** Prefer `refine` to `apply`. `refine` makes the resulting goal-shape explicit at the call site; `apply` leaves the reader to mentally reconstruct what unification produced. Same goes for `simp only` over broad mid-proof `simp`, and named lemmas over `omega`/`decide`/`grind` for goals that aren't genuinely arithmetic / decidable / hammer-territory.

P4. **Minimize `have`s; prefer backwards reasoning.** Lead with `refine` / `calc` / `exact <named lemma>` so each line states what we're trying to prove next. Use `have` only when an intermediate is reused two or more times, or when its name aids readability of a structurally complex term.

## Naming

1. **Mathlib casing convention.** Types/Props/classes: `UpperCamelCase` (`structure Foo`, `class Bar`). Theorems (terms of `Prop`): `snake_case` (`op_congr_left`, `later_true`). Other terms of `Type` (functions, defs): `lowerCamelCase` (`toFun`, `transpAp`). When an `UpperCamelCase` name appears inside a `snake_case` name, demote it to `lowerCamelCase` (`map_natCast`, not `map_NatCast`).

2. **Mathlib morphism conventions.** `_left`/`_right` not `_l`/`_r`. `map_` prefix for morphism fields (`f_ne` → `map_ne`, `homomorphism` → `map_op`). Rearrangement lemmas: `op_op_op_comm`, `op_left_comm`.

3. **Suffix conventions.** `_equiv` for `≡`, `_dist` for `≡{n}≡`, `_of_forall_equiv` or `_pointwise` for pointwise variants.

4. **Theorem names describe what they prove.** With the primary subject as a namespace or prefix.

5. **Drop redundant type prefixes from constructor names.** `Excl.exclInvalid` → `Excl.invalid`. The namespace already provides context.

6. **Names reflect the abstraction they capture.** `HeapOF` → `PartialMapOF` if it works for any `PartialMap`.

7. **Theorem names are unambiguous.** `singleton_map_ne` → `singleton_map_none` (it returns `none`; "ne" suggests inequality).

8. **Greek letters for type variables.** `α`, `β`, `γ` not `A`, `B`, `C`. Domain-specific names (`PROP`, `M`, `K`, `V`) are fine.

9. **Theorem names are fully snake_case.** Even when referring to a type with `UpperCamelCase`. `later_True` → `later_true`.

10. **The `_N` suffix denotes step-indexed variants.** A theorem ending in `_dist` in Rocq aliases as a Lean theorem ending in `N` (`Cinl_inj_dist` → `inl_injN`). The `@[rocq_alias]` argument preserves the Rocq spelling; the Lean identifier follows iris-lean convention.

## Implicit arguments

11. **Class fields use implicit binders** when arguments are inferrable. `op_assoc : ∀ {a b c}, ...` not `∀ a b c, ...`.

12. **Hypothesis parameters use implicit binders** when inferrable. `(h : ∀ {i x}, l[i]? = some x → ...)` not `(h : ∀ i x, ...)`.

13. **Function arguments are implicit when inferrable.** `{Φ Ψ : K → V → M}` not `(Φ Ψ : K → V → M)` when determined by other arguments.

14. **Don't re-bind variables already in scope.** If `{p : Bool}` is in a `variable` block, don't repeat `{p}` in theorem signatures.

15. **Drop inferrable named arguments from type ascriptions.** When `ExclAuthR (F := F) (A := A)` has inferrable named args, drop them: `ExclAuthR (F := F)`.

16. **Narrow type ascription scope to the minimum subexpression** needed for inference. `(●E a : ExclAuthR (F := F)) • ◯E b` not `((●E a : ExclAuthR (F := F)) • ◯E b : ...)`.

17. **Delete inferrable implicit arguments from theorem signatures.** Prefer `theorem foo : ...` over `theorem foo {a b : A} : ...` when `a` and `b` can be inferred from the conclusion. (iris-lean differs from mathlib here.)

## Variable and scope management

18. **Consolidate adjacent `variable` declarations** that share scope into one.

19. **Merge `open` statements.** `open OFE Iris.Std` not separate lines.

20. **Open namespaces to eliminate qualified names.** Then remove all now-redundant qualifiers throughout the file. A qualified name should remain only when the unqualified form would shadow or cause ambiguity.

21. **`namespace` for namespaced definitions; `section` only for variable scoping.** Use `namespace` when definitions should be addressable as `Foo.bar`. Use `section` only to scope `variable` blocks without introducing a namespace.

22. **`section Hom` / `end Hom`** for `variable` blocks that apply to a subset of theorems.

23. **Notation lives inside namespaces.** Don't leave notation floating between `end Foo` and a new section.

24. **Never use `omit`.** Restructure variable scoping so `omit` is unnecessary.

25. **Function parameters belong in signatures, not in `variable`.** `variable` is for shared context across many declarations; actual function arguments belong on each declaration.

26. **Open the namespace once per file.** Don't split a single namespace across multiple `namespace Foo ... end Foo` blocks separated by other code, and don't wrap a portion of it in a redundant `section foo`.

## Class and instance design

27. **Eliminate `haveI`/`letI` for inferrable instances.** Use `attribute [instance]`, `variable`, or restructure so typeclass resolution handles it.

28. **Instance arguments enable dot notation.** `[H : MonoidHomomorphism ...]` lets the user write `H.map_unit`, `H.map_op`.

29. **Element-level predicates as `class`, not `def`.** `class DiscreteE ... : Prop where discrete : ...` enables `[DiscreteE x]` and `.discrete`.

30. **`instance ... where` for typeclass derivations.** Not `theorem ... : Foo := ...`.

31. **`where` syntax for simple instances.** Not `⟨...⟩` and not `by refine { ... }`.

32. **Inline CMRA/typeclass field definitions.** Don't define a separate `@[simp] def Foo.pcore` just to plug it into an instance. Exception: `Valid`, `Equiv`, `Dist` that need `@[simp]` independently.

33. **Drop redundant binders in instance fields.** `assoc := by simp` not `assoc {x y z} := by simp`.

34. **Extract base classes — don't duplicate.** Shared definitions belong in the base class. Remove duplicates from subclasses.

35. **Remove duplicate notation/instances inherited from parent classes.**

36. **Skip Rocq instances that would just be `inferInstance` in Lean.** Mark them with `#rocq_ignore` (justified per the porter's ignore policy: the iris-lean replacement is typeclass synthesis itself).

37. **Lowercase field-helpers.** Helper definitions that supply the body of a typeclass instance field (e.g. `valid`, `validN`, `pcore`, `op` for the CMRA `Valid`/`ValidN`/`pcore`/`op` fields) are conventionally lowercase, not PascalCase. PascalCase is for types and namespaces.

## Proof style

38. **Term-mode over tactic-mode** when branches are short. `match l with | .nil => .rfl | .cons _ _ => ...`.

39. **Dot notation everywhere applicable.** `.rfl`, `.symm`, `.trans`, `.nil`, `.cons`. Also `H.dist` over `equiv_dist.mp H _`, `(IH H).le` over `Dist.le (IH ...) ...`.

40. **Pipe chains.** `op_congr_right (..) |>.trans op_assoc.symm` reads cleaner than nested parentheses.

41. **`simpa` and `grind`** over multi-step `simp` + closer patterns.

42. **`suffices` over `rw [show ... from ...]`.** `suffices H : goal by rwa [...]` separates the rewrite from the proof of the simplified statement.

43. **`[DecidableEq K]` over `open Classical in`** when branching on equality.

44. **No unnecessary parentheses in tactic arguments.** `rcases get? a x` not `rcases (get? a x)`.

45. **Remove redundant outer parentheses in theorem signatures.** `✓{n} (●E a : T) • ◯E a` not `(✓{n} ((●E a : T) • ◯E a))` when precedence makes grouping clear.

46. **`refine .trans ?_ rhs`** over `apply flip Dist.trans rhs`.

47. **Compress `intro`/`apply`/`intro` chains.** `refine fun n => f fun k => ?_`.

48. **`exact` not `apply` when no goals remain.**

49. **`..` for inferrable arguments.** `exact (foo ..)` not `exact (foo f g _ _)`.

50. **`next` over `rename_i`.** `next h => ...` not `· rename_i h; ...`.

51. **Structured `induction ... with`** over bare `induction` + `rename_i`.

52. **`rintro` to combine intro and case split.** `rintro (_|i)` not `intro i; cases i`.

53. **`rintro ⟨a, rfl⟩`** to substitute equalities immediately.

54. **`·.casesOn` over `Bool.rec`.** `p.casesOn .rfl foo` not `Bool.rec .rfl foo p`.

55. **`.symm` on arguments over `_mpr` lemmas.** `foo_mp h.symm` rather than separate `foo_mpr`.

56. **Collapse identical branches with `<;>`.** DRY within proofs.

57. **`obtain` over `rcases` for simple destructuring.** `obtain _|x' := expr` not `rcases expr with _|x'`.

58. **`Option.map` over `<$>`** in algebraic contexts. `(pcore x).map f` not `f <$> pcore x`.

59. **Convert trivial tactic proofs to term-mode.** `by exact H` → `H`, `by rfl` → `rfl`.

60. **`have` (not `let`) for proof bindings in tactic mode.** In term-mode, `let` is fine for sharing subexpressions.

61. **Hoist shared computations out of case splits.** Same `have` in multiple branches → move it before the `cases`.

62. **`@[elab_as_elim]`** on custom induction principles.

63. **No `@[simp]` on predicates/type definitions** that shouldn't auto-unfold.

64. **Delete trivial extensionality/congruence lemmas** that just wrap `congrArg`/`funext`.

65. **Unicode `→` over ASCII `->`.** Always.

66. **Named hypotheses before the colon.** `theorem foo (h : H) : P` not `theorem foo : H → P := fun h =>`. Applies to explicit (especially `Prop`-valued) hypotheses; inferrable implicits should be deleted per rule 17.

67. **`:=` at the end of the signature line.** Proof body indented below.

68. **Multiple rewrites in a single `rw`.** `rw [foo, bar]` not separate `rw` calls.

69. **`<;>` over case-by-case bashing.** When several proofs share the same shape, `cases x <;> cases y <;> first | t₁ | t₂ | t₃` beats `cases x with | A => ... | B => ... | C => ...`. The case-by-case form belongs only when each branch needs genuinely different handling.

70. **Extract a `private theorem` when a proof shape repeats.** If the same multi-step ritual (e.g. `simp [pcore] at h; obtain ⟨a, ha, hcx⟩ := h; subst hcx`) appears in three or more proofs, hoist it. The helper is local, well-typed, and pays for itself after two uses.

## Formatting

71. **No double blank lines.** At most one blank line between definitions.

72. **No stray whitespace.** No double spaces within code, no trailing whitespace.

73. **Space before `:=`.** `def foo : T :=` not `def foo : T:=`.

74. **No leading space after `⟨`.** `⟨foo, bar⟩` not `⟨ foo, bar⟩`.

75. **Line width ~100 chars.** Wrap signatures with 4-space continuation indent.

76. **Declaration ordering within a namespace.** Definitions, then notation/syntax, then law classes, then theorems.

## Documentation

77. **No "Corresponds to Rocq's ..." in docstrings.** Describe behavior in Lean terms; the `@[rocq_alias]` attribute records the Rocq mapping.

78. **No `abbrev` aliases for Rocq names.** Use `@[rocq_alias]`.

79. **Delete commented-out code.** Version control preserves history.

80. **No `set_option` warning suppressions.**

81. **No stale comments.** Abandoned design notes, restated code, and empty section labels all go.

82. **Docstrings on notation-enabling instances.** A short docstring explaining what `∅`, `⊆`, `∪`, `\`, `∈` etc. the instance enables.

83. **Section headers use `/-! ## Title -/`** not plain `/- Title -/`.

84. **Wrap docstrings at ~100 chars.** Same line width as code.

85. **Module docstrings describe concept, not porting story.** No "Port of …", "alternative port", "parallel port", "ported from", "we deviate from / differ from / depart from", or self-explaining commentary on Stage-1 ignore decisions.

86. **Authors line: real names or `TODO: fill in author`.** Generic placeholders (`iris-lean contributors`, `Anonymous`, `Claude`, `AI`) are forbidden; the human owner of the PR fills it in.

## Stage-3 review rubrics

These quantify the principles and per-rule expectations into reproducible acceptance criteria for a ported proof. Each rubric assigns a `pass` / `warn` / `fail` verdict; the reviewer aggregates them into the report.

### R1. Length ratio

Per ported theorem/instance, count `R` = Rocq proof line count (between `Proof.` and `Qed.`/`Defined.`, exclusive), `L` = Lean proof line count.

| Ratio | Verdict |
|---|---|
| `L ≤ R` | `pass` |
| `R < L ≤ 2R` | `pass` (some structural translation overhead is fine) |
| `2R < L ≤ 3R` | `warn` |
| `L > 3R` | `fail` |

Trivial Rocq proofs (`Proof. done. Qed.`, `Proof. by simpl. Qed.`, single-tactic): the Lean side should be a term-mode `:= rfl` / `:= Iff.rfl` / `:= ⟨...⟩` etc. — not a `by simp` block. `R = 1` with multi-line Lean `by` block is a `fail` regardless of ratio.

### R2. Term-mode vs tactic-mode

For Rocq proofs that are pure term-mode (`Proof. apply foo, lem. Qed.`, `Proof. exact foo. Qed.`, `Proof. done. Qed.`), the Lean port should be term-mode `:= ...` not `:= by exact ...` / `:= by apply ...`. Each `:= by exact|apply|trivial|simp <single arg>` whose Rocq counterpart was term-mode is a `warn`.

### R3. Predictable outcome (operationalizes P3)

Scan for tactics whose effect is opaque without running the elaborator:

- **`apply` vs `refine`.** `apply` is acceptable when the residual is a single straightforward goal. Flag `apply` whose use produces multiple residuals or where signature-load is required to predict residuals. Heuristic: `apply f` followed by ≥ 2 separate tactic blocks at the same nesting level is suspect — `refine`-territory.
- **Broad mid-proof `simp`.** `simp [<long list>]` mid-proof is opaque. Acceptable: `simp only [<list>]` (narrower), terminal `simp`, `simp` after a clearly-named structural step.
- **`omega` / `decide` / `grind` on non-numeric / non-decidable / non-large goals.**

Each unjustified `apply` is a `warn`; ≥ 3 in one proof escalates to `fail`. Mid-proof broad `simp` is a `warn`. Misapplied `omega`/`decide`/`grind` is a `warn`.

### R4. Intermediate `have`s (operationalizes P4)

**4.1 — gratuitous single-use `have`s.** A `have` whose body is short (≤ ~30 chars), uneventful (no nested dot-chain or function-application chain), and used exactly once is a candidate for inlining. Each such trivially-inlineable single-use `have` is a `warn`. Multiple in one proof escalate to `fail`. Single-use `have`s with longer or structurally non-trivial expressions are fine.

**4.2 — forwards-heavy proofs.** A proof with ≥ 3 `have h_i := …` lines feeding into a single closing tactic is forwards reasoning — reads bottom-up. Restructure as `calc` / `refine` with holes. `warn` even when each individual `have` is locally justified — the *shape* is wrong. Don't flag if the underlying lemmas genuinely need to be assembled forwards (e.g. matching against a concrete data structure layer by layer).

### R5. Oversized term

Per proof body:
- **Max single-line term width.**
- **Max dot-chain depth.** Length of the longest `a.foo.bar.baz` or `(...).trans (...).mp (...).symm` chain.

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
| more | `fail` |

Concrete suggestion: "look for an iris-lean lemma that packages this case analysis; the Rocq proof discharged it with `apply foo` instead of splitting".

### R8. Redundant `show`

For each `show <type>`:
- **Acceptable**: the goal is a non-trivial reduction of the term that follows, and `show` performs the reduction so the next tactic can see it.
- **Not acceptable**: `show <type>` immediately before `exact <term>` where `<term>` already has type `<type>`. Pure padding.
- **Not acceptable**: a sequence of two or more `show` lines giving different views of the same goal.

Each unjustified `show` is a `warn`; ≥ 2 in one proof escalate to `fail`.

### R9. Inline comments in proofs

iris-lean proof bodies are nearly comment-free. Inline comments inside a `:= by` block are a code smell — they suggest the proof is opaque enough to need explanation, which is itself the problem. Threshold: zero inline proof comments in a typical algebra/BI port. Acceptable: `--` directly above a `theorem`/`def` declaration as a docstring-like blurb. Anything inside a `by` block or between `:=` and the term body is a `warn`.

### R10. Module docstring register

The module `/-! ... -/` docstring should describe the *concept* the file formalizes, not the porting story. **Fail** if it contains:

- "Port of …", "alternative port", "parallel port", "ported from".
- "We deviate from / differ from / depart from the Rocq version".
- Justifications like "iris-lean does not currently provide X, so we abstract over Y".
- Self-explaining commentary on Stage-1 ignore decisions.

**Pass** if the docstring talks about the mathematical / logical concept (what a *user* of the file needs to know).

### R11. Architectural taste (soft check — `warn` only)

- File introduced a typeclass named after itself (e.g. `Frac2.Param`) when neighbours use abstraction-named typeclasses (e.g. `Fraction`)? `warn`: "consider renaming the abstraction class to reflect the concept, not the file".
- File hand-rolled a wrapper `structure` + `instance : COFE ...` when `LeibnizO` (or another existing primitive) would have done it? `warn`: "consider replacing the custom carrier with `LeibnizO α`".
- File ships an abstract typeclass with no concrete instance? `warn`: "consider providing at least one concrete instance to demonstrate inhabitation".

Judgement warnings — surface them, don't block on them.

### R12. Local naming conventions

Local hypothesis names (`have`, `let`, `intro` patterns) should match neighbour-file convention. iris-lean tends to use lowercase `h…` (`hP`, `hPQ`, `hΨ`) rather than `H1`, `H2`, `Hk`. Inconsistent prefix is a `warn`. (Separate from rule 9, which is about *theorem* names.)

### R13. Header authors

The `Authors:` line in the copyright block:
- **Pass** if it contains a real name or the literal placeholder `TODO: fill in author`.
- **Fail** if it contains: `iris-lean contributors`, `Anonymous`, `Claude`, `AI`, or any other generic / made-up author. The porter must not invent authorship — the human owner of the PR fills it in.
