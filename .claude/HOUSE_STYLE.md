# House Style Rules

Style rules for iris-lean. The Stage-4b style reviewer (and, by extension, every porter agent) checks code against every entry below.

The structure is **four principles** (P1–P4); each principle owns a body of concrete sub-rules. Some sub-rules are **review rubrics** (R-prefix) — quantified acceptance criteria with explicit `pass`/`warn`/`fail` tables. Others are plain prescriptions. The reviewer maintains a worksheet enumerating every sub-rule and visits each one for every file under review.

When an iris-lean neighbour-file pattern conflicts with a sub-rule, **principle P1 governs**: cosmetic sub-rules can be softened by a clear local pattern, but the principles themselves and the rubrics (R-prefix) cannot.

---

## P1 — Match existing repository style

The ideal code is indistinguishable from neighbour files in the same folder. iris-lean has its own register that supersedes generic mathlib conventions; calibrate to what's already there before judging the new file.

This principle owns the surface-form sub-rules — naming, formatting, documentation, header — where the "right answer" is whatever the surrounding files already do.

### Naming

P1.1. **Mathlib casing convention.** Types/Props/classes: `UpperCamelCase` (`structure Foo`, `class Bar`). Theorems (terms of `Prop`): `snake_case` (`op_congr_left`, `later_true`). Other terms of `Type` (functions, defs): `lowerCamelCase` (`toFun`, `transpAp`). When an `UpperCamelCase` name appears inside a `snake_case` name, demote it to `lowerCamelCase` (`map_natCast`, not `map_NatCast`).

P1.2. **Mathlib morphism conventions.** `_left`/`_right` not `_l`/`_r`. `map_` prefix for morphism fields (`f_ne` → `map_ne`, `homomorphism` → `map_op`). Rearrangement lemmas: `op_op_op_comm`, `op_left_comm`.

P1.3. **Suffix conventions.** `_equiv` for `≡`, `_dist` for `≡{n}≡`, `_of_forall_equiv` or `_pointwise` for pointwise variants.

P1.4. **The `_N` suffix denotes step-indexed variants.** A theorem ending in `_dist` in Rocq aliases as a Lean theorem ending in `N` (`Cinl_inj_dist` → `inl_injN`). The `@[rocq_alias]` argument preserves the Rocq spelling; the Lean identifier follows iris-lean convention.

P1.5. **Theorem names describe what they prove**, with the primary subject as a namespace or prefix.

P1.6. **Theorem names are unambiguous.** `singleton_map_ne` → `singleton_map_none` (it returns `none`; "ne" suggests inequality).

P1.7. **Drop redundant type prefixes from constructor names.** `Excl.exclInvalid` → `Excl.invalid`. The namespace already provides context.

P1.8. **Names reflect the abstraction they capture.** `HeapOF` → `PartialMapOF` if it works for any `PartialMap`.

P1.9. **Greek letters for type variables.** `α`, `β`, `γ` not `A`, `B`, `C`. Domain-specific names (`PROP`, `M`, `K`, `V`) are fine.

P1.10. **Theorem names are fully snake_case.** Even when referring to a type with `UpperCamelCase`. `later_True` → `later_true`.

### R12. Local hypothesis naming

Local hypothesis names (`have`, `let`, `intro` patterns) match neighbour-file convention. iris-lean tends to use lowercase `h…` (`hP`, `hPQ`, `hΨ`) rather than `H1`, `H2`, `Hk`. Inconsistent prefix is a `warn`.

### Variable and scope management

P1.11. **Consolidate adjacent `variable` declarations** that share scope into one.

P1.12. **Merge `open` statements.** `open OFE Iris.Std` not separate lines.

P1.13. **Open namespaces to eliminate qualified names.** Then remove all now-redundant qualifiers throughout the file. A qualified name should remain only when the unqualified form would shadow or cause ambiguity.

P1.14. **`namespace` for namespaced definitions; `section` only for variable scoping.** Use `namespace` when definitions should be addressable as `Foo.bar`. Use `section` only to scope `variable` blocks without introducing a namespace.

P1.15. **`section Hom` / `end Hom`** for `variable` blocks that apply to a subset of theorems.

P1.16. **Notation lives inside namespaces.** Don't leave notation floating between `end Foo` and a new section.

P1.17. **Never use `omit`.** Restructure variable scoping so `omit` is unnecessary.

P1.18. **Function parameters belong in signatures, not in `variable`.** `variable` is for shared context across many declarations; actual function arguments belong on each declaration.

P1.19. **Open the namespace once per file.** Don't split a single namespace across multiple `namespace Foo ... end Foo` blocks separated by other code, and don't wrap a portion of it in a redundant `section foo`.

### Class and instance design

P1.20. **Eliminate `haveI`/`letI` for inferrable instances.** Use `attribute [instance]`, `variable`, or restructure so typeclass resolution handles it.

P1.21. **Instance arguments enable dot notation.** `[H : MonoidHomomorphism ...]` lets the user write `H.map_unit`, `H.map_op`.

P1.22. **Element-level predicates as `class`, not `def`.** `class DiscreteE ... : Prop where discrete : ...` enables `[DiscreteE x]` and `.discrete`.

P1.23. **`instance ... where` for typeclass derivations.** Not `theorem ... : Foo := ...`.

P1.24. **`where` syntax for simple instances.** Not `⟨...⟩` and not `by refine { ... }`.

P1.25. **Inline CMRA/typeclass field definitions.** Don't define a separate `@[simp] def Foo.pcore` just to plug it into an instance. Exception: `Valid`, `Equiv`, `Dist` that need `@[simp]` independently.

P1.26. **Drop redundant binders in instance fields.** `assoc := by simp` not `assoc {x y z} := by simp`.

P1.27. **Extract base classes — don't duplicate.** Shared definitions belong in the base class. Remove duplicates from subclasses.

P1.28. **Remove duplicate notation/instances inherited from parent classes.**

P1.29. **Skip Rocq instances that would just be `inferInstance` in Lean.** Mark them with `#rocq_ignore` (justified per the porter's ignore policy: the iris-lean replacement is typeclass synthesis itself).

P1.30. **Lowercase field-helpers.** Helper definitions that supply the body of a typeclass instance field (e.g. `valid`, `validN`, `pcore`, `op` for the CMRA `Valid`/`ValidN`/`pcore`/`op` fields) are conventionally lowercase, not PascalCase. PascalCase is for types and namespaces.

### Implicit arguments

P1.31. **Class fields use implicit binders** when arguments are inferrable. `op_assoc : ∀ {a b c}, ...` not `∀ a b c, ...`.

P1.32. **Hypothesis parameters use implicit binders** when inferrable. `(h : ∀ {i x}, l[i]? = some x → ...)` not `(h : ∀ i x, ...)`.

P1.33. **Function arguments are implicit when inferrable.** `{Φ Ψ : K → V → M}` not `(Φ Ψ : K → V → M)` when determined by other arguments.

P1.34. **Don't re-bind variables already in scope.** If `{p : Bool}` is in a `variable` block, don't repeat `{p}` in theorem signatures.

P1.35. **Drop inferrable named arguments from type ascriptions.** When `ExclAuthR (F := F) (A := A)` has inferrable named args, drop them: `ExclAuthR (F := F)`.

P1.36. **Narrow type ascription scope to the minimum subexpression** needed for inference. `(●E a : ExclAuthR (F := F)) • ◯E b` not `((●E a : ExclAuthR (F := F)) • ◯E b : ...)`.

P1.37. **Delete inferrable implicit arguments from theorem signatures.** Prefer `theorem foo : ...` over `theorem foo {a b : A} : ...` when `a` and `b` can be inferred from the conclusion. (iris-lean differs from mathlib here.)

### Formatting

P1.38. **No double blank lines.** At most one blank line between definitions.

P1.39. **No stray whitespace.** No double spaces within code, no trailing whitespace.

P1.40. **Space before `:=`.** `def foo : T :=` not `def foo : T:=`.

P1.41. **No leading space after `⟨`.** `⟨foo, bar⟩` not `⟨ foo, bar⟩`.

P1.42. **Line width ~100 chars.** Wrap signatures with 4-space continuation indent.

P1.43. **Declaration ordering within a namespace.** Definitions, then notation/syntax, then law classes, then theorems.

P1.44. **Unicode `→` over ASCII `->`.** Always.

P1.45. **Named hypotheses before the colon.** `theorem foo (h : H) : P` not `theorem foo : H → P := fun h =>`. Applies to explicit (especially `Prop`-valued) hypotheses; inferrable implicits should be deleted per P1.37.

P1.46. **`:=` at the end of the signature line.** Proof body indented below.

### Documentation

P1.47. **No Rocq-mirroring prose in docstrings or comments.** Don't write "Corresponds to Rocq's `bi.foo_lemma`", "This is the Lean port of `Definition foo` from `frac.v`", or any inline `--` comment that paraphrases what the Rocq source said about a decl. The Rocq↔Lean mapping is recorded by `@[rocq_alias <rocq.name>]` on the decl itself — that *is* the documentation of correspondence. Docstrings and comments describe what the Lean code does, in Lean terms, for a Lean reader who has never seen the Rocq source.

P1.48. **No `abbrev` aliases for Rocq names.** Use `@[rocq_alias]`.

P1.49. **Delete commented-out code.** Version control preserves history.

P1.50. **No `set_option` warning suppressions.**

P1.51. **No stale comments.** Abandoned design notes, restated code, and empty section labels all go.

P1.52. **Docstrings on notation-enabling instances.** A short docstring explaining what `∅`, `⊆`, `∪`, `\`, `∈` etc. the instance enables.

P1.53. **Section headers use `/-! ## Title -/`** not plain `/- Title -/`.

P1.54. **Wrap docstrings at ~100 chars.** Same line width as code.

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

### R13. Header authors

The `Authors:` line in the copyright block:
- **Pass** if it contains a real name or the literal placeholder `TODO: fill in author`.
- **Fail** if it contains: `iris-lean contributors`, `Anonymous`, `Claude`, `AI`, or any other generic / made-up author. The porter must not invent authorship — the human owner of the PR fills it in.

---

## P2 — One line, one idea

Each line expresses one rewrite, one application, one case split, or one named intermediate. Don't splice tactics together with semicolons artificially. Acceptable chaining: parallel branches under `<;>` (`cases x <;> rfl`), short term-mode compositions where each piece is a named lemma, or a `simp only [<short list>]`.

P2.1. **Multiple rewrites in a single `rw`.** `rw [foo, bar]` not separate `rw` calls.

P2.2. **Collapse identical branches with `<;>`.** DRY within proofs.

P2.3. **`<;>` over case-by-case bashing.** When several proofs share the same shape, `cases x <;> cases y <;> first | t₁ | t₂ | t₃` beats `cases x with | A => ... | B => ... | C => ...`. The case-by-case form belongs only when each branch needs genuinely different handling.

P2.4. **Compress `intro`/`apply`/`intro` chains.** `refine fun n => f fun k => ?_`.

### R6. One idea per line

Scan for lines that pack multiple distinct steps:
- Two or more semicolon-separated tactics that are *not* under a `<;>` parallel branch and where the tactics are different operations (e.g. `simp [foo]; rw [bar]; exact baz` is three ideas).
- A `simp`/`rw` rewrite chained with a closing tactic (`simp; exact foo`) where `simp` is doing real work. One-liners like `cases x <;> rfl` or `(lem.mp h).symm` are fine.
- Long term-mode chains where one `.trans`/`.mp`/`.mpr` step is composed with two or more transformations (`(h.symm.trans foo.mp).bar` — three ideas pretending to be one).

Each violation is a `warn`. ≥ 3 violations in a single proof body escalate to `fail`.

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

---

## P3 — Predictable tactic outcome

Prefer `refine` to `apply`. `refine` makes the resulting goal-shape explicit at the call site; `apply` leaves the reader to mentally reconstruct what unification produced. Same goes for `simp only` over broad mid-proof `simp`, and named lemmas over `omega`/`decide`/`grind` for goals that aren't genuinely arithmetic / decidable / hammer-territory.

P3.1. **Term-mode over tactic-mode** when branches are short. `match l with | .nil => .rfl | .cons _ _ => ...`.

P3.2. **Convert trivial tactic proofs to term-mode.** `by exact H` → `H`, `by rfl` → `rfl`.

P3.3. **Dot notation everywhere applicable.** `.rfl`, `.symm`, `.trans`, `.nil`, `.cons`. Also `H.dist` over `equiv_dist.mp H _`, `(IH H).le` over `Dist.le (IH ...) ...`.

P3.4. **Pipe chains.** `op_congr_right (..) |>.trans op_assoc.symm` reads cleaner than nested parentheses.

P3.5. **`refine .trans ?_ rhs`** over `apply flip Dist.trans rhs`.

P3.6. **`exact` not `apply` when no goals remain.**

P3.7. **`..` for inferrable arguments.** `exact (foo ..)` not `exact (foo f g _ _)`.

P3.8. **`simpa` and `grind`** over multi-step `simp` + closer patterns.

P3.9. **`suffices` over `rw [show ... from ...]`.** `suffices H : goal by rwa [...]` separates the rewrite from the proof of the simplified statement.

P3.10. **`[DecidableEq K]` over `open Classical in`** when branching on equality.

P3.11. **No unnecessary parentheses in tactic arguments.** `rcases get? a x` not `rcases (get? a x)`.

P3.12. **Remove redundant outer parentheses in theorem signatures.** `✓{n} (●E a : T) • ◯E a` not `(✓{n} ((●E a : T) • ◯E a))` when precedence makes grouping clear.

P3.13. **`next` over `rename_i`.** `next h => ...` not `· rename_i h; ...`.

P3.14. **Structured `induction ... with`** over bare `induction` + `rename_i`.

P3.15. **`rintro` to combine intro and case split.** `rintro (_|i)` not `intro i; cases i`.

P3.16. **`rintro ⟨a, rfl⟩`** to substitute equalities immediately.

P3.17. **`·.casesOn` over `Bool.rec`.** `p.casesOn .rfl foo` not `Bool.rec .rfl foo p`.

P3.18. **`.symm` on arguments over `_mpr` lemmas.** `foo_mp h.symm` rather than separate `foo_mpr`.

P3.19. **`obtain` over `rcases` for simple destructuring.** `obtain _|x' := expr` not `rcases expr with _|x'`.

P3.20. **`Option.map` over `<$>`** in algebraic contexts. `(pcore x).map f` not `f <$> pcore x`.

P3.21. **`@[elab_as_elim]`** on custom induction principles.

P3.22. **No `@[simp]` on predicates/type definitions** that shouldn't auto-unfold.

P3.23. **Delete trivial extensionality/congruence lemmas** that just wrap `congrArg`/`funext`.

### R3. Predictable outcome

Scan for tactics whose effect is opaque without running the elaborator:

- **`apply` vs `refine`.** `apply` is acceptable when the residual is a single straightforward goal. Flag `apply` whose use produces multiple residuals or where signature-load is required to predict residuals. Heuristic: `apply f` followed by ≥ 2 separate tactic blocks at the same nesting level is suspect — `refine`-territory.
- **Broad mid-proof `simp`.** `simp [<long list>]` mid-proof is opaque. Acceptable: `simp only [<list>]` (narrower), terminal `simp`, `simp` after a clearly-named structural step.
- **`omega` / `decide` / `grind` on non-numeric / non-decidable / non-large goals.**

Each unjustified `apply` is a `warn`; ≥ 3 in one proof escalates to `fail`. Mid-proof broad `simp` is a `warn`. Misapplied `omega`/`decide`/`grind` is a `warn`.

### R8. Redundant `show`

For each `show <type>`:
- **Acceptable**: the goal is a non-trivial reduction of the term that follows, and `show` performs the reduction so the next tactic can see it.
- **Not acceptable**: `show <type>` immediately before `exact <term>` where `<term>` already has type `<type>`. Pure padding.
- **Not acceptable**: a sequence of two or more `show` lines giving different views of the same goal.

Each unjustified `show` is a `warn`; ≥ 2 in one proof escalate to `fail`.

### R9. Inline comments in proofs

iris-lean proof bodies are nearly comment-free. Inline comments inside a `:= by` block are a code smell — they suggest the proof is opaque enough to need explanation, which is itself the problem. Threshold: zero inline proof comments in a typical algebra/BI port. Acceptable: `--` directly above a `theorem`/`def` declaration as a docstring-like blurb. Anything inside a `by` block or between `:=` and the term body is a `warn`.

**Rocq-mirroring comments are a hard `fail`** (per P1.47). An inline comment that paraphrases the Rocq source's prose — `-- in Rocq this is `bi.foo_lemma``, `-- this corresponds to the `apply` step in `Lemma frac_op``, `-- following the Rocq proof, we now case-split` — is forbidden regardless of where it appears. The `@[rocq_alias]` attribute is the place to record correspondence; the comment is redundant noise that ties the Lean reader to a Rocq source they may not have. Flag every such hit individually.

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

---

## P4 — Minimize `have`s; prefer backwards reasoning

Lead with `refine` / `calc` / `exact <named lemma>` so each line states what we're trying to prove next. Use `have` only when an intermediate is reused two or more times, or when its name aids readability of a structurally complex term.

P4.1. **Reduce `have` bindings — prefer backwards reasoning.** Inline single-use `have`s. Use `apply`/`refine` chains over forward `have` chains.

P4.2. **`have` not `let` for proof bindings in tactic mode.** In term-mode, `let` is fine for sharing subexpressions.

P4.3. **Hoist shared computations out of case splits.** Same `have` in multiple branches → move it before the `cases`.

P4.4. **Extract a `private theorem` when a proof shape repeats.** If the same multi-step ritual (e.g. `simp [pcore] at h; obtain ⟨a, ha, hcx⟩ := h; subst hcx`) appears in three or more proofs, hoist it. The helper is local, well-typed, and pays for itself after two uses.

### R4. Intermediate `have`s

**4.1 — gratuitous single-use `have`s.** A `have` whose body is short (≤ ~30 chars), uneventful (no nested dot-chain or function-application chain), and used exactly once is a candidate for inlining. Each such trivially-inlineable single-use `have` is a `warn`. Multiple in one proof escalate to `fail`. Single-use `have`s with longer or structurally non-trivial expressions are fine.

**4.2 — forwards-heavy proofs.** A proof with ≥ 3 `have h_i := …` lines feeding into a single closing tactic is forwards reasoning — reads bottom-up. Restructure as `calc` / `refine` with holes. `warn` even when each individual `have` is locally justified — the *shape* is wrong. Don't flag if the underlying lemmas genuinely need to be assembled forwards (e.g. matching against a concrete data structure layer by layer).
