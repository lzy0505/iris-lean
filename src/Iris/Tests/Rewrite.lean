/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI
import Iris.Std.Rewrite
import Iris.Instances.Classical

/-!
# Examples of the `rw'` Tactic

This file demonstrates how to use the `rw'` tactic for rewriting under separation logic
operators. Unlike Lean's built-in `rewrite`, `rw'` works with:
- Entailment (`⊢`) relations (the primary use case)
- Operators that have registered `@[rw_mono_rule]` monotonicity rules

## Key Features
- `rw' [h]` — apply rewrite rule `h` exactly once
- `rw' [←h]` — apply `h` in reverse direction
- `rw' [!h]` — apply `h` as many times as possible (use sparingly)

## Currently Registered Mono Rules
The following operators have `@[rw_mono_rule]` registered:
- `∧` (and): `and_mono`, `and_congr`
- `∨` (or): `or_mono`, `or_congr`
- `→` (imp): `imp_mono`, `imp_congr`
- `∀` (forall): `forall_mono`, `forall_congr`
- `∃` (exists): `exists_mono`, `exists_congr`
- `∗` (sep): `sep_mono`, `sep_congr`
- `-∗` (wand): `wand_mono`, `wand_congr`
- `∗-∗` (wandIff): `wandIff_congr`
- `<pers>` (persistently): `persistently_mono`
- `<affine>`: `affinely_mono`, `affinely_congr`
- `<absorb>`: `absorbingly_mono`, `absorbingly_congr`

## How It Works
The `rw'` tactic uses:
1. **Transitivity**: splits `A ⊢ C` into `A ⊢ B` and `B ⊢ C`
2. **Monotonicity rules**: descends into operators to find the rewrite site
3. **Reflexivity**: closes unchanged subgoals

This allows rewriting with entailments, not just equalities.
-/

namespace Iris.Examples
open Iris.BI Iris.Instances.Classical

-- Use a concrete BI instance (HeapProp) for these examples
-- The `rw'` tactic requires `Preorder` instances for `trans` and `refl`
variable {Val : Type} {P P' Q Q' R R' S : HeapProp Val} {Φ Ψ : α → HeapProp Val}

/-! ## Basic Rewriting with Entailment

The standard `rewrite` tactic only works with equalities. `rw'` can rewrite
using entailment hypotheses under operators with monotonicity rules.
-/

-- Rewrite P to R inside a conjunction
example (h : P ⊢ R) : P ∧ Q ⊢ R ∧ Q := by
  rw' [h]

-- Rewrite in the right operand
example (h : Q ⊢ R) : P ∧ Q ⊢ P ∧ R := by
  rw' [h]

-- Rewrite inside separating conjunction (∗)
example (h : P ⊢ R) : P ∗ Q ⊢ R ∗ Q := by
  rw' [h]

-- Rewrite in the right operand of sep
example (h : Q ⊢ R) : P ∗ Q ⊢ P ∗ R := by
  rw' [h]

-- Rewrite inside disjunction
example (h : P ⊢ R) : P ∨ Q ⊢ R ∨ Q := by
  rw' [h]

/-! ## Rewriting with Bi-entailment

Bi-entailment (`⊣⊢`) hypotheses can be used for rewriting in either direction.
Use `←` for reverse direction.
-/

-- Forward direction of bi-entailment
example (h : P ⊣⊢ R) : P ∧ Q ⊢ R ∧ Q := by
  rw' [h]

-- Reverse direction using ←
example (h : P ⊣⊢ R) : R ∧ Q ⊢ P ∧ Q := by
  rw' [←h]

-- Bi-entailment goal with bi-entailment hypothesis
example (h : P ⊣⊢ R) : P ∧ Q ⊣⊢ R ∧ Q := by
  rw' [h]

example (h : Q ⊣⊢ R) (h' : P ⊢ Q) : P ⊢ R := by
  rw' [←h]
  exact h'

-- This correctly fails: h : R ⊣⊢ Q, ←h means replace Q with R, but there's no Q in goal P ⊢ R
-- Uncommenting the following would cause a build error:
-- example (h : R ⊣⊢ Q) (h' : P ⊢ Q) : P ⊢ R := by
--   rw' [←h]  -- fails: no Q to replace
--   exact h'
-- Verify it fails using fail_if_success:
example (h : R ⊣⊢ Q) (h' : P ⊢ Q) : P ⊢ R := by
  fail_if_success rw' [←h]
  -- Use the correct approach instead:
  rw' [h]
  exact h'

-- Correct way: use rw' [h] to replace R with Q on the RHS
example (h : R ⊣⊢ Q) (h' : P ⊢ Q) : P ⊢ R := by
  rw' [h]  -- replaces R with Q, goal becomes P ⊢ Q
  exact h'



/-! ## Nested Rewriting

`rw'` descends into nested structures using monotonicity rules.
-/

-- Rewrite deep inside nested conjunctions
example (h : P ⊢ R) : (P ∧ Q) ∧ S ⊢ (R ∧ Q) ∧ S := by
  rw' [h]

-- Rewrite inside nested sep
example (h : P ⊢ R) : (P ∗ Q) ∗ S ⊢ (R ∗ Q) ∗ S := by
  rw' [h]

-- Mixed operators: rewrite inside sep under conjunction
example (h : P ⊢ R) : (P ∗ Q) ∧ S ⊢ (R ∗ Q) ∧ S := by
  rw' [h]

-- Deeply nested
example (h : P ⊢ R) : ((P ∧ Q) ∗ S) ∧ P' ⊢ ((R ∧ Q) ∗ S) ∧ P' := by
  rw' [h]

/-! ## Rewriting under Modalities

`rw'` works with modalities that have monotonicity rules registered.
-/

-- Rewrite under persistently modality
example (h : P ⊢ R) : □ P ⊢ □ R := by
  rw' [h]

-- Persistently inside other operators
example (h : P ⊢ R) : □ P ∧ Q ⊢ □ R ∧ Q := by
  rw' [h]

example (h : P ⊢ R) : □ P ∗ Q ⊢ □ R ∗ Q := by
  rw' [h]

/-! ## Rewriting under Quantifiers

Quantifiers also support rewriting via their monotonicity rules.
Note: The hypothesis must be universally quantified over all indices.
-/

-- Rewrite under universal quantifier
example (h : ∀ a, Φ a ⊢ Ψ a) : (∀ a, Φ a ⊢ Ψ a) := by
  intros a
  rw' [h]

-- Rewrite under existential quantifier
example (h : ∀ a, Φ a ⊢ Ψ a) : (∃ a, Φ a) ⊢ (∃ a, Ψ a) := by
  rw' [h]

-- Quantifier inside other operators
example (h : ∀ a, Φ a ⊢ Ψ a) : (∀ a, Φ a) ∧ Q ⊢ (∀ a, Ψ a) ∧ Q := by
  rw' [h]

/-! ## Rewriting in Wand (Magic Wand)

The wand operator `-∗` is contravariant in its left argument.
This means the direction of rewriting is reversed for the antecedent.
-/

-- Rewrite the consequent (right side) of wand - covariant
example (h : P ⊢ R) : (Q -∗ P) ⊢ (Q -∗ R) := by
  rw' [h]

-- Rewrite the antecedent (left side) - contravariant!
-- If Q ⊢ R, then (R -∗ P) ⊢ (Q -∗ P) (weaker antecedent = stronger wand)
example (h : Q ⊢ R) : (R -∗ P) ⊢ (Q -∗ P) := by
  rw' [h]

-- Wand inside other operators
example (h : P ⊢ R) : (Q -∗ P) ∗ S ⊢ (Q -∗ R) ∗ S := by
  rw' [h]

/-! ## Multiple Rewrites

Chain multiple rewrite rules in sequence.
-/

-- Apply two rewrites in sequence
example (h1 : P ⊢ P') (h2 : Q ⊢ Q') : P ∧ Q ⊢ P' ∧ Q' := by
  rw' [h1, h2]

-- Three rewrites
example (h1 : P ⊢ P') (h2 : Q ⊢ Q') (h3 : R ⊢ R') : P ∧ Q ∧ R ⊢ P' ∧ Q' ∧ R' := by
  rw' [h1, h2, h3]

-- Mix of sep and and
example (h1 : P ⊢ P') (h2 : Q ⊢ Q') : P ∗ Q ⊢ P' ∗ Q' := by
  rw' [h1, h2]

/-! ## Comparison with Standard `rewrite`

Standard `rewrite` only works with `=` or `↔`, not with `⊢`.
-/

-- This requires rw', not rewrite
-- `rewrite [h]` would fail because h : P ⊢ R, not P = R
example (h : P ⊢ R) : P ∗ Q ⊢ R ∗ Q := by
  rw' [h]

/-! ## Practical Examples

More realistic examples combining `rw'` with other reasoning.
-/

-- Weaken a precondition then apply a lemma
example (weaken : P' ⊢ P) (main : P ∗ Q ⊢ R) : P' ∗ Q ⊢ R := by
  rw' [weaken]
  exact main

-- Strengthen a postcondition
example (main : P ⊢ R) (strengthen : R ⊢ R') : P ⊢ R' := by
  rw' [←strengthen]
  exact main

-- Chain reasoning: first rewrite, then apply lemma
example (h1 : P ⊢ P') (h2 : P' ∗ Q ⊢ R) : P ∗ Q ⊢ R := by
  rw' [h1]
  exact h2

-- Frame rule pattern: add context around a rewrite
example (h : P ⊢ P') : P ∗ Q ∗ R ⊢ P' ∗ Q ∗ R := by
  rw' [h]

-- Nested modalities
example (h : P ⊢ Q) : □ (P ∗ R) ⊢ □ (Q ∗ R) := by
  rw' [h]

-- Working with wand and frames
example (h : P ⊢ Q) : (R -∗ P) ⊢ (R -∗ Q) := by
  rw' [h]

end Iris.Examples
