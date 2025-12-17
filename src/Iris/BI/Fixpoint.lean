/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI

/-!
# Least and Greatest Fixpoints for Monotone Predicates

This file defines least and greatest fixpoints for monotone predicates within the Iris
separation logic framework, entirely inside the logic.

## Main Definitions

* `BiMonoPred F`: A typeclass requiring that a function `F : (A → PROP) → (A → PROP)` is
  monotone and non-expansive.
* `bi_least_fixpoint F x`: The least fixpoint, defined as the smallest predicate closed under `F`.
* `bi_greatest_fixpoint F x`: The greatest fixpoint, defined as the largest predicate containing
  fixpoints of `F`.

## Main Results

* `least_fixpoint_unfold`: The least fixpoint satisfies `bi_least_fixpoint F x ≡ F (bi_least_fixpoint F) x`.
* `least_fixpoint_iter`: Basic induction principle for least fixpoints.
* `least_fixpoint_ind`: Stronger induction allowing both the induction hypothesis and the fixpoint.
* `least_fixpoint_ind_wf`: Well-founded-style induction for arbitrary unfoldings.
* `greatest_fixpoint_unfold`: The greatest fixpoint satisfies the unfold equivalence.
* `greatest_fixpoint_coiter`: Basic coinduction principle for greatest fixpoints.
* `greatest_fixpoint_coind`: Stronger coinduction allowing proof of the original fixpoint after one step.
* `greatest_fixpoint_paco`: Parameterized coinduction for arbitrary unfoldings.

## References

This is a translation of the Coq/Rocq file `iris/bi/lib/fixpoint_mono.v` from the Iris project.
-/

namespace Iris.BI

open Iris OFE BI BIBase

variable {PROP : Type _} [BI PROP]
variable {A : Type _} [OFE A]

section Definitions

/-- A typeclass for monotone predicates over a BI.
    Requires that F is monotone and non-expansive. -/
class BiMonoPred (F : (A → PROP) → (A → PROP)) where
  bi_mono_pred (Φ Ψ : A → PROP) [NonExpansive Φ] [NonExpansive Ψ] :
    intuitionistically (BIBase.forall fun x : A => BIBase.wand (Φ x) (Ψ x)) ⊢
    BIBase.forall fun x : A => BIBase.wand (F Φ x) (F Ψ x)
  bi_mono_pred_ne (Φ : A → PROP) [NonExpansive Φ] : NonExpansive (F Φ)

attribute [instance] BiMonoPred.bi_mono_pred_ne

/-- The least fixpoint of a monotone predicate F.
    This is the smallest predicate closed under F. -/
def bi_least_fixpoint (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  iprop(∀ (Φ : A -n> PROP), □ (∀ (y : A), F Φ y -∗ Φ y) -∗ Φ x)

/-- The greatest fixpoint of a monotone predicate F.
    This is the largest predicate containing fixpoints of F. -/
def bi_greatest_fixpoint (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  iprop(∃ (Φ : A -n> PROP), □ (∀ (y : A), Φ y -∗ F Φ y) ∗ Φ x)

end Definitions

section LeastFixpoint

variable (F : (A → PROP) → (A → PROP)) [BiMonoPred F]

/-- Non-expansiveness of the least fixpoint in the inner variable -/
theorem least_fixpoint_ne' (H : ∀ Φ, NonExpansive Φ → NonExpansive (F Φ)) :
    NonExpansive (bi_least_fixpoint F) := by
  sorry

/-- The least fixpoint is proper with respect to equivalence -/
theorem least_fixpoint_proper :
    ∀ (F G : (A → PROP) → (A → PROP)),
    (∀ Φ x, F Φ x ≡ G Φ x) → ∀ x, bi_least_fixpoint F x ≡ bi_least_fixpoint G x := by
  sorry

/-- Folding direction: F applied to the least fixpoint entails the least fixpoint -/
theorem least_fixpoint_unfold_2 (x : A) :
    iprop(F (bi_least_fixpoint F) x ⊢ bi_least_fixpoint F x) := by
  sorry

/-- Unfolding direction: the least fixpoint entails F applied to it -/
theorem least_fixpoint_unfold_1 (x : A) :
    iprop(bi_least_fixpoint F x ⊢ F (bi_least_fixpoint F) x) := by
  sorry

/-- The least fixpoint satisfies the fixpoint equation -/
theorem least_fixpoint_unfold (x : A) :
    bi_least_fixpoint F x ≡ F (bi_least_fixpoint F) x := by
  sorry

/-- Basic induction principle for least fixpoints.
    To prove Φ holds for the least fixpoint, it suffices to show that
    F preserves Φ intuitionistically. -/
theorem least_fixpoint_iter (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), F Φ y -∗ Φ y) -∗ (∀ (x : A), bi_least_fixpoint F x -∗ Φ x)) := by
  sorry

/-- If F preserves affine predicates, then the least fixpoint is affine -/
theorem least_fixpoint_affine
    (H : ∀ x, Affine (F (fun _ => iprop(emp)) x)) :
    ∀ x, Affine (bi_least_fixpoint F x) := by
  sorry

/-- If F preserves absorbing predicates, then the least fixpoint is absorbing -/
theorem least_fixpoint_absorbing
    (H : ∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) :
    ∀ x, Absorbing (bi_least_fixpoint F x) := by
  sorry

/-- If F preserves both affine and persistent predicates,
    then the least fixpoint is persistent -/
theorem least_fixpoint_persistent_affine
    (H_affine : ∀ Φ, (∀ x, Affine (Φ x)) → (∀ x, Affine (F Φ x)))
    (H_pers : ∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x))) :
    ∀ x, Persistent (bi_least_fixpoint F x) := by
  sorry

/-- If F preserves both absorbing and persistent predicates,
    then the least fixpoint is persistent -/
theorem least_fixpoint_persistent_absorbing
    (H_absorb : ∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x)))
    (H_pers : ∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x))) :
    ∀ x, Persistent (bi_least_fixpoint F x) := by
  sorry

end LeastFixpoint

/-- Strong monotonicity for least fixpoints -/
theorem least_fixpoint_strong_mono
    (F : (A → PROP) → (A → PROP)) [BiMonoPred F]
    (G : (A → PROP) → (A → PROP)) [BiMonoPred G] :
    iprop(⊢ □ (∀ (Φ : A → PROP) (x : A), F Φ x -∗ G Φ x) -∗
            (∀ (x : A), bi_least_fixpoint F x -∗ bi_least_fixpoint G x)) := by
  sorry

section LeastFixpointInduction

variable (F : (A → PROP) → (A → PROP)) [BiMonoPred F]

/-- Well-founded induction principle for least fixpoints.
    Allows assuming the property holds for arbitrary many unfoldings. -/
theorem least_fixpoint_ind_wf (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), F (bi_least_fixpoint (fun Ψ a => iprop(Φ a ∧ F Ψ a))) y -∗ Φ y) -∗
            (∀ (x : A), bi_least_fixpoint F x -∗ Φ x)) := by
  sorry

/-- Standard induction principle for least fixpoints.
    Allows assuming both the property Φ and the fixpoint itself under F. -/
theorem least_fixpoint_ind (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), F (fun x => iprop(Φ x ∧ bi_least_fixpoint F x)) y -∗ Φ y) -∗
            (∀ (x : A), bi_least_fixpoint F x -∗ Φ x)) := by
  sorry

end LeastFixpointInduction

section GreatestFixpoint

variable (F : (A → PROP) → (A → PROP)) [BiMonoPred F]

/-- Non-expansiveness of the greatest fixpoint in the outer functor -/
theorem greatest_fixpoint_ne_outer
    (F1 : (A → PROP) → (A → PROP)) (F2 : (A → PROP) → (A → PROP))
    (H : ∀ Φ x n, F1 Φ x ≡{n}≡ F2 Φ x) :
    ∀ x1 x2 n, x1 ≡{n}≡ x2 →
    bi_greatest_fixpoint F1 x1 ≡{n}≡ bi_greatest_fixpoint F2 x2 := by
  sorry

/-- Non-expansiveness of the greatest fixpoint in the inner variable -/
theorem greatest_fixpoint_ne' (H : ∀ Φ, NonExpansive Φ → NonExpansive (F Φ)) :
    NonExpansive (bi_greatest_fixpoint F) := by
  sorry

/-- The greatest fixpoint is proper with respect to equivalence -/
theorem greatest_fixpoint_proper :
    ∀ (F G : (A → PROP) → (A → PROP)),
    (∀ Φ x, F Φ x ≡ G Φ x) → ∀ x, bi_greatest_fixpoint F x ≡ bi_greatest_fixpoint G x := by
  sorry

/-- Unfolding direction: the greatest fixpoint entails F applied to it -/
theorem greatest_fixpoint_unfold_1 (x : A) :
    iprop(bi_greatest_fixpoint F x ⊢ F (bi_greatest_fixpoint F) x) := by
  sorry

/-- Folding direction: F applied to the greatest fixpoint entails the greatest fixpoint -/
theorem greatest_fixpoint_unfold_2 (x : A) :
    iprop(F (bi_greatest_fixpoint F) x ⊢ bi_greatest_fixpoint F x) := by
  sorry

/-- The greatest fixpoint satisfies the fixpoint equation -/
theorem greatest_fixpoint_unfold (x : A) :
    bi_greatest_fixpoint F x ≡ F (bi_greatest_fixpoint F) x := by
  sorry

/-- Basic coinduction principle for greatest fixpoints.
    To prove the greatest fixpoint, it suffices to find a Φ that unfolds to F Φ. -/
theorem greatest_fixpoint_coiter (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), Φ y -∗ F Φ y) -∗ (∀ (x : A), Φ x -∗ bi_greatest_fixpoint F x)) := by
  sorry

/-- If F preserves absorbing predicates, then the greatest fixpoint is absorbing -/
theorem greatest_fixpoint_absorbing
    (H : ∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) :
    ∀ x, Absorbing (bi_greatest_fixpoint F x) := by
  sorry

end GreatestFixpoint

/-- Strong monotonicity for greatest fixpoints -/
theorem greatest_fixpoint_strong_mono
    (F : (A → PROP) → (A → PROP)) [BiMonoPred F]
    (G : (A → PROP) → (A → PROP)) [BiMonoPred G] :
    iprop(⊢ □ (∀ (Φ : A → PROP) (x : A), F Φ x -∗ G Φ x) -∗
            (∀ (x : A), bi_greatest_fixpoint F x -∗ bi_greatest_fixpoint G x)) := by
  sorry

section GreatestFixpointCoinduction

variable (F : (A → PROP) → (A → PROP)) [BiMonoPred F]

/-- Parameterized coinduction for greatest fixpoints (PACO).
    Allows accumulating knowledge through arbitrary unfoldings. -/
theorem greatest_fixpoint_paco (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), Φ y -∗ F (bi_greatest_fixpoint (fun Ψ a => iprop(Φ a ∨ F Ψ a))) y) -∗
            (∀ (x : A), Φ x -∗ bi_greatest_fixpoint F x)) := by
  sorry

/-- Standard coinduction principle for greatest fixpoints.
    Allows returning to either Φ or the fixpoint after one step. -/
theorem greatest_fixpoint_coind (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), Φ y -∗ F (fun x => iprop(Φ x ∨ bi_greatest_fixpoint F x)) y) -∗
            (∀ (x : A), Φ x -∗ bi_greatest_fixpoint F x)) := by
  sorry

end GreatestFixpointCoinduction

end Iris.BI
