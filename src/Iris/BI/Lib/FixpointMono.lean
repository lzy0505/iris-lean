/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI
import Iris.ProofMode


/-!
# Least and Greatest Fixpoints for Monotone Predicates

This file defines least and greatest fixpoints for monotone predicates within the Iris
separation logic framework, entirely inside the logic.

Corresponds to Rocq's  `iris/bi/lib/fixpoint_mono.v`
-/

namespace Iris.BI

open Iris OFE BI BIBase

variable {PROP : Type _} [BI PROP]
variable {A : Type _} [OFE A]

/-- A typeclass for monotone predicates over a BI.
    Requires that F is monotone and non-expansive. -/
class BiMonoPred (F : (A → PROP) → (A → PROP)) where
  bi_mono_pred (Φ Ψ : A → PROP) :
  NonExpansive Φ →
  NonExpansive Ψ →
  (⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x)
    -- intuitionistically (BIBase.forall fun x : A => BIBase.wand (Φ x) (Ψ x)) ⊢
    -- BIBase.forall fun x : A => BIBase.wand (F Φ x) (F Ψ x)
  bi_mono_pred_ne (Φ : A → PROP) [NonExpansive Φ] : NonExpansive (F Φ)

attribute [instance] BiMonoPred.bi_mono_pred_ne

namespace LeastFixpoint

/-- The least fixpoint of a monotone predicate F.
    This is the smallest predicate closed under F. -/
def fp (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  iprop(∀ (Φ : A -n> PROP), □ (∀ (y : A), F Φ y -∗ Φ y) -∗ Φ x)

variable (F : (A → PROP) → (A → PROP)) [BiMonoPred F]

/-- Non-expansiveness of the least fixpoint in the inner variable -/
theorem ne' (H : ∀ Φ, NonExpansive Φ → NonExpansive (F Φ)) :
    NonExpansive (fp F) := by
  constructor
  intros n x y eq
  simp [fp]
  apply forall_ne
  intro Φ
  apply wand_ne.ne
  · apply intuitionistically_ne.ne
    apply forall_ne
    intro y'
    apply wand_ne.ne
    · have : NonExpansive Φ.f := Φ.ne
      apply (H Φ.f this).ne
      apply Dist.rfl
    · apply Dist.rfl
  · apply Φ.ne.ne
    exact eq

/-- The least fixpoint is proper with respect to equivalence -/
theorem proper :
    ∀ (F G : (A → PROP) → (A → PROP)),
    (∀ Φ x, F Φ x ≡ G Φ x) → ∀ x, fp F x ≡ fp G x := by
  intros F G H_equiv x
  simp [fp]
  apply OFE.equiv_dist.2
  intro n
  apply forall_ne
  intro Φ
  apply wand_ne.ne
  · apply intuitionistically_ne.ne
    apply forall_ne
    intro y
    apply wand_ne.ne
    exact (H_equiv Φ.f y).dist
    apply Dist.rfl
  · apply Dist.rfl

/-- Folding direction: F applied to the least fixpoint entails the least fixpoint -/
theorem unfold_2 (x : A) :
    iprop(F (fp F) x ⊢ fp F x) := by
  simp [fp]
  iintro HF Φ □Hincl
  iapply Hincl
  iapply (BiMonoPred.bi_mono_pred (Ψ := Φ)) $$ [], HF
  · sorry
  · sorry

  istop
  apply intuitionistically_intro'

  iintro Hincl y Hy
  simp [fp]
  iapply Hy
  iapply Hincl

/-- Unfolding direction: the least fixpoint entails F applied to it -/
theorem unfold_1 (x : A) :
    iprop(fp F x ⊢ F (fp F) x) := by
  iintro HF
  -- have ne_fp : NonExpansive (fp F) := sorry
  simp [fp]

  -- have ne_fp : True := sorry
  iapply HF $$ %(⟨F (fp F), _⟩)

  istop
  refine intuitionistically_emp.2.trans (intuitionistically_mono ?_)
  -- iintro y Hy
  -- simp
  -- iapply Hy
  -- iintro Φ □Hincl
  -- iapply □Hincl
  sorry
  sorry


/-- The least fixpoint satisfies the fixpoint equation -/
theorem unfold (x : A) :
    fp F x ≡ F (fp F) x := by
  sorry

/-- Basic induction principle for least fixpoints.
    To prove Φ holds for the least fixpoint, it suffices to show that
    F preserves Φ intuitionistically. -/
theorem iter (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), F Φ y -∗ Φ y) -∗ (∀ (x : A), fp F x -∗ Φ x)) := by
  sorry

/-- If F preserves affine predicates, then the least fixpoint is affine -/
theorem affine
    (H : ∀ x, Affine (F (fun _ => iprop(emp)) x)) :
    ∀ x, Affine (fp F x) := by
  sorry

/-- If F preserves absorbing predicates, then the least fixpoint is absorbing -/
theorem absorbing
    (H : ∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) :
    ∀ x, Absorbing (fp F x) := by
  sorry

/-- If F preserves both affine and persistent predicates,
    then the least fixpoint is persistent -/
theorem persistent_affine
    (H_affine : ∀ Φ, (∀ x, Affine (Φ x)) → (∀ x, Affine (F Φ x)))
    (H_pers : ∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x))) :
    ∀ x, Persistent (fp F x) := by
  sorry

/-- If F preserves both absorbing and persistent predicates,
    then the least fixpoint is persistent -/
theorem persistent_absorbing
    (H_absorb : ∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x)))
    (H_pers : ∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x))) :
    ∀ x, Persistent (fp F x) := by
  sorry

/-- Strong monotonicity for least fixpoints -/
theorem strong_mono
    (G : (A → PROP) → (A → PROP)) [BiMonoPred G] :
    iprop(⊢ □ (∀ (Φ : A → PROP) (x : A), F Φ x -∗ G Φ x) -∗
            (∀ (x : A), fp F x -∗ fp G x)) := by
  sorry

/-- Well-founded induction principle for least fixpoints.
    Allows assuming the property holds for arbitrary many unfoldings. -/
theorem ind_wf (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), F (fp (fun Ψ a => iprop(Φ a ∧ F Ψ a))) y -∗ Φ y) -∗
            (∀ (x : A), fp F x -∗ Φ x)) := by
  sorry

/-- Standard induction principle for least fixpoints.
    Allows assuming both the property Φ and the fixpoint itself under F. -/
theorem ind (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), F (fun x => iprop(Φ x ∧ fp F x)) y -∗ Φ y) -∗
            (∀ (x : A), fp F x -∗ Φ x)) := by
  sorry

end LeastFixpoint

section GreatestFixpoint

variable (F : (A → PROP) → (A → PROP)) [BiMonoPred F]

/-- The greatest fixpoint of a monotone predicate F.
    This is the largest predicate containing fixpoints of F. -/
def fp (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  iprop(∃ (Φ : A -n> PROP), □ (∀ (y : A), Φ y -∗ F Φ y) ∗ Φ x)

/-- Non-expansiveness of the greatest fixpoint in the outer functor -/
theorem ne_outer
    (F1 : (A → PROP) → (A → PROP)) (F2 : (A → PROP) → (A → PROP))
    (H : ∀ Φ x n, F1 Φ x ≡{n}≡ F2 Φ x) :
    ∀ x1 x2 n, x1 ≡{n}≡ x2 →
    fp F1 x1 ≡{n}≡ fp F2 x2 := by
  sorry

/-- Non-expansiveness of the greatest fixpoint in the inner variable -/
theorem ne' (H : ∀ Φ, NonExpansive Φ → NonExpansive (F Φ)) :
    NonExpansive (fp F) := by
  sorry

/-- The greatest fixpoint is proper with respect to equivalence -/
theorem proper :
    ∀ (F G : (A → PROP) → (A → PROP)),
    (∀ Φ x, F Φ x ≡ G Φ x) → ∀ x, fp F x ≡ fp G x := by
  sorry

/-- Unfolding direction: the greatest fixpoint entails F applied to it -/
theorem unfold_1 (x : A) :
    iprop(fp F x ⊢ F (fp F) x) := by
  sorry

/-- Folding direction: F applied to the greatest fixpoint entails the greatest fixpoint -/
theorem unfold_2 (x : A) :
    iprop(F (fp F) x ⊢ fp F x) := by
  sorry

/-- The greatest fixpoint satisfies the fixpoint equation -/
theorem unfold (x : A) :
    fp F x ≡ F (fp F) x := by
  sorry

/-- Basic coinduction principle for greatest fixpoints.
    To prove the greatest fixpoint, it suffices to find a Φ that unfolds to F Φ. -/
theorem coiter (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), Φ y -∗ F Φ y) -∗ (∀ (x : A), Φ x -∗ fp F x)) := by
  sorry

/-- If F preserves absorbing predicates, then the greatest fixpoint is absorbing -/
theorem absorbing
    (H : ∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) :
    ∀ x, Absorbing (fp F x) := by
  sorry

/-- Strong monotonicity for greatest fixpoints -/
theorem strong_mono
    (G : (A → PROP) → (A → PROP)) [BiMonoPred G] :
    iprop(⊢ □ (∀ (Φ : A → PROP) (x : A), F Φ x -∗ G Φ x) -∗
            (∀ (x : A), fp F x -∗ fp G x)) := by
  sorry

/-- Parameterized coinduction for greatest fixpoints (PACO).
    Allows accumulating knowledge through arbitrary unfoldings. -/
theorem paco (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), Φ y -∗ F (fp (fun Ψ a => iprop(Φ a ∨ F Ψ a))) y) -∗
            (∀ (x : A), Φ x -∗ fp F x)) := by
  sorry

/-- Standard coinduction principle for greatest fixpoints.
    Allows returning to either Φ or the fixpoint after one step. -/
theorem coind (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), Φ y -∗ F (fun x => iprop(Φ x ∨ fp F x)) y) -∗
            (∀ (x : A), Φ x -∗ fp F x)) := by
  sorry

end GreatestFixpoint

end Iris.BI
