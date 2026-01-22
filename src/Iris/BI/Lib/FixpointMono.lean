/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI
import Iris.ProofMode
import Iris.Std.NonExpansive

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

/-- Automatically derive PreservesNonExpansive from BiMonoPred -/
instance [BiMonoPred F] : PreservesNonExpansive F where
  preserves Φ hΦ := by
    haveI := hΦ
    exact BiMonoPred.bi_mono_pred_ne Φ

/-- Non-expansiveness of the least fixpoint in the inner variable -/
instance ne' [PreservesNonExpansive F] :
    NonExpansive (fp F) := by
  constructor
  intros n x y eq
  simp [fp]
  f_nonexp

/-- The least fixpoint is proper with respect to equivalence -/
theorem proper :
    ∀ (F G : (A → PROP) → (A → PROP)),
    (∀ Φ x, F Φ x ≡ G Φ x) → ∀ x, fp F x ≡ fp G x := by
  intros F G H_equiv x
  simp [fp]

  apply OFE.equiv_dist.2
  intro n
  f_nonexp
  exact (H_equiv ?_ ?_).dist

/-- Folding direction: F applied to the least fixpoint entails the least fixpoint -/
theorem unfold_2 (x : A) :
    iprop(F (fp F) x ⊢ fp F x) := by
  simp [fp]
  iintro HF Φ □Hincl
  iapply Hincl
  iapply (BiMonoPred.bi_mono_pred (Ψ := Φ)) $$ [], HF <;> solve_nonexp

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
  simp [fp]

  iapply HF $$ %(⟨F (fp F), (by solve_nonexp)⟩)

  istop
  refine intuitionistically_emp.2.trans (intuitionistically_mono ?_)

  iintro _ y Hy
  simp
  iapply BiMonoPred.bi_mono_pred $$ [], Hy <;> solve_nonexp
  istop
  refine intuitionistically_emp.2.trans (intuitionistically_mono ?_)
  iintro _ z Hz
  iapply unfold_2
  trivial
  iexact Hz

/-- The least fixpoint satisfies the fixpoint equation -/
theorem unfold (x : A) :
    fp F x ≡ F (fp F) x := by
  apply BI.equiv_iff.mpr
  constructor
  apply unfold_1
  apply unfold_2

omit [BiMonoPred F] in
/-- Basic induction principle for least fixpoints.
    To prove Φ holds for the least fixpoint, it suffices to show that
    F preserves Φ intuitionistically. -/
theorem iter (Φ : A → PROP) [NonExpansive Φ] :
    □ (∀ (y : A), F Φ y -∗ Φ y) ⊢ (∀ (x : A), fp F x -∗ Φ x) := by
  iintro □HΦ x HF
  simp [fp]
  iapply HF $$ %(⟨Φ, _⟩)
  iapply HΦ
  trivial

omit [BiMonoPred F] in
/-- If F preserves affine predicates, then the least fixpoint is affine -/
theorem affine
    (H : ∀ x, Affine (F (fun _ => iprop(emp)) x)) :
    ∀ x, Affine (fp F x) := by
  intro _
  constructor
  iintro H
  iapply @iter (A := A) (F := F) (Φ := (fun _ => (iprop(emp): PROP))) _
  · apply OFE.ne_of_contractive
  istop
  refine intuitionistically_emp.2.trans (intuitionistically_mono ?_)

  iintro _ y
  cases (H y) with
  | mk affine => iapply affine

  iexact H

/-- If F preserves absorbing predicates, then the least fixpoint is absorbing -/
theorem absorbing
    (H : ∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) :
    ∀ x, Absorbing (fp F x) := by
  intro x
  constructor
  simp [BI.absorbingly]
  iintro ⟨Htrue, H⟩
  iapply BI.wand_elim_r (PROP:= PROP) (P := (iprop(True) : PROP))

  isplitl [Htrue]
  · iexact Htrue
  · irevert H
    irevert x
    iapply iter <;> solve_nonexp
    istop
    refine intuitionistically_emp.2.trans (intuitionistically_mono ?_)
    iintro Hemp y HF Htrue
    iapply unfold_2
    trivial

    have H : (∀ y, emp ⊢ (F (fun x => iprop(True -∗ fp F x)) y) -∗ True -∗ F (fun (x : A) => iprop(True -∗ fp F x)) y) := by
      intro y
      iintro _ HF Htrue
      have hh : (Absorbing (F (fun x => iprop(True -∗ fp F x)) y)) := by
        apply H
        infer_instance
      iclear Htrue
      iexact HF
    ihave HF := (H y) $$ Hemp, HF, Htrue

    iapply BiMonoPred.bi_mono_pred $$ [], %y, HF <;> solve_nonexp
    istop
    refine intuitionistically_emp.2.trans (intuitionistically_mono ?_)
    iintro Hemp x HH
    iapply HH
    iapply (BI.true_intro (PROP:= PROP)) $$ Hemp

/-- If F preserves both affine and persistent predicates,
    then the least fixpoint is persistent -/
theorem persistent_affine
    (H_affine : ∀ Φ, (∀ x, Affine (Φ x)) → (∀ x, Affine (F Φ x)))
    (H_pers : ∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x))) :
    ∀ x, Persistent (fp F x) := by
  intros x
  constructor

  suffices h : ∀ x, fp F x ⊢ □ fp F x by
    exact (h x).trans persistently_of_intuitionistically

  intro y
  iintro HF
  iapply (@iter (A := A) (F := F) (Φ := fun z => iprop(□ fp F z))) _ <;> solve_nonexp
  istop
  refine intuitionistically_emp.2.trans (intuitionistically_mono ?_)

  iintro Hemp z HF
  istop
  apply emp_sep.1.trans
  iintro HF

  have hpers : Persistent (F (fun z => iprop(□ fp F z)) z) := by
    apply H_pers
    intro w
    infer_instance

  istop

  have haff : Affine (F (fun z => iprop(□ fp F z)) z) := by
    apply H_affine
    intro w
    infer_instance

  apply (affine_affinely (F (fun z => iprop(□ fp F z)) z)).2.trans
  apply (affinely_mono (persistent (P := F (fun z => iprop(□ fp F z)) z))).trans
  apply intuitionistically_mono

  iintro HF
  iapply unfold_2
  trivial

  iapply BiMonoPred.bi_mono_pred $$ [], HF <;> solve_nonexp
  istop
  refine intuitionistically_emp.2.trans (intuitionistically_mono ?_)

  iintro Hemp w HH
  iapply intuitionistically_elim
  iexact HH

  iexact HF


/-- If F preserves both absorbing and persistent predicates,
    then the least fixpoint is persistent -/
theorem persistent_absorbing
    (H_absorb : ∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x)))
    (H_pers : ∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x))) :
    ∀ x, Persistent (fp F x) := by
  intro x
  have H_absorb_fp := absorbing (F := F) H_absorb
  constructor
  iintro HF
  iapply (@iter (A := A) (F := F) (Φ := fun z => iprop(<pers> fp F z))) _ <;> solve_nonexp
  istop
  refine intuitionistically_emp.2.trans (intuitionistically_mono ?_)
  iintro Hemp y HF
  istop
  apply emp_sep.1.trans
  iintro HF

  have hpers : Persistent (F (fun z => iprop(<pers> fp F z)) y) := by
    apply H_pers
    intro w
    infer_instance

  istop

  apply (persistent (P := F (fun z => iprop(<pers> fp F z)) y)).trans
  apply BI.persistently_mono

  iintro HF
  iapply unfold_2
  trivial
  iapply BiMonoPred.bi_mono_pred $$ [], HF <;> solve_nonexp
  istop
  refine intuitionistically_emp.2.trans (intuitionistically_mono ?_)
  iintro Hemp x HH
  iapply persistently_elim
  iexact HH

  iexact HF

omit [BiMonoPred F] in
/-- Strong monotonicity for least fixpoints -/
theorem strong_mono
    (G : (A → PROP) → (A → PROP)) [BiMonoPred G] :
    iprop(⊢ □ (∀ (Φ : A → PROP) (x : A), F Φ x -∗ G Φ x) -∗
            (∀ (x : A), fp F x -∗ fp G x)) := by
  iintro □Hmon
  iapply @iter (PROP := PROP) (Φ := fp G) <;> solve_nonexp
  istop
  apply intuitionistically_intro'
  iintro Hmon y IH
  iapply unfold_2
  trivial
  iapply Hmon $$ IH

section LeastFixpointInd

variable [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) [BiMonoPred F]

local instance [NonExpansive Φ]: BiMonoPred (fun (Ψ: A → PROP) => (fun (a: A) => iprop(Φ a ∧ F Ψ a))) := by
constructor
· intro Ψ Ψ' Hne Hne'
  iintro □Mon x Ha
  isplit
  · icases Ha with ⟨Ha, -⟩
    iexact Ha
  · icases Ha with ⟨-, Hr⟩
    iapply BiMonoPred.bi_mono_pred $$ [], Hr <;> try infer_instance
    iexact Mon
· intro ?_ ?_
  constructor
  intro ?_ ?_ ?_ ?_
  f_nonexp

/-- Well-founded induction principle for least fixpoints.
    Allows assuming the property holds for arbitrary many unfoldings. -/
theorem ind_wf (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), F (fp (fun Ψ a => iprop(Φ a ∧ F Ψ a))) y -∗ Φ y) -∗
            (∀ (x : A), fp F x -∗ Φ x)) := by
  iintro □Hmon x Hfp
  ihave Hx := unfold_1 (A:=A) (PROP:=PROP) $$ Hfp
  infer_instance
  iapply Hmon
  iapply BiMonoPred.bi_mono_pred $$ [], Hx <;> solve_nonexp

  istop
  apply intuitionistically_intro'

  iintro □Hmon
  iapply iter<;> solve_nonexp
  istop
  apply intuitionistically_intro'
  iintro □Hmon y Hy
  iapply unfold_2
  infer_instance
  isplit
  iapply Hmon <;> iexact Hy
  iexact Hy

/-- Standard induction principle for least fixpoints.
    Allows assuming both the property Φ and the fixpoint itself under F. -/
theorem ind (Φ : A → PROP) [NonExpansive Φ] :
    iprop(⊢ □ (∀ (y : A), F (fun x => iprop(Φ x ∧ fp F x)) y -∗ Φ y) -∗
            (∀ (x : A), fp F x -∗ Φ x)) := by
  iintro □Hmon
  iapply ind_wf<;> try infer_instance
  istop
  apply intuitionistically_intro'
  iintro □Hmon y Hy
  iapply Hmon
  iapply BiMonoPred.bi_mono_pred $$ [], Hy <;> solve_nonexp
  istop
  apply intuitionistically_intro'
  iintro □Hmon x Hx
  isplit
  · ihave Hx := unfold_1 (A:=A) (PROP:= PROP) $$ Hx
    infer_instance
    icases Hx with ⟨Ha, -⟩
    iexact Ha
  · iapply strong_mono $$ [], Hx
    infer_instance

    istop
    apply intuitionistically_intro'
    iintro Hmon _ _ ⟨-, H⟩
    iexact H

end LeastFixpointInd

end LeastFixpoint

namespace GreatestFixpoint

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
