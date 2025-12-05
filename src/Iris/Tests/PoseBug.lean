/-
Test file to reproduce the ipose bug with Lean implications
-/
import Iris.BI
import Iris.ProofMode

namespace Iris.Tests.PoseBug
open Iris.BI Iris.ProofMode

-- set_option trace.Meta.synthInstance true in #synth (AsEmpValid2 (?_ ⊢ Q) R)

-- This should work - direct entailment

theorem test_pose_direct [BI PROP] (Q R : PROP) (H : Q ⊢ R) : Q ⊢ R := by
  iintro HQ
  ipose H as HR
  iapply HR with HQ

-- This works - Lean implication wrapping entailment
theorem test_pose_impl [BI PROP] (cond : Prop) (Q R : PROP) (Hcond : cond) (H : cond → (Q ⊢ R)) : Q ⊢ R := by
  istart
  iintro HQ
  ipose H as HR
  exact Hcond
  iapply HR with HQ

-- Test with nested implications
theorem test_pose_nested [BI PROP] (c1 c2 : Prop) (Q R : PROP) (Hc1 : c1) (Hc2 : c2)
    (H : c1 → c2 → (Q ⊢ R)) : Q ⊢ R := by
  istart
  iintro HQ
  ipose H as HR
  · exact Hc1
  · exact Hc2
  iapply HR with HQ

-- Test: what about the emp-entailment form?
theorem test_pose_emp [BI PROP] (cond : Prop) (Q : PROP) (Hcond : cond) (H : cond → (⊢ Q)) : ⊢ Q := by
  istart
  ipose H as HQ
  exact Hcond
  iexact HQ

-- set_option diagnostics true
theorem test_pose_impl_forall [BI PROP] (cond : A → Prop) (Q R : A → PROP) (HH: ∀ a', cond a' → (Q a' ⊢ R a')) (a: A) (Hcond : cond a)
: Q a ⊢ R a := by
  istart
  iintro HQ
  ipose HH as HR
  · exact Hcond
  iapply HR with HQ


-- Global theorem with BI PROP that needs to be instantiated
theorem HH [BI PROP] (cond : A → Prop) (Q R : A → PROP) : ∀ (a': A) , cond a' → (Q a' ⊢ R a') := by sorry

-- TODO: This test has issues with metavar unification for dependent types
set_option pp.explicit true in
theorem test_pose_impl_forall_global [BI PROP] (cond : A → Prop) (Q R : A → PROP) (a: A) (Hcond : cond a)
: Q a ⊢ R a := by
  istart
  iintro HQ

  -- set_option pp.explicit true in
  -- set_option trace.Meta.synthInstance true in
  ipose (HH cond Q) as HR
  · exact Hcond
  · iapply HR with HQ

end Iris.Tests.PoseBug
