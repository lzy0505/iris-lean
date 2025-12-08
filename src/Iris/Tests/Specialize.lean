/-
Test file for ispecialize tactic - edge cases and potential bugs
-/
import Iris.BI
import Iris.ProofMode

namespace Iris.Tests.SpecializeBug
open Iris.BI Iris.ProofMode

-- ============================================================================
-- Basic wand specialization tests
-- ============================================================================

-- Basic wand specialization with spatial hypotheses
theorem test_specialize_wand_basic [BI PROP] (P Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ HP as HQ
  iexact HQ

-- Wand specialization keeping the same name
theorem test_specialize_wand_same_name [BI PROP] (P Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ HP
  iexact HPQ

-- ============================================================================
-- Intuitionistic hypothesis tests
-- ============================================================================

-- Specialize with intuitionistic hypothesis (spatial wand)
theorem test_specialize_intuitionistic_arg [BI PROP] (P Q : PROP) : □ P ⊢ (P -∗ Q) -∗ Q := by
  iintro □HP HPQ
  ispecialize HPQ HP as HQ
  iexact HQ

-- Specialize intuitionistic wand with spatial hypothesis
theorem test_specialize_intuitionistic_wand [BI PROP] (P Q : PROP) : P ⊢ □ (P -∗ Q) -∗ Q := by
  iintro HP □HPQ
  ispecialize HPQ HP as HQ
  iexact HQ

-- Specialize intuitionistic wand with intuitionistic hypothesis
theorem test_specialize_both_intuitionistic [BI PROP] (P Q : PROP) : □ P ⊢ □ (P -∗ Q) -∗ □ Q := by
  iintro □HP □HPQ
  ispecialize HPQ HP as HQ
  iexact HQ

-- Specialize intuitionistic wand requiring intuitionistic argument
theorem test_specialize_intuitionistic_required [BI PROP] (P Q : PROP) : □ P ⊢ □ (□ P -∗ Q) -∗ □ Q := by
  iintro □HP □HPQ
  ispecialize HPQ HP as HQ
  iexact HQ

-- ============================================================================
-- Universal quantifier tests
-- ============================================================================

-- Basic forall specialization
theorem test_specialize_forall_basic [BI PROP] (Q : Nat → PROP) : ⊢ (∀ x, Q x) -∗ Q 42 := by
  iintro HQ
  ispecialize HQ 42 as HQ'
  iexact HQ'

-- Forall specialization with variable
theorem test_specialize_forall_var [BI PROP] (Q : Nat → PROP) (n : Nat) : ⊢ (∀ x, Q x) -∗ Q n := by
  iintro HQ
  ispecialize HQ n as HQ'
  iexact HQ'

-- Forall specialization with expression
theorem test_specialize_forall_expr [BI PROP] (Q : Nat → PROP) (n : Nat) : ⊢ (∀ x, Q x) -∗ Q (n + 1) := by
  iintro HQ
  ispecialize HQ (n + 1) as HQ'
  iexact HQ'

-- Nested forall specialization
theorem test_specialize_forall_nested [BI PROP] (Q : Nat → Nat → PROP) : ⊢ (∀ x y, Q x y) -∗ Q 1 2 := by
  iintro HQ
  ispecialize HQ 1 2 as HQ'
  iexact HQ'

-- Intuitionistic forall specialization
theorem test_specialize_forall_intuitionistic [BI PROP] (Q : Nat → PROP) : ⊢ □ (∀ x, Q x) -∗ □ Q 0 := by
  iintro □HQ
  ispecialize HQ 0 as HQ'
  iexact HQ'

-- ============================================================================
-- Mixed wand and forall tests
-- ============================================================================

-- Forall followed by wand
theorem test_specialize_forall_then_wand [BI PROP] (P : PROP) (Q : Nat → PROP) :
    P ⊢ (∀ x, P -∗ Q x) -∗ Q 42 := by
  iintro HP HPQ
  ispecialize HPQ 42 HP as HQ
  iexact HQ

-- Wand followed by forall
theorem test_specialize_wand_then_forall [BI PROP] (P : Nat → PROP) (Q : Nat → PROP) :
    P 0 ⊢ (P 0 -∗ ∀ x, Q x) -∗ Q 42 := by
  iintro HP HPQ
  ispecialize HPQ HP 42 as HQ
  iexact HQ

-- Multiple foralls and wands interleaved
theorem test_specialize_interleaved [BI PROP] (P : Nat → PROP) (Q : Nat → Nat → PROP) :
    P 1 ⊢ (∀ x, P x -∗ ∀ y, Q x y) -∗ Q 1 2 := by
  iintro HP HPQ
  ispecialize HPQ 1 HP 2 as HQ
  iexact HQ

-- ============================================================================
-- Multiple arguments tests
-- ============================================================================

-- Multiple wand arguments
theorem test_specialize_multi_wand [BI PROP] (P1 P2 Q : PROP) :
    ⊢ P1 -∗ P2 -∗ (P1 -∗ P2 -∗ Q) -∗ Q := by
  iintro HP1 HP2 HPQ
  ispecialize HPQ HP1 HP2 as HQ
  iexact HQ

-- Multiple forall arguments
theorem test_specialize_multi_forall [BI PROP] (Q : Nat → Nat → Nat → PROP) :
    ⊢ (∀ x y z, Q x y z) -∗ Q 1 2 3 := by
  iintro HQ
  ispecialize HQ 1 2 3 as HQ'
  iexact HQ'

-- Mixed intuitionistic and spatial arguments
theorem test_specialize_mixed_intuit_spatial [BI PROP] (P1 P2 Q : PROP) :
    ⊢ □ P1 -∗ P2 -∗ □ (P1 -∗ P2 -∗ Q) -∗ Q := by
  iintro □HP1 HP2 □HPQ
  ispecialize HPQ HP1 HP2 as HQ
  iexact HQ

-- ============================================================================
-- Edge cases with type parameters
-- ============================================================================

-- Forall with type parameter
theorem test_specialize_forall_type [BI PROP] (Q : α → PROP) (a : α) :
    ⊢ (∀ x, Q x) -∗ Q a := by
  iintro HQ
  ispecialize HQ a as HQ'
  iexact HQ'

-- Forall with multiple type parameters
theorem test_specialize_forall_multi_type [BI PROP] (Q : α → β → PROP) (a : α) (b : β) :
    ⊢ (∀ x y, Q x y) -∗ Q a b := by
  iintro HQ
  ispecialize HQ a b as HQ'
  iexact HQ'

-- ============================================================================
-- Complex scenarios
-- ============================================================================

-- Real-world example: specializing an invariant opening lemma style
theorem test_specialize_complex [BI PROP] (P Q R : PROP) (Φ : α → PROP) :
    P ∗ Q ∗ □ R ⊢ □ (R -∗ ∃ x, Φ x) -∗ ∃ x, Φ x ∗ P ∗ Q := by
  iintro ⟨HP, HQ, □HR⟩ □HRΦ
  ispecialize HRΦ HR as HΦ
  icases HΦ with ⟨x, HΦ⟩
  iexists x
  isplitr
  · iexact HΦ
  isplitl [HP]
  · iexact HP
  · iexact HQ

-- Specialization where the argument matches exactly
theorem test_specialize_exact_match [BI PROP] (P Q : PROP) : ⊢ P -∗ (P -∗ Q) -∗ Q := by
  iintro HP H
  ispecialize H HP as HQ
  iexact HQ

-- ============================================================================
-- Preservation of intuitionistic context
-- ============================================================================

-- Specializing should preserve other intuitionistic hypotheses
theorem test_specialize_preserve_intuit [BI PROP] (P Q R : PROP) :
    □ R ⊢ P -∗ (P -∗ Q) -∗ Q := by
  iintro □HR HP HPQ
  ispecialize HPQ HP as HQ
  iexact HQ

-- Multiple intuitionistic hypotheses preserved
theorem test_specialize_multi_intuit_preserve [BI PROP] (P Q R S : PROP) :
    □ R ∗ □ S ⊢ P -∗ (P -∗ Q) -∗ Q := by
  iintro ⟨□HR, □HS⟩ HP HPQ
  ispecialize HPQ HP as HQ
  iexact HQ

-- ============================================================================
-- Self-specialization (using same hypothesis for argument)
-- ============================================================================

-- Using intuitionistic hypothesis multiple times
theorem test_specialize_reuse_intuit [BI PROP] (P Q : PROP) :
    □ P ⊢ □ (P -∗ P -∗ Q) -∗ □ Q := by
  iintro □HP □HPQ
  ispecialize HPQ HP HP as HQ
  iexact HQ

-- ============================================================================
-- Affine specializations
-- ============================================================================

-- Specializing affine hypothesis
theorem test_specialize_affine [BI PROP] (P Q : PROP) : <affine> P ⊢ (<affine> P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ HP as HQ
  iexact HQ

-- Specializing intuitionistic hypothesis with wand expecting intuitionistic
theorem test_specialize_intuit_to_intuit [BI PROP] (P Q : PROP) :
    □ P ⊢ (□ P -∗ Q) -∗ Q := by
  iintro □HP HPQ
  ispecialize HPQ HP as HQ
  iexact HQ

-- ============================================================================
-- Pure propositions
-- ============================================================================

-- Specializing with pure proposition hypothesis
theorem test_specialize_with_pure [BI PROP] [BIAffine PROP] (φ : Prop) (Q : PROP) (hφ : φ) :
    ⊢ (⌜φ⌝ -∗ Q) -∗ Q := by
  iintro HPQ
  irevert hφ
  iexact HPQ

-- ============================================================================
-- More intuitionistic patterns
-- ============================================================================

-- Intuitionistic wand with intuitionistic result
theorem test_specialize_intuit_result [BI PROP] (P Q : PROP) : ⊢ □ P -∗ □ (P -∗ □ Q) -∗ □ Q := by
  iintro □HP □HPQ
  ispecialize HPQ HP as HQ
  iexact HQ

-- ============================================================================
-- Combination with other tactics
-- ============================================================================

-- Specialize then split (using sep instead of and)
theorem test_specialize_then_split [BI PROP] [BIAffine PROP] (P Q R : PROP) :
    P ⊢ (P -∗ Q ∗ R) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ HP as HQR
  icases HQR with ⟨HQ, _⟩
  iexact HQ

-- Specialize then exists
theorem test_specialize_then_exists [BI PROP] (P : PROP) (Q : Nat → PROP) :
    P ⊢ (P -∗ ∃ x, Q x) -∗ ∃ x, Q x := by
  iintro HP HPQ
  ispecialize HPQ HP as HQ
  iexact HQ

-- Specialize result of cases
theorem test_cases_then_specialize [BI PROP] [BIAffine PROP] (P Q : PROP) :
    ⊢ (P ∨ Q) -∗ □ (P -∗ Q) -∗ □ (Q -∗ Q) -∗ Q := by
  iintro HPQ □HPQ' □HQQ
  icases HPQ with (HP | HQ)
  · ispecialize HPQ' HP as HQ
    iexact HQ
  · ispecialize HQQ HQ as HQ'
    iexact HQ'

end Iris.Tests.SpecializeBug
