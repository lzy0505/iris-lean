/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Oliver Soeser, Michael Sammler
-/
import Iris.BI
import Iris.ProofMode

namespace Iris.Tests
open Iris.BI

/- This file contains tests with various scenarios for all available tactics. -/

-- start stop
/-- Tests `istart` and `istop` for entering and exiting proof mode -/
example [BI PROP] (Q : PROP) (H : Q ⊢ Q) : Q ⊢ Q := by
  istart
  iintro _HQ
  istop
  exact H

-- rename
namespace rename

/-- Tests basic hypothesis renaming with `irename` -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  irename HQ => H
  iexact H

/-- Tests renaming a hypothesis by its type -/
example [BI PROP] (P Q : PROP) : □ P ∗ Q ⊢ Q := by
  iintro ⟨_HP, HQ⟩
  irename: Q => H
  iexact H

/-- Tests renaming a hypothesis twice -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  irename HQ => H
  irename H => HQ
  iexact HQ

/-- Tests renaming a hypothesis to itself (no-op) -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  irename HQ => HQ
  iexact HQ

end rename

-- clear
namespace clear

/-- Tests clearing an intuitionistic hypothesis with `iclear` -/
example [BI PROP] (Q : PROP) : □ P ⊢ Q -∗ Q := by
  iintro □HP
  iintro HQ
  iclear HP
  iexact HQ

/-- Tests clearing a spatial affine hypothesis with `iclear` -/
example [BI PROP] (Q : PROP) : <affine> P ⊢ Q -∗ Q := by
  iintro HP
  iintro HQ
  iclear HP
  iexact HQ

-- theorem select1 [BI PROP] (Q : PROP) : <affine> P ∗ <affine> P'  ∗ <affine> P'' ∗ □ R ∗ □ R' ∗ □ R' ⊢ Q -∗ Q := by
--   iintro ⟨HP, HP', HP'', □ R, □ R', □ R''⟩
--   iclear HP
--   -- iclear %
--   iclear [*]
--   iclear R
--   iclear #
--   iintro HQ
--   iexact HQ

-- theorem select2 [BI PROP] (Q : PROP) : <affine> P ∗ <affine> P'  ∗ <affine> P'' ∗ □ R ∗ □ R' ∗ □ R' ⊢ Q -∗ Q := by
--   iintro ⟨HP, HP', HP'', □ R, □ R', □ R''⟩
--   iclear HP % HP' R
--   iclear [* #]
--   iintro HQ
--   iexact HQ

end clear

-- intro
namespace intro

/-- Tests introducing a spatial hypothesis -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iexact HQ

/-- Tests introducing an intuitionistic hypothesis with the `□` pattern -/
example [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro □HQ
  iexact HQ

/-- Tests introducing an affine persistent proposition as intuitionistic -/
example [BI PROP] (Q : PROP) : <affine> <pers> Q ⊢ Q := by
  iintro □HQ
  iexact HQ

/-- Tests introducing a persistent implication in the spatial context -/
example [BI PROP] (Q : PROP) : ⊢ <pers> Q → Q := by
  iintro HQ
  iexact HQ

/-- Tests dropping a hypothesis in an implication with the `-` pattern -/
example [BI PROP] (Q : PROP) : ⊢ P → Q -∗ Q := by
  iintro - HQ
  iexact HQ

/-- Tests dropping a hypothesis in an implication in a non-empty context -/
example [BI PROP] (Q : PROP) : ⊢ Q -∗ P → Q := by
  iintro HQ -
  iexact HQ

/-- Tests introducing an universally quantified variable -/
example [BI PROP] : ⊢@{PROP} ∀ x, ⌜x = 0⌝ → ⌜x = 0⌝ := by
  iintro x
  iintro H
  iexact H

/-- Tests introducing and extracting a pure hypothesis in affine BI -/
example [BI PROP] [BIAffine PROP] φ (Q : PROP) : ⊢ ⌜φ⌝ -∗ Q -∗ Q := by
  iintro ⌜Hφ⌝ HQ
  iexact HQ

/-- Tests introducing with disjunction pattern inside intuitionistic -/
example [BI PROP] (P1 P2 Q : PROP) : □ (P1 ∨ P2) ∗ Q ⊢ Q := by
  iintro ⟨□(_HP1 | _HP2), HQ⟩
  <;> iexact HQ

/-- Tests introducing multiple spatial hypotheses -/
example [BI PROP] (P Q : PROP) : ⊢ <affine> P -∗ Q -∗ Q := by
  iintro _HP HQ
  iexact HQ

/-- Tests introducing multiple intuitionistic hypotheses -/
example [BI PROP] (Q : PROP) : ⊢ □ P -∗ □ Q -∗ Q := by
  iintro □_HP □HQ
  iexact HQ

/-- Tests introducing with complex nested patterns -/
example [BI PROP] (Q : PROP) : ⊢ □ (P1 ∧ P2) -∗ Q ∨ Q -∗ Q := by
  iintro □⟨_HP1, ∗_HP2⟩ (HQ | HQ)
  <;> iexact HQ

end intro

-- revert
namespace revert

theorem spatial [BI PROP] (P Q : PROP) (H : ⊢ P -∗ Q) : P ⊢ Q := by
  iintro HP
  irevert HP
  exact H

theorem intuitionistic [BI PROP] (P : PROP) (H : ⊢ □ P -∗ P) : □ P ⊢ P := by
  iintro □HP
  irevert HP
  exact H

theorem pure [BI PROP] (P : PROP) (Hφ : φ) : ⊢ (⌜φ⌝ -∗ P) -∗ P := by
  iintro H
  irevert Hφ
  iexact H

theorem «forall» [BI PROP] (x : α) (Φ : α → PROP) : ⊢ (∀ x, Φ x) → Φ x := by
  iintro H
  irevert x
  iexact H

theorem multiple_spatial [BI PROP] (P Q : PROP) :
    ⊢ (P -∗ P) -∗ P -∗ <affine> Q -∗ P := by
  iintro H HP HQ
  irevert HP
  iexact H

theorem multiple_intuitionistic [BI PROP] (P Q : PROP) :
    ⊢ (□ P -∗ P) -∗ □ P -∗ <affine> Q -∗ P := by
  iintro H □HP HQ
  irevert HP
  iexact H

end revert

-- exists
namespace «exists»

/-- Tests `iexists` with a BI proposition -/
example [BI PROP] : ⊢@{PROP} ∃ x, x := by
  iexists iprop(True)
  ipure_intro
  exact True.intro

/-- Tests `iexists` with a natural number -/
example [BI PROP] : ⊢@{PROP} ∃ (_x : Nat), True ∨ False := by
  iexists 42
  ileft
  ipure_intro
  exact True.intro

/-- Tests `iexists` with Prop -/
example [BI PROP] : ⊢@{PROP} ⌜∃ x, x ∨ False⌝ := by
  iexists True
  ipure_intro
  exact Or.inl True.intro


/-- Tests `iexists` with a named metavariable -/
example [BI PROP] : ⊢@{PROP} ∃ x, ⌜x = 42⌝ := by
  iexists ?y
  ipure_intro
  rfl

/-- Tests `iexists` with anonymous metavariable -/
example [BI PROP] : ⊢@{PROP} ∃ x, ⌜x = 42⌝ := by
  iexists _
  ipure_intro
  rfl

/-- Tests `iexists` with two quantifiers -/
example [BI PROP] : ⊢@{PROP} ∃ x y : Nat, ⌜x = y⌝ := by
  iexists _, 1
  ipure_intro
  rfl


end «exists»

-- exact
namespace exact

/-- Tests basic `iexact` -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iexact HQ

/-- Tests `iexact` with affine pers to intuitionistic -/
example [BI PROP] (Q : PROP) : <affine> <pers> Q ⊢ □ Q := by
  iintro HQ
  iexact HQ

/-- Tests `iexact` with intuitionistic hypothesis -/
example [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro HQ
  iexact HQ

end exact

-- assumption
namespace assumption

/-- Tests `iassumption` for exact match -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro _HQ
  iassumption

/-- Tests `iassumption` with affine pers to intuitionistic -/
example [BI PROP] (Q : PROP) : <affine> <pers> Q ⊢ □ Q := by
  iintro _HQ
  iassumption

/-- Tests `iassumption` with intuitionistic hypothesis -/
example [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro □_HQ
  iassumption

/-- Tests `iassumption` using a Lean hypothesis -/
example [BI PROP] (Q : PROP) (H : ⊢ Q) : <affine> P ⊢ Q := by
  iintro _HP
  iassumption

/-- Tests `iassumption` with Lean hypothesis first introduced -/
example [BI PROP] (Q : PROP) : <affine> ⌜⊢ Q⌝ ⊢ Q := by
  iintro ⌜H⌝
  iassumption

end assumption

-- apply
namespace apply

/-- Tests `iapply` with exact match -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro HQ
  iapply HQ

/-- Tests `iapply` with wand -/
example [BI PROP] (P Q : PROP) : ⊢ P -∗ (P -∗ Q) -∗ Q := by
  iintro HP H
  iapply H $$ HP

/-- Tests `iapply` with multiple hypotheses -/
example [BI PROP] (P Q R : PROP) : ⊢ P -∗ Q -∗ (P -∗ Q -∗ R) -∗ R := by
  iintro HP HQ H
  iapply H $$ HP, HQ

/-- Tests `iapply` with nested wand application -/
example [BI PROP] (P Q R S : PROP) : ⊢ (P -∗ Q) -∗ P -∗ R -∗ (Q -∗ R -∗ S) -∗ S := by
  iintro HPQ HP HR H
  iapply H $$ [HPQ, HP], HR
  iapply HPQ $$ HP

/-- Tests `iapply` with intuitionistic exact -/
example [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iintro □HQ
  iapply HQ

/-- Tests `iapply` with intuitionistic wand argument -/
example [BI PROP] (P Q : PROP) : ⊢ □ P -∗ (P -∗ Q) -∗ Q := by
  iintro HP H
  iapply H $$ HP

/-- Tests `iapply` with multiple intuitionistic hypotheses and subgoals -/
example [BI PROP] (P Q R : PROP) : ⊢ □ P -∗ Q -∗ □ (P -∗ Q -∗ □ R) -∗ R := by
  iintro □HP HQ □H
  iapply H $$ [], [HQ] as Q
  case Q => iexact HQ
  iexact HP

/-- Tests `iapply` with later modality -/
example [BI PROP] (P Q : PROP) : ⊢ (▷ P -∗ Q) -∗ P -∗ Q := by
  iintro H HP
  iapply H $$ HP

/-- Tests `iapply` with implication -/
example [BI PROP] [BIAffine PROP] (P Q : PROP) : ⊢ (P → Q) -∗ <pers> P -∗ Q := by
  iintro H HP
  iapply H $$ HP

/-- Tests `iapply` with later and implication -/
example [BI PROP] [BIAffine PROP] (P Q : PROP) : ⊢ (▷ P → Q) -∗ P -∗ Q := by
  iintro H HP
  iapply H $$ HP

/-- Tests `iapply` with Lean hypothesis -/
example [BI PROP] (Q : PROP) (H : ⊢ Q) : ⊢ Q := by
  iapply H

/-- Tests `iapply` with lemma -/
example [BI PROP] (Q : PROP) : Q ⊢ (emp ∗ Q) ∗ emp := by
  iapply (wand_intro sep_emp.mpr)
  iemp_intro

/-- Tests `iapply` with pure sidecondition -/
example [BI PROP] (Q : PROP) (H : 0 = 0 → ⊢ Q) : ⊢ Q := by
  iapply H
  rfl

/-- Tests `iapply` with lemma with sidecondition -/
example [BI PROP] : ⊢@{PROP} ⌜1 = 1⌝ := by
  istart
  iapply (pure_intro (P:=emp))
  . rfl
  iemp_intro

/-- Tests `iapply` with entailment as Lean hypothesis -/
example [BI PROP] (P Q : PROP) (H : P ⊢ Q) (HP : ⊢ P) : ⊢ Q := by
  iapply H
  iapply HP

/-- Tests `iapply` with wand entailment as Lean hypothesis -/
example [BI PROP] (P Q : PROP) (H : ⊢ P -∗ Q) (HP : ⊢ P) : ⊢ Q := by
  iapply H $$ []
  iapply HP

/-- Tests `iapply` with constructed term -/
example [BI PROP] (P Q : PROP) (H1 : P ⊢ Q) (H2 : Q ⊢ R) : P ⊢ R := by
  iintro HP
  iapply (wand_intro (emp_sep.mp.trans H2))
  . ipure_intro; trivial
  iapply H1 $$ HP

/-- Tests `iapply` with Lean wand entailment and subgoal -/
example [BI PROP] (P Q R : PROP) (H : P ⊢ Q -∗ R) (HP : ⊢ P) : ⊢ Q -∗ R := by
  iintro HQ
  iapply H $$ [], HQ
  iapply HP

/-- Tests `iapply` with lemma and subgoal -/
example [BI PROP] (P Q R : PROP) (H : P ∗ Q ⊢ R) (HP : ⊢ P) : ⊢ Q -∗ R := by
  iintro HQ
  iapply (wand_intro H) $$ [], HQ
  iapply HP

/-- Tests `iapply` with forall -/
example [BI PROP] (P : α → PROP) (a : α) (H : ⊢ ∀ x, P x) : ⊢ P a := by
  istart
  iapply H

/-- Tests `iapply` with Lean forall -/
example [BI PROP] (P : α → PROP) (a : α) (H : ∀ x, ⊢ P x) : ⊢ P a := by
  iapply H

/-- Tests `iapply` with forall specialization -/
example [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  iapply H $$ %a, %b, HP

/-- Tests `iapply` with forall specialization from hypothesis -/
example [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $$ %a, %b, HP

/-- Tests `iapply` with tactic -/
example [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $$ %by exact a, %b, [HP]
  iapply HP

/-- error: ispecialize: iprop(P a -∗ Q b) is not a lean premise -/
#guard_msgs in
example [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $$ %a, %b, %_, HP

/-- Tests `iapply` using unification for foralls -/
example [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $$ HP

/-- Tests `iapply` using manually created metavariables -/
example [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $$ %?_, %?_, HP

/-- Tests `iapply` using unification in two steps, instantiating metavars  -/
example [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H
  iapply HP

/-- Tests `iapply` with intuitionistic forall from Lean -/
example [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ □ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  iapply H $$ %a, HP

/-- Tests `iapply` with intuitionistic forall from hypothesis -/
example [BI PROP] (P Q : α → PROP) (a b : α) : (□ ∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  iapply H $$ %a, %b, HP

/-- Tests `iapply` with two wands and subgoals -/
example [BI PROP] (P Q : Nat → PROP) :
  (P 1 -∗ P 2 -∗ Q 1) ⊢ □ P 1 -∗ P 2 -∗ Q 1 := by
  iintro H □HP1 HP2
  iapply H
  . iexact HP1
  . iexact HP2

/-- Tests `iapply` selecting left conjunct -/
example [BI PROP] (P Q : Nat → PROP) :
  ((P 1 -∗ P 2) ∧ (Q 1 -∗ Q 2)) ⊢ P 1 -∗ P 2 := by
  iintro H HP1
  iapply H
  iexact HP1

/-- Tests `iapply` selecting right conjunct -/
example [BI PROP] (P Q : Nat → PROP) :
  ((P 1 -∗ P 2) ∧ (Q 1 -∗ Q 2)) ⊢ Q 1 -∗ Q 2 := by
  iintro H HQ1
  iapply H
  iexact HQ1

/-- Tests `iapply` selecting left conjunct (exact match) -/
example [BI PROP] (P Q : Nat → PROP) :
  (P 1 ∧ Q 1) ⊢ P 1 := by
  iintro H
  iapply H

/-- Tests `iapply` selecting right conjunct (exact match) -/
example [BI PROP] (P Q : Nat → PROP) :
  (P 1 ∧ Q 1) ⊢ Q 1 := by
  iintro H
  iapply H

end apply

-- have
namespace ihave

/-- Tests `ihave` with Lean hypothesis -/
example [BI PROP] (Q : PROP) (H : ⊢ Q) : ⊢ Q := by
  ihave HQ := H
  iexact HQ

/-- Tests `ihave` with forall specialization via case -/
example [BI PROP] (Q : Nat → PROP) (H : ∀ x, ⊢ Q x) : ⊢ Q 1 := by
  ihave HQ := H
  case x => exact 1
  iapply HQ

/-- Tests `ihave` with forall specialization via named hole -/
example [BI PROP] (Q : Nat → PROP) (H : ∀ x, ⊢ Q x) : ⊢ Q 1 := by
  ihave HQ := H ?res
  case res => exact 1
  iexact HQ

/-- Tests `ihave` with two named holes -/
example [BI PROP] (Q : Nat → Nat → PROP) (H : ∀ x y, ⊢ Q x y) : ⊢ Q 1 1 := by
  ihave HQ := H ?res ?res
  case res => exact 1
  iexact HQ

/-- Tests `ihave` creating metavars -/
example [BI PROP] (Q : Nat → PROP) (H : ∀ x, ⊢ Q x) : ⊢ Q 1 := by
  ihave HQ := H
  iexact HQ

/-- Tests `ihave` with typeclass argument (failing search) -/
example [BI PROP] (Q : Nat → PROP) (H : ∀ (P : PROP) [Persistent P], ⊢ P) : ⊢ Q 1 := by
  ihave HQ := H
  rotate_right 1; exact iprop(□ Q 1)
  . apply inferInstance
  iexact HQ

/-- Tests `ihave` with typeclass argument (successful search) -/
example [BI PROP] (Q : Nat → PROP) (H : ∀ (P : PROP) [Persistent P], ⊢ P) : ⊢ Q 1 := by
  ihave HQ := H iprop(□ Q _)
  rotate_right 1; exact 1
  iexact HQ

/-- Tests `ihave` from spatial hypothesis -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iintro H
  ihave HQ := H
  iexact HQ

/-- Tests `ihave` with Lean entailment -/
example [BI PROP] (P Q : PROP) (H : P ⊢ Q) : ⊢ P -∗ Q := by
  ihave HPQ := H
  iexact HPQ

/-- Tests `ihave` with forall specialization from Lean -/
example [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  ihave H' := H $$ %a, %b
  iapply H' $$ HP

/-- Tests `ihave` with forall specialization from hypothesis -/
example [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  ihave H' := H $$ %a, %b, HP
  iexact H'

/-- Tests `ihave` with intuitionistic forall specialization from Lean -/
example [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ □ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  ihave H' := H $$ %a, %b
  iapply H' $$ HP

/-- Tests `ihave` with intuitionistic forall specialization and subgoal -/
example [BI PROP] (P Q : α → PROP) (a b : α) : (□ ∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
  iintro H HP
  ihave H' := H $$ %a, %b, [HP]
  . iexact HP
  iexact H'

end ihave

-- ex falso
namespace exfalso

/-- Tests false elimination via empty pattern -/
example [BI PROP] (Q : PROP) : False ⊢ Q := by
  iintro ⟨⟩

/-- Tests `iexfalso` with false hypothesis -/
example [BI PROP] (P : PROP) : □ P ⊢ False -∗ Q := by
  iintro _HP HF
  iexfalso
  iexact HF

/-- Tests `iexfalso` with pure false from Lean -/
example [BI PROP] (P : PROP) (HF : False) : ⊢ P := by
  istart
  iexfalso
  ipure_intro
  exact HF

end exfalso

-- pure
namespace pure

/-- Tests `ipure` to move pure hypothesis to Lean context -/
example [BI PROP] (Q : PROP) : <affine> ⌜φ⌝ ⊢ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  ipure Hφ
  iexact HQ

/-- Tests `ipure` with multiple pure hypotheses -/
example [BI PROP] (Q : PROP) : <affine> ⌜φ1⌝ ⊢ <affine> ⌜φ2⌝ -∗ Q -∗ Q := by
  iintro Hφ1
  iintro Hφ2
  iintro HQ
  ipure Hφ1
  ipure Hφ2
  iexact HQ

/-- Tests `ipure` with conjunction containing pure -/
example [BI PROP] (Q : PROP) : (⌜φ1⌝ ∧ <affine> ⌜φ2⌝) ⊢ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  ipure Hφ
  iexact HQ

end pure

-- intuitionistic
namespace intuitionistic

/-- Tests `iintuitionistic` to move hypothesis to intuitionistic context -/
example [BI PROP] (P : PROP) : □ P ⊢ Q -∗ Q := by
  iintro HP
  iintro HQ
  iintuitionistic HP
  iexact HQ

/-- Tests `iintuitionistic` with multiple hypotheses -/
example [BI PROP] (P : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro HP
  iintro HQ
  iintuitionistic HP
  iintuitionistic HQ
  iexact HQ

/-- Tests `iintuitionistic` applied twice to same hypothesis -/
example [BI PROP] (P : PROP) : □ P ⊢ Q -∗ Q := by
  iintro HP
  iintro HQ
  iintuitionistic HP
  iintuitionistic HP
  iexact HQ

end intuitionistic

-- spatial
namespace spatial

/-- Tests `ispatial` to move hypothesis to spatial context -/
example [BI PROP] (P : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro □HP
  iintro □HQ
  ispatial HP
  iexact HQ

/-- Tests `ispatial` with multiple hypotheses -/
example [BI PROP] (P : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro □HP
  iintro □HQ
  ispatial HP
  ispatial HQ
  iexact HQ

/-- Tests `ispatial` applied twice to same hypothesis -/
example [BI PROP] (P : PROP) : □ P ⊢ □ Q -∗ Q := by
  iintro □HP
  iintro □HQ
  ispatial HP
  ispatial HP
  iexact HQ

end spatial

-- emp intro
namespace empintro

/-- Tests `iemp_intro` for proving emp -/
example [BI PROP] : ⊢@{PROP} emp := by
  iemp_intro

/-- Tests `iemp_intro` with affine environment -/
example [BI PROP] (P : PROP) : <affine> P ⊢ emp := by
  iintro _HP
  iemp_intro

end empintro

-- pure intro
namespace pureintro

/-- Tests `ipure_intro` for True -/
example [BI PROP] : ⊢@{PROP} ⌜True⌝ := by
  ipure_intro
  exact True.intro

/-- Tests `ipure_intro` for disjunction -/
example [BI PROP] : ⊢@{PROP} True ∨ False := by
  ipure_intro
  apply Or.inl True.intro

/-- Tests `ipure_intro` with context -/
example [BI PROP] (H : A → B) (P Q : PROP) : <affine> P ⊢ <pers> Q → ⌜A⌝ → ⌜B⌝ := by
  iintro _HP □_HQ
  ipure_intro
  exact H

end pureintro

-- specialize
namespace specialize

/-- Tests `ispecialize` with spatial wand -/
example [BI PROP] (Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ $$ HP
  iexact HPQ

/-- Tests `ispecialize` with subgoal -/
example [BI PROP] (Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ $$ [HP]
  . iexact HP
  iexact HPQ

/-- Tests `ispecialize` with named subgoal -/
example [BI PROP] (Q : PROP) : P ⊢ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ $$ [HP] as G
  case G => iexact HP
  iexact HPQ

/-- Tests `ispecialize` with intuitionistic wand -/
example [BI PROP] (Q : PROP) : □ P ⊢ □ (P -∗ Q) -∗ □ Q := by
  iintro □HP □HPQ
  ispecialize HPQ $$ HP
  iexact HPQ

/-- Tests `ispecialize` with intuitionistic wand and subgoal -/
example [BI PROP] (Q : PROP) : □ P ⊢ □ (P -∗ Q) -∗ Q := by
  iintro □HP □HPQ
  ispecialize HPQ $$ []
  . iexact HP
  iexact HPQ

/-- Tests `ispecialize` with intuitionistic wand requiring intuitionistic argument -/
example [BI PROP] (Q : PROP) : □ P ⊢ □ (□ P -∗ Q) -∗ □ Q := by
  iintro □HP □HPQ
  ispecialize HPQ $$ HP
  iexact HPQ

/-- Tests `ispecialize` with intuitionistic premise and spatial wand -/
example [BI PROP] (Q : PROP) : □ P ⊢ (P -∗ Q) -∗ Q := by
  iintro □HP HPQ
  ispecialize HPQ $$ HP
  iexact HPQ

/-- Tests `ispecialize` with intuitionistic premise required by spatial wand -/
example [BI PROP] (Q : PROP) : □ P ⊢ (□ P -∗ Q) -∗ Q := by
  iintro □HP HPQ
  ispecialize HPQ $$ HP
  iexact HPQ

/-- Tests `ispecialize` with spatial premise and intuitionistic wand -/
example [BI PROP] (Q : PROP) : P ⊢ □ (P -∗ Q) -∗ Q := by
  iintro HP □HPQ
  ispecialize HPQ $$ HP
  iexact HPQ

/-- Tests `ispecialize` with multiple spatial arguments -/
example [BI PROP] (Q : PROP) : ⊢ P1 -∗ P2 -∗ (P1 -∗ P2 -∗ Q) -∗ Q := by
  iintro HP1 HP2 HPQ
  ispecialize HPQ $$ HP1, HP2
  iexact HPQ

/-- Tests `ispecialize` with multiple subgoals -/
example [BI PROP] (Q : PROP) : ⊢ P1 -∗ P2 -∗ (P1 -∗ P2 -∗ Q) -∗ Q := by
  iintro HP1 HP2 HPQ
  ispecialize HPQ $$ [HP1], [HP2]
  . iexact HP1
  . iexact HP2
  iexact HPQ

/-- Tests `ispecialize` with multiple intuitionistic arguments -/
example [BI PROP] (Q : PROP) :
    ⊢ □ P1 -∗ □ P2 -∗ □ (P1 -∗ □ P2 -∗ Q) -∗ □ Q := by
  iintro □HP1 □HP2 □HPQ
  ispecialize HPQ $$ HP1, HP2
  iexact HPQ

/-- Tests `ispecialize` with mixed spatial and intuitionistic arguments -/
example [BI PROP] (Q : PROP) :
    ⊢ P1 -∗ □ P2 -∗ P3 -∗ □ (P1 -∗ P2 -∗ P3 -∗ Q) -∗ Q := by
  iintro HP1 □HP2 HP3 HPQ
  ispecialize HPQ $$ HP1, HP2, HP3
  iexact HPQ

/-- Tests `ispecialize` with forall in spatial context -/
example [BI PROP] (Q : Nat → PROP) : ⊢ (∀ x, Q x) -∗ Q (y + 1) := by
  iintro HQ
  ispecialize HQ $$ %(y + 1)
  iexact HQ

/-- Tests `ispecialize` with forall in intuitionistic context -/
example [BI PROP] (Q : Nat → PROP) : ⊢ □ (∀ x, Q x) -∗ □ Q y := by
  iintro □HQ
  ispecialize HQ $$ %y
  iexact HQ

/-- Tests `ispecialize` with forall returning intuitionistic proposition -/
example [BI PROP] (Q : Nat → PROP) : ⊢ (∀ x, □ Q x) -∗ □ Q y := by
  iintro HQ
  ispecialize HQ $$ %y
  iexact HQ

/-- Tests `ispecialize` with multiple forall in spatial context -/
example [BI PROP] (Q : Nat → Nat → PROP) :
    ⊢ (∀ x, ∀ y, Q x y) -∗ Q x y := by
  iintro HQ
  ispecialize HQ $$ %x, %y
  iexact HQ

/-- Tests `ispecialize` with multiple forall in intuitionistic context -/
example [BI PROP] (Q : Nat → Nat → PROP) :
    ⊢ □ (∀ x, ∀ y, Q x y) -∗ □ Q x y := by
  iintro □HQ
  ispecialize HQ $$ %x, %y
  iexact HQ

/-- Tests `ispecialize` with nested forall and intuitionistic -/
example [BI PROP] (Q : Nat → Nat → PROP) : ⊢ (∀ x, □ (∀ y, Q x y)) -∗ □ Q x y := by
  iintro HQ
  ispecialize HQ $$ %x, %y
  iexact HQ

/-- Tests `ispecialize` with mixed forall and wand specialization -/
example [BI PROP] (Q : Nat → PROP) :
    ⊢ □ P1 -∗ P2 -∗ (□ P1 -∗ (∀ x, P2 -∗ Q x)) -∗ Q y := by
  iintro □HP1 HP2 HPQ
  ispecialize HPQ $$ HP1, %y, HP2
  iexact HPQ

/-- Tests `ispecialize` with pure True wand using `.intro` -/
example [BI PROP] (P : PROP) :
    ⊢ (True -∗ P) -∗ P := by
  iintro H
  ispecialize H $$ %.intro
  iexact H

/-- Tests `ispecialize` with pure wand using tactic -/
example [BI PROP] (P : PROP) :
    ⊢ (True -∗ P) -∗ P := by
  iintro H
  ispecialize H $$ %(by grind)
  iexact H

/-- Tests `ispecialize` alternating pure and spatial arguments -/
example [BI PROP] (P Q : PROP) :
    ⊢ (∀ x, P -∗ ⌜x = 1⌝ -∗ Q) -∗ P -∗ Q := by
  iintro H HP
  ispecialize H $$ %_, HP, %rfl
  iexact H

/-- Tests `ispecialize` with pure subgoal -/
example [BI PROP] (P Q : PROP) :
    ⊢ (∀ x, P -∗ ⌜x = 1⌝ -∗ Q) -∗ P -∗ Q := by
  iintro H HP
  ispecialize H $$ %_, HP, %_
  · rfl
  iexact H

end specialize

-- split
namespace split

/-- Tests `isplit` for conjunction -/
example [BI PROP] (Q : PROP) : Q ⊢ Q ∧ Q := by
  iintro HQ
  isplit
  <;> iexact HQ

/-- Tests `isplitl` with explicit left hypotheses -/
example [BI PROP] [BIAffine PROP] (Q : PROP) : ⊢ P -∗ Q -∗ R -∗ P ∗ Q := by
  iintro HP
  iintro HQ
  iintro _HR
  isplitl [HP _HR]
  · iexact HP
  · iexact HQ

/-- Tests `isplitr` with explicit right hypotheses -/
example [BI PROP] [BIAffine PROP] (Q : PROP) : ⊢ P -∗ Q -∗ R -∗ P ∗ Q := by
  iintro HP
  iintro HQ
  iintro _HR
  isplitr [HQ]
  · iexact HP
  · iexact HQ

/-- Tests `isplitl` without argument -/
example [BI PROP] [BIAffine PROP] (Q : PROP) : ⊢ P -∗ □ Q -∗ R -∗ P ∗ Q := by
  iintro HP
  iintro □HQ
  iintro _HR
  isplitl
  · iexact HP
  · iexact HQ

/-- Tests `isplitr` without argument -/
example [BI PROP] [BIAffine PROP] (Q : PROP) : ⊢ □ P -∗ Q -∗ R -∗ P ∗ Q := by
  iintro □HP
  iintro HQ
  iintro _HR
  isplitr
  · iexact HP
  · iexact HQ

end split

-- left / right
namespace leftright

/-- Tests `ileft` -/
example [BI PROP] (P : PROP) : P ⊢ P ∨ Q := by
  iintro HP
  ileft
  iexact HP

/-- Tests `iright` -/
example [BI PROP] (Q : PROP) : Q ⊢ P ∨ Q := by
  iintro HQ
  iright
  iexact HQ

/-- Tests nested disjunction with left and right -/
example [BI PROP] (P Q : PROP) : ⊢ P -∗ Q -∗ P ∗ (R ∨ Q ∨ R) := by
  iintro HP HQ
  isplitl [HP]
  · iassumption
  iright
  ileft
  iexact HQ

end leftright

-- cases
namespace cases

/-- Tests `icases` for simple renaming -/
example [BI PROP] (P : PROP) : P ⊢ P := by
  iintro HP
  icases HP with H
  iexact H

/-- Tests `icases` to clear hypothesis -/
example [BI PROP] (P Q : PROP) : ⊢ P -∗ <affine> Q -∗ P := by
  iintro HP
  iintro HQ
  icases HQ with -
  iexact HP

/-- Tests `icases` with nested conjunction -/
example [BI PROP] (Q : PROP) : □ (P1 ∧ P2 ∧ Q) ⊢ Q := by
  iintro □HP
  icases HP with ⟨_HP1, _HP2, HQ⟩
  iexact HQ

/-- Tests `icases` with intuitionistic conjunction -/
example [BI PROP] (Q : PROP) : □ P ∧ Q ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨_HP, HQ⟩
  iexact HQ

/-- Tests `icases` on conjunction with persistent left -/
example [BI PROP] (Q : PROP) : <pers> Q ∧ <affine> P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨□HQ, _HP⟩
  iexact HQ

/-- Tests `icases` on conjunction with persistent right -/
example [BI PROP] (Q : PROP) : Q ∧ <pers> P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨HQ, _HP⟩
  iexact HQ

/-- Tests `icases` with nested separating conjunction -/
example [BI PROP] [BIAffine PROP] (Q : PROP) : P1 ∗ P2 ∗ Q ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨_HP1, _HP2, HQ⟩
  iexact HQ

/-- Tests `icases` with nested disjunction -/
example [BI PROP] (Q : PROP) : Q ⊢ <affine> (P1 ∨ P2 ∨ P3) -∗ Q := by
  iintro HQ
  iintro HP
  icases HP with (_HP1 | _HP2 | _HP3)
  <;> iexact HQ

/-- Tests `icases` with complex mixed conjunction and disjunction -/
example [BI PROP] [BIAffine PROP] (Q : PROP) :
    (P11 ∨ P12 ∨ P13) ∗ P2 ∗ (P31 ∨ P32 ∨ P33) ∗ Q ⊢ Q := by
  iintro HP
  icases HP with ⟨_HP11 | _HP12 | _HP13, HP2, HP31 | HP32 | HP33, HQ⟩
  <;> iexact HQ

/-- Tests `icases` moving pure to Lean context with ⌜⌝ -/
example [BI PROP] (Q : PROP) : ⊢ <affine> ⌜⊢ Q⌝ -∗ Q := by
  iintro HQ
  icases HQ with ⌜HQ⌝
  istop
  exact HQ

/-- Tests `icases` moving pure to Lean context with % -/
example [BI PROP] (Q : PROP) : ⊢ <affine> ⌜⊢ Q⌝ -∗ Q := by
  iintro HQ
  icases HQ with %HQ
  istop
  exact HQ

/-- Tests `icases` moving to intuitionistic with □ -/
example [BI PROP] (Q : PROP) : ⊢ □ Q -∗ Q := by
  iintro HQ
  icases HQ with □HQ
  iexact HQ

/-- Tests `icases` moving to intuitionistic with # -/
example [BI PROP] (Q : PROP) : ⊢ □ Q -∗ Q := by
  iintro HQ
  icases HQ with #HQ
  iexact HQ

/-- Tests `icases` moving to spatial with ∗ -/
example [BI PROP] (Q : PROP) : ⊢ □ Q -∗ Q := by
  iintro □HQ
  icases HQ with ∗HQ
  iexact HQ

/-- Tests `icases` moving to spatial with * -/
example [BI PROP] (Q : PROP) : ⊢ □ Q -∗ Q := by
  iintro □HQ
  icases HQ with *HQ
  iexact HQ

/-- Tests `icases` with pure in conjunction -/
example [BI PROP] (Q : PROP) : ⊢ <affine> ⌜φ⌝ ∗ Q -∗ Q := by
  iintro HφQ
  icases HφQ with ⟨⌜Hφ⌝, HQ⟩
  iexact HQ

/-- Tests `icases` with pure in disjunction -/
example [BI PROP] (Q : PROP) :
    ⊢ <affine> ⌜φ1⌝ ∨ <affine> ⌜φ2⌝ -∗ Q -∗ Q := by
  iintro Hφ
  iintro HQ
  icases Hφ with (⌜Hφ1⌝ | ⌜Hφ2⌝)
  <;> iexact HQ

/-- Tests `icases` with intuitionistic in conjunction -/
example [BI PROP] (Q : PROP) : ⊢ □ P ∗ Q -∗ Q := by
  iintro HPQ
  icases HPQ with ⟨□_HP, HQ⟩
  iexact HQ

/-- Tests `icases` with intuitionistic in disjunction -/
example [BI PROP] (Q : PROP) : ⊢ □ Q ∨ Q -∗ Q := by
  iintro HQQ
  icases HQQ with (□HQ | HQ)
  <;> iexact HQ

/-- Tests `icases` moving to spatial inside intuitionistic conjunction -/
example [BI PROP] (Q : PROP) : ⊢ □ (P ∧ Q) -∗ Q := by
  iintro □HPQ
  icases HPQ with ⟨_HP, ∗HQ⟩
  iexact HQ

/-- Tests `icases` with or inside intuitionistic, moving one to spatial -/
example [BI PROP] (Q : PROP) : ⊢ □ (Q ∨ Q) -∗ Q := by
  iintro □HPQ
  icases HPQ with (HQ | ∗HQ)
  <;> iexact HQ

/-- Tests `icases` moving whole hypothesis to intuitionistic then destructing -/
example [BI PROP] (Q : PROP) : ⊢ □ (P ∧ Q) -∗ Q := by
  iintro HPQ
  icases HPQ with □⟨_HP, ∗HQ⟩
  iexact HQ

/-- Tests `icases` with or, moving whole to intuitionistic -/
example [BI PROP] (Q : PROP) : ⊢ □ (Q ∨ Q) -∗ Q := by
  iintro HPQ
  icases HPQ with □(HQ | ∗HQ)
  <;> iexact HQ

/-- Tests `icases` clearing in conjunction -/
example [BI PROP] [BIAffine PROP] (Q : PROP) : Q ∗ P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨HQ, -⟩
  iexact HQ

/-- Tests `icases` clearing in disjunction -/
example [BI PROP] [BIAffine PROP] (Q : PROP) : Q ⊢ P1 ∨ P2 -∗ Q := by
  iintro HQ
  iintro HP
  icases HP with (- | _HP2)
  <;> iexact HQ

/-- Tests `icases` destructing conjunction left -/
example [BI PROP] (Q : PROP) : P ∧ Q ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨-, HQ⟩
  iexact HQ

/-- Tests `icases` destructing conjunction right -/
example [BI PROP] (Q : PROP) : Q ∧ P ⊢ Q := by
  iintro HQP
  icases HQP with ⟨HQ, -⟩
  iexact HQ

/-- Tests `icases` destructing multiple conjunctions  -/
example [BI PROP] (Q : PROP) : P1 ∧ P2 ∧ Q ∧ P3 ⊢ Q := by
  iintro HPQ
  icases HPQ with ⟨-, -, HQ, -⟩
  iexact HQ

/-- Tests `icases` destructing intuitionistic conjunction, clearing left -/
example [BI PROP] (Q : PROP) : □ (P ∧ Q) ⊢ Q := by
  iintro □HPQ
  icases HPQ with ⟨-, HQ⟩
  iexact HQ

/-- Tests `icases` destructing intuitionistic conjunction, clearing right -/
example [BI PROP] (Q : PROP) : □ (Q ∧ P) ⊢ Q := by
  iintro □HQP
  icases HQP with ⟨HQ, -⟩
  iexact HQ

/-- Tests `icases` destructing multiple intuitionistic conjunctions -/
example [BI PROP] (Q : PROP) : □ (P1 ∧ P2 ∧ Q ∧ P3) ⊢ Q := by
  iintro □HPQ
  icases HPQ with ⟨-, -, HQ, -⟩
  iexact HQ

/-- Tests `icases` with existential -/
example [BI PROP] (Q : Nat → PROP) : (∃ x, Q x) ⊢ ∃ x, Q x ∨ False := by
  iintro ⟨x, H⟩
  iexists x
  ileft
  iexact H

/-- Tests `icases` with intuitionistic existential -/
example [BI PROP] (Q : Nat → PROP) : □ (∃ x, Q x) ⊢ ∃ x, □ Q x ∨ False := by
  iintro ⟨x, □H⟩
  iexists x
  ileft
  iexact H

end cases
