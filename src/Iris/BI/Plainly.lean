/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.BI.Classes
import Iris.BI.BI
import Iris.BI.DerivedLaws
import Iris.Algebra

namespace Iris
open BI

/-- Bidirectional entailment on separation logic propositions. -/
local macro:25 P:term:29 " ⊣⊢ " Q:term:29 : term => ``(BI.BiEquiv iprop($P) iprop($Q))

class Plainly (PROP : Type _) where
  plainly : PROP → PROP
export Plainly(plainly)

syntax "■ " term:40 : term

macro_rules
  | `(iprop(■ $P))  => ``(Plainly.plainly iprop($P))

delab_rule Plainly.plainly
  | `($_ $P) => do ``(iprop(■ $(← Iris.BI.unpackIprop P)))

def Plainly.plainlyIf [Iris.BI.BIBase PROP] [Plainly PROP] (p : Bool) (P : PROP) : PROP :=
  iprop(if p then ■ P else P)

syntax:max "■?" term:max ppHardSpace term:40 : term

macro_rules
  | `(iprop(■? $p $P))  => ``(Plainly.plainlyIf $p iprop($P))

delab_rule Plainly.plainlyIf
  | `($_ $p $P) => do ``(iprop(■? $p $(← Iris.BI.unpackIprop P)))


-- FIXME: These names are inconsistent
class BIPlainly (PROP : Type _) [Iris.BI PROP] extends Plainly PROP where
  [ne : Iris.OFE.NonExpansive (Plainly.plainly (PROP := PROP))]
  mono {P Q : PROP} : (P ⊢ Q) → ■ P ⊢ ■ Q
  elim_persistently {P : PROP} : ■ P ⊢ <pers> P
  idem {P : PROP} : ■ P ⊢ ■ ■ P
  plainly_sForall_2 {Φ : PROP → Prop} : (∀ p, ⌜Φ p⌝ → ■ p) ⊢ ■ sForall Φ
  plainly_impl_plainly {P Q : PROP} : (■ P → ■ Q) ⊢ ■ (■ P → Q)
  emp_intro {P : PROP} : P ⊢ ■ emp
  plainly_absorb {P Q : PROP} : ■ P ∗ Q ⊢ ■ P
  later_plainly {P : PROP} : ▷ ■ P ⊣⊢ ■ ▷ P

class BIPersistentlyImplPlainly (PROP : Type _) [Iris.BI PROP] [BIPlainly PROP] where
  pers_impl_plainly (P Q : PROP) : (■ P → <pers> Q) ⊢ <pers> (■ P → Q)

class BIPlainlyExists (PROP : Type _) [Iris.BI PROP] [BIPlainly PROP] where
  plainly_sExists_1 {Φ : PROP → Prop} : ■ sExists Φ ⊢ ∃ p, ⌜Φ p⌝ ∧ ■ p

namespace BI
open Iris.Std

export BIPlainly (plainly_sForall_2 plainly_impl_plainly plainly_absorb later_plainly)
export BIPersistentlyImplPlainly (pers_impl_plainly)
export BIPlainlyExists (plainly_sExists_1)

class Plain [BI PROP] [Plainly PROP] [BIPlainly PROP] (P : PROP) where
  plain : P ⊢ ■ P

instance [BI PROP] [BIPlainly PROP] (P : PROP) : Plain iprop(■ P) :=
  ⟨BIPlainly.idem⟩

section PlainlyLaws
open BIPlainly

variable [BI PROP] [BIPlainly PROP]
variable {P Q R : PROP}

theorem affinely_plainly_elim : <affine> ■ P ⊢ P :=
  (affinely_mono elim_persistently).trans persistently_and_emp_elim

theorem persistently_elim_plainly : <pers> ■ P ⊣⊢ ■ P :=
  BI.equiv_entails.mpr ⟨absorbingly_of_persistently.trans <| sep_symm.trans plainly_absorb,
   idem.trans elim_persistently⟩

theorem plainly_forall_2 {Ψ : α → PROP} : (∀ a, ■ (Ψ a)) ⊢ ■ (∀ a, Ψ a) := by
  refine (forall_intro ?_).trans plainly_sForall_2
  intro P
  refine imp_intro' ?_
  refine (BI.equiv_entails.mp and_comm).1.trans <| imp_elim' <| pure_elim _ .rfl ?_
  rintro ⟨_, Ha⟩
  rewrite [← Ha]
  exact imp_intro' <| and_elim_l.trans <| forall_elim _

theorem plainly_persistently_elim : ■ <pers> P ⊣⊢ ■ P := by
  apply BI.equiv_entails.mpr; constructor
  · refine ((BI.equiv_entails.mp true_and).2.trans <| and_mono emp_intro .rfl).trans ?_
    refine .trans ?_ (mono <| (BI.equiv_entails.mp and_forall_bool).2.trans persistently_and_emp_elim)
    refine (BI.equiv_entails.mp and_forall_bool).1.trans ?_
    refine .trans ?_ plainly_forall_2
    refine forall_mono ?_
    exact (·.casesOn .rfl .rfl)
  · exact idem.trans <| mono elim_persistently

theorem absorbingly_elim_plainly : <absorb> ■ P ⊣⊢ ■ P := by
  apply BI.equiv_entails.mpr; constructor
  · refine (absorbingly_mono <| (BI.equiv_entails.mp persistently_elim_plainly).2).trans ?_
    refine .trans ?_ (BI.equiv_entails.mp persistently_elim_plainly).1
    exact (BI.equiv_entails.mp absorbingly_persistently).1.trans .rfl
  · refine .trans ?_ (absorbingly_mono (BI.equiv_entails.mp persistently_elim_plainly).1)
    refine (BI.equiv_entails.mp persistently_elim_plainly).2.trans ?_
    exact .trans .rfl (BI.equiv_entails.mp absorbingly_persistently).2

theorem plainly_and_sep_elim : ■ P ∧ Q ⊢ (emp ∧ P) ∗ Q :=
  (and_mono elim_persistently .rfl).trans persistently_and_sep_elim_emp

theorem plainly_and_sep_assoc : ■ P ∧ (Q ∗ R) ⊣⊢ (■ P ∧ Q) ∗ R := by
  apply BI.equiv_entails.mpr; constructor
  · refine (and_mono (BI.equiv_entails.mp persistently_elim_plainly).2 BIBase.Entails.rfl).trans ?_
    refine .trans ?_ (sep_mono (and_mono (BI.equiv_entails.mp persistently_elim_plainly).1 .rfl) .rfl)
    exact (BI.equiv_entails.mp persistently_and_sep_assoc).1
  · refine .trans ?_ (and_mono (BI.equiv_entails.mp persistently_elim_plainly).1 .rfl)
    refine (sep_mono (and_mono (BI.equiv_entails.mp persistently_elim_plainly).2 .rfl) .rfl).trans ?_
    exact (BI.equiv_entails.mp persistently_and_sep_assoc).2

theorem plainly_and_emp_elim : emp ∧ ■ P ⊢ P :=
  (and_mono .rfl elim_persistently).trans persistently_and_emp_elim

theorem plainly_into_absorbingly : ■ P ⊢ <absorb> P :=
  elim_persistently.trans absorbingly_of_persistently

theorem plainly_elim [Absorbing P] : ■ P ⊢ P :=
  elim_persistently.trans persistently_elim

theorem plainly_idemp : ■ ■ P ⊣⊢ ■ P :=
  BI.equiv_entails.mpr ⟨plainly_into_absorbingly.trans (BI.equiv_entails.mp absorbingly_elim_plainly).1, idem⟩

theorem plainly_intro' (H : ■ P ⊢ Q) : ■ P ⊢ ■ Q :=
  (BI.equiv_entails.mp plainly_idemp).2.trans <| mono <| H

theorem plainly_pure {φ} : ■ ⌜φ⌝ ⊣⊢ (⌜φ⌝ : PROP) := by
  apply BI.equiv_entails.mpr; constructor
  · exact elim_persistently.trans persistently_elim
  · refine pure_elim' fun φ => ?_
    apply Entails.trans (Q := «forall» (fun x : Empty => iprop(■ True)))
    · exact forall_intro Empty.rec
    · exact plainly_forall_2.trans (mono <| pure_intro φ)

theorem plainly_forall {Ψ : α → PROP} : ■ (∀ a, Ψ a) ⊣⊢ ∀ a, ■ (Ψ a) :=
  BI.equiv_entails.mpr ⟨forall_intro (mono <| forall_elim ·), plainly_forall_2⟩

theorem plainly_exists_2 {α : Sort _} {Ψ : α → PROP} : (∃ a, ■ (Ψ a)) ⊢ ■ (∃ a, Ψ a) :=
  exists_elim (mono <| exists_intro ·)

theorem plainly_exists_1 [BIPlainlyExists PROP] {Ψ : α → PROP} :
    ■ (∃ a, Ψ a) ⊢ ∃ a, ■ (Ψ a) := by
  refine plainly_sExists_1.trans ?_
  refine exists_elim fun p => imp_elim <| pure_elim' ?_
  rintro ⟨a, rfl⟩
  exact imp_intro' <| exists_intro' a and_elim_l

theorem plainly_exists [BIPlainlyExists PROP] {Ψ : α → PROP} : ■ (∃ a, Ψ a) ⊣⊢ ∃ a, ■ (Ψ a) :=
  BI.equiv_entails.mpr ⟨plainly_exists_1, plainly_exists_2⟩

theorem plainly_and : ■ (P ∧ Q) ⊣⊢ ■ P ∧ ■ Q := by
  apply BI.equiv_entails.mpr; constructor
  · refine (mono (BI.equiv_entails.mp and_forall_bool).1).trans (.trans ?_ (BI.equiv_entails.mp and_forall_bool).2)
    exact (BI.equiv_entails.mp plainly_forall).1.trans (forall_mono (·.casesOn .rfl .rfl))
  · refine ((BI.equiv_entails.mp and_forall_bool).1).trans (.trans ?_ (mono <| (BI.equiv_entails.mp and_forall_bool).2))
    refine .trans (forall_mono ?_) (BI.equiv_entails.mp plainly_forall).2
    exact (·.casesOn .rfl .rfl)

theorem plainly_or_2 : ■ P ∨ ■ Q ⊢ ■ (P ∨ Q) := by
  refine (BI.equiv_entails.mp or_exists_bool).1.trans (.trans ?_ (mono <| (BI.equiv_entails.mp or_exists_bool).2))
  refine .trans (exists_mono ?_) plainly_exists_2
  exact (·.casesOn .rfl .rfl)

theorem plainly_or [BIPlainlyExists PROP] : ■ (P ∨ Q) ⊣⊢ ■ P ∨ ■ Q := by
  apply BI.equiv_entails.mpr; constructor
  · refine (mono (BI.equiv_entails.mp or_exists_bool).1).trans (.trans ?_ (BI.equiv_entails.mp or_exists_bool).2)
    exact plainly_exists_1.trans <| exists_mono (·.casesOn .rfl .rfl)
  · exact plainly_or_2

theorem plainly_impl : ■ (P → Q) ⊢ ■ P → ■ Q := by
  refine imp_intro' <| (BI.equiv_entails.mp plainly_and).2.trans ?_
  exact mono imp_elim_r

theorem plainly_emp_2 : (emp : PROP) ⊢ ■ emp := emp_intro

theorem plainly_sep_dup : ■ P ⊣⊢ ■ P ∗ ■ P := by
  apply BI.equiv_entails.mpr; constructor
  · refine (BI.equiv_entails.mp and_self).2.trans ?_
    refine ((and_mono .rfl (BI.equiv_entails.mp emp_sep).2).trans (BI.equiv_entails.mp plainly_and_sep_assoc).1).trans ?_
    exact (sep_mono and_elim_l .rfl).trans .rfl
  · exact plainly_absorb

theorem plainly_and_sep_l_1 : ■ P ∧ Q ⊢ ■ P ∗ Q := by
  refine ((and_mono BIBase.Entails.rfl (BI.equiv_entails.mp emp_sep).2).trans (BI.equiv_entails.mp plainly_and_sep_assoc).1).trans ?_
  exact (sep_mono and_elim_l .rfl).trans .rfl

theorem plainly_and_sep_r_1 : P ∧ ■ Q ⊢ P ∗ ■ Q :=
  (BI.equiv_entails.mp and_comm).1.trans <| plainly_and_sep_l_1.trans sep_symm

theorem plainly_true_emp : ■ True ⊣⊢ ■ (emp : PROP) :=
  BI.equiv_entails.mpr ⟨emp_intro, mono true_intro⟩

theorem plainly_and_sep : ■ (P ∧ Q) ⊢ ■ (P ∗ Q) := by
  refine ((BI.equiv_entails.mp plainly_and).1.trans <| (and_mono idem .rfl).trans (BI.equiv_entails.mp plainly_and).2).trans ?_
  refine (mono <| and_mono .rfl (BI.equiv_entails.mp emp_sep).2).trans ?_
  refine (mono <| (BI.equiv_entails.mp plainly_and_sep_assoc).1).trans ?_
  refine (mono <| sep_mono (BI.equiv_entails.mp and_comm).1 .rfl).trans ?_
  exact (mono <| sep_mono plainly_and_emp_elim .rfl).trans .rfl

theorem plainly_affinely_elim : ■ <affine> P ⊣⊢ ■ P := by
  apply BI.equiv_entails.mpr; constructor
  · refine (BI.equiv_entails.mp plainly_and).1.trans ?_
    refine (and_mono (BI.equiv_entails.mp plainly_true_emp).2 .rfl).trans ?_
    exact (and_mono (BI.equiv_entails.mp plainly_pure).1 .rfl).trans and_elim_r
  · refine .trans ?_ (BI.equiv_entails.mp plainly_and).2
    refine .trans ?_ (and_mono (BI.equiv_entails.mp plainly_true_emp).1 .rfl)
    refine .trans ?_ (and_mono (BI.equiv_entails.mp plainly_pure).2 .rfl)
    exact and_intro true_intro .rfl

theorem intuitionistically_plainly_elim : □ ■ P ⊢ □ P :=
  (BI.equiv_entails.mp intuitionistically_affinely).2.trans <| intuitionistically_mono affinely_plainly_elim

theorem intuitionistically_plainly : □ ■ P ⊢ ■ □ P := by
  refine (affinely_elim.trans ?_).trans (BI.equiv_entails.mp plainly_affinely_elim).2
  exact (BI.equiv_entails.mp persistently_elim_plainly).1.trans (BI.equiv_entails.mp plainly_persistently_elim).2

theorem and_sep_plainly : ■ P ∧ ■ Q ⊣⊢ ■ P ∗ ■ Q :=
  BI.equiv_entails.mpr ⟨plainly_and_sep_l_1, and_intro plainly_absorb (sep_symm.trans plainly_absorb)⟩

theorem plainly_sep_2 : ■ P ∗ ■ Q ⊢ ■ (P ∗ Q) :=
  (BI.equiv_entails.mp and_sep_plainly).2.trans <| (BI.equiv_entails.mp plainly_and).2.trans plainly_and_sep

theorem plainly_sep [BIPositive PROP] : ■ (P ∗ Q) ⊣⊢ ■ P ∗ ■ Q := by
  apply BI.equiv_entails.mpr; constructor
  · refine (BI.equiv_entails.mp plainly_affinely_elim).2.trans ?_
    refine (mono <| (BI.equiv_entails.mp affinely_sep).1).trans ?_
    refine .trans ?_ (BI.equiv_entails.mp and_sep_plainly).1
    refine and_intro (mono ?_) (mono ?_)
    · exact ((sep_mono .rfl affinely_elim_emp).trans (BI.equiv_entails.mp sep_emp).1).trans affinely_elim
    · exact ((sep_mono affinely_elim_emp .rfl).trans (BI.equiv_entails.mp emp_sep).1).trans affinely_elim
  · exact plainly_sep_2

theorem plainly_wand : ■ (P -∗ Q) ⊢ ■ P -∗ ■ Q :=
  wand_intro <| plainly_sep_2.trans (mono wand_elim_l)

theorem plainly_entails_l (H : P ⊢ ■ Q) : P ⊢ ■ Q ∗ P :=
  (and_intro H .rfl).trans plainly_and_sep_l_1

theorem plainly_entails_r (H : P ⊢ ■ Q) : P ⊢ P ∗ ■ Q :=
  (and_intro .rfl H).trans plainly_and_sep_r_1

theorem plainly_impl_wand_2 : ■ (P -∗ Q) ⊢ ■ (P → Q) := by
  refine plainly_intro' (imp_intro ?_)
  refine (and_mono .rfl (BI.equiv_entails.mp emp_sep).2).trans ?_
  refine (BI.equiv_entails.mp plainly_and_sep_assoc).1.trans ?_
  refine (sep_mono ((BI.equiv_entails.mp and_comm).1.trans plainly_and_emp_elim) .rfl).trans ?_
  exact wand_elim_l

theorem impl_wand_plainly_2 : (■ P -∗ Q) ⊢ (■ P → Q) :=
  imp_intro' <| plainly_and_sep_l_1.trans wand_elim_r

theorem impl_wand_affinely_plainly : (■ P → Q) ⊣⊢ (<affine> ■ P -∗ Q) := by
  apply BI.equiv_entails.mpr; constructor
  · refine (imp_mono_l (BI.equiv_entails.mp persistently_elim_plainly).1).trans ?_
    refine (BI.equiv_entails.mp intuitionistically_wand).2.trans ?_
    exact wand_mono_l <| affinely_mono (BI.equiv_entails.mp persistently_elim_plainly).2
  · refine .trans ?_ (imp_mono_l (BI.equiv_entails.mp persistently_elim_plainly).2)
    refine .trans ?_ (BI.equiv_entails.mp intuitionistically_wand).1
    exact wand_mono_l affinely_of_intuitionistically

theorem persistently_wand_affinely_plainly [BIPersistentlyImplPlainly PROP] :
    (<affine> ■ P -∗ <pers> Q) ⊢ <pers> (<affine> ■ P -∗ Q) := by
  refine (BI.equiv_entails.mp impl_wand_affinely_plainly).2.trans  ?_
  refine .trans ?_ (persistently_mono (BI.equiv_entails.mp impl_wand_affinely_plainly).1)
  exact pers_impl_plainly _ _

theorem plainly_wand_affinely_plainly : (<affine> ■ P -∗ ■ Q) ⊢ ■ (<affine> ■ P -∗ Q) := by
  refine (BI.equiv_entails.mp impl_wand_affinely_plainly).2.trans ?_
  refine .trans ?_ (mono (BI.equiv_entails.mp impl_wand_affinely_plainly).1)
  exact plainly_impl_plainly

section AffineBI

variable [BIAffine PROP]

theorem plainly_emp : ■ emp ⊣⊢ (emp : PROP) :=
  BI.equiv_entails.mpr ⟨plainly_elim, plainly_emp_2⟩

theorem plainly_and_sep_l : ■ P ∧ Q ⊣⊢ ■ P ∗ Q :=
  BI.equiv_entails.mpr ⟨plainly_and_sep_l_1, sep_and⟩

theorem plainly_and_sep_r : P ∧ ■ Q ⊣⊢ P ∗ ■ Q := by
  apply BI.equiv_entails.mpr; constructor
  · exact (BI.equiv_entails.mp and_comm).1.trans <| (BI.equiv_entails.mp plainly_and_sep_l).1.trans sep_symm
  · exact sep_symm.trans <| (BI.equiv_entails.mp plainly_and_sep_l).2.trans (BI.equiv_entails.mp and_comm).2

theorem plainly_impl_wand : ■ (P → Q) ⊣⊢ ■ (P -∗ Q) := by
  apply BI.equiv_entails.mpr; constructor
  · refine plainly_intro' <| wand_intro' ?_
    refine (BI.equiv_entails.mp plainly_and_sep_r).2.trans ?_
    exact (and_mono .rfl plainly_elim).trans imp_elim_r
  · exact plainly_impl_wand_2

theorem impl_wand_plainly : (■ P → Q) ⊣⊢ (■ P -∗ Q) :=
  BI.equiv_entails.mpr ⟨imp_wand_1, impl_wand_plainly_2⟩

end AffineBI

end PlainlyLaws

end Iris.BI
