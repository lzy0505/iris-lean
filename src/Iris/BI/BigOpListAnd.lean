/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp

namespace Iris.BI

open Iris.Algebra
open BIBase

/-- Bidirectional entailment on separation logic propositions. -/
local macro:25 P:term:29 " ⊣⊢ " Q:term:29 : term => ``(BI.BiEquiv iprop($P) iprop($Q))

/-! # Big Conjunction over Lists

This file contains lemmas about `bigAndL`, the big conjunction over lists.
The main sections are:
- Basic structural lemmas (nil, cons, singleton, app)
- Monotonicity and congruence
- Typeclass closure (Persistent, Affine)
- Lookup/access lemmas
- Operator interaction (and, sep, pure)
- Modality interaction (persistently)
- Higher-order lemmas (intro, forall)
-/

variable {PROP : Type _} [BI PROP] {A : Type _}

namespace BigAndL

/-! ## Basic Structural Lemmas -/

@[simp]
theorem nil {Φ : Nat → A → PROP} :
    bigAndL Φ ([] : List A) ⊣⊢ iprop(True) := by
  simp only [bigAndL, bigOpL]
  exact .rfl

theorem nil' {Φ : Nat → A → PROP} {l : List A} (h : l = []) :
    bigAndL Φ l ⊣⊢ iprop(True) := by
  subst h; exact nil

theorem cons {Φ : Nat → A → PROP} {x : A} {xs : List A} :
    bigAndL Φ (x :: xs) ⊣⊢ Φ 0 x ∧ bigAndL (fun n => Φ (n + 1)) xs := by
  simp only [bigAndL, bigOpL]
  exact .rfl

theorem singleton {Φ : Nat → A → PROP} {x : A} :
    bigAndL Φ [x] ⊣⊢ Φ 0 x :=
  BigOpL.singleton Φ x

theorem app {Φ : Nat → A → PROP} {l₁ l₂ : List A} :
    bigAndL Φ (l₁ ++ l₂) ⊣⊢
      bigAndL Φ l₁ ∧ bigAndL (fun n => Φ (n + l₁.length)) l₂ :=
  BigOpL.append Φ l₁ l₂

theorem snoc {Φ : Nat → A → PROP} {l : List A} {x : A} :
    bigAndL Φ (l ++ [x]) ⊣⊢ bigAndL Φ l ∧ Φ l.length x :=
  BigOpL.snoc Φ l x

/-! ## Monotonicity and Congruence -/

theorem mono {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Φ k x ⊢ Ψ k x) :
    bigAndL Φ l ⊢ bigAndL Ψ l := by
  induction l generalizing Φ Ψ with
  | nil => exact Entails.rfl
  | cons y ys ih =>
    simp only [bigAndL, bigOpL]
    apply and_mono
    · exact h 0 y rfl
    · apply ih
      intro k x hget
      exact h (k + 1) x hget

theorem proper {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Φ k x ⊣⊢ Ψ k x) :
    bigAndL Φ l ⊣⊢ bigAndL Ψ l :=
  BigOpL.congr h

theorem congr {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Φ k x ⊣⊢ Ψ k x) :
    bigAndL Φ l ⊣⊢ bigAndL Ψ l :=
  BigOpL.congr' h

/-! ## Typeclass Closure -/

instance persistent {Φ : Nat → A → PROP} {l : List A} [∀ k x, Persistent (Φ k x)] :
    Persistent (bigAndL Φ l) where
  persistent := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigAndL, bigOpL]
      exact (BI.equiv_entails.mp persistently_true).2
    | cons x xs ih =>
      simp only [bigAndL, bigOpL]
      have h1 : Φ 0 x ⊢ <pers> Φ 0 x := Persistent.persistent
      have h2 : bigAndL (fun n => Φ (n + 1)) xs ⊢ <pers> bigAndL (fun n => Φ (n + 1)) xs := ih
      exact (and_mono h1 h2).trans (BI.equiv_entails.mp persistently_and).2

instance affine {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] :
    Affine (bigAndL Φ l) where
  affine := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigAndL, bigOpL]
      exact (BI.equiv_entails.mp true_emp).1
    | cons x xs ih =>
      simp only [bigAndL, bigOpL]
      exact and_elim_l.trans Affine.affine

/-! ## Unit/True Lemma -/

theorem true_l {l : List A} :
    bigAndL (fun _ _ => iprop(True : PROP)) l ⊣⊢ iprop(True) :=
  BigOpL.unit_const l

/-! ## Distribution over And -/

theorem and' {Φ Ψ : Nat → A → PROP} {l : List A} :
    bigAndL (fun k x => iprop(Φ k x ∧ Ψ k x)) l ⊣⊢ bigAndL Φ l ∧ bigAndL Ψ l :=
  BigOpL.op_distr Φ Ψ l

theorem and_2 {Φ Ψ : Nat → A → PROP} {l : List A} :
    bigAndL Φ l ∧ bigAndL Ψ l ⊣⊢ bigAndL (fun k x => iprop(Φ k x ∧ Ψ k x)) l :=
  and'.symm

/-! ## Take and Drop -/

theorem take_drop {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    bigAndL Φ l ⊣⊢
      bigAndL Φ (l.take n) ∧ bigAndL (fun k => Φ (n + k)) (l.drop n) :=
  BigOpL.take_drop Φ l n

/-! ## Fmap -/

theorem fmap {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    bigAndL Φ (l.map f) ⊣⊢ bigAndL (fun k x => Φ k (f x)) l := by
  induction l generalizing Φ with
  | nil => simp only [List.map_nil]; exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, bigAndL, bigOpL]
    exact and_congr OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

/-! ## Lookup Lemmas -/

-- Extract an element from bigAndL using the lookup function
-- This is simpler than the sep version because and is idempotent
theorem lookup {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    bigAndL Φ l ⊢ Φ i x := by
  induction l generalizing i Φ with
  | nil => simp at h
  | cons y ys ih =>
    simp only [bigAndL, bigOpL]
    cases i with
    | zero =>
      simp at h
      subst h
      exact and_elim_l
    | succ j =>
      simp at h
      exact and_elim_r.trans (ih h)

-- Note: big_andL_lookup_acc is not in Rocq; we only have the simpler lookup lemma above

/-! ## Higher-Order Lemmas -/

-- Introduction rule: if P entails each Φ k x, then P entails the big and
theorem intro {P : PROP} {Φ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → P ⊢ Φ k x) :
    P ⊢ bigAndL Φ l := by
  induction l generalizing Φ with
  | nil =>
    simp only [bigAndL, bigOpL]
    exact true_intro
  | cons y ys ih =>
    simp only [bigAndL, bigOpL]
    apply and_intro
    · exact h 0 y rfl
    · exact ih (fun k x hget => h (k + 1) x hget)

-- bigAndL is equivalent to forall
theorem forall' {Φ : Nat → A → PROP} {l : List A} :
    bigAndL Φ l ⊣⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) := by
  apply BI.equiv_entails.mpr
  constructor
  · -- Forward: bigAndL Φ l ⊢ ∀ k x, ⌜l[k]? = some x⌝ → Φ k x
    apply forall_intro; intro k
    apply forall_intro; intro x
    apply imp_intro
    -- Goal: bigAndL Φ l ∧ ⌜l[k]? = some x⌝ ⊢ Φ k x
    apply (BI.equiv_entails.mp and_comm).1.trans
    apply pure_elim_l
    intro hget
    exact lookup hget
  · -- Backward: (∀ k x, ⌜l[k]? = some x⌝ → Φ k x) ⊢ bigAndL Φ l
    apply intro
    intro k x hget
    calc ((∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x)) : PROP)
        ⊢ ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) := forall_elim k
      _ ⊢ iprop(⌜l[k]? = some x⌝ → Φ k x) := forall_elim x
      _ ⊢ Φ k x := by
          apply (and_intro Entails.rfl (pure_intro hget)).trans
          exact imp_elim Entails.rfl

-- Implication under bigAndL
theorem impl {Φ Ψ : Nat → A → PROP} {l : List A} :
    bigAndL Φ l ∧ (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x)) ⊢
      bigAndL Ψ l := by
  -- Use intro to construct bigAndL Ψ l
  apply intro
  intro k x hget
  -- Goal: bigAndL Φ l ∧ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x → Ψ k x) ⊢ Ψ k x
  calc (bigAndL Φ l ∧ (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x)) : PROP)
      ⊢ Φ k x ∧ (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x)) := by
        exact and_mono (lookup hget) Entails.rfl
    _ ⊢ Φ k x ∧ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) := by
        apply and_mono Entails.rfl
        calc ((∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x)) : PROP)
            ⊢ ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) := forall_elim k
          _ ⊢ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) := forall_elim x
    _ ⊢ iprop(⌜l[k]? = some x⌝) ∧ Φ k x ∧ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) := by
        apply and_intro (pure_intro hget)
        exact Entails.rfl
    _ ⊢ Ψ k x := by
        apply pure_elim_l; intro _
        -- Goal: Φ k x ∧ (⌜l[k]? = some x⌝ → Φ k x → Ψ k x) ⊢ Ψ k x
        -- Strategy: combine Φ k x with ⌜l[k]? = some x⌝ and apply the implication
        have step1 : (Φ k x ∧ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) : PROP) ⊢ iprop(Φ k x → Ψ k x) :=
          calc (Φ k x ∧ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) : PROP)
              ⊢ iprop(⌜l[k]? = some x⌝) ∧ (Φ k x ∧ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x)) := by
                apply and_intro (pure_intro hget) Entails.rfl
            _ ⊢ (iprop(⌜l[k]? = some x⌝) ∧ Φ k x) ∧ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) :=
                (BI.equiv_entails.mp and_assoc).2
            _ ⊢ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) ∧ (iprop(⌜l[k]? = some x⌝) ∧ Φ k x) :=
                (BI.equiv_entails.mp and_comm).1
            _ ⊢ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) ∧ iprop(⌜l[k]? = some x⌝) := by
                apply and_mono Entails.rfl and_elim_l
            _ ⊢ iprop(⌜l[k]? = some x⌝) ∧ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) :=
                (BI.equiv_entails.mp and_comm).1
            _ ⊢ iprop(Φ k x → Ψ k x) := imp_elim_r
        -- To apply Φ k x → Ψ k x to Φ k x, we need (Φ k x → Ψ k x) ∧ Φ k x ⊢ Ψ k x
        -- We have: Φ k x ∧ (⌜l[k]? = some x⌝ → Φ k x → Ψ k x) ⊢ Φ k x → Ψ k x (via step1)
        -- And we have: Φ k x ∧ (⌜l[k]? = some x⌝ → Φ k x → Ψ k x) ⊢ Φ k x (via and_elim_l)
        -- Combine these and apply modus ponens
        have step2 : (Φ k x ∧ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) : PROP) ⊢ Φ k x := and_elim_l
        exact (and_intro step1 step2).trans imp_elim_l

/-! ## Modality Interaction -/

theorem persistently {Φ : Nat → A → PROP} {l : List A} :
    iprop(<pers> bigAndL Φ l) ⊣⊢ bigAndL (fun k x => iprop(<pers> Φ k x)) l := by
  induction l generalizing Φ with
  | nil =>
    simp only [bigAndL, bigOpL]
    exact persistently_true
  | cons x xs ih =>
    simp only [bigAndL, bigOpL]
    calc iprop(<pers> (Φ 0 x ∧ bigAndL (fun n => Φ (n + 1)) xs))
        ⊣⊢ iprop(<pers> Φ 0 x ∧ <pers> bigAndL (fun n => Φ (n + 1)) xs) := persistently_and
      _ ⊣⊢ iprop(<pers> Φ 0 x ∧ bigAndL (fun n k => iprop(<pers> Φ (n + 1) k)) xs) :=
          and_congr OFE.Equiv.rfl ih

/-! ## Pure Propositions -/

theorem pure_1 {φ : Nat → A → Prop} {l : List A} :
    bigAndL (fun k x => iprop(⌜φ k x⌝ : PROP)) l ⊢ iprop(⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) := by
  -- Use forall' to convert to BI forall, then use pure_forall and pure_imp
  calc bigAndL (fun k x => iprop(⌜φ k x⌝ : PROP)) l
      ⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → ⌜φ k x⌝) := (BI.equiv_entails.mp forall').1
    _ ⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x → φ k x⌝ : PROP) :=
        forall_mono fun _ => forall_mono fun _ => (BI.equiv_entails.mp pure_imp).1
    _ ⊢ ∀ k, iprop(⌜∀ x, l[k]? = some x → φ k x⌝ : PROP) :=
        forall_mono fun _ => (BI.equiv_entails.mp pure_forall).1
    _ ⊢ iprop(⌜∀ k, ∀ x, l[k]? = some x → φ k x⌝ : PROP) :=
        (BI.equiv_entails.mp pure_forall).1

theorem pure_2 {φ : Nat → A → Prop} {l : List A} :
    iprop(⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) ⊢ bigAndL (fun k x => iprop(⌜φ k x⌝ : PROP)) l := by
  -- Use forall' backward direction
  calc iprop(⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP)
      ⊢ ∀ k, iprop(⌜∀ x, l[k]? = some x → φ k x⌝ : PROP) := pure_forall_2
    _ ⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x → φ k x⌝ : PROP) :=
        forall_mono fun _ => pure_forall_2
    _ ⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → ⌜φ k x⌝) :=
        forall_mono fun _ => forall_mono fun _ => pure_imp_2
    _ ⊢ bigAndL (fun k x => iprop(⌜φ k x⌝ : PROP)) l := (BI.equiv_entails.mp forall').2

theorem pure {φ : Nat → A → Prop} {l : List A} :
    bigAndL (fun k x => iprop(⌜φ k x⌝ : PROP)) l ⊣⊢ iprop(⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) :=
  BI.equiv_entails.mpr ⟨pure_1, pure_2⟩

-- Note: big_andL_sep_2 is not in Rocq; it was a speculative addition

/-! ## Element Access -/

-- Extract an element from bigAndL using membership
theorem elem_of {Φ : A → PROP} {l : List A} {x : A}
    (h : x ∈ l) :
    bigAndL (fun _ => Φ) l ⊢ Φ x := by
  have ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
  have hlookup : l[i]? = some x := List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
  exact lookup hlookup

/-! ## Zip with Sequence -/

/-- Big and over zip with a shifted sequence.
    Relates `[∧ list] ky ∈ zip (range' n len) l, Φ ky` to `[∧ list] k↦y ∈ l, Φ (n + k, y)`.
    This lemma allows rewriting a big conjunction over a zipped list with an enumeration
    starting at `n` into a big conjunction with indexed access where indices are offset by `n`. -/
theorem zip_seq {Φ : Nat × A → PROP} {n : Nat} {l : List A} :
    bigAndL (fun _ => Φ) ((List.range' n l.length).zip l) ⊣⊢
      bigAndL (fun i x => Φ (n + i, x)) l := by
  have h := BigOpL.zip_seq (op := and) (unit := iprop(True)) Φ n l
  exact BI.equiv_entails.mpr ⟨BI.equiv_entails.mp h |>.1, BI.equiv_entails.mp h |>.2⟩

/-- Big and over zip with a sequence starting at 0.
    Relates `[∧ list] ky ∈ zip (range len) l, Φ ky` to `[∧ list] k↦y ∈ l, Φ (k, y)`.
    This is a special case of `zip_seq` with `n = 0`, useful for converting between
    explicit enumeration via zip and implicit indexed big conjunction. -/
theorem zip_seqZ {Φ : Nat × A → PROP} {l : List A} :
    bigAndL (fun _ => Φ) ((List.range l.length).zip l) ⊣⊢
      bigAndL (fun i x => Φ (i, x)) l := by
  have h := BigOpL.zip_with_range (op := and) (unit := iprop(True)) Φ l
  exact BI.equiv_entails.mpr ⟨BI.equiv_entails.mp h |>.1, BI.equiv_entails.mp h |>.2⟩

/-! ## Bind -/

theorem bind {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    bigAndL (fun _ => Φ) (l.flatMap f) ⊣⊢
      bigAndL (fun _ x => bigAndL (fun _ => Φ) (f x)) l := by
  induction l with
  | nil => exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, bigAndL, bigOpL]
    exact OFE.Equiv.trans app (and_congr OFE.Equiv.rfl ih)

/-! ## Later Modality -/

theorem later {Φ : Nat → A → PROP} {l : List A} :
    iprop(▷ bigAndL Φ l) ⊣⊢ bigAndL (fun k x => iprop(▷ Φ k x)) l := by
  induction l generalizing Φ with
  | nil =>
    simp only [bigAndL, bigOpL]
    exact later_true
  | cons x xs ih =>
    simp only [bigAndL, bigOpL]
    calc iprop(▷ (Φ 0 x ∧ bigAndL (fun n => Φ (n + 1)) xs))
        ⊣⊢ iprop(▷ Φ 0 x ∧ ▷ bigAndL (fun n => Φ (n + 1)) xs) := later_and
      _ ⊣⊢ iprop(▷ Φ 0 x ∧ bigAndL (fun n k => iprop(▷ Φ (n + 1) k)) xs) :=
          and_congr OFE.Equiv.rfl ih

theorem laterN {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    iprop(▷^[n] bigAndL Φ l) ⊣⊢ bigAndL (fun k x => iprop(▷^[n] Φ k x)) l := by
  induction n with
  | zero =>
    exact OFE.Equiv.rfl
  | succ m ih =>
    calc iprop(▷ ▷^[m] bigAndL Φ l)
        ⊣⊢ iprop(▷ bigAndL (fun k x => iprop(▷^[m] Φ k x)) l) :=
          later_congr ih
      _ ⊣⊢ bigAndL (fun k x => iprop(▷ ▷^[m] Φ k x)) l := later

/-! ## Permutation -/

theorem perm {Φ : A → PROP} {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    bigAndL (fun _ => Φ) l₁ ⊣⊢ bigAndL (fun _ => Φ) l₂ :=
  BigOpL.perm Φ hp

end BigAndL

end Iris.BI
