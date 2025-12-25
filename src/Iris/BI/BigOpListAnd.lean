/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp

namespace Iris.BI

open Iris.Algebra
open BIBase


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
    ([∧ list] k ↦ x ∈ ([] : List A), Φ k x) ⊣⊢ iprop(True) := by
  simp only [bigAndL, bigOpL]
  exact .rfl

theorem nil' {Φ : Nat → A → PROP} {l : List A} (h : l = []) :
    ([∧ list] k ↦ x ∈ l, Φ k x) ⊣⊢ iprop(True) := by
  subst h; exact nil

theorem cons {Φ : Nat → A → PROP} {x : A} {xs : List A} :
    ([∧ list] k ↦ y ∈ (x :: xs), Φ k y) ⊣⊢ Φ 0 x ∧ [∧ list] n ↦ y ∈ xs, Φ (n + 1) y := by
  simp only [bigAndL, bigOpL]
  exact .rfl

theorem singleton {Φ : Nat → A → PROP} {x : A} :
    ([∧ list] k ↦ y ∈ [x], Φ k y) ⊣⊢ Φ 0 x :=
  equiv_iff.mp (BigOpL.singleton Φ x)

theorem app {Φ : Nat → A → PROP} {l₁ l₂ : List A} :
    ([∧ list] k ↦ x ∈ (l₁ ++ l₂), Φ k x) ⊣⊢
      ([∧ list] k ↦ x ∈ l₁, Φ k x) ∧ [∧ list] n ↦ x ∈ l₂, Φ (n + l₁.length) x :=
  equiv_iff.mp (BigOpL.append Φ l₁ l₂)

theorem snoc {Φ : Nat → A → PROP} {l : List A} {x : A} :
    ([∧ list] k ↦ y ∈ (l ++ [x]), Φ k y) ⊣⊢ ([∧ list] k ↦ y ∈ l, Φ k y) ∧ Φ l.length x :=
  equiv_iff.mp (BigOpL.snoc Φ l x)

/-! ## Monotonicity and Congruence -/

theorem mono {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Φ k x ⊢ Ψ k x) :
    ([∧ list] k ↦ x ∈ l, Φ k x) ⊢ [∧ list] k ↦ x ∈ l, Ψ k x := by
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
    (h : ∀ k x, l[k]? = some x → Φ k x ≡ Ψ k x) :
    ([∧ list] k ↦ x ∈ l, Φ k x) ≡ [∧ list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr h

theorem congr {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Φ k x ≡ Ψ k x) :
    ([∧ list] k ↦ x ∈ l, Φ k x) ≡ [∧ list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr' h

/-! ## Typeclass Closure -/

instance persistent {Φ : Nat → A → PROP} {l : List A} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∧ list] k ↦ x ∈ l, Φ k x) where
  persistent := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigAndL, bigOpL]
      exact persistently_true.2
    | cons x xs ih =>
      simp only [bigAndL, bigOpL]
      have h1 : Φ 0 x ⊢ <pers> Φ 0 x := Persistent.persistent
      have h2 : ([∧ list] n ↦ y ∈ xs, Φ (n + 1) y) ⊢ <pers> [∧ list] n ↦ y ∈ xs, Φ (n + 1) y := ih
      exact (and_mono h1 h2).trans persistently_and.2

instance affine {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] :
    Affine ([∧ list] k ↦ x ∈ l, Φ k x) where
  affine := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigAndL, bigOpL]
      exact true_emp.1
    | cons x xs ih =>
      simp only [bigAndL, bigOpL]
      exact and_elim_l.trans Affine.affine

/-! ## Unit/True Lemma -/

theorem true_l {l : List A} :
    ([∧ list] _x ∈ l, iprop(True : PROP)) ≡ iprop(True) :=
  BigOpL.unit_const l

/-! ## Distribution over And -/

theorem and' {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∧ list] k ↦ x ∈ l, iprop(Φ k x ∧ Ψ k x)) ≡
      iprop(([∧ list] k ↦ x ∈ l, Φ k x) ∧ [∧ list] k ↦ x ∈ l, Ψ k x) :=
  BigOpL.op_distr Φ Ψ l

theorem and_2 {Φ Ψ : Nat → A → PROP} {l : List A} :
    iprop(([∧ list] k ↦ x ∈ l, Φ k x) ∧ [∧ list] k ↦ x ∈ l, Ψ k x) ≡
      [∧ list] k ↦ x ∈ l, iprop(Φ k x ∧ Ψ k x) :=
  and'.symm

/-! ## Take and Drop -/

theorem take_drop {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∧ list] k ↦ x ∈ l, Φ k x) ≡
      iprop(([∧ list] k ↦ x ∈ (l.take n), Φ k x) ∧ [∧ list] k ↦ x ∈ (l.drop n), Φ (n + k) x) :=
  BigOpL.take_drop Φ l n

/-! ## Fmap -/

theorem fmap {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    ([∧ list] k ↦ y ∈ (l.map f), Φ k y) ≡ [∧ list] k ↦ x ∈ l, Φ k (f x) := by
  induction l generalizing Φ with
  | nil => simp only [List.map_nil]; exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, bigAndL, bigOpL]
    exact Monoid.op_proper OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

/-! ## Lookup Lemmas -/

-- Extract an element from bigAndL using the lookup function
-- This is simpler than the sep version because and is idempotent
theorem lookup {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∧ list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x := by
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
    P ⊢ [∧ list] k ↦ x ∈ l, Φ k x := by
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
    ([∧ list] k ↦ x ∈ l, Φ k x) ⊣⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) := by
  constructor
  · -- Forward: [∧ list] k ↦ x ∈ l, Φ k x ⊢ ∀ k x, ⌜l[k]? = some x⌝ → Φ k x
    apply forall_intro; intro k
    apply forall_intro; intro x
    apply imp_intro
    -- Goal: [∧ list] k ↦ x ∈ l, Φ k x ∧ ⌜l[k]? = some x⌝ ⊢ Φ k x
    apply and_comm.1.trans
    apply pure_elim_l
    intro hget
    exact lookup hget
  · -- Backward: (∀ k x, ⌜l[k]? = some x⌝ → Φ k x) ⊢ [∧ list] k ↦ x ∈ l, Φ k x
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
    ([∧ list] k ↦ x ∈ l, Φ k x) ∧ (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x)) ⊢
      [∧ list] k ↦ x ∈ l, Ψ k x := by
  -- Use intro to construct [∧ list] k ↦ x ∈ l, Ψ k x
  apply intro
  intro k x hget
  -- Goal: [∧ list] k ↦ x ∈ l, Φ k x ∧ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x → Ψ k x) ⊢ Ψ k x
  calc (([∧ list] k ↦ x ∈ l, Φ k x) ∧ (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x)) : PROP)
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
                and_assoc.2
            _ ⊢ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) ∧ (iprop(⌜l[k]? = some x⌝) ∧ Φ k x) :=
                and_comm.1
            _ ⊢ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) ∧ iprop(⌜l[k]? = some x⌝) := by
                apply and_mono Entails.rfl and_elim_l
            _ ⊢ iprop(⌜l[k]? = some x⌝) ∧ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) :=
                and_comm.1
            _ ⊢ iprop(Φ k x → Ψ k x) := imp_elim_r
        -- To apply Φ k x → Ψ k x to Φ k x, we need (Φ k x → Ψ k x) ∧ Φ k x ⊢ Ψ k x
        -- We have: Φ k x ∧ (⌜l[k]? = some x⌝ → Φ k x → Ψ k x) ⊢ Φ k x → Ψ k x (via step1)
        -- And we have: Φ k x ∧ (⌜l[k]? = some x⌝ → Φ k x → Ψ k x) ⊢ Φ k x (via and_elim_l)
        -- Combine these and apply modus ponens
        have step2 : (Φ k x ∧ iprop(⌜l[k]? = some x⌝ → Φ k x → Ψ k x) : PROP) ⊢ Φ k x := and_elim_l
        exact (and_intro step1 step2).trans imp_elim_l

/-! ## Modality Interaction -/

theorem persistently {Φ : Nat → A → PROP} {l : List A} :
    iprop(<pers> [∧ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∧ list] k ↦ x ∈ l, iprop(<pers> Φ k x) := by
  induction l generalizing Φ with
  | nil =>
    simp only [bigAndL, bigOpL]
    exact persistently_true
  | cons x xs ih =>
    simp only [bigAndL, bigOpL]
    calc iprop(<pers> (Φ 0 x ∧ [∧ list] n ↦ y ∈ xs, Φ (n + 1) y))
        ⊣⊢ iprop(<pers> Φ 0 x ∧ <pers> [∧ list] n ↦ y ∈ xs, Φ (n + 1) y) := persistently_and
      _ ⊣⊢ iprop(<pers> Φ 0 x ∧ [∧ list] n ↦ y ∈ xs, iprop(<pers> Φ (n + 1) y)) :=
          and_congr .rfl ih

/-! ## Pure Propositions -/

theorem pure_1 {φ : Nat → A → Prop} {l : List A} :
    ([∧ list] k ↦ x ∈ l, iprop(⌜φ k x⌝ : PROP)) ⊢ iprop(⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) := by
  -- Use forall' to convert to BI forall, then use pure_forall and pure_imp
  calc ([∧ list] k ↦ x ∈ l, iprop(⌜φ k x⌝ : PROP))
      ⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → ⌜φ k x⌝) := forall'.1
    _ ⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x → φ k x⌝ : PROP) :=
        forall_mono fun _ => forall_mono fun _ => pure_imp.1
    _ ⊢ ∀ k, iprop(⌜∀ x, l[k]? = some x → φ k x⌝ : PROP) :=
        forall_mono fun _ => pure_forall.1
    _ ⊢ iprop(⌜∀ k, ∀ x, l[k]? = some x → φ k x⌝ : PROP) :=
        pure_forall.1

theorem pure_2 {φ : Nat → A → Prop} {l : List A} :
    iprop(⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) ⊢ [∧ list] k ↦ x ∈ l, iprop(⌜φ k x⌝ : PROP) := by
  -- Use forall' backward direction
  calc iprop(⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP)
      ⊢ ∀ k, iprop(⌜∀ x, l[k]? = some x → φ k x⌝ : PROP) := pure_forall_2
    _ ⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x → φ k x⌝ : PROP) :=
        forall_mono fun _ => pure_forall_2
    _ ⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → ⌜φ k x⌝) :=
        forall_mono fun _ => forall_mono fun _ => pure_imp_2
    _ ⊢ [∧ list] k ↦ x ∈ l, iprop(⌜φ k x⌝ : PROP) := forall'.2

theorem pure {φ : Nat → A → Prop} {l : List A} :
    ([∧ list] k ↦ x ∈ l, iprop(⌜φ k x⌝ : PROP)) ⊣⊢ iprop(⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) :=
  ⟨pure_1, pure_2⟩

-- Note: big_andL_sep_2 is not in Rocq; it was a speculative addition

/-! ## Element Access -/

-- Extract an element from bigAndL using membership
theorem elem_of {Φ : A → PROP} {l : List A} {x : A}
    (h : x ∈ l) :
    ([∧ list] y ∈ l, Φ y) ⊢ Φ x := by
  have ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
  have hlookup : l[i]? = some x := List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
  exact lookup hlookup

/-! ## Zip with Sequence -/

/-- Big and over zip with a shifted sequence.
    Relates `[∧ list] ky ∈ zip (range' n len) l, Φ ky` to `[∧ list] k↦y ∈ l, Φ (n + k, y)`.
    This lemma allows rewriting a big conjunction over a zipped list with an enumeration
    starting at `n` into a big conjunction with indexed access where indices are offset by `n`. -/
theorem zip_seq {Φ : Nat × A → PROP} {n : Nat} {l : List A} :
    ([∧ list] ky ∈ ((List.range' n l.length).zip l), Φ ky) ≡
      [∧ list] i ↦ x ∈ l, Φ (n + i, x) :=
  BigOpL.zip_seq (op := and) (unit := iprop(True)) Φ n l

/-- Big and over zip with a sequence starting at 0.
    Relates `[∧ list] ky ∈ zip (range len) l, Φ ky` to `[∧ list] k↦y ∈ l, Φ (k, y)`.
    This is a special case of `zip_seq` with `n = 0`, useful for converting between
    explicit enumeration via zip and implicit indexed big conjunction. -/
theorem zip_seqZ {Φ : Nat × A → PROP} {l : List A} :
    ([∧ list] ky ∈ ((List.range l.length).zip l), Φ ky) ≡
      [∧ list] i ↦ x ∈ l, Φ (i, x) :=
  BigOpL.zip_with_range (op := and) (unit := iprop(True)) Φ l

/-! ## Bind -/

theorem bind {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    ([∧ list] y ∈ (l.flatMap f), Φ y) ⊣⊢
      [∧ list] x ∈ l, [∧ list] y ∈ (f x), Φ y := by
  induction l with
  | nil => exact .rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, bigAndL, bigOpL]
    exact app.trans (and_congr .rfl ih)

/-! ## Later Modality -/

theorem later {Φ : Nat → A → PROP} {l : List A} :
    iprop(▷ [∧ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∧ list] k ↦ x ∈ l, iprop(▷ Φ k x) := by
  induction l generalizing Φ with
  | nil =>
    simp only [bigAndL, bigOpL]
    exact later_true
  | cons x xs ih =>
    simp only [bigAndL, bigOpL]
    calc iprop(▷ (Φ 0 x ∧ [∧ list] n ↦ y ∈ xs, Φ (n + 1) y))
        ⊣⊢ iprop(▷ Φ 0 x ∧ ▷ [∧ list] n ↦ y ∈ xs, Φ (n + 1) y) := later_and
      _ ⊣⊢ iprop(▷ Φ 0 x ∧ [∧ list] n ↦ y ∈ xs, iprop(▷ Φ (n + 1) y)) :=
          and_congr .rfl ih

theorem laterN {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    iprop(▷^[n] [∧ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∧ list] k ↦ x ∈ l, iprop(▷^[n] Φ k x) := by
  induction n with
  | zero =>
    exact .rfl
  | succ m ih =>
    calc iprop(▷ ▷^[m] [∧ list] k ↦ x ∈ l, Φ k x)
        ⊣⊢ iprop(▷ [∧ list] k ↦ x ∈ l, iprop(▷^[m] Φ k x)) :=
          later_congr ih
      _ ⊣⊢ [∧ list] k ↦ x ∈ l, iprop(▷ ▷^[m] Φ k x) := later

/-! ## Permutation -/

theorem perm {Φ : A → PROP} {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    ([∧ list] x ∈ l₁, Φ x) ≡ [∧ list] x ∈ l₂, Φ x :=
  BigOpL.perm Φ hp

end BigAndL

end Iris.BI
