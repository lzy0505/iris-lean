/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp

namespace Iris.BI

open Iris.Algebra
open BIBase

/-! # Big Disjunction over Lists

This file contains lemmas about `bigOrL`, the big disjunction over lists.
The main sections are:
- Basic structural lemmas (nil, cons, singleton, app)
- Monotonicity and congruence
- Lookup/access lemmas
- Operator interaction (or, sep, pure)
- Higher-order lemmas (intro, exist)
-/

variable {PROP : Type _} [BI PROP] {A : Type _}

namespace BigOrL

/-! ## Basic Structural Lemmas -/

@[simp]
theorem nil {Φ : Nat → A → PROP} :
    bigOrL Φ ([] : List A) ⊣⊢ iprop(False) := by
  simp only [bigOrL, bigOpL]
  exact .rfl

theorem nil' {Φ : Nat → A → PROP} {l : List A} (h : l = []) :
    bigOrL Φ l ⊣⊢ iprop(False) := by
  subst h; exact nil

theorem cons {Φ : Nat → A → PROP} {x : A} {xs : List A} :
    bigOrL Φ (x :: xs) ⊣⊢ Φ 0 x ∨ bigOrL (fun n => Φ (n + 1)) xs := by
  simp only [bigOrL, bigOpL]
  exact .rfl

theorem singleton {Φ : Nat → A → PROP} {x : A} :
    bigOrL Φ [x] ⊣⊢ Φ 0 x :=
  equiv_iff.mp (BigOpL.singleton Φ x)

theorem app {Φ : Nat → A → PROP} {l₁ l₂ : List A} :
    bigOrL Φ (l₁ ++ l₂) ⊣⊢
      bigOrL Φ l₁ ∨ bigOrL (fun n => Φ (n + l₁.length)) l₂ :=
  equiv_iff.mp (BigOpL.append Φ l₁ l₂)

theorem snoc {Φ : Nat → A → PROP} {l : List A} {x : A} :
    bigOrL Φ (l ++ [x]) ⊣⊢ bigOrL Φ l ∨ Φ l.length x :=
  equiv_iff.mp (BigOpL.snoc Φ l x)

/-! ## Monotonicity and Congruence -/

theorem mono {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Φ k x ⊢ Ψ k x) :
    bigOrL Φ l ⊢ bigOrL Ψ l := by
  induction l generalizing Φ Ψ with
  | nil => exact Entails.rfl
  | cons y ys ih =>
    simp only [bigOrL, bigOpL]
    apply or_mono
    · exact h 0 y rfl
    · apply ih
      intro k x hget
      exact h (k + 1) x hget

theorem proper {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Φ k x ≡ Ψ k x) :
    bigOrL Φ l ≡ bigOrL Ψ l :=
  BigOpL.congr h

theorem congr {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Φ k x ≡ Ψ k x) :
    bigOrL Φ l ≡ bigOrL Ψ l :=
  BigOpL.congr' h

/-! ## Unit/False Lemma -/

theorem false_l {l : List A} :
    bigOrL (fun _ _ => (iprop(False) : PROP)) l ≡ iprop(False) :=
  BigOpL.unit_const l

/-! ## Distribution over Or -/

theorem or' {Φ Ψ : Nat → A → PROP} {l : List A} :
    bigOrL (fun k x => iprop(Φ k x ∨ Ψ k x)) l ≡ iprop(bigOrL Φ l ∨ bigOrL Ψ l) :=
  BigOpL.op_distr Φ Ψ l

theorem or_2 {Φ Ψ : Nat → A → PROP} {l : List A} :
    iprop(bigOrL Φ l ∨ bigOrL Ψ l) ≡ bigOrL (fun k x => iprop(Φ k x ∨ Ψ k x)) l :=
  or'.symm

/-! ## Take and Drop -/

theorem take_drop {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    bigOrL Φ l ≡
      iprop(bigOrL Φ (l.take n) ∨ bigOrL (fun k => Φ (n + k)) (l.drop n)) :=
  BigOpL.take_drop Φ l n

/-! ## Fmap -/

theorem fmap {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    bigOrL Φ (l.map f) ≡ bigOrL (fun k x => Φ k (f x)) l := by
  induction l generalizing Φ with
  | nil => simp only [List.map_nil]; exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, bigOrL, bigOpL]
    exact Monoid.op_proper OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

/-! ## Higher-Order Lemmas -/

-- Introduction rule: if l[k]? = some x, then Φ k x entails the big or
theorem intro {Φ : Nat → A → PROP} {l : List A} {k : Nat} {x : A}
    (h : l[k]? = some x) :
    Φ k x ⊢ bigOrL Φ l := by
  induction l generalizing k Φ with
  | nil => simp at h
  | cons y ys ih =>
    simp only [bigOrL, bigOpL]
    cases k with
    | zero =>
      simp at h
      subst h
      exact or_intro_l
    | succ j =>
      simp at h
      exact (ih (Φ := fun n => Φ (n + 1)) h).trans or_intro_r

-- bigOrL is equivalent to an existential quantification
theorem exist {Φ : Nat → A → PROP} {l : List A} :
    bigOrL Φ l ⊣⊢ ∃ k, ∃ x, iprop(⌜l[k]? = some x⌝ ∧ Φ k x) := by
  constructor
  · -- Forward: induction on l
    induction l generalizing Φ with
    | nil =>
      simp only [bigOrL, bigOpL]
      exact false_elim
    | cons y ys ih =>
      simp only [bigOrL, bigOpL]
      apply or_elim
      · -- Φ 0 y ⊢ ∃ k x, ⌜(y :: ys)[k]? = some x⌝ ∧ Φ k x
        calc Φ 0 y
            ⊢ iprop(⌜(y :: ys)[0]? = some y⌝ ∧ Φ 0 y) := (and_intro (pure_intro rfl) Entails.rfl)
          _ ⊢ ∃ x, iprop(⌜(y :: ys)[0]? = some x⌝ ∧ Φ 0 x) := exists_intro' y Entails.rfl
          _ ⊢ ∃ k, ∃ x, iprop(⌜(y :: ys)[k]? = some x⌝ ∧ Φ k x) := exists_intro' 0 Entails.rfl
      · -- bigOrL (Φ ∘ Nat.succ) ys ⊢ ∃ k x, ⌜(y :: ys)[k]? = some x⌝ ∧ Φ k x
        calc bigOrL (fun n => Φ (n + 1)) ys
            ⊢ ∃ k, ∃ x, iprop(⌜ys[k]? = some x⌝ ∧ Φ (k + 1) x) := ih
          _ ⊢ ∃ k, ∃ x, iprop(⌜(y :: ys)[k + 1]? = some x⌝ ∧ Φ (k + 1) x) := by
              apply exists_mono; intro k
              apply exists_mono; intro x
              apply and_mono _ Entails.rfl
              apply pure_mono; intro h; exact h
          _ ⊢ ∃ k, ∃ x, iprop(⌜(y :: ys)[k]? = some x⌝ ∧ Φ k x) := by
              apply exists_elim; intro k
              exact exists_intro' (k + 1) Entails.rfl
  · -- Backward: ∃ k x, ⌜l[k]? = some x⌝ ∧ Φ k x ⊢ bigOrL Φ l
    apply exists_elim; intro k
    apply exists_elim; intro x
    apply pure_elim_l; intro hget
    exact intro hget

/-! ## Pure Propositions -/

theorem pure {φ : Nat → A → Prop} {l : List A} :
    bigOrL (fun k x => iprop(⌜φ k x⌝ : PROP)) l ⊣⊢ iprop(⌜∃ k x, l[k]? = some x ∧ φ k x⌝ : PROP) := by
  -- Following Rocq: use exist theorem and pure_exists
  calc bigOrL (fun k x => iprop(⌜φ k x⌝ : PROP)) l
      ⊣⊢ ∃ k, ∃ x, iprop(⌜l[k]? = some x⌝ ∧ ⌜φ k x⌝) := exist
    _ ⊣⊢ ∃ k, ∃ x, iprop(⌜l[k]? = some x ∧ φ k x⌝ : PROP) := by
        apply exists_congr; intro k
        apply exists_congr; intro x
        exact pure_and
    _ ⊣⊢ ∃ k, iprop(⌜∃ x, l[k]? = some x ∧ φ k x⌝ : PROP) := by
        apply exists_congr; intro k
        exact pure_exists
    _ ⊣⊢ iprop(⌜∃ k, ∃ x, l[k]? = some x ∧ φ k x⌝ : PROP) := pure_exists

/-! ## Interaction with Sep -/

-- Distribute sep from the left: P ∗ [∨ list] ⊣⊢ [∨ list] k ↦ x, P ∗ Φ k x
theorem sep_l {P : PROP} {Φ : Nat → A → PROP} {l : List A} :
    iprop(P ∗ bigOrL Φ l) ⊣⊢ bigOrL (fun k x => iprop(P ∗ Φ k x)) l := by
  -- Following Rocq: rewrite using exist and sep_exists_l
  calc iprop(P ∗ bigOrL Φ l)
      ⊣⊢ iprop(P ∗ (∃ k, ∃ x, iprop(⌜l[k]? = some x⌝ ∧ Φ k x))) := sep_congr .rfl exist
    _ ⊣⊢ ∃ k, iprop(P ∗ (∃ x, iprop(⌜l[k]? = some x⌝ ∧ Φ k x))) := sep_exists_l
    _ ⊣⊢ ∃ k, ∃ x, iprop(P ∗ (⌜l[k]? = some x⌝ ∧ Φ k x)) := by
        apply exists_congr; intro k; exact sep_exists_l
    _ ⊣⊢ ∃ k, ∃ x, iprop(⌜l[k]? = some x⌝ ∧ (P ∗ Φ k x)) := by
        apply exists_congr; intro k
        apply exists_congr; intro x
        -- Use persistent_and_affinely_sep_l and associativity
        -- ⌜l[k]? = some x⌝ is Persistent and Affine, so we can reorder
        calc iprop(P ∗ (⌜l[k]? = some x⌝ ∧ Φ k x))
            ⊣⊢ iprop(P ∗ (<affine> ⌜l[k]? = some x⌝ ∗ Φ k x)) := by
                apply sep_congr .rfl
                exact persistent_and_affinely_sep_l
          _ ⊣⊢ iprop((P ∗ <affine> ⌜l[k]? = some x⌝) ∗ Φ k x) := sep_assoc.symm
          _ ⊣⊢ iprop((<affine> ⌜l[k]? = some x⌝ ∗ P) ∗ Φ k x) := sep_congr sep_comm .rfl
          _ ⊣⊢ iprop(<affine> ⌜l[k]? = some x⌝ ∗ (P ∗ Φ k x)) := sep_assoc
          _ ⊣⊢ iprop(⌜l[k]? = some x⌝ ∧ (P ∗ Φ k x)) := persistent_and_affinely_sep_l.symm
    _ ⊣⊢ bigOrL (fun k x => iprop(P ∗ Φ k x)) l := exist.symm

-- Distribute sep from the right: [∨ list] ∗ P ⊣⊢ [∨ list] k ↦ x, Φ k x ∗ P
theorem sep_r {Φ : Nat → A → PROP} {P : PROP} {l : List A} :
    iprop(bigOrL Φ l ∗ P) ⊣⊢ bigOrL (fun k x => iprop(Φ k x ∗ P)) l := by
  calc iprop(bigOrL Φ l ∗ P)
      ⊣⊢ iprop(P ∗ bigOrL Φ l) := sep_comm
    _ ⊣⊢ bigOrL (fun k x => iprop(P ∗ Φ k x)) l := sep_l
    _ ⊣⊢ bigOrL (fun k x => iprop(Φ k x ∗ P)) l :=
        equiv_iff.mp (congr (fun k x => equiv_iff.mpr sep_comm))

/-! ## Lookup Lemmas -/

-- Extract an element via membership
theorem elem_of {Φ : A → PROP} {l : List A} {x : A}
    (h : x ∈ l) :
    Φ x ⊢ bigOrL (fun _ => Φ) l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [bigOrL, bigOpL]
    cases h with
    | head => exact or_intro_l
    | tail _ hmem => exact (ih hmem).trans or_intro_r

/-! ## Bind -/

theorem bind {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    bigOrL (fun _ => Φ) (l.flatMap f) ⊣⊢
      bigOrL (fun _ x => bigOrL (fun _ => Φ) (f x)) l := by
  induction l with
  | nil => exact .rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, bigOrL, bigOpL]
    exact app.trans (or_congr .rfl ih)

/-! ## Modality Interaction -/

theorem persistently {Φ : Nat → A → PROP} {l : List A} :
    iprop(<pers> bigOrL Φ l) ⊣⊢ bigOrL (fun k x => iprop(<pers> Φ k x)) l := by
  induction l generalizing Φ with
  | nil =>
    simp only [bigOrL, bigOpL]
    -- <pers> False ⊣⊢ False
    constructor
    · -- <pers> False ⊢ False
      exact persistently_elim.trans false_elim
    · -- False ⊢ <pers> False
      exact false_elim
  | cons x xs ih =>
    simp only [bigOrL, bigOpL]
    calc iprop(<pers> (Φ 0 x ∨ bigOrL (fun n => Φ (n + 1)) xs))
        ⊣⊢ iprop(<pers> Φ 0 x ∨ <pers> bigOrL (fun n => Φ (n + 1)) xs) := persistently_or
      _ ⊣⊢ iprop(<pers> Φ 0 x ∨ bigOrL (fun n k => iprop(<pers> Φ (n + 1) k)) xs) :=
          or_congr .rfl ih

/-- Later distributes over non-empty big disjunctions.
    The proof follows Rocq's approach using the singleton lemma to avoid needing `▷ False ⊢ False`. -/
theorem later {Φ : Nat → A → PROP} {l : List A} (hne : l ≠ []) :
    iprop(▷ bigOrL Φ l) ⊣⊢ bigOrL (fun k x => iprop(▷ Φ k x)) l := by
  induction l generalizing Φ with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil =>
      -- Singleton case: bigOrL Φ [x] ⊣⊢ Φ 0 x (by singleton lemma)
      -- So ▷ bigOrL Φ [x] ⊣⊢ ▷ Φ 0 x and bigOrL (fun k x => ▷ Φ k x) [x] ⊣⊢ ▷ Φ 0 x
      calc iprop(▷ bigOrL Φ [x])
          ⊣⊢ iprop(▷ Φ 0 x) := later_congr singleton
        _ ⊣⊢ bigOrL (fun k x => iprop(▷ Φ k x)) [x] :=
            (singleton (Φ := fun k x => iprop(▷ Φ k x))).symm
    | cons y ys =>
      -- l = x :: y :: ys, which has at least two elements
      simp only [bigOrL, bigOpL]
      calc iprop(▷ (Φ 0 x ∨ bigOrL (fun n => Φ (n + 1)) (y :: ys)))
          ⊣⊢ iprop(▷ Φ 0 x ∨ ▷ bigOrL (fun n => Φ (n + 1)) (y :: ys)) := later_or
        _ ⊣⊢ iprop(▷ Φ 0 x ∨ bigOrL (fun n k => iprop(▷ Φ (n + 1) k)) (y :: ys)) := by
            apply or_congr .rfl
            exact ih (by simp)

theorem laterN {Φ : Nat → A → PROP} {l : List A} {n : Nat} (hne : l ≠ []) :
    iprop(▷^[n] bigOrL Φ l) ⊣⊢ bigOrL (fun k x => iprop(▷^[n] Φ k x)) l := by
  induction n with
  | zero => exact .rfl
  | succ m ih =>
    calc iprop(▷ ▷^[m] bigOrL Φ l)
        ⊣⊢ iprop(▷ bigOrL (fun k x => iprop(▷^[m] Φ k x)) l) :=
          later_congr ih
      _ ⊣⊢ bigOrL (fun k x => iprop(▷ ▷^[m] Φ k x)) l := later hne

/-! ## Permutation -/

theorem perm {Φ : A → PROP} {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    bigOrL (fun _ => Φ) l₁ ≡ bigOrL (fun _ => Φ) l₂ :=
  BigOpL.perm Φ hp

end BigOrL

end Iris.BI
