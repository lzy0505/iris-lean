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
    ([∨ list] k ↦ x ∈ ([] : List A), Φ k x) ⊣⊢ iprop(False) := by
  simp only [bigOrL, bigOpL]
  exact .rfl

theorem nil' {Φ : Nat → A → PROP} {l : List A} (h : l = []) :
    ([∨ list] k ↦ x ∈ l, Φ k x) ⊣⊢ iprop(False) := by
  subst h; exact nil

theorem cons {Φ : Nat → A → PROP} {x : A} {xs : List A} :
    ([∨ list] k ↦ y ∈ (x :: xs), Φ k y) ⊣⊢ Φ 0 x ∨ [∨ list] n ↦ y ∈ xs, Φ (n + 1) y := by
  simp only [bigOrL, bigOpL]
  exact .rfl

theorem singleton {Φ : Nat → A → PROP} {x : A} :
    ([∨ list] k ↦ y ∈ [x], Φ k y) ⊣⊢ Φ 0 x :=
  equiv_iff.mp (BigOpL.singleton Φ x)

theorem app {Φ : Nat → A → PROP} {l₁ l₂ : List A} :
    ([∨ list] k ↦ x ∈ (l₁ ++ l₂), Φ k x) ⊣⊢
      ([∨ list] k ↦ x ∈ l₁, Φ k x) ∨ [∨ list] n ↦ x ∈ l₂, Φ (n + l₁.length) x :=
  equiv_iff.mp (BigOpL.append Φ l₁ l₂)

theorem snoc {Φ : Nat → A → PROP} {l : List A} {x : A} :
    ([∨ list] k ↦ y ∈ (l ++ [x]), Φ k y) ⊣⊢ ([∨ list] k ↦ y ∈ l, Φ k y) ∨ Φ l.length x :=
  equiv_iff.mp (BigOpL.snoc Φ l x)

/-! ## Monotonicity and Congruence -/

theorem mono {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Φ k x ⊢ Ψ k x) :
    ([∨ list] k ↦ x ∈ l, Φ k x) ⊢ [∨ list] k ↦ x ∈ l, Ψ k x := by
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
    ([∨ list] k ↦ x ∈ l, Φ k x) ≡ [∨ list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr h

theorem congr {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Φ k x ≡ Ψ k x) :
    ([∨ list] k ↦ x ∈ l, Φ k x) ≡ [∨ list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr' h

/-! ## Unit/False Lemma -/

theorem false_l {l : List A} :
    ([∨ list] _k ∈ l, iprop(False : PROP)) ≡ iprop(False) :=
  BigOpL.unit_const l

/-! ## Distribution over Or -/

theorem or' {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∨ list] k ↦ x ∈ l, iprop(Φ k x ∨ Ψ k x)) ≡
      iprop(([∨ list] k ↦ x ∈ l, Φ k x) ∨ [∨ list] k ↦ x ∈ l, Ψ k x) :=
  BigOpL.op_distr Φ Ψ l

theorem or_2 {Φ Ψ : Nat → A → PROP} {l : List A} :
    iprop(([∨ list] k ↦ x ∈ l, Φ k x) ∨ [∨ list] k ↦ x ∈ l, Ψ k x) ≡
      [∨ list] k ↦ x ∈ l, iprop(Φ k x ∨ Ψ k x) :=
  or'.symm

/-! ## Take and Drop -/

theorem take_drop {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∨ list] k ↦ x ∈ l, Φ k x) ≡
      iprop(([∨ list] k ↦ x ∈ (l.take n), Φ k x) ∨ [∨ list] k ↦ x ∈ (l.drop n), Φ (n + k) x) :=
  BigOpL.take_drop Φ l n

/-! ## Fmap -/

theorem fmap {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    ([∨ list] k ↦ y ∈ (l.map f), Φ k y) ≡ [∨ list] k ↦ x ∈ l, Φ k (f x) := by
  induction l generalizing Φ with
  | nil => simp only [List.map_nil]; exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, bigOrL, bigOpL]
    exact Monoid.op_proper OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

/-! ## Higher-Order Lemmas -/

-- Introduction rule: if l[k]? = some x, then Φ k x entails the big or
theorem intro {Φ : Nat → A → PROP} {l : List A} {k : Nat} {x : A}
    (h : l[k]? = some x) :
    Φ k x ⊢ [∨ list] i ↦ y ∈ l, Φ i y := by
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
    ([∨ list] k ↦ x ∈ l, Φ k x) ⊣⊢ ∃ k, ∃ x, iprop(⌜l[k]? = some x⌝ ∧ Φ k x) := by
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
      · -- [∨ list] k ↦ x ∈ ys, Φ (k + 1) x ⊢ ∃ k x, ⌜(y :: ys)[k]? = some x⌝ ∧ Φ k x
        calc ([∨ list] k ↦ x ∈ ys, Φ (k + 1) x)
            ⊢ ∃ k, ∃ x, iprop(⌜ys[k]? = some x⌝ ∧ Φ (k + 1) x) := ih
          _ ⊢ ∃ k, ∃ x, iprop(⌜(y :: ys)[k + 1]? = some x⌝ ∧ Φ (k + 1) x) := by
              apply exists_mono; intro k
              apply exists_mono; intro x
              apply and_mono _ Entails.rfl
              apply pure_mono; intro h; exact h
          _ ⊢ ∃ k, ∃ x, iprop(⌜(y :: ys)[k]? = some x⌝ ∧ Φ k x) := by
              apply exists_elim; intro k
              exact exists_intro' (k + 1) Entails.rfl
  · -- Backward: ∃ k x, ⌜l[k]? = some x⌝ ∧ Φ k x ⊢ [∨ list] k ↦ x ∈ l, Φ k x
    apply exists_elim; intro k
    apply exists_elim; intro x
    apply pure_elim_l; intro hget
    exact intro hget

/-! ## Pure Propositions -/

theorem pure {φ : Nat → A → Prop} {l : List A} :
    ([∨ list] k ↦ x ∈ l, (⌜φ k x⌝ : PROP)) ⊣⊢ iprop(⌜∃ k x, l[k]? = some x ∧ φ k x⌝ : PROP) := by
  -- Following Rocq: use exist theorem and pure_exists
  calc ([∨ list] k ↦ x ∈ l, (⌜φ k x⌝ : PROP))
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
    iprop(P ∗ [∨ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(P ∗ Φ k x) := by
  -- Following Rocq: rewrite using exist and sep_exists_l
  calc iprop(P ∗ [∨ list] k ↦ x ∈ l, Φ k x)
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
    _ ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(P ∗ Φ k x) := exist.symm

-- Distribute sep from the right: [∨ list] ∗ P ⊣⊢ [∨ list] k ↦ x, Φ k x ∗ P
theorem sep_r {Φ : Nat → A → PROP} {P : PROP} {l : List A} :
    iprop(([∨ list] k ↦ x ∈ l, Φ k x) ∗ P) ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(Φ k x ∗ P) := by
  calc iprop(([∨ list] k ↦ x ∈ l, Φ k x) ∗ P)
      ⊣⊢ iprop(P ∗ [∨ list] k ↦ x ∈ l, Φ k x) := sep_comm
    _ ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(P ∗ Φ k x) := sep_l
    _ ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(Φ k x ∗ P) :=
        equiv_iff.mp (congr (fun k x => equiv_iff.mpr sep_comm))

/-! ## Lookup Lemmas -/

-- Extract an element via membership
theorem elem_of {Φ : A → PROP} {l : List A} {x : A}
    (h : x ∈ l) :
    Φ x ⊢ [∨ list] y ∈ l, Φ y := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [bigOrL, bigOpL]
    cases h with
    | head => exact or_intro_l
    | tail _ hmem => exact (ih hmem).trans or_intro_r

/-! ## Bind -/

theorem bind {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    ([∨ list] y ∈ (l.flatMap f), Φ y) ⊣⊢
      [∨ list] x ∈ l, [∨ list] y ∈ (f x), Φ y := by
  induction l with
  | nil => exact .rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, bigOrL, bigOpL]
    exact app.trans (or_congr .rfl ih)

/-! ## Modality Interaction -/

theorem persistently {Φ : Nat → A → PROP} {l : List A} :
    iprop(<pers> [∨ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(<pers> Φ k x) := by
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
    calc iprop(<pers> (Φ 0 x ∨ [∨ list] n ↦ y ∈ xs, Φ (n + 1) y))
        ⊣⊢ iprop(<pers> Φ 0 x ∨ <pers> [∨ list] n ↦ y ∈ xs, Φ (n + 1) y) := persistently_or
      _ ⊣⊢ iprop(<pers> Φ 0 x ∨ [∨ list] n ↦ y ∈ xs, iprop(<pers> Φ (n + 1) y)) :=
          or_congr .rfl ih

/-- Later distributes over non-empty big disjunctions.
    The proof follows Rocq's approach using the singleton lemma to avoid needing `▷ False ⊢ False`. -/
theorem later {Φ : Nat → A → PROP} {l : List A} (hne : l ≠ []) :
    iprop(▷ [∨ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(▷ Φ k x) := by
  induction l generalizing Φ with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil =>
      -- Singleton case: [∨ list] k ↦ y ∈ [x], Φ k y ⊣⊢ Φ 0 x (by singleton lemma)
      -- So ▷ [∨ list] ... ⊣⊢ ▷ Φ 0 x and [∨ list] k ↦ y ∈ [x], ▷ Φ k y ⊣⊢ ▷ Φ 0 x
      calc iprop(▷ [∨ list] k ↦ y ∈ [x], Φ k y)
          ⊣⊢ iprop(▷ Φ 0 x) := later_congr singleton
        _ ⊣⊢ [∨ list] k ↦ y ∈ [x], iprop(▷ Φ k y) :=
            (singleton (Φ := fun k y => iprop(▷ Φ k y))).symm
    | cons y ys =>
      -- l = x :: y :: ys, which has at least two elements
      simp only [bigOrL, bigOpL]
      calc iprop(▷ (Φ 0 x ∨ [∨ list] n ↦ z ∈ (y :: ys), Φ (n + 1) z))
          ⊣⊢ iprop(▷ Φ 0 x ∨ ▷ [∨ list] n ↦ z ∈ (y :: ys), Φ (n + 1) z) := later_or
        _ ⊣⊢ iprop(▷ Φ 0 x ∨ [∨ list] n ↦ z ∈ (y :: ys), iprop(▷ Φ (n + 1) z)) := by
            apply or_congr .rfl
            exact ih (by simp)

theorem laterN {Φ : Nat → A → PROP} {l : List A} {n : Nat} (hne : l ≠ []) :
    iprop(▷^[n] [∨ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(▷^[n] Φ k x) := by
  induction n with
  | zero => exact .rfl
  | succ m ih =>
    calc iprop(▷ ▷^[m] [∨ list] k ↦ x ∈ l, Φ k x)
        ⊣⊢ iprop(▷ [∨ list] k ↦ x ∈ l, iprop(▷^[m] Φ k x)) :=
          later_congr ih
      _ ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(▷ ▷^[m] Φ k x) := later hne

/-! ## Permutation -/

theorem perm {Φ : A → PROP} {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    ([∨ list] x ∈ l₁, Φ x) ≡ [∨ list] x ∈ l₂, Φ x :=
  BigOpL.perm Φ hp

/-! ## Submultiset Lemma -/

/-- Corresponds to `big_orL_submseteq` in Rocq Iris.
    If l1 is a submultiset of l2 (i.e., l1 ++ l ~ l2 for some l),
    then the big or over l1 entails the big or over l2.
    Note: direction is opposite to BigAndL - here we go FROM smaller TO larger. -/
theorem submseteq {Φ : A → PROP} {l₁ l₂ l : List A}
    (h : (l₁ ++ l).Perm l₂) :
    ([∨ list] x ∈ l₁, Φ x) ⊢ [∨ list] x ∈ l₂, Φ x := by
  have hperm := (equiv_iff.mp (perm (Φ := Φ) h)).1
  -- [∨ list] x ∈ l₁, Φ x ⊢ [∨ list] x ∈ l₁, Φ x ∨ [∨ list] x ∈ l, Φ x ⊢ [∨ list] x ∈ (l₁ ++ l), Φ x ⊢ [∨ list] x ∈ l₂, Φ x
  have step1 : ([∨ list] x ∈ l₁, Φ x) ⊢ ([∨ list] x ∈ l₁, Φ x) ∨ [∨ list] x ∈ l, Φ x :=
    or_intro_l (Q := [∨ list] x ∈ l, Φ x)
  have step2 : (([∨ list] x ∈ l₁, Φ x) ∨ [∨ list] x ∈ l, Φ x) ⊢ [∨ list] x ∈ (l₁ ++ l), Φ x :=
    (app (Φ := fun _ => Φ) (l₁ := l₁) (l₂ := l)).2
  exact step1.trans (step2.trans hperm)

/-! ## Monotonicity Instances -/

/-- Corresponds to `big_orL_mono'` in Rocq Iris.
    Unconditional version of `mono` - pointwise entailment implies big or entailment. -/
theorem mono' {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Φ k x ⊢ Ψ k x) :
    ([∨ list] k ↦ x ∈ l, Φ k x) ⊢ [∨ list] k ↦ x ∈ l, Ψ k x :=
  mono fun k x _ => h k x

/-- Corresponds to `big_orL_id_mono'` in Rocq Iris.
    If lists are pairwise entailing, so are their big ors.
    Uses indexed lookup instead of Forall2. -/
theorem id_mono' {l₁ l₂ : List PROP}
    (hlen : l₁.length = l₂.length)
    (h : ∀ (i : Nat) (P Q : PROP), l₁[i]? = some P → l₂[i]? = some Q → P ⊢ Q) :
    ([∨ list] P ∈ l₁, P) ⊢ [∨ list] P ∈ l₂, P := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact Entails.rfl
    | cons _ _ => simp at hlen
  | cons P Ps ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons Q Qs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [bigOrL, bigOpL]
      have h0 : P ⊢ Q := h 0 P Q rfl rfl
      have htail : ∀ (i : Nat) (P' Q' : PROP), Ps[i]? = some P' → Qs[i]? = some Q' → P' ⊢ Q' :=
        fun i P' Q' hp hq => h (i + 1) P' Q' hp hq
      exact or_mono h0 (ih hlen htail)

/-! ## Typeclass Closure -/

/-- Persistent instance for empty list - trivially persistent via False. -/
instance nil_persistent {Φ : Nat → A → PROP} :
    Persistent ([∨ list] k ↦ x ∈ ([] : List A), Φ k x) := by
  simp only [bigOrL, bigOpL]
  infer_instance

/-- Corresponds to `big_orL_persistent` in Rocq Iris.
    Conditional persistent: if all elements are persistent, the big or is persistent. -/
theorem persistent_cond {Φ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Persistent (Φ k x)) :
    Persistent ([∨ list] k ↦ x ∈ l, Φ k x) where
  persistent := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigOrL, bigOpL]
      exact (false_elim (P := iprop(<pers> (False : PROP))))
    | cons y ys ih =>
      simp only [bigOrL, bigOpL]
      have h0 : Persistent (Φ 0 y) := h 0 y rfl
      have htail : ∀ k x, ys[k]? = some x → Persistent (Φ (k + 1) x) := fun k x hget => h (k + 1) x hget
      have iha := ih htail
      -- P ∨ Q ⊢ <pers> (P ∨ Q) when P and Q are both persistent
      -- We have: P ∨ Q ⊢ <pers> P ∨ <pers> Q ⊢ <pers> (P ∨ Q)
      apply or_elim
      · exact h0.persistent.trans (persistently_mono or_intro_l)
      · exact iha.trans (persistently_mono or_intro_r)

/-- Corresponds to `big_orL_persistent'` in Rocq Iris.
    Typeclass instance: if all values of Φ are persistent, the big or is persistent. -/
instance persistent {Φ : Nat → A → PROP} {l : List A} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∨ list] k ↦ x ∈ l, Φ k x) :=
  persistent_cond fun _ _ _ => inferInstance

/-! ## Zip with Sequence -/

/-- Corresponds to `big_orL_zip_seq` in Rocq Iris.
    Big or over zip with a shifted sequence.
    Relates `[∨ list] ky ∈ zip (range' n len) l, Φ ky` to `[∨ list] k↦y ∈ l, Φ (n + k, y)`. -/
theorem zip_seq {Φ : Nat × A → PROP} {n : Nat} {l : List A} :
    ([∨ list] ky ∈ ((List.range' n l.length).zip l), Φ ky) ≡
      [∨ list] i ↦ x ∈ l, Φ (n + i, x) :=
  BigOpL.zip_seq (op := or) (unit := iprop(False)) Φ n l

/-- Corresponds to `big_orL_zip_seqZ` in Rocq Iris (for Nat, not Z).
    Big or over zip with a sequence starting at 0.
    This is a special case of `zip_seq` with `n = 0`. -/
theorem zip_seqZ {Φ : Nat × A → PROP} {l : List A} :
    ([∨ list] ky ∈ ((List.range l.length).zip l), Φ ky) ≡
      [∨ list] i ↦ x ∈ l, Φ (i, x) :=
  BigOpL.zip_with_range (op := or) (unit := iprop(False)) Φ l

end BigOrL

end Iris.BI
