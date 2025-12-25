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

/-- Corresponds to `big_orL_nil` in Rocq Iris. -/
@[simp]
theorem nil {Φ : Nat → A → PROP} :
    ([∨ list] k ↦ x ∈ ([] : List A), Φ k x) ⊣⊢ iprop(False) := by
  simp only [bigOrL, bigOpL]
  exact .rfl

/-- Corresponds to `big_orL_nil'` in Rocq Iris. -/
theorem nil' {Φ : Nat → A → PROP} {l : List A} (h : l = []) :
    ([∨ list] k ↦ x ∈ l, Φ k x) ⊣⊢ iprop(False) := by
  subst h; exact nil

/-- Corresponds to `big_orL_cons` in Rocq Iris. -/
theorem cons {Φ : Nat → A → PROP} {x : A} {xs : List A} :
    ([∨ list] k ↦ y ∈ (x :: xs), Φ k y) ⊣⊢ Φ 0 x ∨ [∨ list] n ↦ y ∈ xs, Φ (n + 1) y := by
  simp only [bigOrL, bigOpL]
  exact .rfl

/-- Corresponds to `big_orL_singleton` in Rocq Iris. -/
theorem singleton {Φ : Nat → A → PROP} {x : A} :
    ([∨ list] k ↦ y ∈ [x], Φ k y) ⊣⊢ Φ 0 x :=
  equiv_iff.mp (BigOpL.singleton Φ x)

/-- Corresponds to `big_orL_app` in Rocq Iris. -/
theorem app {Φ : Nat → A → PROP} {l₁ l₂ : List A} :
    ([∨ list] k ↦ x ∈ (l₁ ++ l₂), Φ k x) ⊣⊢
      ([∨ list] k ↦ x ∈ l₁, Φ k x) ∨ [∨ list] n ↦ x ∈ l₂, Φ (n + l₁.length) x :=
  equiv_iff.mp (BigOpL.append Φ l₁ l₂)

/-- Corresponds to `big_orL_snoc` in Rocq Iris. -/
theorem snoc {Φ : Nat → A → PROP} {l : List A} {x : A} :
    ([∨ list] k ↦ y ∈ (l ++ [x]), Φ k y) ⊣⊢ ([∨ list] k ↦ y ∈ l, Φ k y) ∨ Φ l.length x :=
  equiv_iff.mp (BigOpL.snoc Φ l x)

/-! ## Monotonicity and Congruence -/

/-- Corresponds to `big_orL_mono` in Rocq Iris. -/
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

/-- Corresponds to `big_orL_proper` in Rocq Iris. -/
theorem proper {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Φ k x ≡ Ψ k x) :
    ([∨ list] k ↦ x ∈ l, Φ k x) ≡ [∨ list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr h

/-- No direct Rocq equivalent; unconditional version of `proper`. -/
theorem congr {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Φ k x ≡ Ψ k x) :
    ([∨ list] k ↦ x ∈ l, Φ k x) ≡ [∨ list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr' h

/-! ## Unit/False Lemma -/

/-- Corresponds to `big_orL_false` in Rocq Iris. -/
theorem false_l {l : List A} :
    ([∨ list] _k ∈ l, iprop(False : PROP)) ≡ iprop(False) :=
  BigOpL.unit_const l

/-! ## Distribution over Or -/

/-- Corresponds to `big_orL_or` in Rocq Iris. -/
theorem or' {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∨ list] k ↦ x ∈ l, iprop(Φ k x ∨ Ψ k x)) ≡
      iprop(([∨ list] k ↦ x ∈ l, Φ k x) ∨ [∨ list] k ↦ x ∈ l, Ψ k x) :=
  BigOpL.op_distr Φ Ψ l

/-- No direct Rocq equivalent; reverse direction of `or'`. -/
theorem or_2 {Φ Ψ : Nat → A → PROP} {l : List A} :
    iprop(([∨ list] k ↦ x ∈ l, Φ k x) ∨ [∨ list] k ↦ x ∈ l, Ψ k x) ≡
      [∨ list] k ↦ x ∈ l, iprop(Φ k x ∨ Ψ k x) :=
  or'.symm

/-! ## Take and Drop -/

/-- Corresponds to `big_orL_take_drop` in Rocq Iris. -/
theorem take_drop {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∨ list] k ↦ x ∈ l, Φ k x) ≡
      iprop(([∨ list] k ↦ x ∈ (l.take n), Φ k x) ∨ [∨ list] k ↦ x ∈ (l.drop n), Φ (n + k) x) :=
  BigOpL.take_drop Φ l n

/-! ## Fmap -/

/-- Corresponds to `big_orL_fmap` in Rocq Iris. -/
theorem fmap {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    ([∨ list] k ↦ y ∈ (l.map f), Φ k y) ≡ [∨ list] k ↦ x ∈ l, Φ k (f x) := by
  induction l generalizing Φ with
  | nil => simp only [List.map_nil]; exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, bigOrL, bigOpL]
    exact Monoid.op_proper OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

/-! ## Higher-Order Lemmas -/

/-- Corresponds to `big_orL_intro` in Rocq Iris. -/
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

/-- Corresponds to `big_orL_exist` in Rocq Iris. -/
theorem exist {Φ : Nat → A → PROP} {l : List A} :
    ([∨ list] k ↦ x ∈ l, Φ k x) ⊣⊢ ∃ k, ∃ x, iprop(⌜l[k]? = some x⌝ ∧ Φ k x) := by
  constructor
  · -- Forward: induction on l
    induction l generalizing Φ with
    | nil => simp only [bigOrL, bigOpL]; exact false_elim
    | cons y ys ih =>
      simp only [bigOrL, bigOpL]
      apply or_elim
      · -- Φ 0 y ⊢ ∃ k x, ⌜(y :: ys)[k]? = some x⌝ ∧ Φ k x
        -- Following Rocq: rewrite -(exist_intro 0) -(exist_intro x) pure_True // left_id
        exact exists_intro' 0 (exists_intro' y (and_intro (pure_intro rfl) .rfl))
      · -- [∨ list] k ↦ x ∈ ys, Φ (k + 1) x ⊢ ∃ k x, ⌜(y :: ys)[k]? = some x⌝ ∧ Φ k x
        -- Following Rocq: rewrite IH. apply exist_elim=> k. by rewrite -(exist_intro (S k)).
        refine ih.trans (exists_elim fun k => exists_intro' (k + 1) .rfl)
  · -- Backward: apply exist_elim=> k; apply exist_elim=> x. apply pure_elim_l=> ?. by apply: big_orL_intro.
    exact exists_elim fun k => exists_elim fun x => pure_elim_l (intro ·)

/-! ## Pure Propositions -/

/-- Corresponds to `big_orL_pure` in Rocq Iris. -/
theorem pure {φ : Nat → A → Prop} {l : List A} :
    ([∨ list] k ↦ x ∈ l, (⌜φ k x⌝ : PROP)) ⊣⊢ iprop(⌜∃ k x, l[k]? = some x ∧ φ k x⌝ : PROP) :=
  -- Following Rocq: rewrite big_orL_exist. rewrite pure_exist (twice). rewrite -pure_and. done.
  exist.trans <| (exists_congr fun _ => (exists_congr fun _ => pure_and).trans pure_exists).trans pure_exists

/-! ## Interaction with Sep -/

/-- Corresponds to `big_orL_sep_l` in Rocq Iris. -/
theorem sep_l {P : PROP} {Φ : Nat → A → PROP} {l : List A} :
    iprop(P ∗ [∨ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(P ∗ Φ k x) :=
  -- Following Rocq: rewrite !big_orL_exist sep_exist_l. f_equiv=> k. rewrite sep_exist_l. f_equiv=> x.
  -- by rewrite !persistent_and_affinely_sep_l !assoc (comm _ P).
  (sep_congr .rfl exist).trans <| sep_exists_l.trans <| (exists_congr fun _ =>
    sep_exists_l.trans <| exists_congr fun _ =>
      -- P ∗ (⌜_⌝ ∧ Φ) ⊣⊢ ⌜_⌝ ∧ (P ∗ Φ) via persistent_and_affinely_sep_l, assoc, comm
      (sep_congr .rfl persistent_and_affinely_sep_l).trans <|
        sep_assoc.symm.trans <| (sep_congr sep_comm .rfl).trans <|
          sep_assoc.trans persistent_and_affinely_sep_l.symm).trans exist.symm

/-- Corresponds to `big_orL_sep_r` in Rocq Iris. -/
theorem sep_r {Φ : Nat → A → PROP} {P : PROP} {l : List A} :
    iprop(([∨ list] k ↦ x ∈ l, Φ k x) ∗ P) ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(Φ k x ∗ P) :=
  -- Following Rocq: setoid_rewrite (comm bi_sep). apply big_orL_sep_l.
  sep_comm.trans <| sep_l.trans (equiv_iff.mp (congr fun _ _ => equiv_iff.mpr sep_comm))

/-! ## Lookup Lemmas -/

/-- Corresponds to `big_orL_elem_of` in Rocq Iris. -/
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

/-- Corresponds to `big_orL_bind` in Rocq Iris. -/
theorem bind {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    ([∨ list] y ∈ (l.flatMap f), Φ y) ⊣⊢
      [∨ list] x ∈ l, [∨ list] y ∈ (f x), Φ y := by
  induction l with
  | nil => exact .rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, bigOrL, bigOpL]
    exact app.trans (or_congr .rfl ih)

/-! ## Modality Interaction -/

/-- Corresponds to `big_orL_persistently` in Rocq Iris. -/
theorem persistently {Φ : Nat → A → PROP} {l : List A} :
    iprop(<pers> [∨ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(<pers> Φ k x) :=
  -- Following Rocq: apply (big_opL_commute _).
  equiv_iff.mp (BigOpL.commute bi_persistently_or_homomorphism Φ l)

/-- Corresponds to `big_orL_later` in Rocq Iris.
    Later distributes over non-empty big disjunctions. -/
theorem later {Φ : Nat → A → PROP} {l : List A} (hne : l ≠ []) :
    iprop(▷ [∨ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(▷ Φ k x) :=
  -- Following Rocq: apply (big_opL_commute1 _).
  equiv_iff.mp (BigOpL.commute_weak bi_later_or_weak_homomorphism Φ l hne)

/-- Corresponds to `big_orL_laterN` in Rocq Iris. -/
theorem laterN {Φ : Nat → A → PROP} {l : List A} {n : Nat} (hne : l ≠ []) :
    iprop(▷^[n] [∨ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∨ list] k ↦ x ∈ l, iprop(▷^[n] Φ k x) := by
  -- Following Rocq: apply (big_opL_commute1 _).
  induction n with
  | zero => exact .rfl
  | succ m ih => exact (later_congr ih).trans (later hne)

/-! ## Permutation -/

/-- Corresponds to `big_orL_Permutation` in Rocq Iris. -/
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

/-- Corresponds to `big_orL_nil_persistent` in Rocq Iris (typeclass instance). -/
instance nil_persistent {Φ : Nat → A → PROP} :
    Persistent ([∨ list] k ↦ x ∈ ([] : List A), Φ k x) := by
  simp only [bigOrL, bigOpL]
  infer_instance

/-- Corresponds to `big_orL_persistent` in Rocq Iris (conditional version). -/
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

/-- Corresponds to `big_orL_persistent'` in Rocq Iris (typeclass instance). -/
instance persistent {Φ : Nat → A → PROP} {l : List A} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∨ list] k ↦ x ∈ l, Φ k x) :=
  persistent_cond fun _ _ _ => inferInstance

/-! ## Zip with Sequence -/

/-- Corresponds to `big_orL_zip_seq` in Rocq Iris. -/
theorem zip_seq {Φ : Nat × A → PROP} {n : Nat} {l : List A} :
    ([∨ list] ky ∈ ((List.range' n l.length).zip l), Φ ky) ≡
      [∨ list] i ↦ x ∈ l, Φ (n + i, x) :=
  BigOpL.zip_seq (op := or) (unit := iprop(False)) Φ n l

/-- Corresponds to `big_orL_zip_seqZ` in Rocq Iris (uses Nat, not Z). -/
theorem zip_seqZ {Φ : Nat × A → PROP} {l : List A} :
    ([∨ list] ky ∈ ((List.range l.length).zip l), Φ ky) ≡
      [∨ list] i ↦ x ∈ l, Φ (i, x) :=
  BigOpL.zip_with_range (op := or) (unit := iprop(False)) Φ l

/-! ## Missing Lemmas from Rocq Iris

The following lemmas from Rocq Iris are not ported:
- `big_orL_ne`: OFE-level non-expansiveness (handled at algebra layer)
- `big_orL_timeless`, `big_orL_timeless'`: Requires `or_timeless` infrastructure
-/

end BigOrL

end Iris.BI
