/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp
import Iris.BI.Instances
import Iris.Std.TC

namespace Iris.BI

open Iris.Algebra
open Iris.Std
open BIBase


/-! # Big Separating Conjunction over Lists

This file contains lemmas about `bigSepL`, the big separating conjunction over lists.
The main sections are:
- Basic structural lemmas (nil, cons, singleton, app, snoc)
- Monotonicity and congruence
- Typeclass closure (Persistent, Affine, Absorbing, Timeless)
- Lookup/access lemmas
- Operator interaction (sep, and, emp, pure)
- Modality interaction (persistently, later)
- Higher-order lemmas (intro, forall, impl, wand)
- Functional lemmas (fmap, omap, bind)
-/

variable {PROP : Type _} [BI PROP] {A : Type _}

namespace BigSepL

/-! ## Basic Structural Lemmas -/

/-- Corresponds to `big_sepL_nil` in Rocq Iris. -/
@[simp]
theorem nil {Φ : Nat → A → PROP} :
    ([∗ list] k ↦ x ∈ ([] : List A), Φ k x) ⊣⊢ emp := by
  simp only [bigSepL, bigOpL]
  exact .rfl

/-- Corresponds to `big_sepL_nil'` in Rocq Iris. -/
theorem nil' {Φ : Nat → A → PROP} {l : List A} (h : l = []) :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊣⊢ emp := by
  subst h; exact nil

/-- Corresponds to `big_sepL_cons` in Rocq Iris. -/
theorem cons {Φ : Nat → A → PROP} {x : A} {xs : List A} :
    ([∗ list] k ↦ y ∈ x :: xs, Φ k y) ⊣⊢ Φ 0 x ∗ [∗ list] k ↦ y ∈ xs, Φ (k + 1) y := by
  simp only [bigSepL, bigOpL]
  exact .rfl

/-- Corresponds to `big_sepL_singleton` in Rocq Iris. -/
theorem singleton {Φ : Nat → A → PROP} {x : A} :
    ([∗ list] k ↦ y ∈ [x], Φ k y) ⊣⊢ Φ 0 x :=
  equiv_iff.mp (BigOpL.singleton Φ x)

/-- Corresponds to `big_sepL_app` in Rocq Iris. -/
theorem app {Φ : Nat → A → PROP} {l₁ l₂ : List A} :
    ([∗ list] k ↦ x ∈ l₁ ++ l₂, Φ k x) ⊣⊢
      ([∗ list] k ↦ x ∈ l₁, Φ k x) ∗ [∗ list] k ↦ x ∈ l₂, Φ (k + l₁.length) x :=
  equiv_iff.mp (BigOpL.append Φ l₁ l₂)

/-- Corresponds to `big_sepL_snoc` in Rocq Iris. -/
theorem snoc {Φ : Nat → A → PROP} {l : List A} {x : A} :
    ([∗ list] k ↦ y ∈ l ++ [x], Φ k y) ⊣⊢ ([∗ list] k ↦ y ∈ l, Φ k y) ∗ Φ l.length x :=
  equiv_iff.mp (BigOpL.snoc Φ l x)

/-! ## Monotonicity and Congruence -/

/-- Corresponds to `big_sepL_mono` in Rocq Iris. -/
theorem mono {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Φ k x ⊢ Ψ k x) :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊢ [∗ list] k ↦ x ∈ l, Ψ k x := by
  induction l generalizing Φ Ψ with
  | nil => exact Entails.rfl
  | cons y ys ih =>
    simp only [bigSepL, bigOpL]
    apply sep_mono
    · exact h 0 y rfl
    · apply ih
      intro k x hget
      exact h (k + 1) x hget

/-- Corresponds to `big_sepL_proper` in Rocq Iris. -/
theorem proper {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Φ k x ≡ Ψ k x) :
    ([∗ list] k ↦ x ∈ l, Φ k x) ≡ [∗ list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr h

/-- Unconditional version of `proper`. No direct Rocq equivalent. -/
theorem congr {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Φ k x ≡ Ψ k x) :
    ([∗ list] k ↦ x ∈ l, Φ k x) ≡ [∗ list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr' h

/-- Corresponds to `big_sepL_ne` in Rocq Iris.
    Non-expansiveness: if predicates are n-equivalent pointwise, so are their big seps. -/
theorem ne {Φ Ψ : Nat → A → PROP} {l : List A} {n : Nat}
    (h : ∀ k x, l[k]? = some x → Φ k x ≡{n}≡ Ψ k x) :
    ([∗ list] k ↦ x ∈ l, Φ k x) ≡{n}≡ [∗ list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr_ne h

/-- Corresponds to `big_sepL_mono'` in Rocq Iris.
    Monotonicity without lookup condition: pointwise entailment lifts to bigSepL. -/
theorem mono' {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Φ k x ⊢ Ψ k x) :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊢ [∗ list] k ↦ x ∈ l, Ψ k x :=
  mono (fun k x _ => h k x)

/-- Corresponds to `big_sepL_flip_mono'` in Rocq Iris.
    Flip monotonicity: pointwise reverse entailment lifts to bigSepL. -/
theorem flip_mono' {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Ψ k x ⊢ Φ k x) :
    ([∗ list] k ↦ x ∈ l, Ψ k x) ⊢ [∗ list] k ↦ x ∈ l, Φ k x :=
  mono (fun k x _ => h k x)

/-- Corresponds to `big_sepL_id_mono'` in Rocq Iris.
    Identity monotonicity: pairwise entailment on lists lifts to bigSepL.
    This is a version where the predicate is just the identity. -/
theorem id_mono' {Ps Qs : List PROP}
    (hlen : Ps.length = Qs.length)
    (h : ∀ (i : Nat) (P Q : PROP), Ps[i]? = some P → Qs[i]? = some Q → P ⊢ Q) :
    ([∗ list] P ∈ Ps, P) ⊢ [∗ list] Q ∈ Qs, Q := by
  induction Ps generalizing Qs with
  | nil =>
    cases Qs with
    | nil => exact Entails.rfl
    | cons _ _ => simp at hlen
  | cons P Ps' ih =>
    cases Qs with
    | nil => simp at hlen
    | cons Q Qs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [bigSepL, bigOpL]
      apply sep_mono
      · exact h 0 P Q rfl rfl
      · apply ih hlen
        intro i P' Q' hP' hQ'
        exact h (i + 1) P' Q' hP' hQ'

/-! ## Typeclass Closure -/

/-- Corresponds to `big_sepL_persistent'` in Rocq Iris. -/
instance persistent {Φ : Nat → A → PROP} {l : List A} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∗ list] k ↦ x ∈ l, Φ k x) where
  persistent := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigSepL, bigOpL]
      exact persistently_emp_2
    | cons x xs ih =>
      simp only [bigSepL, bigOpL]
      have h1 : Φ 0 x ⊢ <pers> Φ 0 x := Persistent.persistent
      have h2 : bigSepL (fun n => Φ (n + 1)) xs ⊢ <pers> bigSepL (fun n => Φ (n + 1)) xs := ih
      exact (sep_mono h1 h2).trans persistently_sep_2

/-- Corresponds to `big_sepL_affine'` in Rocq Iris. -/
instance affine {Φ : Nat → A → PROP} {l : List A} [∀ k x, Affine (Φ k x)] :
    Affine ([∗ list] k ↦ x ∈ l, Φ k x) where
  affine := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigSepL, bigOpL]
      exact Entails.rfl
    | cons x xs ih =>
      simp only [bigSepL, bigOpL]
      have h1 : Φ 0 x ⊢ emp := Affine.affine
      have h2 : bigSepL (fun n => Φ (n + 1)) xs ⊢ emp := ih
      exact (sep_mono h1 h2).trans sep_emp.1

/-- Corresponds to `big_sepL_persistent_id` in Rocq Iris.
    When all propositions in a list are Persistent, their big sep is Persistent.
    This is for the identity function case: `[∗ list] _ ↦ P ∈ Ps, P` where `Ps : List PROP`. -/
theorem persistent_id {Ps : List PROP} (hPs : ∀ P, P ∈ Ps → Persistent P) :
    Persistent ([∗ list] P ∈ Ps, P) where
  persistent := by
    induction Ps with
    | nil =>
      simp only [bigSepL, bigOpL]
      exact persistently_emp_2
    | cons P Ps' ih =>
      simp only [bigSepL, bigOpL]
      have hP : Persistent P := hPs P List.mem_cons_self
      have hPs' : ∀ Q, Q ∈ Ps' → Persistent Q := fun Q hQ => hPs Q (List.mem_cons_of_mem _ hQ)
      have : Persistent (bigSepL (fun _ (P : PROP) => P) Ps') := ⟨ih hPs'⟩
      have h1 : P ⊢ <pers> P := hP.persistent
      have h2 : bigSepL (fun _ (P : PROP) => P) Ps' ⊢ <pers> bigSepL (fun _ (P : PROP) => P) Ps' :=
        this.persistent
      exact (sep_mono h1 h2).trans persistently_sep_2

/-- Corresponds to `big_sepL_affine_id` in Rocq Iris.
    When all propositions in a list are Affine, their big sep is Affine.
    This is for the identity function case: `[∗ list] _ ↦ P ∈ Ps, P` where `Ps : List PROP`. -/
theorem affine_id {Ps : List PROP} (hPs : ∀ P, P ∈ Ps → Affine P) :
    Affine ([∗ list] P ∈ Ps, P) where
  affine := by
    induction Ps with
    | nil =>
      simp only [bigSepL, bigOpL]
      exact Entails.rfl
    | cons P Ps' ih =>
      simp only [bigSepL, bigOpL]
      have hP : Affine P := hPs P List.mem_cons_self
      have hPs' : ∀ Q, Q ∈ Ps' → Affine Q := fun Q hQ => hPs Q (List.mem_cons_of_mem _ hQ)
      have : Affine (bigSepL (fun _ (P : PROP) => P) Ps') := ⟨ih hPs'⟩
      have h1 : P ⊢ emp := hP.affine
      have h2 : bigSepL (fun _ (P : PROP) => P) Ps' ⊢ emp := this.affine
      exact (sep_mono h1 h2).trans sep_emp.1

/-- Corresponds to `big_sepL_nil_timeless` in Rocq Iris.
    Empty list is timeless (when emp is timeless). -/
instance nil_timeless [Timeless (emp : PROP)] {Φ : Nat → A → PROP} :
    Timeless ([∗ list] k ↦ x ∈ ([] : List A), Φ k x) where
  timeless := by
    simp only [bigSepL, bigOpL]
    exact Timeless.timeless

-- Note: The following timeless instances require a sep_timeless instance to be defined.
-- They are postponed until the infrastructure is in place.
-- See translation_plan_bi_list.md for status.

-- /-- bigSepL is timeless if all elements are timeless (unconditional version). -/
-- instance timeless' [Timeless (emp : PROP)] {Φ : Nat → A → PROP} {l : List A}
--     [∀ k x, Timeless (Φ k x)] :
--     Timeless (bigSepL Φ l) where
--   timeless := by
--     induction l generalizing Φ with
--     | nil =>
--       simp only [bigSepL, bigOpL]
--       exact Timeless.timeless
--     | cons y ys ih =>
--       simp only [bigSepL, bigOpL]
--       -- Requires sep_timeless instance
--       exact inferInstance

-- /-- When all propositions in a list are Timeless, their big sep is Timeless.
--     This is for the identity function case: `[∗ list] _ ↦ P ∈ Ps, P` where `Ps : List PROP`. -/
-- theorem timeless_id [Timeless (emp : PROP)] {Ps : List PROP}
--     (hPs : ∀ P, P ∈ Ps → Timeless P) :
--     Timeless (bigSepL (fun _ (P : PROP) => P) Ps) where
--   timeless := by
--     induction Ps with
--     | nil =>
--       simp only [bigSepL, bigOpL]
--       exact Timeless.timeless
--     | cons P Ps' ih =>
--       simp only [bigSepL, bigOpL]
--       -- Requires sep_timeless instance
--       exact inferInstance

/-! ## Unit/Emp Lemma -/

/-- Corresponds to `big_sepL_emp` in Rocq Iris. -/
theorem emp_l {l : List A} :
    ([∗ list] _x ∈ l, (emp : PROP)) ⊣⊢ emp :=
  equiv_iff.mp (BigOpL.unit_const l)

/-! ## Distribution over Sep -/

/-- Corresponds to `big_sepL_sep` in Rocq Iris. -/
theorem sep' {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗ list] k ↦ x ∈ l, Φ k x ∗ Ψ k x) ⊣⊢ ([∗ list] k ↦ x ∈ l, Φ k x) ∗ [∗ list] k ↦ x ∈ l, Ψ k x :=
  equiv_iff.mp (BigOpL.op_distr Φ Ψ l)

/-- Corresponds to `big_sepL_sep_2` in Rocq Iris. -/
theorem sep_2 {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗ list] k ↦ x ∈ l, Φ k x) ∗ ([∗ list] k ↦ x ∈ l, Ψ k x) ⊣⊢ [∗ list] k ↦ x ∈ l, Φ k x ∗ Ψ k x :=
  sep'.symm

/-! ## Distribution over And -/

/-- Corresponds to `big_sepL_and` in Rocq Iris (one direction only). -/
theorem and' {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗ list] k ↦ x ∈ l, Φ k x ∧ Ψ k x) ⊢
      ([∗ list] k ↦ x ∈ l, Φ k x) ∧ [∗ list] k ↦ x ∈ l, Ψ k x :=
  and_intro (mono fun _ _ _ => and_elim_l) (mono fun _ _ _ => and_elim_r)

/-! ## Wand Lemma -/

/-- Corresponds to `big_sepL_wand` in Rocq Iris. -/
theorem wand {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊢ ([∗ list] k ↦ x ∈ l, Φ k x -∗ Ψ k x) -∗ [∗ list] k ↦ x ∈ l, Ψ k x := by
  apply wand_intro
  calc iprop(bigSepL Φ l ∗ bigSepL (fun k x => iprop(Φ k x -∗ Ψ k x)) l)
      ⊢ bigSepL (fun k x => iprop(Φ k x ∗ (Φ k x -∗ Ψ k x))) l := sep_2.1
    _ ⊢ bigSepL Ψ l := mono fun _ _ _ => wand_elim_r

/-! ## Pure Interaction -/

/-- Corresponds to `big_sepL_pure_1` in Rocq Iris. -/
theorem pure_1 {φ : Nat → A → Prop} {l : List A} :
    ([∗ list] k ↦ x ∈ l, ⌜φ k x⌝) ⊢ (⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) := by
  induction l generalizing φ with
  | nil =>
    simp only [bigSepL, bigOpL]
    exact pure_intro (fun _ _ h => by simp at h)
  | cons y ys ih =>
    simp only [bigSepL, bigOpL]
    calc iprop(⌜φ 0 y⌝ ∗ bigSepL (fun n x => iprop(⌜φ (n + 1) x⌝)) ys)
        ⊢ iprop(⌜φ 0 y⌝ ∗ ⌜∀ k x, ys[k]? = some x → φ (k + 1) x⌝) := sep_mono_r ih
      _ ⊢ iprop(⌜φ 0 y⌝ ∧ ⌜∀ k x, ys[k]? = some x → φ (k + 1) x⌝) := sep_and
      _ ⊢ iprop(⌜φ 0 y ∧ (∀ k x, ys[k]? = some x → φ (k + 1) x)⌝) := pure_and.1
      _ ⊢ (⌜∀ k x, (y :: ys)[k]? = some x → φ k x⌝ : PROP) := pure_mono (fun ⟨hy, hys⟩ k x hget => by
          cases k with
          | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hget; subst hget; exact hy
          | succ k => simp only [List.getElem?_cons_succ] at hget; exact hys k x hget)

/-- Corresponds to `big_sepL_affinely_pure_2` in Rocq Iris. -/
theorem affinely_pure_2 {φ : Nat → A → Prop} {l : List A} :
    iprop(<affine> ⌜∀ k x, l[k]? = some x → φ k x⌝) ⊢
      ([∗ list] k ↦ x ∈ l, <affine> ⌜φ k x⌝ : PROP) := by
  induction l generalizing φ with
  | nil =>
    simp only [bigSepL, bigOpL]
    exact affinely_elim_emp
  | cons y ys ih =>
    simp only [bigSepL, bigOpL]
    -- Goal: <affine> ⌜∀ k x, (y :: ys)[k]? = some x → φ k x⌝ ⊢
    --       <affine> ⌜φ 0 y⌝ ∗ bigSepL (fun n x => <affine> ⌜φ (n + 1) x⌝) ys
    have h1 : (iprop(<affine> ⌜∀ k x, (y :: ys)[k]? = some x → φ k x⌝) : PROP) ⊢
              iprop(<affine> ⌜φ 0 y ∧ (∀ k x, ys[k]? = some x → φ (k + 1) x)⌝) := by
      apply affinely_mono
      apply pure_mono
      intro h
      constructor
      · exact h 0 y rfl
      · intro k x hget
        exact h (k + 1) x hget
    have h2 : (iprop(<affine> ⌜φ 0 y ∧ (∀ k x, ys[k]? = some x → φ (k + 1) x)⌝) : PROP) ⊢
              iprop(<affine> (⌜φ 0 y⌝ ∧ ⌜∀ k x, ys[k]? = some x → φ (k + 1) x⌝)) :=
      affinely_mono pure_and.2
    have h3 : (iprop(<affine> (⌜φ 0 y⌝ ∧ ⌜∀ k x, ys[k]? = some x → φ (k + 1) x⌝)) : PROP) ⊢
              iprop(<affine> ⌜φ 0 y⌝ ∧ <affine> ⌜∀ k x, ys[k]? = some x → φ (k + 1) x⌝) :=
      affinely_and.1
    have h4 : (iprop(<affine> ⌜φ 0 y⌝ ∧ <affine> ⌜∀ k x, ys[k]? = some x → φ (k + 1) x⌝) : PROP) ⊢
              iprop(<affine> ⌜φ 0 y⌝ ∗ <affine> ⌜∀ k x, ys[k]? = some x → φ (k + 1) x⌝) :=
      persistent_and_sep_1
    have h5 : (iprop(<affine> ⌜φ 0 y⌝ ∗ <affine> ⌜∀ k x, ys[k]? = some x → φ (k + 1) x⌝) : PROP) ⊢
              iprop(<affine> ⌜φ 0 y⌝ ∗ bigSepL (fun n x => iprop(<affine> ⌜φ (n + 1) x⌝)) ys) :=
      sep_mono_r ih
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- Corresponds to `big_sepL_pure` in Rocq Iris. Requires `BIAffine`. -/
theorem pure' [BIAffine PROP] {φ : Nat → A → Prop} {l : List A} :
    ([∗ list] k ↦ x ∈ l, ⌜φ k x⌝) ⊣⊢ (⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) :=
  ⟨pure_1,
   -- ⌜∀ k x, l[k]? = some x → φ k x⌝ ⊢ bigSepL (fun k x => ⌜φ k x⌝) l
   -- Use: P ⊣⊢ <affine> P (in BIAffine)
   calc (⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP)
       ⊢ iprop(<affine> ⌜∀ k x, l[k]? = some x → φ k x⌝) := (affine_affinely _).2
     _ ⊢ (bigSepL (fun k x => iprop(<affine> ⌜φ k x⌝)) l : PROP) := affinely_pure_2
     _ ⊢ bigSepL (fun k x => iprop(⌜φ k x⌝)) l := mono fun _ _ _ => affinely_elim⟩

/-! ## Take and Drop -/

/-- Corresponds to `big_sepL_take_drop` in Rocq Iris. -/
theorem take_drop {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊣⊢
      ([∗ list] k ↦ x ∈ l.take n, Φ k x) ∗ [∗ list] k ↦ x ∈ l.drop n, Φ (n + k) x :=
  equiv_iff.mp (BigOpL.take_drop Φ l n)

/-! ## Fmap -/

/-- Corresponds to `big_sepL_fmap` in Rocq Iris. -/
theorem fmap {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    ([∗ list] k ↦ y ∈ l.map f, Φ k y) ≡ [∗ list] k ↦ x ∈ l, Φ k (f x) := by
  induction l generalizing Φ with
  | nil => simp only [List.map_nil]; exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, bigSepL, bigOpL]
    exact Monoid.op_proper OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

/-! ## FilterMap (omap) -/

/-- Corresponds to `big_sepL_omap` in Rocq Iris.
    Big sep over filterMap: the mapped elements with emp for filtered-out elements. -/
theorem omap {B : Type _} (f : A → Option B) {Φ : B → PROP} {l : List A} :
    ([∗ list] y ∈ l.filterMap f, Φ y) ≡
      [∗ list] x ∈ l, (f x).elim emp Φ := by
  induction l with
  | nil => exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons, bigSepL, bigOpL]
    cases hx : f x <;> simp only [Option.elim]
    · exact OFE.Equiv.trans ih (OFE.Equiv.symm (equiv_iff.mpr emp_sep))
    · exact Monoid.op_proper OFE.Equiv.rfl ih

/-! ## Bind (flatMap) -/

/-- Corresponds to `big_sepL_bind` in Rocq Iris.
    Big sep over bind (flatMap): nested iteration. -/
theorem bind {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    ([∗ list] y ∈ l.flatMap f, Φ y) ≡
      [∗ list] x ∈ l, [∗ list] y ∈ f x, Φ y := by
  induction l with
  | nil => exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, bigSepL, bigOpL]
    exact OFE.Equiv.trans (equiv_iff.mpr app) (Monoid.op_proper OFE.Equiv.rfl ih)

/-! ## Lookup Lemmas -/

/-- Corresponds to `big_sepL_lookup_acc` in Rocq Iris.
    Extract an element from bigSepL using the lookup function. -/
theorem lookup_acc {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊣⊢
      Φ i x ∗ (∀ y, Φ i y -∗ [∗ list] k ↦ z ∈ l.set i y, Φ k z) := by
  induction l generalizing i Φ x with
  | nil => simp at h
  | cons z zs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [bigSepL, bigOpL, List.set_cons_zero]
      constructor
      · -- Forward: Φ 0 z ∗ bigSepL ... ⊢ Φ 0 z ∗ ∀ y, Φ 0 y -∗ ...
        apply sep_mono_r
        apply forall_intro
        intro y
        apply wand_intro
        exact sep_comm.1
      · -- Backward: Φ 0 z ∗ ∀ y, Φ 0 y -∗ ... ⊢ Φ 0 z ∗ bigSepL ...
        calc iprop(Φ 0 z ∗ ∀ y, Φ 0 y -∗ Φ 0 y ∗ bigSepL (fun n => Φ (n + 1)) zs)
            ⊢ iprop(Φ 0 z ∗ (Φ 0 z -∗ Φ 0 z ∗ bigSepL (fun n => Φ (n + 1)) zs)) :=
              sep_mono_r (forall_elim z)
          _ ⊢ iprop(Φ 0 z ∗ bigSepL (fun n => Φ (n + 1)) zs) := wand_elim_r
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      simp only [bigSepL, bigOpL, List.set_cons_succ]
      have ih' := ih (i := j) (Φ := fun n => Φ (n + 1)) h
      -- ih' : bigSepL (fun n => Φ (n + 1)) zs ⊣⊢ Φ (j + 1) x ∗ ∀ y, Φ (j + 1) y -∗ bigSepL (fun n => Φ (n + 1)) (zs.set j y)
      -- We need to show:
      --   Φ 0 z ∗ bigSepL (fun n => Φ (n + 1)) zs ⊣⊢
      --   Φ (j + 1) x ∗ ∀ y, Φ (j + 1) y -∗ Φ 0 z ∗ bigSepL (fun n => Φ (n + 1)) (zs.set j y)
      constructor
      · -- Forward direction
        calc iprop(Φ 0 z ∗ bigSepL (fun n => Φ (n + 1)) zs)
            ⊢ iprop(Φ 0 z ∗ (Φ (j + 1) x ∗ ∀ y, Φ (j + 1) y -∗ bigSepL (fun n => Φ (n + 1)) (zs.set j y))) :=
              sep_mono_r ih'.1
          _ ⊢ iprop((Φ 0 z ∗ Φ (j + 1) x) ∗ ∀ y, Φ (j + 1) y -∗ bigSepL (fun n => Φ (n + 1)) (zs.set j y)) :=
              sep_assoc.2
          _ ⊢ iprop((Φ (j + 1) x ∗ Φ 0 z) ∗ ∀ y, Φ (j + 1) y -∗ bigSepL (fun n => Φ (n + 1)) (zs.set j y)) :=
              sep_mono_l sep_comm.1
          _ ⊢ iprop(Φ (j + 1) x ∗ Φ 0 z ∗ ∀ y, Φ (j + 1) y -∗ bigSepL (fun n => Φ (n + 1)) (zs.set j y)) :=
              sep_assoc.1
          _ ⊢ iprop(Φ (j + 1) x ∗ ∀ y, Φ (j + 1) y -∗ Φ 0 z ∗ bigSepL (fun n => Φ (n + 1)) (zs.set j y)) := by
              apply sep_mono_r
              apply forall_intro; intro y
              apply wand_intro
              calc iprop((Φ 0 z ∗ ∀ y, Φ (j + 1) y -∗ bigSepL (fun n => Φ (n + 1)) (zs.set j y)) ∗ Φ (j + 1) y)
                  ⊢ iprop(Φ 0 z ∗ (∀ y, Φ (j + 1) y -∗ bigSepL (fun n => Φ (n + 1)) (zs.set j y)) ∗ Φ (j + 1) y) :=
                    sep_assoc.1
                _ ⊢ iprop(Φ 0 z ∗ ((Φ (j + 1) y -∗ bigSepL (fun n => Φ (n + 1)) (zs.set j y)) ∗ Φ (j + 1) y)) :=
                    sep_mono_r (sep_mono_l (forall_elim y))
                _ ⊢ iprop(Φ 0 z ∗ (Φ (j + 1) y ∗ (Φ (j + 1) y -∗ bigSepL (fun n => Φ (n + 1)) (zs.set j y)))) :=
                    sep_mono_r sep_comm.1
                _ ⊢ iprop(Φ 0 z ∗ bigSepL (fun n => Φ (n + 1)) (zs.set j y)) :=
                    sep_mono_r wand_elim_r
      · -- Backward direction
        -- Key insight: h says zs[j]? = some x, so zs.set j x = zs
        have hset_eq : zs.set j x = zs := by
          apply List.ext_getElem?
          intro k
          simp only [List.getElem?_set]
          by_cases hjk : j = k
          · subst hjk
            have hlt : j < zs.length := List.getElem?_eq_some_iff.mp h |>.1
            simp only [hlt, ↓reduceIte, h]
          · simp only [hjk, ↓reduceIte]
        calc iprop(Φ (j + 1) x ∗ ∀ y, Φ (j + 1) y -∗ Φ 0 z ∗ bigSepL (fun n => Φ (n + 1)) (zs.set j y))
            ⊢ iprop(Φ (j + 1) x ∗ (Φ (j + 1) x -∗ Φ 0 z ∗ bigSepL (fun n => Φ (n + 1)) (zs.set j x))) :=
              sep_mono_r (forall_elim x)
          _ ⊢ iprop(Φ 0 z ∗ bigSepL (fun n => Φ (n + 1)) (zs.set j x)) := wand_elim_r
          _ ⊢ iprop(Φ 0 z ∗ bigSepL (fun n => Φ (n + 1)) zs) := by rw [hset_eq]; exact .rfl

/-- Corresponds to `big_sepL_lookup` in Rocq Iris.
    Simplified lookup: works when either all Φ are affine or Φ i x is absorbing.
    Uses `TCOr` to encode the typeclass disjunction. -/
theorem lookup {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    [TCOr (∀ k y, Affine (Φ k y)) (Absorbing (Φ i x))] →
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x
  | TCOr.l => by
    -- All Φ k y are affine. Use take_drop_middle decomposition.
    have hi : i < l.length := List.getElem?_eq_some_iff.mp h |>.1
    have hx : l[i] = x := List.getElem?_eq_some_iff.mp h |>.2
    have hlen : (l.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi)
    -- l = take i l ++ x :: drop (i + 1) l  (take_drop_middle)
    have hmiddle : l = l.take i ++ x :: l.drop (i + 1) := by
      have htake : l.take (i + 1) = l.take i ++ [x] := by
        rw [List.take_succ_eq_append_getElem hi, hx]
      calc l = l.take (i + 1) ++ l.drop (i + 1) := (List.take_append_drop (i + 1) l).symm
        _ = (l.take i ++ [x]) ++ l.drop (i + 1) := by rw [htake]
        _ = l.take i ++ ([x] ++ l.drop (i + 1)) := List.append_assoc ..
        _ = l.take i ++ (x :: l.drop (i + 1)) := by rfl
    -- Rewrite with hmiddle and apply app
    rw [hmiddle]
    have happ := @app PROP _ A Φ (l.take i) (x :: l.drop (i + 1))
    calc bigSepL Φ (l.take i ++ x :: l.drop (i + 1))
        ⊢ bigSepL Φ (l.take i) ∗ bigSepL (fun k => Φ (k + (l.take i).length)) (x :: l.drop (i + 1)) :=
          happ.1
      _ ⊢ bigSepL Φ (l.take i) ∗ (Φ i x ∗ bigSepL (fun k => Φ (k + 1 + i)) (l.drop (i + 1))) := by
          simp only [hlen, bigSepL, bigOpL, Nat.zero_add]; exact Entails.rfl
      _ ⊢ Φ i x := sep_elim_r.trans sep_elim_l
  | TCOr.r => (lookup_acc h).1.trans sep_elim_l

/-- Corresponds to `big_sepL_insert_acc` in Rocq Iris.
    Insert accessor version (one direction of lookup_acc). -/
theorem insert_acc {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x ∗ (∀ y, Φ i y -∗ [∗ list] k ↦ z ∈ l.set i y, Φ k z) :=
  (lookup_acc h).1

/-- Corresponds to `big_sepL_elem_of_acc` in Rocq Iris.
    Element-of version of lookup_acc (no index). -/
theorem elem_of_acc {Φ : A → PROP} {l : List A} {x : A}
    (h : x ∈ l) :
    ([∗ list] y ∈ l, Φ y) ⊢ Φ x ∗ (Φ x -∗ [∗ list] y ∈ l, Φ y) := by
  have ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
  have hlookup : l[i]? = some x := List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
  have hacc := (lookup_acc (Φ := fun _ => Φ) hlookup).1
  calc bigSepL (fun _ => Φ) l
      ⊢ iprop(Φ x ∗ (∀ y, Φ y -∗ bigSepL (fun _ => Φ) (l.set i y))) := hacc
    _ ⊢ iprop(Φ x ∗ (Φ x -∗ bigSepL (fun _ => Φ) (l.set i x))) := sep_mono_r (forall_elim x)
    _ ⊢ iprop(Φ x ∗ (Φ x -∗ bigSepL (fun _ => Φ) l)) := by
        have hset : l.set i x = l := by
          apply List.ext_getElem?
          intro k
          simp only [List.getElem?_set]
          by_cases hik : i = k
          · subst hik; simp only [hi, ↓reduceIte, hlookup]
          · simp only [hik, ↓reduceIte]
        rw [hset]; exact Entails.rfl

/-- Corresponds to `big_sepL_elem_of` in Rocq Iris.
    Element-of version of lookup using `TCOr`. -/
theorem elem_of {Φ : A → PROP} {l : List A} {x : A}
    (h : x ∈ l) :
    [TCOr (∀ y, Affine (Φ y)) (Absorbing (Φ x))] →
    ([∗ list] y ∈ l, Φ y) ⊢ Φ x
  | TCOr.l => by
    have ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
    have hlookup : l[i]? = some x := List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
    haveI : ∀ (k : Nat) (y : A), Affine ((fun _ y => Φ y) k y) := fun _ y => inferInstance
    exact lookup (Φ := fun _ y => Φ y) hlookup
  | TCOr.r => by
    have ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
    have hlookup : l[i]? = some x := List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
    haveI : Absorbing ((fun _ y => Φ y) i x) := inferInstance
    exact lookup (Φ := fun _ y => Φ y) hlookup

/-! ## Delete Lemmas -/

/-- Corresponds to `big_sepL_delete` in Rocq Iris.
    Extracting an element from bigSepL, leaving emp at that position. -/
theorem delete {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊣⊢
      Φ i x ∗ [∗ list] k ↦ y ∈ l, if k = i then emp else Φ k y := by
  induction l generalizing i Φ with
  | nil => simp at h
  | cons z zs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [bigSepL, bigOpL, ↓reduceIte]
      -- Need: Φ 0 z ∗ bigSepL ... zs ⊣⊢ Φ 0 z ∗ (emp ∗ bigSepL ... zs)
      constructor <;> apply sep_mono_r
      · calc bigSepL (fun n => Φ (n + 1)) zs
            ⊢ bigSepL (fun n y => if n + 1 = 0 then emp else Φ (n + 1) y) zs :=
              mono fun k y _ => by simp only [Nat.add_one_ne_zero, ↓reduceIte]; exact Entails.rfl
          _ ⊢ emp ∗ bigSepL (fun n y => if n + 1 = 0 then emp else Φ (n + 1) y) zs := emp_sep.2
      · calc iprop(emp ∗ bigSepL (fun n y => if n + 1 = 0 then emp else Φ (n + 1) y) zs)
            ⊢ bigSepL (fun n y => if n + 1 = 0 then emp else Φ (n + 1) y) zs := emp_sep.1
          _ ⊢ bigSepL (fun n => Φ (n + 1)) zs :=
              mono fun k y _ => by simp only [Nat.add_one_ne_zero, ↓reduceIte]; exact Entails.rfl
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      simp only [bigSepL, bigOpL]
      have ih' := ih (i := j) (Φ := fun n => Φ (n + 1)) h
      -- ih' : bigSepL (Φ . + 1) zs ⊣⊢ Φ (j+1) x ∗ bigSepL (fun k y => if k = j then emp else Φ (k+1) y) zs
      calc iprop(Φ 0 z ∗ bigSepL (fun n => Φ (n + 1)) zs)
          ⊣⊢ iprop(Φ 0 z ∗ (Φ (j + 1) x ∗ bigSepL (fun k y => if k = j then emp else Φ (k + 1) y) zs)) :=
            ⟨sep_mono_r ih'.1, sep_mono_r ih'.2⟩
        _ ⊣⊢ iprop(Φ (j + 1) x ∗ (Φ 0 z ∗ bigSepL (fun k y => if k = j then emp else Φ (k + 1) y) zs)) := by
            calc iprop(Φ 0 z ∗ (Φ (j + 1) x ∗ bigSepL (fun k y => if k = j then emp else Φ (k + 1) y) zs))
                ⊣⊢ iprop((Φ 0 z ∗ Φ (j + 1) x) ∗ bigSepL (fun k y => if k = j then emp else Φ (k + 1) y) zs) :=
                    sep_assoc.symm
              _ ⊣⊢ iprop((Φ (j + 1) x ∗ Φ 0 z) ∗ bigSepL (fun k y => if k = j then emp else Φ (k + 1) y) zs) :=
                    ⟨sep_mono_l sep_comm.1, sep_mono_l sep_comm.2⟩
              _ ⊣⊢ iprop(Φ (j + 1) x ∗ (Φ 0 z ∗ bigSepL (fun k y => if k = j then emp else Φ (k + 1) y) zs)) :=
                    sep_assoc
        _ ⊣⊢ Φ (j + 1) x ∗ bigSepL (fun k y => if k = j + 1 then emp else Φ k y) (z :: zs) := by
            constructor <;> apply sep_mono_r
            · simp only [bigSepL, bigOpL]
              have hne0 : (0 : Nat) ≠ j + 1 := Nat.zero_ne_add_one j
              simp only [hne0, ↓reduceIte]
              apply sep_mono_r
              apply mono
              intro k y _
              by_cases hkj : k = j
              · subst hkj; simp only [↓reduceIte]; exact Entails.rfl
              · simp only [hkj, ↓reduceIte]
                have hkj' : k + 1 ≠ j + 1 := by omega
                simp only [hkj', ↓reduceIte]; exact Entails.rfl
            · simp only [bigSepL, bigOpL]
              have hne0 : (0 : Nat) ≠ j + 1 := Nat.zero_ne_add_one j
              simp only [hne0, ↓reduceIte]
              apply sep_mono_r
              apply mono
              intro k y _
              by_cases hkj : k = j
              · subst hkj; simp only [↓reduceIte]; exact Entails.rfl
              · simp only [hkj, ↓reduceIte]
                have hkj' : k + 1 ≠ j + 1 := by omega
                simp only [hkj', ↓reduceIte]; exact Entails.rfl

/-- Corresponds to `big_sepL_delete'` in Rocq Iris.
    BIAffine version of delete using implication instead of emp. -/
theorem delete' [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊣⊢ Φ i x ∗ [∗ list] k ↦ y ∈ l, ⌜k ≠ i⌝ → Φ k y := by
  calc bigSepL Φ l
      ⊣⊢ Φ i x ∗ bigSepL (fun k y => if k = i then emp else Φ k y) l := delete h
    _ ⊣⊢ Φ i x ∗ bigSepL (fun k y => iprop(⌜k ≠ i⌝ → Φ k y)) l := by
        constructor <;> apply sep_mono_r
        · apply mono; intro k y _
          by_cases hki : k = i
          · subst hki; simp only [↓reduceIte, ne_eq, not_true_eq_false]
            apply imp_intro'
            exact (pure_elim_l (φ := False) (R := Φ k y) (fun hf => False.elim hf)).trans Entails.rfl
          · simp only [hki, ↓reduceIte, ne_eq, not_false_eq_true]
            exact true_imp.2
        · apply mono; intro k y _
          by_cases hki : k = i
          · subst hki; simp only [↓reduceIte, ne_eq, not_true_eq_false]
            exact Affine.affine
          · simp only [hki, ↓reduceIte, ne_eq, not_false_eq_true]
            exact true_imp.1

/-! ## Higher-Order Lemmas -/

/-- Corresponds to `big_sepL_intro` in Rocq Iris.
    Introduction rule: if P entails each Φ k x, then P entails the big sep.
    This requires P to be intuitionistic (persistent and affine) to duplicate. -/
theorem intro {P : PROP} {Φ : Nat → A → PROP} {l : List A} [Intuitionistic P]
    (h : ∀ k x, l[k]? = some x → P ⊢ Φ k x) :
    P ⊢ [∗ list] k ↦ x ∈ l, Φ k x := by
  induction l generalizing Φ with
  | nil =>
    simp only [bigSepL, bigOpL]
    exact Intuitionistic.intuitionistic.trans (affinely_elim_emp (PROP := PROP))
  | cons y ys ih =>
    simp only [bigSepL, bigOpL]
    have h1 : P ⊢ Φ 0 y := h 0 y rfl
    have h2 : P ⊢ bigSepL (fun n => Φ (n + 1)) ys := ih (fun k x hget => h (k + 1) x hget)
    -- Use intuitionistic to duplicate P: P ⊢ □ P, and □ P ∗ □ P ⊣⊢ □ P
    have hbox : P ⊢ □ P := Intuitionistic.intuitionistic
    have hdup : iprop(□ P) ⊢ iprop(□ P ∗ □ P) := intuitionistically_sep_idem.2
    exact hbox.trans (hdup.trans (sep_mono (intuitionistically_elim.trans h1)
      (intuitionistically_elim.trans h2)))

/-- Corresponds to `big_sepL_forall` in Rocq Iris.
    bigSepL entails forall when all elements are persistent. -/
theorem forall' {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP]
    [∀ k x, Persistent (Φ k x)] :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) := by
  apply forall_intro; intro k
  apply forall_intro; intro x
  apply imp_intro'
  apply pure_elim_l
  intro hget
  -- Use lookup_acc to extract element
  have hacc : bigSepL Φ l ⊢ Φ k x ∗ (∀ y, Φ k y -∗ bigSepL Φ (l.set k y)) :=
    (lookup_acc hget).1
  -- We need: bigSepL Φ l ⊢ Φ k x
  -- Since Φ k x is persistent:
  -- 1. Φ k x ⊢ <pers> Φ k x (by Persistent.persistent)
  -- 2. <pers> P ∗ Q ⊢ <pers> P (by persistently_absorb_r composed with sep_comm)
  -- 3. <pers> P ⊢ P (by persistently_elim, since BIAffine implies Absorbing)
  calc bigSepL Φ l
      ⊢ iprop(Φ k x ∗ (∀ y, Φ k y -∗ bigSepL Φ (l.set k y))) := hacc
    _ ⊢ iprop(<pers> Φ k x ∗ (∀ y, Φ k y -∗ bigSepL Φ (l.set k y))) := sep_mono_l Persistent.persistent
    _ ⊢ iprop(<pers> Φ k x) := sep_comm.1.trans persistently_absorb_r
    _ ⊢ Φ k x := persistently_elim

/-- Corresponds to `big_sepL_impl` in Rocq Iris.
    Implication under bigSepL (wand version, matching Iris/Rocq style). -/
theorem impl {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊢ □ (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x)) -∗ [∗ list] k ↦ x ∈ l, Ψ k x := by
  apply wand_intro
  -- Goal: bigSepL Φ l ∗ □ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x) ⊢ bigSepL Ψ l
  -- Step 1: Use intro to get bigSepL (fun k x => Φ k x -∗ Ψ k x) l from the □ hypothesis
  -- Step 2: Combine with sep_2 to get bigSepL (fun k x => Φ k x ∗ (Φ k x -∗ Ψ k x)) l
  -- Step 3: Apply mono with wand_elim_l pointwise
  have h1 : iprop(□ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x)) ⊢ bigSepL (fun k x => iprop(Φ k x -∗ Ψ k x)) l := by
    haveI : Intuitionistic iprop(□ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x)) :=
      intuitionistically_intuitionistic _
    apply intro
    intro k x hget
    calc iprop(□ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x))
        ⊢ iprop(∀ k x, ⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x) := intuitionistically_elim
      _ ⊢ iprop(⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x) := forall_elim k |>.trans (forall_elim x)
      _ ⊢ iprop(⌜True⌝ → Φ k x -∗ Ψ k x) := imp_mono_l (pure_mono (fun _ => hget))
      _ ⊢ Φ k x -∗ Ψ k x := (true_imp (P := iprop(Φ k x -∗ Ψ k x))).1
  calc iprop(bigSepL Φ l ∗ □ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x))
      ⊢ iprop(bigSepL Φ l ∗ bigSepL (fun k x => iprop(Φ k x -∗ Ψ k x)) l) := sep_mono_r h1
    _ ⊢ bigSepL (fun k x => iprop(Φ k x ∗ (Φ k x -∗ Ψ k x))) l := sep_2.1
    _ ⊢ bigSepL Ψ l := mono (fun _ _ _ => wand_elim_r)

/-- Corresponds to `big_sepL_lookup_acc_impl` in Rocq Iris.
    Lookup with ability to change predicate when restoring.
    This is the most general form: extract element, then restore with a different predicate. -/
theorem lookup_acc_impl {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    iprop([∗ list] k ↦ x ∈ l, Φ k x) ⊢
      Φ i x ∗ ∀ (Ψ: Nat → A → PROP), □ (∀ k y, iprop(⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y)) -∗
        Ψ i x -∗  ([∗ list] k ↦ x ∈ l, Ψ k x) := by
  -- Use delete to extract element
  have hdel := (delete (Φ := Φ) h).1
  calc bigSepL Φ l
      ⊢ iprop(Φ i x ∗ bigSepL (fun k y => if k = i then emp else Φ k y) l) := hdel
    _ ⊢ Φ i x ∗ ∀ Ψ, □ (∀ k y, iprop(⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y)) -∗
          Ψ i x -∗ bigSepL Ψ l := by
        apply sep_mono_r
        apply forall_intro; intro Ψ
        apply wand_intro
        apply wand_intro
        -- Goal: (bigSepL (if k = i then emp else Φ k y) l ∗ □ (...)) ∗ Ψ i x ⊢ bigSepL Ψ l
        -- Strategy: Use delete on Ψ to show we need Ψ i x and bigSepL (if k = i then emp else Ψ) l
        have hdel_psi := (delete (Φ := Ψ) h).2
        calc iprop((bigSepL (fun k y => if k = i then emp else Φ k y) l ∗
                  □ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y)) ∗ Ψ i x)
            ⊢ iprop(Ψ i x ∗ (bigSepL (fun k y => if k = i then emp else Φ k y) l ∗
                  □ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y))) := by
                have := @sep_comm PROP _
                  iprop((bigSepL (fun k y => if k = i then emp else Φ k y) l ∗
                    □ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y)))
                  iprop(Ψ i x)
                exact this.1
          _ ⊢ iprop(Ψ i x ∗ bigSepL (fun k y => if k = i then emp else Ψ k y) l) := by
                apply sep_mono_r
                -- Transform bigSepL with Φ to bigSepL with Ψ using the □ hypothesis
                -- For positions k ≠ i: use the hypothesis to transform Φ k y to Ψ k y
                -- For position i: both are emp
                calc iprop(bigSepL (fun k y => if k = i then emp else Φ k y) l ∗
                      □ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y))
                    ⊢ iprop(bigSepL (fun k y => if k = i then emp else Φ k y) l ∗
                          bigSepL (fun k y => if k = i then emp else iprop(Φ k y -∗ Ψ k y)) l) := by
                        apply sep_mono_r
                        haveI : Intuitionistic iprop(□ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y)) :=
                          intuitionistically_intuitionistic _
                        apply intro
                        intro k y hget
                        by_cases hki : k = i
                        · -- k = i: goal is □(...) ⊢ emp
                          subst hki
                          simp only [↓reduceIte]
                          exact Intuitionistic.intuitionistic.trans (affinely_elim_emp (PROP := PROP))
                        · -- k ≠ i: goal is □(...) ⊢ Φ k y -∗ Ψ k y
                          simp only [hki, ↓reduceIte]
                          calc iprop(□ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y))
                              ⊢ iprop(∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y) := intuitionistically_elim
                            _ ⊢ iprop(⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y) :=
                                forall_elim k |>.trans (forall_elim y)
                            _ ⊢ iprop(⌜True⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y) :=
                                imp_mono_l (pure_mono (fun _ => hget))
                            _ ⊢ iprop(⌜k ≠ i⌝ → Φ k y -∗ Ψ k y) := true_imp.1
                            _ ⊢ iprop(⌜True⌝ → Φ k y -∗ Ψ k y) := imp_mono_l (pure_mono (fun _ => hki))
                            _ ⊢ Φ k y -∗ Ψ k y := true_imp.1
                  _ ⊢ bigSepL (fun k y => iprop((if k = i then emp else Φ k y) ∗
                          (if k = i then emp else iprop(Φ k y -∗ Ψ k y)))) l := sep_2.1
                  _ ⊢ bigSepL (fun k y => if k = i then emp else Ψ k y) l := by
                        apply mono
                        intro k y _
                        by_cases hki : k = i
                        · subst hki
                          simp only [↓reduceIte]
                          exact emp_sep.1
                        · simp only [hki, ↓reduceIte]
                          exact wand_elim_r
          _ ⊢ bigSepL Ψ l := hdel_psi

/-! ## Modality Interaction -/

/-- Corresponds to `big_sepL_persistently` in Rocq Iris. Requires `BIAffine`. -/
theorem persistently {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] :
    iprop(<pers> [∗ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗ list] k ↦ x ∈ l, <pers> Φ k x := by
  induction l generalizing Φ with
  | nil =>
    simp only [bigSepL, bigOpL]
    exact persistently_emp' (PROP := PROP)
  | cons x xs ih =>
    simp only [bigSepL, bigOpL]
    calc iprop(<pers> (Φ 0 x ∗ bigSepL (fun n => Φ (n + 1)) xs))
        ⊣⊢ iprop(<pers> Φ 0 x ∗ <pers> bigSepL (fun n => Φ (n + 1)) xs) := persistently_sep
      _ ⊣⊢ iprop(<pers> Φ 0 x ∗ bigSepL (fun n k => iprop(<pers> Φ (n + 1) k)) xs) :=
          ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

/-! ## Later Modality -/

/-- Corresponds to `big_sepL_later` in Rocq Iris.
    Later distributes over bigSepL (equivalence requires BIAffine for emp case). -/
theorem later [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} :
    iprop(▷ [∗ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗ list] k ↦ x ∈ l, ▷ Φ k x := by
  induction l generalizing Φ with
  | nil =>
    simp only [bigSepL, bigOpL]
    exact later_emp
  | cons x xs ih =>
    simp only [bigSepL, bigOpL]
    calc iprop(▷ (Φ 0 x ∗ bigSepL (fun n => Φ (n + 1)) xs))
        ⊣⊢ iprop(▷ Φ 0 x ∗ ▷ bigSepL (fun n => Φ (n + 1)) xs) := later_sep
      _ ⊣⊢ iprop(▷ Φ 0 x ∗ bigSepL (fun n k => iprop(▷ Φ (n + 1) k)) xs) :=
          ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

/-- Corresponds to `big_sepL_later_2` in Rocq Iris.
    Later distribution (one direction, no BIAffine needed). -/
theorem later_2 {Φ : Nat → A → PROP} {l : List A} :
    ([∗ list] k ↦ x ∈ l, ▷ Φ k x) ⊢ iprop(▷ [∗ list] k ↦ x ∈ l, Φ k x) := by
  induction l generalizing Φ with
  | nil =>
    simp only [bigSepL, bigOpL]
    exact later_intro
  | cons x xs ih =>
    simp only [bigSepL, bigOpL]
    calc iprop(▷ Φ 0 x ∗ bigSepL (fun n y => iprop(▷ Φ (n + 1) y)) xs)
        ⊢ iprop(▷ Φ 0 x ∗ ▷ bigSepL (fun n => Φ (n + 1)) xs) := sep_mono_r ih
      _ ⊢ iprop(▷ (Φ 0 x ∗ bigSepL (fun n => Φ (n + 1)) xs)) := later_sep.2

/-- Corresponds to `big_sepL_laterN` in Rocq Iris.
    LaterN distributes over bigSepL (equivalence requires BIAffine). -/
theorem laterN [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    iprop(▷^[n] [∗ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗ list] k ↦ x ∈ l, ▷^[n] Φ k x := by
  induction n with
  | zero =>
    exact .rfl
  | succ m ih =>
    calc iprop(▷ ▷^[m] bigSepL Φ l)
        ⊣⊢ iprop(▷ bigSepL (fun k x => iprop(▷^[m] Φ k x)) l) :=
          later_congr ih
      _ ⊣⊢ bigSepL (fun k x => iprop(▷ ▷^[m] Φ k x)) l := later

/-- Corresponds to `big_sepL_laterN_2` in Rocq Iris.
    LaterN distribution (one direction). -/
theorem laterN_2 {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∗ list] k ↦ x ∈ l, ▷^[n] Φ k x) ⊢ iprop(▷^[n] [∗ list] k ↦ x ∈ l, Φ k x) := by
  induction n with
  | zero =>
    exact Entails.rfl
  | succ m ih =>
    calc bigSepL (fun k x => iprop(▷ ▷^[m] Φ k x)) l
        ⊢ iprop(▷ bigSepL (fun k x => iprop(▷^[m] Φ k x)) l) := later_2
      _ ⊢ iprop(▷ ▷^[m] bigSepL Φ l) := later_mono ih

/-! ## Permutation -/

/-- Corresponds to `big_sepL_Permutation` in Rocq Iris. -/
theorem perm {Φ : A → PROP} {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    ([∗ list] x ∈ l₁, Φ x) ⊣⊢ [∗ list] x ∈ l₂, Φ x :=
  equiv_iff.mp (BigOpL.perm Φ hp)

/-! ## Submultiset Lemma -/

/-- Corresponds to `big_sepL_submseteq` in Rocq Iris.
    If l1 can be obtained from l2 by removing some elements (preserving multiset),
    then the big sep over l2 entails the big sep over l1 (when all elements are Affine).
    This uses the characterization: l1 ⊆+ l2 iff ∃ l, l1 ++ l ~ l2 (where ~ is permutation). -/
theorem submseteq {Φ : A → PROP} [∀ x, Affine (Φ x)] {l₁ l₂ l : List A}
    (h : (l₁ ++ l).Perm l₂) :
    ([∗ list] x ∈ l₂, Φ x) ⊢ [∗ list] x ∈ l₁, Φ x := by
  have hperm := (perm (Φ := Φ) h).2
  have happ := (app (Φ := fun _ => Φ) (l₁ := l₁) (l₂ := l)).1
  exact hperm.trans (happ.trans sep_elim_l)

/-! ## Duplication -/

/-- Corresponds to `big_sepL_dup` in Rocq Iris.
    Duplicate a resource across a list using a duplication wand. -/
theorem dup {P : PROP} [Affine P] {l : List A} :
    iprop(□ (P -∗ P ∗ P)) ⊢ P -∗ [∗ list] _x ∈ l, P := by
  apply wand_intro
  induction l with
  | nil =>
    simp only [bigSepL, bigOpL]
    exact Affine.affine
  | cons x xs ih =>
    simp only [bigSepL, bigOpL]
    -- We have: □ (P -∗ P ∗ P) ∗ P ⊢ P ∗ bigSepL (fun _ _ => P) xs
    -- 1. Duplicate the □ using intuitionistically_sep_dup
    -- 2. Use one copy with wand_elim_r to get P ∗ P
    -- 3. Use induction hypothesis with other copy
    have hdup : iprop(□ (P -∗ P ∗ P)) ⊢ iprop(□ (P -∗ P ∗ P) ∗ □ (P -∗ P ∗ P)) :=
      intuitionistically_sep_idem.2
    have hassoc1 : iprop((□ (P -∗ P ∗ P) ∗ □ (P -∗ P ∗ P)) ∗ P) ⊢
        iprop(□ (P -∗ P ∗ P) ∗ (□ (P -∗ P ∗ P) ∗ P)) :=
      sep_assoc.1
    have hassoc2 : iprop(□ (P -∗ P ∗ P) ∗ (P ∗ P)) ⊢ iprop((□ (P -∗ P ∗ P) ∗ P) ∗ P) :=
      sep_assoc.2
    calc iprop(□ (P -∗ P ∗ P) ∗ P)
        ⊢ iprop((□ (P -∗ P ∗ P) ∗ □ (P -∗ P ∗ P)) ∗ P) := sep_mono_l hdup
      _ ⊢ iprop(□ (P -∗ P ∗ P) ∗ (□ (P -∗ P ∗ P) ∗ P)) := hassoc1
      _ ⊢ iprop(□ (P -∗ P ∗ P) ∗ ((P -∗ P ∗ P) ∗ P)) := sep_mono_r (sep_mono_l intuitionistically_elim)
      _ ⊢ iprop(□ (P -∗ P ∗ P) ∗ (P ∗ P)) := sep_mono_r wand_elim_l
      _ ⊢ iprop((□ (P -∗ P ∗ P) ∗ P) ∗ P) := hassoc2
      _ ⊢ iprop(bigSepL (fun _ _ => P) xs ∗ P) := sep_mono_l ih
      _ ⊢ P ∗ bigSepL (fun _ _ => P) xs := sep_comm.1

/-! ## Replicate -/

/-- Corresponds to `big_sepL_replicate` in Rocq Iris.
    bigSepL over a list equals bigSep over replicate. -/
theorem replicate {P : PROP} {l : List A} :
    ([∗ list] _x ∈ List.replicate l.length P, P) ⊣⊢ [∗ list] _x ∈ l, P := by
  induction l with
  | nil =>
    simp only [List.length_nil, List.replicate]
    exact .rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.replicate, bigSepL, BigOpL.cons]
    exact ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

/-! ## Zip-Related Lemmas -/

/-- Corresponds to `big_sepL_zip_seq` in Rocq Iris.
    Big sep over zip with a shifted sequence. -/
theorem zip_seq {Φ : Nat × A → PROP} {n : Nat} {l : List A} :
    ([∗ list] p ∈ (List.range' n l.length).zip l, Φ p) ⊣⊢
      [∗ list] i ↦ x ∈ l, Φ (n + i, x) :=
  equiv_iff.mp (BigOpL.zip_seq Φ n l)

/-- Lean-only: Big sep over zip with a sequence starting at 0.
    No direct Rocq equivalent (uses zero-indexed range). -/
theorem zip_with_range {Φ : Nat × A → PROP} {l : List A} :
    ([∗ list] p ∈ (List.range l.length).zip l, Φ p) ⊣⊢
      [∗ list] i ↦ x ∈ l, Φ (i, x) :=
  equiv_iff.mp (BigOpL.zip_with_range Φ l)

/-- Corresponds to `big_sepL_sep_zip` in Rocq Iris.
    Big sep over zipped list splits into product of big seps. -/
theorem sep_zip {B : Type _} {Φ : Nat → A → PROP} {Ψ : Nat → B → PROP}
    {l₁ : List A} {l₂ : List B} (hlen : l₁.length = l₂.length) :
    ([∗ list] i ↦ xy ∈ l₁.zip l₂, Φ i xy.1 ∗ Ψ i xy.2) ⊣⊢
      ([∗ list] i ↦ x ∈ l₁, Φ i x) ∗ [∗ list] i ↦ y ∈ l₂, Ψ i y := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil =>
    cases l₂ with
    | nil =>
      simp only [List.zip_nil_left, bigSepL, bigOpL]
      exact emp_sep.symm
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zip_cons_cons, bigSepL, bigOpL]
      -- Goal: (Φ 0 x ∗ Ψ 0 y) ∗ bigSepL ... ⊣⊢ (Φ 0 x ∗ bigSepL Φ' xs) ∗ (Ψ 0 y ∗ bigSepL Ψ' ys)
      have ih' := ih (Φ := fun n => Φ (n + 1)) (Ψ := fun n => Ψ (n + 1)) hlen
      -- ih' : bigSepL ... (xs.zip ys) ⊣⊢ bigSepL Φ' xs ∗ bigSepL Ψ' ys
      calc (Φ 0 x ∗ Ψ 0 y) ∗ bigSepL (fun i xy => iprop(Φ (i + 1) xy.1 ∗ Ψ (i + 1) xy.2)) (xs.zip ys)
          ⊣⊢ (Φ 0 x ∗ Ψ 0 y) ∗ (bigSepL (fun n => Φ (n + 1)) xs ∗ bigSepL (fun n => Ψ (n + 1)) ys) :=
            ⟨sep_mono_r ih'.1, sep_mono_r ih'.2⟩
        _ ⊣⊢ Φ 0 x ∗ (Ψ 0 y ∗ (bigSepL (fun n => Φ (n + 1)) xs ∗ bigSepL (fun n => Ψ (n + 1)) ys)) :=
            sep_assoc
        _ ⊣⊢ Φ 0 x ∗ ((Ψ 0 y ∗ bigSepL (fun n => Φ (n + 1)) xs) ∗ bigSepL (fun n => Ψ (n + 1)) ys) :=
            ⟨sep_mono_r sep_assoc.2, sep_mono_r sep_assoc.1⟩
        _ ⊣⊢ Φ 0 x ∗ ((bigSepL (fun n => Φ (n + 1)) xs ∗ Ψ 0 y) ∗ bigSepL (fun n => Ψ (n + 1)) ys) :=
            ⟨sep_mono_r (sep_mono_l sep_comm.1), sep_mono_r (sep_mono_l sep_comm.2)⟩
        _ ⊣⊢ Φ 0 x ∗ (bigSepL (fun n => Φ (n + 1)) xs ∗ (Ψ 0 y ∗ bigSepL (fun n => Ψ (n + 1)) ys)) :=
            ⟨sep_mono_r sep_assoc.1, sep_mono_r sep_assoc.2⟩
        _ ⊣⊢ (Φ 0 x ∗ bigSepL (fun n => Φ (n + 1)) xs) ∗ (Ψ 0 y ∗ bigSepL (fun n => Ψ (n + 1)) ys) :=
            sep_assoc.symm

/-- Corresponds to `big_sepL_sep_zip_with` in Rocq Iris.
    Big sep over zip_with with extraction functions. -/
theorem sep_zip_with {B C : Type _}
    (f : A → B → C) (g1 : C → A) (g2 : C → B)
    {Φ : Nat → A → PROP} {Ψ : Nat → B → PROP} {l₁ : List A} {l₂ : List B}
    (hg1 : ∀ x y, g1 (f x y) = x)
    (hg2 : ∀ x y, g2 (f x y) = y)
    (hlen : l₁.length = l₂.length) :
    ([∗ list] i ↦ c ∈ List.zipWith f l₁ l₂, Φ i (g1 c) ∗ Ψ i (g2 c)) ⊣⊢
      ([∗ list] i ↦ x ∈ l₁, Φ i x) ∗ [∗ list] i ↦ y ∈ l₂, Ψ i y := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil =>
    cases l₂ with
    | nil =>
      simp only [List.zipWith_nil_left, bigSepL, bigOpL]
      exact emp_sep.symm
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zipWith_cons_cons, bigSepL, bigOpL, hg1, hg2]
      have ih' := ih (l₂ := ys) (Φ := fun n => Φ (n + 1)) (Ψ := fun n => Ψ (n + 1)) hlen
      calc (Φ 0 x ∗ Ψ 0 y) ∗ bigSepL (fun i c => iprop(Φ (i + 1) (g1 c) ∗ Ψ (i + 1) (g2 c))) (List.zipWith f xs ys)
          ⊣⊢ (Φ 0 x ∗ Ψ 0 y) ∗ (bigSepL (fun n => Φ (n + 1)) xs ∗ bigSepL (fun n => Ψ (n + 1)) ys) :=
            ⟨sep_mono_r ih'.1, sep_mono_r ih'.2⟩
        _ ⊣⊢ Φ 0 x ∗ (Ψ 0 y ∗ (bigSepL (fun n => Φ (n + 1)) xs ∗ bigSepL (fun n => Ψ (n + 1)) ys)) :=
            sep_assoc
        _ ⊣⊢ Φ 0 x ∗ ((Ψ 0 y ∗ bigSepL (fun n => Φ (n + 1)) xs) ∗ bigSepL (fun n => Ψ (n + 1)) ys) :=
            ⟨sep_mono_r sep_assoc.2, sep_mono_r sep_assoc.1⟩
        _ ⊣⊢ Φ 0 x ∗ ((bigSepL (fun n => Φ (n + 1)) xs ∗ Ψ 0 y) ∗ bigSepL (fun n => Ψ (n + 1)) ys) :=
            ⟨sep_mono_r (sep_mono_l sep_comm.1), sep_mono_r (sep_mono_l sep_comm.2)⟩
        _ ⊣⊢ Φ 0 x ∗ (bigSepL (fun n => Φ (n + 1)) xs ∗ (Ψ 0 y ∗ bigSepL (fun n => Ψ (n + 1)) ys)) :=
            ⟨sep_mono_r sep_assoc.1, sep_mono_r sep_assoc.2⟩
        _ ⊣⊢ (Φ 0 x ∗ bigSepL (fun n => Φ (n + 1)) xs) ∗ (Ψ 0 y ∗ bigSepL (fun n => Ψ (n + 1)) ys) :=
            sep_assoc.symm

/-- Corresponds to `big_sepL_zip_with` in Rocq Iris.
    Big sep over zip_with expressed in terms of conditional. -/
theorem zip_with {B C : Type _} (f : A → B → C) {Φ : Nat → C → PROP}
    {l₁ : List A} {l₂ : List B} :
    ([∗ list] k ↦ c ∈ List.zipWith f l₁ l₂, Φ k c) ⊣⊢
      [∗ list] k ↦ x ∈ l₁, match l₂[k]? with | some y => Φ k (f x y) | none => emp := by
  induction l₁ generalizing l₂ Φ with
  | nil =>
    simp only [List.zipWith_nil_left, bigSepL, bigOpL]
    exact .rfl
  | cons x xs ih =>
    cases l₂ with
    | nil =>
      simp only [List.zipWith_nil_right, List.getElem?_nil, bigSepL, bigOpL]
      -- Goal: emp ⊣⊢ emp ∗ bigSepL (fun _ _ => emp) xs
      calc (emp : PROP)
          ⊣⊢ emp ∗ emp := emp_sep.symm
        _ ⊣⊢ emp ∗ bigSepL (fun _ _ => (emp : PROP)) xs := ⟨sep_mono_r emp_l.2, sep_mono_r emp_l.1⟩
    | cons y ys =>
      simp only [List.zipWith_cons_cons, List.getElem?_cons_zero, List.getElem?_cons_succ,
                 bigSepL, bigOpL]
      have ih' := ih (l₂ := ys) (Φ := fun n => Φ (n + 1))
      exact ⟨sep_mono_r ih'.1, sep_mono_r ih'.2⟩

end BigSepL

end Iris.BI
