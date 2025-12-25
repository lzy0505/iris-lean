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

-- # Big Separating Conjunction over Lists

variable {PROP : Type _} [BI PROP] {A : Type _}

namespace BigSepL

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

/-- Corresponds to second `big_sepL_nil'` in Rocq Iris.
    An affine proposition entails the bigSepL over an empty list. -/
theorem nil'_affine {P : PROP} [Affine P] {Φ : Nat → A → PROP} :
    P ⊢ [∗ list] k ↦ x ∈ ([] : List A), Φ k x :=
  Affine.affine.trans nil.2

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

/-- Corresponds to `big_sepL_ne` in Rocq Iris. -/
theorem ne {Φ Ψ : Nat → A → PROP} {l : List A} {n : Nat}
    (h : ∀ k x, l[k]? = some x → Φ k x ≡{n}≡ Ψ k x) :
    ([∗ list] k ↦ x ∈ l, Φ k x) ≡{n}≡ [∗ list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr_ne h

/-- Corresponds to `big_sepL_mono'` in Rocq Iris. -/
theorem mono' {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Φ k x ⊢ Ψ k x) :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊢ [∗ list] k ↦ x ∈ l, Ψ k x :=
  mono (fun k x _ => h k x)

/-- Corresponds to `big_sepL_flip_mono'` in Rocq Iris. -/
theorem flip_mono' {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Ψ k x ⊢ Φ k x) :
    ([∗ list] k ↦ x ∈ l, Ψ k x) ⊢ [∗ list] k ↦ x ∈ l, Φ k x :=
  mono (fun k x _ => h k x)

/-- Corresponds to `big_sepL_id_mono'` in Rocq Iris. -/
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

/-- Corresponds to `big_sepL_persistent_id` in Rocq Iris. -/
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

/-- Corresponds to `big_sepL_affine_id` in Rocq Iris. -/
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

/-- Corresponds to `big_sepL_persistent` in Rocq Iris. -/
theorem persistent_cond {Φ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Persistent (Φ k x)) :
    Persistent ([∗ list] k ↦ x ∈ l, Φ k x) where
  persistent := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigSepL, bigOpL]
      exact persistently_emp_2
    | cons y ys ih =>
      simp only [bigSepL, bigOpL]
      have h0 : Persistent (Φ 0 y) := h 0 y rfl
      have hrest : ∀ k x, ys[k]? = some x → Persistent (Φ (k + 1) x) :=
        fun k x hget => h (k + 1) x hget
      have h1 : Φ 0 y ⊢ <pers> Φ 0 y := h0.persistent
      have hPers : Persistent (bigSepL (fun n => Φ (n + 1)) ys) := ⟨ih hrest⟩
      have h2 : bigSepL (fun n => Φ (n + 1)) ys ⊢ <pers> bigSepL (fun n => Φ (n + 1)) ys :=
        hPers.persistent
      exact (sep_mono h1 h2).trans persistently_sep_2

/-- Corresponds to `big_sepL_affine` in Rocq Iris. -/
theorem affine_cond {Φ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Affine (Φ k x)) :
    Affine ([∗ list] k ↦ x ∈ l, Φ k x) where
  affine := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigSepL, bigOpL]
      exact Entails.rfl
    | cons y ys ih =>
      simp only [bigSepL, bigOpL]
      have h0 : Affine (Φ 0 y) := h 0 y rfl
      have hrest : ∀ k x, ys[k]? = some x → Affine (Φ (k + 1) x) :=
        fun k x hget => h (k + 1) x hget
      have h1 : Φ 0 y ⊢ emp := h0.affine
      have hAff : Affine (bigSepL (fun n => Φ (n + 1)) ys) := ⟨ih hrest⟩
      have h2 : bigSepL (fun n => Φ (n + 1)) ys ⊢ emp := hAff.affine
      exact (sep_mono h1 h2).trans sep_emp.1

/-- Corresponds to `big_sepL_nil_timeless` in Rocq Iris. -/
instance nil_timeless [Timeless (emp : PROP)] {Φ : Nat → A → PROP} :
    Timeless ([∗ list] k ↦ x ∈ ([] : List A), Φ k x) where
  timeless := by
    simp only [bigSepL, bigOpL]
    exact Timeless.timeless

/-- Corresponds to `big_sepL_emp` in Rocq Iris. -/
theorem emp_l {l : List A} :
    ([∗ list] _x ∈ l, (emp : PROP)) ⊣⊢ emp :=
  equiv_iff.mp (BigOpL.unit_const l)

/-- Corresponds to `big_sepL_sep` in Rocq Iris. -/
theorem sep' {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗ list] k ↦ x ∈ l, Φ k x ∗ Ψ k x) ⊣⊢ ([∗ list] k ↦ x ∈ l, Φ k x) ∗ [∗ list] k ↦ x ∈ l, Ψ k x :=
  equiv_iff.mp (BigOpL.op_distr Φ Ψ l)

/-- Corresponds to `big_sepL_sep_2` in Rocq Iris. -/
theorem sep_2 {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗ list] k ↦ x ∈ l, Φ k x) ∗ ([∗ list] k ↦ x ∈ l, Ψ k x) ⊣⊢ [∗ list] k ↦ x ∈ l, Φ k x ∗ Ψ k x :=
  sep'.symm

/-- Corresponds to `big_sepL_and` in Rocq Iris (one direction only). -/
theorem and' {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗ list] k ↦ x ∈ l, Φ k x ∧ Ψ k x) ⊢
      ([∗ list] k ↦ x ∈ l, Φ k x) ∧ [∗ list] k ↦ x ∈ l, Ψ k x :=
  and_intro (mono fun _ _ _ => and_elim_l) (mono fun _ _ _ => and_elim_r)

/-- Corresponds to `big_sepL_wand` in Rocq Iris. -/
theorem wand {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊢ ([∗ list] k ↦ x ∈ l, Φ k x -∗ Ψ k x) -∗ [∗ list] k ↦ x ∈ l, Ψ k x :=
  wand_intro <| sep_2.1.trans (mono fun _ _ _ => wand_elim_r)

/-- Corresponds to `big_sepL_pure_1` in Rocq Iris. -/
theorem pure_1 {φ : Nat → A → Prop} {l : List A} :
    ([∗ list] k ↦ x ∈ l, ⌜φ k x⌝) ⊢ (⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) := by
  induction l generalizing φ with
  | nil => exact pure_intro fun _ _ h => nomatch h
  | cons y ys ih =>
    refine (sep_mono_r ih).trans <| sep_and.trans <| pure_and.1.trans <| pure_mono ?_
    intro ⟨hy, hys⟩ k x hget
    match k with
    | 0 => exact Option.some.inj hget ▸ hy
    | k + 1 => exact hys k x hget

/-- Corresponds to `big_sepL_affinely_pure_2` in Rocq Iris. -/
theorem affinely_pure_2 {φ : Nat → A → Prop} {l : List A} :
    iprop(<affine> ⌜∀ k x, l[k]? = some x → φ k x⌝) ⊢
      ([∗ list] k ↦ x ∈ l, <affine> ⌜φ k x⌝ : PROP) := by
  induction l generalizing φ with
  | nil => exact affinely_elim_emp
  | cons y ys ih =>
    refine (affinely_mono <| pure_mono fun h => ⟨h 0 y rfl, fun k x hget => h (k + 1) x hget⟩).trans <|
      (affinely_mono pure_and.2).trans <| affinely_and.1.trans <| persistent_and_sep_1.trans (sep_mono_r ih)

/-- Corresponds to `big_sepL_pure` in Rocq Iris. Requires `BIAffine`. -/
theorem pure' [BIAffine PROP] {φ : Nat → A → Prop} {l : List A} :
    ([∗ list] k ↦ x ∈ l, ⌜φ k x⌝) ⊣⊢ (⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) :=
  ⟨pure_1, (affine_affinely _).2.trans <| affinely_pure_2.trans (mono fun _ _ _ => affinely_elim)⟩

/-- Corresponds to `big_sepL_take_drop` in Rocq Iris. -/
theorem take_drop {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊣⊢
      ([∗ list] k ↦ x ∈ l.take n, Φ k x) ∗ [∗ list] k ↦ x ∈ l.drop n, Φ (n + k) x :=
  equiv_iff.mp (BigOpL.take_drop Φ l n)

/-- Corresponds to `big_sepL_fmap` in Rocq Iris. -/
theorem fmap {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    ([∗ list] k ↦ y ∈ l.map f, Φ k y) ≡ [∗ list] k ↦ x ∈ l, Φ k (f x) := by
  induction l generalizing Φ with
  | nil => simp only [List.map_nil]; exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, bigSepL, bigOpL]
    exact Monoid.op_proper OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

/-- Corresponds to `big_sepL_omap` in Rocq Iris. -/
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

/-- Corresponds to `big_sepL_bind` in Rocq Iris. -/
theorem bind {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    ([∗ list] y ∈ l.flatMap f, Φ y) ≡
      [∗ list] x ∈ l, [∗ list] y ∈ f x, Φ y := by
  induction l with
  | nil => exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, bigSepL, bigOpL]
    exact OFE.Equiv.trans (equiv_iff.mpr app) (Monoid.op_proper OFE.Equiv.rfl ih)

/-- Corresponds to `big_sepL_lookup_acc` in Rocq Iris. -/
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
      exact ⟨sep_mono_r (forall_intro fun y => wand_intro sep_comm.1),
             (sep_mono_r (forall_elim z)).trans wand_elim_r⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      simp only [bigSepL, bigOpL, List.set_cons_succ]
      have ih' := ih (i := j) (Φ := fun n => Φ (n + 1)) h
      have hset_eq : zs.set j x = zs := by
        apply List.ext_getElem?; intro k
        simp only [List.getElem?_set]
        by_cases hjk : j = k
        · subst hjk; simp only [(List.getElem?_eq_some_iff.mp h).1, ↓reduceIte, h]
        · simp only [hjk, ↓reduceIte]
      constructor
      · refine (sep_mono_r ih'.1).trans <| sep_assoc.2.trans <| (sep_mono_l sep_comm.1).trans <|
          sep_assoc.1.trans <| sep_mono_r <| forall_intro fun y => wand_intro ?_
        exact sep_assoc.1.trans <| (sep_mono_r <| (sep_mono_l (forall_elim y)).trans <|
          sep_comm.1.trans wand_elim_r)
      · conv => rhs; rw [← hset_eq]
        exact (sep_mono_r (forall_elim x)).trans wand_elim_r

/-- Corresponds to `big_sepL_lookup` in Rocq Iris. -/
theorem lookup {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    [TCOr (∀ k y, Affine (Φ k y)) (Absorbing (Φ i x))] →
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x
  | TCOr.l => by
    have hi : i < l.length := List.getElem?_eq_some_iff.mp h |>.1
    have hx : l[i] = x := List.getElem?_eq_some_iff.mp h |>.2
    have hlen : (l.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi)
    have hmiddle : l = l.take i ++ x :: l.drop (i + 1) := by
      have htake : l.take (i + 1) = l.take i ++ [x] := by rw [List.take_succ_eq_append_getElem hi, hx]
      calc l = l.take (i + 1) ++ l.drop (i + 1) := (List.take_append_drop (i + 1) l).symm
        _ = (l.take i ++ [x]) ++ l.drop (i + 1) := by rw [htake]
        _ = l.take i ++ ([x] ++ l.drop (i + 1)) := List.append_assoc ..
        _ = l.take i ++ (x :: l.drop (i + 1)) := rfl
    rw [hmiddle]
    refine app.1.trans <| sep_elim_r.trans ?_
    simp only [bigSepL, bigOpL, Nat.zero_add, hlen]
    exact sep_elim_l
  | TCOr.r => (lookup_acc h).1.trans sep_elim_l

/-- Corresponds to `big_sepL_insert_acc` in Rocq Iris. -/
theorem insert_acc {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x ∗ (∀ y, Φ i y -∗ [∗ list] k ↦ z ∈ l.set i y, Φ k z) :=
  (lookup_acc h).1

/-- Corresponds to `big_sepL_elem_of_acc` in Rocq Iris. -/
theorem elem_of_acc {Φ : A → PROP} {l : List A} {x : A}
    (h : x ∈ l) :
    ([∗ list] y ∈ l, Φ y) ⊢ Φ x ∗ (Φ x -∗ [∗ list] y ∈ l, Φ y) := by
  have ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
  have hlookup : l[i]? = some x := List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
  have hset : l.set i x = l := by
    apply List.ext_getElem?; intro k
    simp only [List.getElem?_set]
    by_cases hik : i = k
    · subst hik; simp only [hi, ↓reduceIte, hlookup]
    · simp only [hik, ↓reduceIte]
  conv => rhs; rw [← hset]
  exact (lookup_acc hlookup).1.trans (sep_mono_r (forall_elim x))

/-- Corresponds to `big_sepL_elem_of` in Rocq Iris. -/
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

/-- Corresponds to `big_sepL_delete` in Rocq Iris. -/
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
      have hmono : ∀ k y, (Φ (k + 1) y) ⊣⊢ (if k + 1 = 0 then emp else Φ (k + 1) y) := fun k _ => by
        simp only [Nat.add_one_ne_zero, ↓reduceIte]; exact .rfl
      exact ⟨sep_mono_r <| (mono fun k y _ => (hmono k y).1).trans emp_sep.2,
             sep_mono_r <| emp_sep.1.trans (mono fun k y _ => (hmono k y).2)⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      simp only [bigSepL, bigOpL]
      have ih' := ih (i := j) (Φ := fun n => Φ (n + 1)) h
      have hne0 : (0 : Nat) ≠ j + 1 := Nat.zero_ne_add_one j
      have hmono : ∀ k y, (if k = j then emp else Φ (k + 1) y) ⊣⊢
          (if k + 1 = j + 1 then emp else Φ (k + 1) y) := fun k _ => by
        simp only [Nat.add_right_cancel_iff]; exact .rfl
      refine (sep_congr_r ih').trans <| sep_left_comm.trans <| sep_congr_r ?_
      simp only [bigSepL, hne0, ↓reduceIte]
      exact sep_congr_r (equiv_iff.mp (proper fun k y _ => equiv_iff.mpr (hmono k y)))

/-- Corresponds to `big_sepL_delete'` in Rocq Iris. -/
theorem delete' [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊣⊢ Φ i x ∗ [∗ list] k ↦ y ∈ l, ⌜k ≠ i⌝ → Φ k y := by
  have hmono : ∀ k y, (if k = i then emp else Φ k y) ⊣⊢ iprop(⌜k ≠ i⌝ → Φ k y) := fun k y => by
    by_cases hki : k = i <;> simp only [hki, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true]
    · exact ⟨imp_intro' <| (pure_elim_l (R := Φ i y) fun hf => hf.elim), Affine.affine⟩
    · exact true_imp.symm
  exact (delete h).trans <| sep_congr_r <| equiv_iff.mp <| proper fun k y _ => equiv_iff.mpr (hmono k y)

/-- Corresponds to `big_sepL_intro` in Rocq Iris. -/
theorem intro {P : PROP} {Φ : Nat → A → PROP} {l : List A} [Intuitionistic P]
    (h : ∀ k x, l[k]? = some x → P ⊢ Φ k x) :
    P ⊢ [∗ list] k ↦ x ∈ l, Φ k x := by
  induction l generalizing Φ with
  | nil => exact Intuitionistic.intuitionistic.trans affinely_elim_emp
  | cons y ys ih =>
    exact Intuitionistic.intuitionistic.trans <| intuitionistically_sep_idem.2.trans <|
      sep_mono (intuitionistically_elim.trans (h 0 y rfl))
               (intuitionistically_elim.trans (ih fun k x hget => h (k + 1) x hget))

/-- Forward direction of `big_sepL_forall` in Rocq Iris. -/
theorem forall_1' {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP]
    [∀ k x, Persistent (Φ k x)] :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) := by
  refine forall_intro fun k => forall_intro fun x => imp_intro' <| pure_elim_l fun hget => ?_
  exact (lookup_acc hget).1.trans <| (sep_mono_l Persistent.persistent).trans <|
    sep_comm.1.trans <| persistently_absorb_r.trans persistently_elim

/-- Backward direction of `big_sepL_forall` in Rocq Iris. -/
theorem forall_2' {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP]
    [∀ k x, Persistent (Φ k x)] :
    (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x)) ⊢ [∗ list] k ↦ x ∈ l, Φ k x := by
  induction l generalizing Φ with
  | nil => exact Affine.affine
  | cons y ys ih =>
    have head_step : iprop(∀ k x, ⌜(y :: ys)[k]? = some x⌝ → Φ k x) ⊢ Φ 0 y :=
      (forall_elim 0).trans (forall_elim y) |>.trans <|
        (and_intro (pure_intro rfl) .rfl).trans imp_elim_r
    have tail_step : iprop(∀ k x, ⌜(y :: ys)[k]? = some x⌝ → Φ k x)
        ⊢ iprop(∀ k x, ⌜ys[k]? = some x⌝ → Φ (k + 1) x) :=
      forall_intro fun k => forall_intro fun z => (forall_elim (k + 1)).trans (forall_elim z)
    exact and_self.2.trans (and_mono_l head_step) |>.trans persistent_and_sep_1 |>.trans <|
      sep_mono_r (tail_step.trans ih)

/-- Corresponds to `big_sepL_forall` in Rocq Iris. -/
theorem forall' {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP]
    [∀ k x, Persistent (Φ k x)] :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊣⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) :=
  ⟨forall_1', forall_2'⟩

/-- Corresponds to `big_sepL_impl` in Rocq Iris. -/
theorem impl {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊢ □ (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x)) -∗ [∗ list] k ↦ x ∈ l, Ψ k x := by
  apply wand_intro
  have h1 : iprop(□ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x)) ⊢ bigSepL (fun k x => iprop(Φ k x -∗ Ψ k x)) l := by
    haveI : Intuitionistic iprop(□ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x)) :=
      intuitionistically_intuitionistic _
    exact intro fun k x hget => intuitionistically_elim.trans <|
      (forall_elim k).trans (forall_elim x) |>.trans <| (imp_mono_l (pure_mono fun _ => hget)).trans true_imp.1
  exact (sep_mono_r h1).trans <| sep_2.1.trans (mono fun _ _ _ => wand_elim_r)

/-- Corresponds to `big_sepL_lookup_acc_impl` in Rocq Iris. -/
theorem lookup_acc_impl {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    iprop([∗ list] k ↦ x ∈ l, Φ k x) ⊢
      Φ i x ∗ ∀ (Ψ: Nat → A → PROP), □ (∀ k y, iprop(⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y)) -∗
        Ψ i x -∗  ([∗ list] k ↦ x ∈ l, Ψ k x) := by
  refine (delete h).1.trans <| sep_mono_r <| forall_intro fun Ψ => wand_intro <| wand_intro ?_
  have hdel_psi := (delete (Φ := Ψ) h).2
  refine sep_comm.1.trans <| (sep_mono_r ?_).trans hdel_psi
  have htrans : iprop(bigSepL (fun k y => if k = i then emp else Φ k y) l ∗
        □ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y))
      ⊢ bigSepL (fun k y => if k = i then emp else Ψ k y) l := by
    have hwand : iprop(□ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y))
        ⊢ bigSepL (fun k y => if k = i then emp else iprop(Φ k y -∗ Ψ k y)) l := by
      haveI : Intuitionistic iprop(□ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y)) :=
        intuitionistically_intuitionistic _
      exact intro fun k y hget => by
        by_cases hki : k = i
        · subst hki; simp only [↓reduceIte]
          exact Intuitionistic.intuitionistic.trans (affinely_elim_emp (PROP := PROP))
        · simp only [hki, ↓reduceIte]
          exact intuitionistically_elim.trans <| (forall_elim k).trans (forall_elim y) |>.trans <|
            (imp_mono_l (pure_mono fun _ => hget)).trans true_imp.1 |>.trans <|
            (imp_mono_l (pure_mono fun _ => hki)).trans true_imp.1
    refine (sep_mono_r hwand).trans <| sep_2.1.trans <| mono fun k y _ => by
      by_cases hki : k = i
      · subst hki; simp only [↓reduceIte]; exact emp_sep.1
      · simp only [hki, ↓reduceIte]; exact wand_elim_r
  exact htrans

/-- Corresponds to `big_sepL_persistently` in Rocq Iris. Requires `BIAffine`. -/
theorem persistently {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] :
    iprop(<pers> [∗ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗ list] k ↦ x ∈ l, <pers> Φ k x := by
  induction l generalizing Φ with
  | nil => simp only [bigSepL, bigOpL]; exact persistently_emp' (PROP := PROP)
  | cons x xs ih =>
    simp only [bigSepL, bigOpL]
    exact persistently_sep.trans ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

/-- Corresponds to `big_sepL_later` in Rocq Iris. -/
theorem later [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} :
    iprop(▷ [∗ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗ list] k ↦ x ∈ l, ▷ Φ k x := by
  induction l generalizing Φ with
  | nil => simp only [bigSepL, bigOpL]; exact later_emp
  | cons x xs ih =>
    simp only [bigSepL, bigOpL]
    exact later_sep.trans ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

/-- Corresponds to `big_sepL_later_2` in Rocq Iris. -/
theorem later_2 {Φ : Nat → A → PROP} {l : List A} :
    ([∗ list] k ↦ x ∈ l, ▷ Φ k x) ⊢ iprop(▷ [∗ list] k ↦ x ∈ l, Φ k x) := by
  induction l generalizing Φ with
  | nil => simp only [bigSepL, bigOpL]; exact later_intro
  | cons x xs ih =>
    simp only [bigSepL, bigOpL]
    exact (sep_mono_r ih).trans later_sep.2

/-- Corresponds to `big_sepL_laterN` in Rocq Iris. -/
theorem laterN [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    iprop(▷^[n] [∗ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗ list] k ↦ x ∈ l, ▷^[n] Φ k x := by
  induction n with
  | zero => exact .rfl
  | succ m ih => exact (later_congr ih).trans later

/-- Corresponds to `big_sepL_laterN_2` in Rocq Iris. -/
theorem laterN_2 {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∗ list] k ↦ x ∈ l, ▷^[n] Φ k x) ⊢ iprop(▷^[n] [∗ list] k ↦ x ∈ l, Φ k x) := by
  induction n with
  | zero => exact .rfl
  | succ m ih => exact later_2.trans (later_mono ih)

/-- Corresponds to `big_sepL_Permutation` in Rocq Iris. -/
theorem perm {Φ : A → PROP} {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    ([∗ list] x ∈ l₁, Φ x) ⊣⊢ [∗ list] x ∈ l₂, Φ x :=
  equiv_iff.mp (BigOpL.perm Φ hp)

/-- Corresponds to `big_sepL_submseteq` in Rocq Iris. -/
theorem submseteq {Φ : A → PROP} [∀ x, Affine (Φ x)] {l₁ l₂ l : List A}
    (h : (l₁ ++ l).Perm l₂) :
    ([∗ list] x ∈ l₂, Φ x) ⊢ [∗ list] x ∈ l₁, Φ x := by
  have hperm := (perm (Φ := Φ) h).2
  have happ := (app (Φ := fun _ => Φ) (l₁ := l₁) (l₂ := l)).1
  exact hperm.trans (happ.trans sep_elim_l)

/-- Corresponds to `big_sepL_dup` in Rocq Iris. -/
theorem dup {P : PROP} [Affine P] {l : List A} :
     □ (P -∗ P ∗ P) ∗ P ⊢ ([∗ list] _x ∈ l, P) := by
  induction l with
  | nil => exact sep_elim_r.trans Affine.affine
  | cons _ _ ih =>
    refine (sep_mono_l intuitionistically_sep_idem.2).trans <| sep_assoc.1.trans <|
      (sep_mono_r <| (sep_mono_l intuitionistically_elim).trans wand_elim_l).trans <|
      sep_assoc.2.trans <| (sep_mono_l ih).trans sep_comm.1

/-- Corresponds to `big_sepL_replicate` in Rocq Iris. -/
theorem replicate {P : PROP} {l : List A} :
    ([∗ list] _x ∈ List.replicate l.length P, P) ⊣⊢ [∗ list] _x ∈ l, P := by
  induction l with
  | nil =>
    simp only [List.length_nil, List.replicate]
    exact .rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.replicate, bigSepL, BigOpL.cons]
    exact ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

/-- Corresponds to `big_sepL_zip_seq` in Rocq Iris. -/
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

/-- Corresponds to `big_sepL_sep_zip` in Rocq Iris. -/
theorem sep_zip {B : Type _} {Φ : Nat → A → PROP} {Ψ : Nat → B → PROP}
    {l₁ : List A} {l₂ : List B} (hlen : l₁.length = l₂.length) :
    ([∗ list] i ↦ xy ∈ l₁.zip l₂, Φ i xy.1 ∗ Ψ i xy.2) ⊣⊢
      ([∗ list] i ↦ x ∈ l₁, Φ i x) ∗ [∗ list] i ↦ y ∈ l₂, Ψ i y := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil =>
    cases l₂ with
    | nil => simp only [List.zip_nil_left, bigSepL, bigOpL]; exact emp_sep.symm
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zip_cons_cons, bigSepL, bigOpL]
      have ih' := ih (Φ := fun n => Φ (n + 1)) (Ψ := fun n => Ψ (n + 1)) hlen
      exact (sep_congr_r ih').trans sep_sep_sep_comm

/-- Corresponds to `big_sepL_sep_zip_with` in Rocq Iris. -/
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
    | nil => simp only [List.zipWith_nil_left, bigSepL, bigOpL]; exact emp_sep.symm
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zipWith_cons_cons, bigSepL, bigOpL, hg1, hg2]
      have ih' := ih (l₂ := ys) (Φ := fun n => Φ (n + 1)) (Ψ := fun n => Ψ (n + 1)) hlen
      exact (sep_congr_r ih').trans sep_sep_sep_comm

/-- Corresponds to `big_sepL_zip_with` in Rocq Iris. -/
theorem zip_with {B C : Type _} (f : A → B → C) {Φ : Nat → C → PROP}
    {l₁ : List A} {l₂ : List B} :
    ([∗ list] k ↦ c ∈ List.zipWith f l₁ l₂, Φ k c) ⊣⊢
      [∗ list] k ↦ x ∈ l₁, match l₂[k]? with | some y => Φ k (f x y) | none => emp := by
  induction l₁ generalizing l₂ Φ with
  | nil => simp only [List.zipWith_nil_left, bigSepL, bigOpL]; exact .rfl
  | cons x xs ih =>
    cases l₂ with
    | nil =>
      simp only [List.zipWith_nil_right, List.getElem?_nil, bigSepL, bigOpL]
      exact emp_sep.symm.trans (sep_congr_r (emp_l (l := xs)).symm)
    | cons y ys =>
      simp only [List.zipWith_cons_cons, List.getElem?_cons_zero, List.getElem?_cons_succ,
                 bigSepL, bigOpL]
      exact sep_congr_r (ih (l₂ := ys) (Φ := fun n => Φ (n + 1)))

/-! ## Missing Lemmas from Rocq Iris

The following lemmas from Rocq Iris are not ported:
- `big_sepL_timeless`, `big_sepL_timeless'`, `big_sepL_timeless_id`: Requires `sep_timeless` infrastructure
- `big_sepL_zip_seqZ`: Uses Z (integers); only Nat version available
-/

end BigSepL

end Iris.BI
