/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp
import Iris.BI.BigOpList
import Iris.Std.TC

namespace Iris.BI

open Iris.Algebra
open Iris.Std
open BIBase


/-! # Big Separating Conjunction over Two Lists

This file contains the definition and lemmas for `bigSepL2`, which is the big
separating conjunction over two lists simultaneously. If the lists have different
lengths, the result is `False`.

The main sections are:
- Core definition
- Basic structural lemmas (nil, cons, singleton, app)
- Monotonicity and congruence
- Typeclass closure (Persistent, Affine)
- Operator interaction (sep, emp)
- Alternative characterizations (via zip)
-/

variable {PROP : Type _} [BI PROP] {A B : Type _}

/-! ## Core Definition -/

/-- Big separating conjunction over two lists simultaneously.
    Returns `False` if lists have different lengths. -/
def bigSepL2 [BI PROP] {A B : Type _} (Φ : Nat → A → B → PROP)
    (l1 : List A) (l2 : List B) : PROP :=
  match l1, l2 with
  | [], [] => emp
  | x1 :: xs1, x2 :: xs2 => sep (Φ 0 x1 x2) (bigSepL2 (fun n => Φ (n + 1)) xs1 xs2)
  | _, _ => iprop(False)

/-! ## Notation -/

-- Notation for bigSepL2 without index
syntax "[∗ " "list" "] " ident ";" ident " ∈ " term ";" term ", " term : term
-- Notation for bigSepL2 with index
syntax "[∗ " "list" "] " ident " ↦ " ident ";" ident " ∈ " term ";" term ", " term : term

macro_rules
  | `([∗ list] $x1:ident;$x2:ident ∈ $l1;$l2, $P) =>
      `(bigSepL2 (fun _ $x1 $x2 => $P) $l1 $l2)
  | `([∗ list] $k:ident ↦ $x1:ident;$x2:ident ∈ $l1;$l2, $P) =>
      `(bigSepL2 (fun $k $x1 $x2 => $P) $l1 $l2)

-- iprop macro rules
macro_rules
  | `(iprop([∗ list] $x1:ident;$x2:ident ∈ $l1;$l2, $P)) =>
      `(bigSepL2 (fun _ $x1 $x2 => iprop($P)) $l1 $l2)
  | `(iprop([∗ list] $k:ident ↦ $x1:ident;$x2:ident ∈ $l1;$l2, $P)) =>
      `(bigSepL2 (fun $k $x1 $x2 => iprop($P)) $l1 $l2)

namespace BigSepL2

/-! ## Basic Structural Lemmas -/

/-- Corresponds to `big_sepL2_nil` in Rocq Iris. -/
@[simp]
theorem nil {Φ : Nat → A → B → PROP} :
    ([∗ list] k ↦ x;x' ∈ ([] : List A);([] : List B), Φ k x x') ⊣⊢ emp := by
  simp only [bigSepL2]
  exact .rfl

/-- Corresponds to `big_sepL2_nil'` in Rocq Iris. -/
theorem nil' {P : PROP} [Affine P] {Φ : Nat → A → B → PROP} :
    P ⊢ ([∗ list] k ↦ x;x' ∈ ([] : List A);([] : List B), Φ k x x') :=
  Affine.affine.trans nil.2

/-- Corresponds to `big_sepL2_nil_inv_l` in Rocq Iris. -/
theorem nil_inv_l {Φ : Nat → A → B → PROP} {l2 : List B} :
   ([∗ list] k ↦ x;x' ∈ [];l2, Φ k x x')  ⊢ ⌜l2 = []⌝ := by
  cases l2 with
  | nil => exact pure_intro rfl
  | cons y ys => simp only [bigSepL2]; exact false_elim

/-- Corresponds to `big_sepL2_nil_inv_r` in Rocq Iris. -/
theorem nil_inv_r {Φ : Nat → A → B → PROP} {l1 : List A} :
    ([∗ list] k ↦ x;x' ∈ l1;[], Φ k x x') ⊢ ⌜l1 = []⌝ := by
  cases l1 with
  | nil => exact pure_intro rfl
  | cons x xs => simp only [bigSepL2]; exact false_elim

/-- Corresponds to `big_sepL2_cons` in Rocq Iris. -/
theorem cons {Φ : Nat → A → B → PROP} {x1 : A} {x2 : B} {xs1 : List A} {xs2 : List B} :
    ([∗ list] k ↦ y1;y2 ∈ x1 :: xs1;x2 :: xs2, Φ k y1 y2) ⊣⊢
      Φ 0 x1 x2 ∗ [∗ list] k ↦ y1;y2 ∈ xs1;xs2, Φ (k + 1) y1 y2 := by
  simp only [bigSepL2]
  exact .rfl

/-- Corresponds to `big_sepL2_cons_inv_l` in Rocq Iris. -/
theorem cons_inv_l {Φ : Nat → A → B → PROP} {x1 : A} {xs1 : List A} {l2 : List B} :
    ([∗ list] k ↦ y1;y2 ∈ x1 :: xs1;l2, Φ k y1 y2) ⊣⊢
      ∃ x2 xs2, ⌜l2 = x2 :: xs2⌝ ∧ (Φ 0 x1 x2 ∗ [∗ list] k ↦ y1;y2 ∈ xs1;xs2, Φ (k + 1) y1 y2) := by
  cases l2 with
  | nil =>
    simp only [bigSepL2]
    constructor
    · exact false_elim
    · exact exists_elim fun _ => exists_elim fun _ =>
        and_elim_l.trans (pure_elim' (fun h => nomatch h))
  | cons y ys =>
    simp only [bigSepL2]
    constructor
    · exact (and_intro (pure_intro rfl) Entails.rfl).trans
        ((exists_intro (Ψ := fun xs2 => iprop(⌜y :: ys = y :: xs2⌝ ∧
          (Φ 0 x1 y ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2))) ys).trans
        (exists_intro (Ψ := fun x2 => iprop(∃ xs2, ⌜y :: ys = x2 :: xs2⌝ ∧
          (Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2))) y))
    · exact exists_elim fun x2 => exists_elim fun xs2 =>
        pure_elim_l fun h => by cases h; exact Entails.rfl

/-- Corresponds to `big_sepL2_cons_inv_r` in Rocq Iris. -/
theorem cons_inv_r {Φ : Nat → A → B → PROP} {l1 : List A} {x2 : B} {xs2 : List B} :
    ([∗ list] k ↦ y1;y2 ∈ l1;x2 :: xs2, Φ k y1 y2) ⊣⊢
      ∃ x1 xs1, ⌜l1 = x1 :: xs1⌝ ∧ (Φ 0 x1 x2 ∗ [∗ list] k ↦ y1;y2 ∈ xs1;xs2, Φ (k + 1) y1 y2) := by
  cases l1 with
  | nil =>
    simp only [bigSepL2]
    constructor
    · exact false_elim
    · exact exists_elim fun _ => exists_elim fun _ =>
        and_elim_l.trans (pure_elim' (fun h => nomatch h))
  | cons x xs =>
    simp only [bigSepL2]
    constructor
    · exact (and_intro (pure_intro rfl) Entails.rfl).trans
        ((exists_intro (Ψ := fun xs1 => iprop(⌜x :: xs = x :: xs1⌝ ∧
          (Φ 0 x x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2))) xs).trans
        (exists_intro (Ψ := fun x1 => iprop(∃ xs1, ⌜x :: xs = x1 :: xs1⌝ ∧
          (Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2))) x))
    · exact exists_elim fun x1 => exists_elim fun xs1 =>
        pure_elim_l fun h => by cases h; exact Entails.rfl

/-- Corresponds to `big_sepL2_singleton` in Rocq Iris. -/
theorem singleton {Φ : Nat → A → B → PROP} {x : A} {y : B} :
    ([∗ list] k ↦ x1;x2 ∈ [x];[y], Φ k x1 x2) ⊣⊢ Φ 0 x y := by
  simp only [bigSepL2]
  exact sep_emp

/-! ## Length Lemma -/

/-- Corresponds to `big_sepL2_length` in Rocq Iris. -/
theorem length {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ iprop(⌜l1.length = l2.length⌝) := by
  induction l1 generalizing l2 Φ with
  | nil =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact pure_intro rfl
    | cons => simp only [bigSepL2]; exact false_elim
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact false_elim
    | cons x2 xs2 =>
      simp only [bigSepL2, List.length_cons]
      have hlength := ih (Φ := fun n => Φ (n + 1)) (l2 := xs2)
      calc iprop(Φ 0 x1 x2 ∗ [∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2)
          ⊢ iprop(True ∗ ⌜xs1.length = xs2.length⌝) := sep_mono true_intro hlength
        _ ⊢ iprop(⌜xs1.length = xs2.length⌝) := ( (true_sep (PROP := PROP))).1
        _ ⊢ iprop(⌜xs1.length + 1 = xs2.length + 1⌝) := pure_mono (congrArg (· + 1))

/-! ## Monotonicity and Congruence -/

/-- Corresponds to `big_sepL2_mono` in Rocq Iris. -/
theorem mono {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ⊢ Ψ k x1 x2) :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ ([∗ list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  induction l1 generalizing l2 Φ Ψ with
  | nil =>
    cases l2 with
    | nil => exact Entails.rfl
    | cons => simp only [bigSepL2]; exact Entails.rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact Entails.rfl
    | cons x2 xs2 =>
      simp only [bigSepL2]
      apply sep_mono
      · exact h 0 x1 x2 rfl rfl
      · apply ih
        intro k y1 y2 hget1 hget2
        exact h (k + 1) y1 y2 hget1 hget2

/-- Corresponds to `big_sepL2_proper` in Rocq Iris. -/
theorem proper {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ⊣⊢ Ψ k x1 x2) :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢ ([∗ list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  constructor
  · apply mono; intro k x1 x2 h1 h2; exact ( (h k x1 x2 h1 h2)).1
  · apply mono; intro k x1 x2 h1 h2; exact ( (h k x1 x2 h1 h2)).2

/-- No direct Rocq equivalent; simplified version of `proper` that doesn't require lookup hypotheses.
    Useful when the predicate transformation is unconditional. -/
theorem congr {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, Φ k x1 x2 ⊣⊢ Ψ k x1 x2) :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢ ([∗ list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  apply proper
  intro k x1 x2 _ _
  exact h k x1 x2

/-- Corresponds to `big_sepL2_ne` in Rocq Iris. -/
theorem ne {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {n : Nat}
    (h : ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ≡{n}≡ Ψ k x1 x2) :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ≡{n}≡ ([∗ list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  induction l1 generalizing l2 Φ Ψ with
  | nil =>
    cases l2 with
    | nil => exact OFE.Dist.rfl
    | cons => simp only [bigSepL2]; exact OFE.Dist.rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact OFE.Dist.rfl
    | cons x2 xs2 =>
      simp only [bigSepL2]
      apply sep_ne.ne
      · exact h 0 x1 x2 rfl rfl
      · apply ih
        intro k y1 y2 hget1 hget2
        exact h (k + 1) y1 y2 hget1 hget2

/-- No direct Rocq equivalent; monotonicity without lookup condition. -/
theorem mono' {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, Φ k x1 x2 ⊢ Ψ k x1 x2) :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ ([∗ list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  mono (fun k x1 x2 _ _ => h k x1 x2)

/-- No direct Rocq equivalent; flip version of mono'. -/
theorem flip_mono' {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, Ψ k x1 x2 ⊢ Φ k x1 x2) :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) ⊢ ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) :=
  mono (fun k x1 x2 _ _ => h k x1 x2)

/-! ## Alternative Characterization via Zip -/

/-- Corresponds to `big_sepL2_alt` in Rocq Iris. -/
theorem alt {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) := by
  constructor
  · -- Forward direction: bigSepL2 → ⌜length⌝ ∧ bigSepL
    -- Following Coq: apply and_intro, prove length separately and bigSepL separately
    apply and_intro
    · -- Prove bigSepL2 ⊢ ⌜length l1 = length l2⌝
      exact length
    · -- Prove bigSepL2 ⊢ bigSepL (using induction)
      induction l1 generalizing l2 Φ with
      | nil =>
        cases l2 with
        | nil => simp only [bigSepL2, List.zip_nil_left, bigSepL, bigOpL]; exact Entails.rfl
        | cons => simp only [bigSepL2]; exact false_elim
      | cons x xs ih =>
        cases l2 with
        | nil => simp only [bigSepL2]; exact false_elim
        | cons y ys =>
          simp only [bigSepL2, List.zip_cons_cons, bigSepL, bigOpL]
          exact sep_mono_r (ih (Φ := fun n => Φ (n + 1)) (l2 := ys))
  · -- Backward direction: ⌜length⌝ ∧ bigSepL → bigSepL2
    -- Following Coq: use pure_elim_l to get length proof, then prove bigSepL → bigSepL2
    exact pure_elim_l fun hlen => by
      induction l1 generalizing l2 Φ with
      | nil =>
        cases l2 with
        | nil => simp only [bigSepL2, List.zip_nil_left, bigSepL, bigOpL]; exact Entails.rfl
        | cons => simp at hlen
      | cons x xs ih =>
        cases l2 with
        | nil => simp at hlen
        | cons y ys =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          simp only [bigSepL2, List.zip_cons_cons, bigSepL, bigOpL]
          exact sep_mono_r (ih (Φ := fun n => Φ (n + 1)) (l2 := ys) hlen)

/-! ## Typeclass Closure -/

/-- Corresponds to `big_sepL2_persistent'` in Rocq Iris. -/
instance persistent {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    [∀ k x1 x2, Persistent (Φ k x1 x2)] :
    Persistent ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) where
  persistent := by
    induction l1 generalizing l2 Φ with
    | nil =>
      cases l2 with
      | nil => simp only [bigSepL2]; exact persistently_emp_2
      | cons => simp only [bigSepL2]; exact false_elim.trans (persistently_mono false_elim)
    | cons x1 xs1 ih =>
      cases l2 with
      | nil => simp only [bigSepL2]; exact false_elim.trans (persistently_mono false_elim)
      | cons x2 xs2 =>
        simp only [bigSepL2]
        have h1 : Φ 0 x1 x2 ⊢ <pers> Φ 0 x1 x2 := Persistent.persistent
        have h2 : ([∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2) ⊢
            iprop(<pers> [∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2) := ih
        exact (sep_mono h1 h2).trans persistently_sep_2

/-- Corresponds to `big_sepL2_affine'` in Rocq Iris. -/
instance affine {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    [∀ k x1 x2, Affine (Φ k x1 x2)] :
    Affine ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) where
  affine := by
    induction l1 generalizing l2 Φ with
    | nil =>
      cases l2 with
      | nil => simp only [bigSepL2]; exact Entails.rfl
      | cons => simp only [bigSepL2]; exact false_elim
    | cons x1 xs1 ih =>
      cases l2 with
      | nil => simp only [bigSepL2]; exact false_elim
      | cons x2 xs2 =>
        simp only [bigSepL2]
        have h1 : Φ 0 x1 x2 ⊢ emp := Affine.affine
        have h2 : ([∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2) ⊢ emp := ih
        exact (sep_mono h1 h2).trans ( sep_emp).1

/-! ## Distribution over Sep -/

/-- Corresponds to `big_sepL2_sep` in Rocq Iris. -/
theorem sep' {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 ∗ Ψ k x1 x2) ⊣⊢
      ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ ([∗ list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  induction l1 generalizing l2 Φ Ψ with
  | nil =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact emp_sep.symm
    | cons => simp only [bigSepL2]; exact ⟨false_elim, sep_elim_l.trans false_elim⟩
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact ⟨false_elim, sep_elim_l.trans false_elim⟩
    | cons x2 xs2 =>
      simp only [bigSepL2]
      calc iprop((Φ 0 x1 x2 ∗ Ψ 0 x1 x2) ∗
              [∗ list] k ↦ y1;y2 ∈ xs1;xs2, Φ (k + 1) y1 y2 ∗ Ψ (k + 1) y1 y2)
          ⊣⊢ iprop((Φ 0 x1 x2 ∗ Ψ 0 x1 x2) ∗
              (([∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2) ∗
               ([∗ list] n ↦ y1;y2 ∈ xs1;xs2, Ψ (n + 1) y1 y2))) :=
            sep_congr .rfl ih
        _ ⊣⊢ iprop((Φ 0 x1 x2 ∗ [∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2) ∗
              (Ψ 0 x1 x2 ∗ [∗ list] n ↦ y1;y2 ∈ xs1;xs2, Ψ (n + 1) y1 y2)) := sep_sep_sep_comm

/-- Corresponds to `big_sepL2_sep_2` in Rocq Iris. -/
theorem sep_2 {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ ([∗ list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) ⊣⊢
      ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 ∗ Ψ k x1 x2) :=
  sep'.symm

/-! ## Distribution over And -/

/-- Corresponds to `big_sepL2_and` in Rocq Iris. -/
theorem and' {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 ∧ Ψ k x1 x2) ⊢
      ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∧ ([∗ list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  apply and_intro
  · exact mono fun k x1 x2 _ _ => and_elim_l
  · exact mono fun k x1 x2 _ _ => and_elim_r

/-! ## Pure Proposition Lemmas -/

/-- Corresponds to `big_sepL2_pure_1` in Rocq Iris. -/
theorem pure_1 {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, (⌜φ k x1 x2⌝ : PROP)) ⊢
      iprop(⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) := by
  -- Use alt to convert to bigSepL, then use Iris.BI.BigSepL.pure_1
  calc ([∗ list] k ↦ x1;x2 ∈ l1;l2, (⌜φ k x1 x2⌝ : PROP))
      ⊢ iprop(⌜l1.length = l2.length⌝ ∧
          bigSepL (fun k p => iprop(⌜φ k p.1 p.2⌝ : PROP)) (l1.zip l2) : PROP) := ( alt).1
    _ ⊢ iprop(⌜l1.length = l2.length⌝ ∧
          ⌜∀ k p, (l1.zip l2)[k]? = some p → φ k p.1 p.2⌝ : PROP) :=
        and_mono Entails.rfl Iris.BI.BigSepL.pure_1
    _ ⊢ iprop(⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) := by
        apply and_elim_r.trans
        apply pure_mono; intro hφ k x1 x2 h1 h2
        -- Convert between (l1.zip l2)[k]? and l1[k]?, l2[k]?
        have : (l1.zip l2)[k]? = some (x1, x2) := by
          simp only [List.getElem?_zip_eq_some]
          exact ⟨h1, h2⟩
        exact hφ k (x1, x2) this

/-- Corresponds to `big_sepL2_affinely_pure_2` in Rocq Iris. -/
theorem affinely_pure_2 {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    iprop(<affine> ⌜l1.length = l2.length ∧
      ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) ⊢
      ([∗ list] k ↦ x1;x2 ∈ l1;l2, (<affine> ⌜φ k x1 x2⌝ : PROP)) := by
  -- Split the affinely pure conjunction
  have split_affine : iprop(<affine> ⌜l1.length = l2.length ∧
      ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) ⊢
      iprop(<affine> ⌜l1.length = l2.length⌝ ∧
        <affine> ⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) := by
    calc iprop(<affine> ⌜l1.length = l2.length ∧
          ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP)
        ⊢ iprop(<affine> (⌜l1.length = l2.length⌝ ∧
          ⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝) : PROP) :=
          affinely_mono ( pure_and).2
      _ ⊢ iprop(<affine> ⌜l1.length = l2.length⌝ ∧
          <affine> ⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) :=
          ( affinely_and).1
  -- Convert via alt
  have step1 : iprop(<affine> ⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) ⊢
      iprop(<affine> ⌜∀ k p, (l1.zip l2)[k]? = some p → φ k p.1 p.2⌝ : PROP) := by
    apply affinely_mono
    apply pure_mono; intro hφ k p hp
    have ⟨h1, h2⟩ : l1[k]? = some p.1 ∧ l2[k]? = some p.2 := by
      simp only [List.getElem?_zip_eq_some] at hp
      exact hp
    exact hφ k p.1 p.2 h1 h2
  have step2 : iprop(<affine> ⌜∀ k p, (l1.zip l2)[k]? = some p → φ k p.1 p.2⌝ : PROP) ⊢
      bigSepL (fun k p => iprop(<affine> ⌜φ k p.1 p.2⌝ : PROP)) (l1.zip l2) :=
    Iris.BI.BigSepL.affinely_pure_2
  -- Use affinely_elim to extract the length proof for step3
  have step3 : iprop(<affine> ⌜l1.length = l2.length⌝ ∧
        bigSepL (fun k p => iprop(<affine> ⌜φ k p.1 p.2⌝ : PROP)) (l1.zip l2) : PROP) ⊢
      iprop(⌜l1.length = l2.length⌝ ∧
        bigSepL (fun k p => iprop(<affine> ⌜φ k p.1 p.2⌝ : PROP)) (l1.zip l2) : PROP) :=
    and_mono affinely_elim Entails.rfl
  have step4 : iprop(⌜l1.length = l2.length⌝ ∧
      bigSepL (fun k p => iprop(<affine> ⌜φ k p.1 p.2⌝ : PROP)) (l1.zip l2) : PROP) ⊢
      ([∗ list] k ↦ x1;x2 ∈ l1;l2, (<affine> ⌜φ k x1 x2⌝ : PROP)) :=
    ( (alt (Φ := fun k x1 x2 => iprop(<affine> ⌜φ k x1 x2⌝ : PROP))
      (l1 := l1) (l2 := l2)).symm).1
  -- Combine: split, then use step1 on RHS, step2 on result, combine with length
  calc iprop(<affine> ⌜l1.length = l2.length ∧
        ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP)
      ⊢ iprop(<affine> ⌜l1.length = l2.length⌝ ∧
          <affine> ⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) :=
        split_affine
    _ ⊢ iprop(<affine> ⌜l1.length = l2.length⌝ ∧
          bigSepL (fun k p => iprop(<affine> ⌜φ k p.1 p.2⌝ : PROP)) (l1.zip l2) : PROP) :=
        and_mono Entails.rfl (step1.trans step2)
    _ ⊢ iprop(⌜l1.length = l2.length⌝ ∧
          bigSepL (fun k p => iprop(<affine> ⌜φ k p.1 p.2⌝ : PROP)) (l1.zip l2) : PROP) :=
        step3
    _ ⊢ ([∗ list] k ↦ x1;x2 ∈ l1;l2, (<affine> ⌜φ k x1 x2⌝ : PROP)) :=
        step4

/-- Corresponds to `big_sepL2_pure` in Rocq Iris. -/
theorem pure [BIAffine PROP] {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, (⌜φ k x1 x2⌝ : PROP)) ⊣⊢
      iprop(⌜l1.length = l2.length ∧
        ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) := by
  constructor
  · -- Forward direction: combine length and pure_1 using pure_and
    have hlength := @length PROP _ A B (fun k x1 x2 => iprop(⌜φ k x1 x2⌝)) l1 l2
    have hpure1 := @pure_1 PROP _ A B φ l1 l2
    exact (and_intro hlength hpure1).trans ( pure_and).1
  · -- Backward direction
    calc iprop(⌜l1.length = l2.length ∧
          ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP)
        ⊢ iprop(<affine> ⌜l1.length = l2.length ∧
          ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) :=
          ( (affine_affinely (PROP := PROP) _)).2
      _ ⊢ ([∗ list] k ↦ x1;x2 ∈ l1;l2, (<affine> ⌜φ k x1 x2⌝ : PROP)) :=
          affinely_pure_2
      _ ⊢ ([∗ list] k ↦ x1;x2 ∈ l1;l2, (⌜φ k x1 x2⌝ : PROP)) := by
          apply mono; intro k x1 x2 _ _
          exact affinely_elim

/-! ## Unit/Emp Lemma -/

/-- When the predicate is constantly emp, bigSepL2 reduces to a length equality check. -/
theorem emp_l [BIAffine PROP] {l1 : List A} {l2 : List B} :
    ([∗ list] _k ↦ _x1;_x2 ∈ l1;l2, (emp : PROP)) ⊣⊢ iprop(⌜l1.length = l2.length⌝) := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil =>
      simp only [bigSepL2]
      exact (true_emp (PROP := PROP)).symm.trans (pure_true (PROP := PROP) rfl).symm
    | cons => simp only [bigSepL2]; exact ⟨false_elim, pure_elim' (fun h => nomatch h)⟩
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact ⟨false_elim, pure_elim' (fun h => nomatch h)⟩
    | cons x2 xs2 =>
      simp only [bigSepL2, List.length_cons]
      calc iprop(emp ∗ [∗ list] _k ↦ _y1;_y2 ∈ xs1;xs2, (emp : PROP))
          ⊣⊢ ([∗ list] _k ↦ _y1;_y2 ∈ xs1;xs2, (emp : PROP)) := emp_sep
        _ ⊣⊢ iprop(⌜xs1.length = xs2.length⌝) := ih
        _ ⊣⊢ iprop(⌜xs1.length + 1 = xs2.length + 1⌝) := ⟨pure_mono (congrArg (· + 1)),
            pure_mono Nat.succ.inj⟩

/-! ## App Lemma -/

/-- One-directional app lemma using wand. This does NOT require a length proof.
    Corresponds exactly to Rocq's `big_sepL2_app`. -/
theorem app' {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ⊢
      ([∗ list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) -∗
      ([∗ list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) := by
  apply wand_intro'
  -- Goal after wand_intro': bigSepL2 l1b l2b ∗ bigSepL2 l1a l2a ⊢ bigSepL2 (l1a ++ l1b) (l2a ++ l2b)
  induction l1a generalizing l2a Φ with
  | nil =>
    cases l2a with
    | nil =>
      simp only [bigSepL2, List.nil_append, List.length_nil, Nat.add_zero]
      exact sep_emp.1
    | cons =>
      simp only [bigSepL2, List.nil_append]
      exact sep_elim_r.trans (false_elim (P := [∗ list] k ↦ y1;y2 ∈ l1b;_, Φ k y1 y2))
  | cons x1 xs1 ih =>
    cases l2a with
    | nil =>
      simp only [bigSepL2, List.nil_append]
      exact sep_elim_r.trans (false_elim (P := [∗ list] k ↦ y1;y2 ∈ _;l2b, Φ k y1 y2))
    | cons x2 xs2 =>
      simp only [bigSepL2, List.cons_append, List.length_cons]
      -- ih : bigSepL2 (Φ (·+xs1.length+1)) l1b l2b ∗ bigSepL2 (Φ (·+1)) xs1 xs2
      --      ⊢ bigSepL2 (Φ (·+1)) (xs1 ++ l1b) (xs2 ++ l2b)
      have ihspec := ih (Φ := fun n => Φ (n + 1)) (l2a := xs2)
      have hcongr : ([∗ list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + (xs1.length + 1)) y1 y2) ⊣⊢
                   ([∗ list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + xs1.length + 1) y1 y2) :=
        congr fun n _ _ => by simp only [Nat.add_assoc]; exact BiEntails.rfl
      -- Goal: bigSepL2 (Φ (·+(xs1.length+1))) l1b l2b ∗ (Φ 0 x1 x2 ∗ bigSepL2 (Φ (·+1)) xs1 xs2)
      --       ⊢ Φ 0 x1 x2 ∗ bigSepL2 (Φ (·+1)) (xs1 ++ l1b) (xs2 ++ l2b)
      calc iprop(([∗ list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + (xs1.length + 1)) y1 y2) ∗
              (Φ 0 x1 x2 ∗ [∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2))
          ⊢ iprop(([∗ list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + xs1.length + 1) y1 y2) ∗
              (Φ 0 x1 x2 ∗ [∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2)) := sep_mono_l hcongr.1
        _ ⊢ iprop((Φ 0 x1 x2 ∗ [∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2) ∗
              [∗ list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + xs1.length + 1) y1 y2) := sep_symm
        _ ⊢ iprop(Φ 0 x1 x2 ∗ (([∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2) ∗
              [∗ list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + xs1.length + 1) y1 y2)) := sep_assoc.1
        _ ⊢ iprop(Φ 0 x1 x2 ∗ (([∗ list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + xs1.length + 1) y1 y2) ∗
              [∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2)) := sep_mono_r sep_symm
        _ ⊢ iprop(Φ 0 x1 x2 ∗ [∗ list] n ↦ y1;y2 ∈ xs1 ++ l1b;xs2 ++ l2b, Φ (n + 1) y1 y2) :=
            sep_mono_r ihspec

/-- Inverse direction of app: splitting an appended bigSepL2 requires one pair of lengths to match.
    Uses disjunctive condition like Rocq's `big_sepL2_app_inv`. -/
private theorem app_inv_core {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗ list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊢
      ([∗ list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
      ([∗ list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) := by
  induction l1a generalizing l2a Φ with
  | nil =>
    cases l2a with
    | nil =>
      simp only [bigSepL2, List.nil_append, List.length_nil, Nat.add_zero]
      exact emp_sep.2
    | cons y ys =>
      -- l2a = y :: ys, l1a = [], so length 0 ≠ length (y::ys) - contradiction via inl
      -- or use l1b.length = l2b.length via inr
      cases hlen with
      | inl h => exact absurd h (by simp only [List.length_nil, List.length_cons]; omega)
      | inr h =>
        -- LHS: bigSepL2 Φ l1b ((y :: ys) ++ l2b) which has mismatched lengths, hence False
        simp only [bigSepL2, List.nil_append]
        have hne : l1b.length ≠ (y :: ys ++ l2b).length := by
          simp only [List.length_cons, List.length_append]
          omega
        exact length.trans (pure_elim' fun heq => absurd heq hne)
  | cons x1 xs1 ih =>
    cases l2a with
    | nil =>
      cases hlen with
      | inl h => exact absurd h (by simp only [List.length_nil, List.length_cons]; omega)
      | inr h =>
        simp only [bigSepL2, List.nil_append]
        have hne : (x1 :: xs1 ++ l1b).length ≠ l2b.length := by
          simp only [List.length_cons, List.length_append]
          omega
        exact length.trans (pure_elim' fun heq => absurd heq hne)
    | cons x2 xs2 =>
      simp only [bigSepL2, List.cons_append, List.length_cons]
      have hlen' : xs1.length = xs2.length ∨ l1b.length = l2b.length := by
        cases hlen with
        | inl h => left; simp only [List.length_cons] at h; omega
        | inr h => right; exact h
      have ihspec := ih (Φ := fun n => Φ (n + 1)) (l2a := xs2) hlen'
      have hcongr : ([∗ list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + xs1.length + 1) y1 y2) ⊣⊢
                   ([∗ list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + (xs1.length + 1)) y1 y2) :=
        congr fun n _ _ => by simp only [Nat.add_assoc]; exact BiEntails.rfl
      calc iprop(Φ 0 x1 x2 ∗ [∗ list] n ↦ y1;y2 ∈ xs1 ++ l1b;xs2 ++ l2b, Φ (n + 1) y1 y2)
          ⊢ iprop(Φ 0 x1 x2 ∗ (([∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2) ∗
              [∗ list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + xs1.length + 1) y1 y2)) := sep_mono_r ihspec
        _ ⊢ iprop(Φ 0 x1 x2 ∗ (([∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2) ∗
              [∗ list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + (xs1.length + 1)) y1 y2)) :=
            sep_mono_r (sep_mono_r hcongr.2)
        _ ⊢ iprop((Φ 0 x1 x2 ∗ [∗ list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2) ∗
              [∗ list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + (xs1.length + 1)) y1 y2) := sep_assoc.2

/-- bi-entailment version when we know one pair of lengths match.
    Uses disjunctive condition like Rocq's `big_sepL2_app_same_length`. -/
theorem app {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗ list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊣⊢
      ([∗ list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
      ([∗ list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) :=
  ⟨app_inv_core hlen, sep_symm.trans (wand_elim' app')⟩

theorem app_inv {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗ list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊣⊢
      ([∗ list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
      ([∗ list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) := by
  exact app hlen

/-! ## Snoc Lemma -/

/-- Corresponds to `big_sepL2_snoc` in Rocq Iris. -/
theorem snoc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {x : A} {y : B} :
    ([∗ list] k ↦ x1;x2 ∈ l1 ++ [x];l2 ++ [y], Φ k x1 x2) ⊣⊢
      ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ Φ l1.length x y := by
  -- Use disjunctive app with Or.inr: [x].length = [y].length = 1
  have h := app (Φ := Φ) (l1a := l1) (l2a := l2) (l1b := [x]) (l2b := [y]) (Or.inr rfl)
  simp only [bigSepL2] at h
  -- h : bigSepL2 Φ (l1 ++ [x]) (l2 ++ [y]) ⊣⊢ bigSepL2 Φ l1 l2 ∗ (Φ (0 + l1.length) x y ∗ emp)
  calc ([∗ list] k ↦ y1;y2 ∈ l1 ++ [x];l2 ++ [y], Φ k y1 y2)
      ⊣⊢ iprop(([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ∗ (Φ (0 + l1.length) x y ∗ emp)) := h
    _ ⊣⊢ iprop(([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ∗ Φ (0 + l1.length) x y) := sep_congr .rfl sep_emp
    _ ⊣⊢ iprop(([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ∗ Φ l1.length x y) := by simp only [Nat.zero_add]; exact BiEntails.rfl

/-! ## Fmap Lemmas -/

/-- Corresponds to `big_sepL2_fmap_l` in Rocq Iris. -/
theorem fmap_l {C : Type _} (f : C → A) {Φ : Nat → A → B → PROP}
    {l1 : List C} {l2 : List B} :
    ([∗ list] k ↦ x;y ∈ l1.map f;l2, Φ k x y) ⊣⊢ ([∗ list] k ↦ x;y ∈ l1;l2, Φ k (f x) y) := by
  induction l1 generalizing l2 Φ with
  | nil =>
    cases l2 with
    | nil => simp only [List.map_nil, bigSepL2]; exact BiEntails.rfl
    | cons => simp only [List.map_nil, bigSepL2]; exact BiEntails.rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [List.map_cons, bigSepL2]; exact BiEntails.rfl
    | cons x2 xs2 =>
      simp only [List.map_cons, bigSepL2]
      exact sep_congr .rfl (ih (Φ := fun n => Φ (n + 1)))

/-- Corresponds to `big_sepL2_fmap_r` in Rocq Iris. -/
theorem fmap_r {C : Type _} (f : C → B) {Φ : Nat → A → B → PROP}
    {l1 : List A} {l2 : List C} :
    ([∗ list] k ↦ x;y ∈ l1;l2.map f, Φ k x y) ⊣⊢ ([∗ list] k ↦ x;y ∈ l1;l2, Φ k x (f y)) := by
  induction l1 generalizing l2 Φ with
  | nil =>
    cases l2 with
    | nil => simp only [List.map_nil, bigSepL2]; exact BiEntails.rfl
    | cons => simp only [List.map_cons, bigSepL2]; exact BiEntails.rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [List.map_nil, bigSepL2]; exact BiEntails.rfl
    | cons x2 xs2 =>
      simp only [List.map_cons, bigSepL2]
      exact sep_congr .rfl (ih (Φ := fun n => Φ (n + 1)))

/-- No direct Rocq equivalent; combined fmap_l and fmap_r. -/
theorem fmap {C D : Type _} (f : C → A) (g : D → B) {Φ : Nat → A → B → PROP}
    {l1 : List C} {l2 : List D} :
    ([∗ list] k ↦ x;y ∈ l1.map f;l2.map g, Φ k x y) ⊣⊢
      ([∗ list] k ↦ x;y ∈ l1;l2, Φ k (f x) (g y)) := by
  calc ([∗ list] k ↦ x;y ∈ l1.map f;l2.map g, Φ k x y)
      ⊣⊢ ([∗ list] k ↦ x;y ∈ l1;(l2.map g), Φ k (f x) y) := fmap_l f
    _ ⊣⊢ ([∗ list] k ↦ x;y ∈ l1;l2, Φ k (f x) (g y)) := fmap_r g

/-! ## Flip Lemma -/

/-- Corresponds to `big_sepL2_flip` in Rocq Iris. -/
theorem flip {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x;y ∈ l2;l1, Φ k y x) ⊣⊢ ([∗ list] k ↦ x;y ∈ l1;l2, Φ k x y) := by
  induction l1 generalizing l2 Φ with
  | nil =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact BiEntails.rfl
    | cons => simp only [bigSepL2]; exact BiEntails.rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact BiEntails.rfl
    | cons x2 xs2 =>
      simp only [bigSepL2]
      exact sep_congr .rfl (ih (Φ := fun n => Φ (n + 1)))

/-! ## Fst/Snd Lemma -/

/-- Corresponds to `big_sepL2_fst_snd` in Rocq Iris. -/
theorem fst_snd {Φ : Nat → A → B → PROP} {l : List (A × B)} :
    ([∗ list] k ↦ x;y ∈ l.map Prod.fst;l.map Prod.snd, Φ k x y) ⊣⊢
      bigSepL (fun k p => Φ k p.1 p.2) l := by
  -- Using big_sepL2_alt and properties of zip and fmap
  calc ([∗ list] k ↦ x;y ∈ l.map Prod.fst;l.map Prod.snd, Φ k x y)
      ⊣⊢ iprop(⌜(l.map Prod.fst).length = (l.map Prod.snd).length⌝ ∧
          bigSepL (fun k p => Φ k p.1 p.2) ((l.map Prod.fst).zip (l.map Prod.snd))) := alt
    _ ⊣⊢ iprop(⌜l.length = l.length⌝ ∧
          bigSepL (fun k p => Φ k p.1 p.2) ((l.map Prod.fst).zip (l.map Prod.snd))) := by
        simp only [List.length_map]; exact BiEntails.rfl
    _ ⊣⊢ iprop(⌜True⌝ ∧
          bigSepL (fun k p => Φ k p.1 p.2) ((l.map Prod.fst).zip (l.map Prod.snd))) := by
        apply and_congr
        · exact pure_true (PROP := PROP) rfl
        · exact BiEntails.rfl
    _ ⊣⊢ bigSepL (fun k p => Φ k p.1 p.2) ((l.map Prod.fst).zip (l.map Prod.snd)) :=
        true_and (PROP := PROP)
    _ ⊣⊢ bigSepL (fun k p => Φ k p.1 p.2) l := by
        -- Need to show that (l.map fst).zip (l.map snd) = l for pairs
        have : (l.map Prod.fst).zip (l.map Prod.snd) = l := by
          induction l with
          | nil => rfl
          | cons hd tl ih => simp only [List.map_cons, List.zip_cons_cons, ih, Prod.eta]
        rw [this]; exact .rfl

/-! ## App Inverse Lemmas -/

/-- When we have bigSepL2 of l1' ++ l1'' with some l2, we can split l2 to match. -/
theorem app_inv_l {Φ : Nat → A → B → PROP} {l1' l1'' : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1' ++ l1'';l2, Φ k x1 x2) ⊢
      iprop(∃ l2' l2'', ⌜l2 = l2' ++ l2''⌝ ∧
        (([∗ list] k ↦ x1;x2 ∈ l1';l2', Φ k x1 x2) ∗
         ([∗ list] k ↦ x1;x2 ∈ l1'';l2'', Φ (k + l1'.length) x1 x2))) := by
  -- Introduce existential witnesses: l2' = take (length l1') l2, l2'' = drop (length l1') l2
  -- Then prove the result by induction
  induction l1' generalizing l2 Φ with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    -- Need: bigSepL2 Φ l1'' l2 ⊢ ∃ l2' l2'', ⌜l2 = l2' ++ l2''⌝ ∧ (bigSepL2 Φ [] l2' ∗ bigSepL2 Φ l1'' l2'')
    -- Choose l2' = [], l2'' = l2
    -- Note: bigSepL2 Φ [] [] = emp
    calc bigSepL2 Φ l1'' l2
        ⊢ iprop(emp ∗ bigSepL2 Φ l1'' l2) := ( emp_sep.symm).1
      _ ⊢ iprop(bigSepL2 Φ [] [] ∗ bigSepL2 Φ l1'' l2) := sep_mono_l ( nil.symm).1
      _ ⊢ iprop(⌜l2 = [] ++ l2⌝ ∧ (bigSepL2 Φ [] [] ∗ bigSepL2 Φ l1'' l2)) :=
          and_intro (pure_intro rfl) Entails.rfl
      _ ⊢ iprop(∃ l2'', ⌜l2 = [] ++ l2''⌝ ∧ (bigSepL2 Φ [] [] ∗ bigSepL2 Φ l1'' l2'')) :=
          exists_intro' l2 Entails.rfl
      _ ⊢ iprop(∃ l2' l2'', ⌜l2 = l2' ++ l2''⌝ ∧ (bigSepL2 Φ [] l2' ∗ bigSepL2 Φ l1'' l2'')) :=
          exists_intro' ([] : List B) Entails.rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil =>
      simp only [bigSepL2, List.cons_append]
      exact false_elim
    | cons x2 xs2 =>
      simp only [bigSepL2, List.cons_append, List.length_cons]
      -- Apply ih to the tail
      calc iprop(Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) (xs1 ++ l1'') xs2)
          ⊢ iprop(Φ 0 x1 x2 ∗ (∃ l2' l2'', ⌜xs2 = l2' ++ l2''⌝ ∧
              (bigSepL2 (fun n => Φ (n + 1)) xs1 l2' ∗
               bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2''))) := sep_mono_r ih
        _ ⊢ iprop(∃ l2', Φ 0 x1 x2 ∗ (∃ l2'', ⌜xs2 = l2' ++ l2''⌝ ∧
              (bigSepL2 (fun n => Φ (n + 1)) xs1 l2' ∗
               bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2''))) :=
            ( sep_exists_l).1
        _ ⊢ iprop(∃ l2', ∃ l2'', Φ 0 x1 x2 ∗ (⌜xs2 = l2' ++ l2''⌝ ∧
              (bigSepL2 (fun n => Φ (n + 1)) xs1 l2' ∗
               bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2''))) :=
            exists_mono fun _ => ( sep_exists_l).1
        _ ⊢ iprop(∃ l2' l2'', ⌜x2 :: xs2 = l2' ++ l2''⌝ ∧
              (bigSepL2 Φ (x1 :: xs1) l2' ∗
               bigSepL2 (fun n => Φ (n + (xs1.length + 1))) l1'' l2'')) := by
            -- Need to shift the existential: l2' in ih becomes (x2 :: l2') in the result
            apply exists_elim; intro l2'_tail
            apply exists_elim; intro l2''
            -- Rearrange: P ∗ (⌜Q⌝ ∧ (R ∗ S)) → ⌜Q'⌝ ∧ ((P ∗ R) ∗ S')
            have step : iprop(Φ 0 x1 x2 ∗ (⌜xs2 = l2'_tail ++ l2''⌝ ∧
                    (bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail ∗
                     bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2'')))
                ⊢ iprop(⌜x2 :: xs2 = (x2 :: l2'_tail) ++ l2''⌝ ∧
                    (bigSepL2 Φ (x1 :: xs1) (x2 :: l2'_tail) ∗
                     bigSepL2 (fun n => Φ (n + (xs1.length + 1))) l1'' l2'')) :=
              calc iprop(Φ 0 x1 x2 ∗ (⌜xs2 = l2'_tail ++ l2''⌝ ∧
                      (bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail ∗
                       bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2'')))
                  ⊢ iprop(Φ 0 x1 x2 ∗ (<affine> ⌜xs2 = l2'_tail ++ l2''⌝ ∗
                      (bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail ∗
                       bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2''))) :=
                    sep_mono_r ( persistent_and_affinely_sep_l).1
                _ ⊢ iprop((Φ 0 x1 x2 ∗ <affine> ⌜xs2 = l2'_tail ++ l2''⌝) ∗
                      (bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail ∗
                       bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2'')) :=
                    ( sep_assoc.symm).1
                _ ⊢ iprop((<affine> ⌜xs2 = l2'_tail ++ l2''⌝ ∗ Φ 0 x1 x2) ∗
                      (bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail ∗
                       bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2'')) :=
                    sep_mono_l ( sep_comm).1
                _ ⊢ iprop(<affine> ⌜xs2 = l2'_tail ++ l2''⌝ ∗
                      (Φ 0 x1 x2 ∗ (bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail ∗
                       bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2''))) :=
                    ( sep_assoc).1
                _ ⊢ iprop(<affine> ⌜xs2 = l2'_tail ++ l2''⌝ ∗
                      ((Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail) ∗
                       bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2'')) :=
                    sep_mono_r ( sep_assoc.symm).1
                _ ⊢ iprop(⌜xs2 = l2'_tail ++ l2''⌝ ∧
                      ((Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail) ∗
                       bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2'')) :=
                    ( persistent_and_affinely_sep_l.symm).1
                _ ⊢ iprop(⌜x2 :: xs2 = (x2 :: l2'_tail) ++ l2''⌝ ∧
                      ((Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail) ∗
                       bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2'')) := by
                    apply and_mono _ Entails.rfl
                    apply pure_mono
                    intro h; simp only [List.cons_append, h]
                _ ⊢ iprop(⌜x2 :: xs2 = (x2 :: l2'_tail) ++ l2''⌝ ∧
                      ((Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail) ∗
                       bigSepL2 (fun n => Φ (n + (xs1.length + 1))) l1'' l2'')) := by
                    apply and_mono Entails.rfl
                    apply sep_mono_r
                    apply mono
                    intro k _ _ _ _
                    simp only [Nat.add_assoc]
                    exact Entails.rfl
                _ ⊢ iprop(⌜x2 :: xs2 = (x2 :: l2'_tail) ++ l2''⌝ ∧
                      (bigSepL2 Φ (x1 :: xs1) (x2 :: l2'_tail) ∗
                       bigSepL2 (fun n => Φ (n + (xs1.length + 1))) l1'' l2'')) := by
                    apply and_mono Entails.rfl
                    simp only [bigSepL2]
                    exact Entails.rfl
            -- Now introduce the existentials with the correct witnesses
            -- First introduce l2' = x2 :: l2'_tail, then l2'' = l2''
            exact step.trans ((exists_intro' l2'' Entails.rfl).trans
              (exists_intro (Ψ := fun l2' => iprop(∃ l2'', ⌜x2 :: xs2 = l2' ++ l2''⌝ ∧
                (bigSepL2 Φ (x1 :: xs1) l2' ∗
                 bigSepL2 (fun n => Φ (n + (xs1.length + 1))) l1'' l2''))) (x2 :: l2'_tail)))

/-- When we have bigSepL2 of l1 with l2' ++ l2'', we can split l1 to match. -/
theorem app_inv_r {Φ : Nat → A → B → PROP} {l1 : List A} {l2' l2'' : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2' ++ l2'', Φ k x1 x2) ⊢
      iprop(∃ l1' l1'', ⌜l1 = l1' ++ l1''⌝ ∧
        (([∗ list] k ↦ x1;x2 ∈ l1';l2', Φ k x1 x2) ∗
         ([∗ list] k ↦ x1;x2 ∈ l1'';l2'', Φ (k + l2'.length) x1 x2))) := by
  -- By symmetry with app_inv_l, using flip
  calc ([∗ list] k ↦ x1;x2 ∈ l1;l2' ++ l2'', Φ k x1 x2)
      ⊢ bigSepL2 (fun k x y => Φ k y x) (l2' ++ l2'') l1 := ( flip.symm).1
    _ ⊢ iprop(∃ l1' l1'', ⌜l1 = l1' ++ l1''⌝ ∧
          (bigSepL2 (fun k x y => Φ k y x) l2' l1' ∗
           bigSepL2 (fun n x y => Φ (n + l2'.length) y x) l2'' l1'')) := app_inv_l
    _ ⊢ iprop(∃ l1' l1'', ⌜l1 = l1' ++ l1''⌝ ∧
          (bigSepL2 Φ l1' l2' ∗ bigSepL2 (fun n => Φ (n + l2'.length)) l1'' l2'')) := by
        apply exists_mono; intro l1'
        apply exists_mono; intro l1''
        apply and_mono Entails.rfl
        apply sep_mono
        · exact ( flip).1
        · exact ( flip).1

/-! ## Lookup/Access Lemmas -/

/-- Lookup access pattern: extract element at index i and get a wand to restore. -/
theorem lookup_acc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
      iprop(Φ i x1 x2 ∗ (Φ i x1 x2 -∗ [∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)) := by
  -- Prove by induction
  induction l1 generalizing l2 i Φ with
  | nil => simp at h1
  | cons y1 ys1 ih =>
    cases l2 with
    | nil => simp at h2
    | cons y2 ys2 =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero] at h1 h2
        cases h1; cases h2
        simp only [bigSepL2]
        -- bigSepL2 gives us: Φ 0 y1 y2 ∗ rest
        -- We need: Φ 0 y1 y2 ∗ (Φ 0 y1 y2 -∗ Φ 0 y1 y2 ∗ rest)
        exact sep_mono_r (wand_intro (( sep_comm).1))
      | succ j =>
        simp only [List.getElem?_cons_succ] at h1 h2
        simp only [bigSepL2]
        -- Use ih on the tail
        have ihj := ih (l2 := ys2) (i := j) (Φ := fun n => Φ (n + 1)) h1 h2
        -- ihj : bigSepL2 (Φ (·+1)) ys1 ys2 ⊢ Φ (j+1) x1 x2 ∗ (Φ (j+1) x1 x2 -∗ bigSepL2 (Φ (·+1)) ys1 ys2)
        calc iprop(Φ 0 y1 y2 ∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2)
            ⊢ iprop(Φ 0 y1 y2 ∗ (Φ (j + 1) x1 x2 ∗
                (Φ (j + 1) x1 x2 -∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2))) := sep_mono_r ihj
          _ ⊢ iprop((Φ 0 y1 y2 ∗ Φ (j + 1) x1 x2) ∗
                (Φ (j + 1) x1 x2 -∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2)) :=
              ( sep_assoc.symm).1
          _ ⊢ iprop((Φ (j + 1) x1 x2 ∗ Φ 0 y1 y2) ∗
                (Φ (j + 1) x1 x2 -∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2)) :=
              sep_mono_l ( sep_comm).1
          _ ⊢ iprop(Φ (j + 1) x1 x2 ∗ (Φ 0 y1 y2 ∗
                (Φ (j + 1) x1 x2 -∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2))) :=
              ( sep_assoc).1
          _ ⊢ iprop(Φ (j + 1) x1 x2 ∗
                (Φ (j + 1) x1 x2 -∗ (Φ 0 y1 y2 ∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2))) := by
              apply sep_mono_r
              apply wand_intro
              calc iprop((Φ 0 y1 y2 ∗ (Φ (j + 1) x1 x2 -∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2)) ∗
                      Φ (j + 1) x1 x2)
                  ⊢ iprop(Φ 0 y1 y2 ∗ ((Φ (j + 1) x1 x2 -∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2) ∗
                      Φ (j + 1) x1 x2)) := ( sep_assoc).1
                _ ⊢ iprop(Φ 0 y1 y2 ∗ (Φ (j + 1) x1 x2 ∗
                      (Φ (j + 1) x1 x2 -∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2))) :=
                    sep_mono_r ( sep_comm).1
                _ ⊢ iprop(Φ 0 y1 y2 ∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2) :=
                    sep_mono_r wand_elim_r

/-- Corresponds to `big_sepL2_lookup` in Rocq Iris.
    Simplified lookup: works when either all Φ are affine or Φ i x1 x2 is absorbing.
    Uses `TCOr` to encode the typeclass disjunction. -/
theorem lookup {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    [TCOr (∀ j y1 y2, Affine (Φ j y1 y2)) (Absorbing (Φ i x1 x2))] →
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ Φ i x1 x2
  | TCOr.l => by
    -- All Φ j y1 y2 are affine. Use take_drop_middle decomposition.
    have hi1 : i < l1.length := List.getElem?_eq_some_iff.mp h1 |>.1
    have hi2 : i < l2.length := List.getElem?_eq_some_iff.mp h2 |>.1
    have hx1 : l1[i] = x1 := List.getElem?_eq_some_iff.mp h1 |>.2
    have hx2 : l2[i] = x2 := List.getElem?_eq_some_iff.mp h2 |>.2
    have hlen1 : (l1.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi1)
    have hlen2 : (l2.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi2)
    -- l1 = take i l1 ++ x1 :: drop (i + 1) l1  (take_drop_middle)
    have hmiddle1 : l1 = l1.take i ++ x1 :: l1.drop (i + 1) := by
      have htake : l1.take (i + 1) = l1.take i ++ [x1] := by
        rw [List.take_succ_eq_append_getElem hi1, hx1]
      calc l1 = l1.take (i + 1) ++ l1.drop (i + 1) := (List.take_append_drop (i + 1) l1).symm
        _ = (l1.take i ++ [x1]) ++ l1.drop (i + 1) := by rw [htake]
        _ = l1.take i ++ ([x1] ++ l1.drop (i + 1)) := List.append_assoc ..
        _ = l1.take i ++ (x1 :: l1.drop (i + 1)) := by rfl
    have hmiddle2 : l2 = l2.take i ++ x2 :: l2.drop (i + 1) := by
      have htake : l2.take (i + 1) = l2.take i ++ [x2] := by
        rw [List.take_succ_eq_append_getElem hi2, hx2]
      calc l2 = l2.take (i + 1) ++ l2.drop (i + 1) := (List.take_append_drop (i + 1) l2).symm
        _ = (l2.take i ++ [x2]) ++ l2.drop (i + 1) := by rw [htake]
        _ = l2.take i ++ ([x2] ++ l2.drop (i + 1)) := List.append_assoc ..
        _ = l2.take i ++ (x2 :: l2.drop (i + 1)) := by rfl
    -- Rewrite with hmiddle and apply app
    rw [hmiddle1, hmiddle2]
    have happ := @app PROP _ A B Φ (l1.take i) (x1 :: l1.drop (i + 1))
      (l2.take i) (x2 :: l2.drop (i + 1)) (Or.inl (hlen1.trans hlen2.symm))
    calc bigSepL2 Φ (l1.take i ++ x1 :: l1.drop (i + 1)) (l2.take i ++ x2 :: l2.drop (i + 1))
        ⊢ bigSepL2 Φ (l1.take i) (l2.take i) ∗
          bigSepL2 (fun k => Φ (k + (l1.take i).length)) (x1 :: l1.drop (i + 1)) (x2 :: l2.drop (i + 1)) :=
          happ.1
      _ ⊢ bigSepL2 Φ (l1.take i) (l2.take i) ∗
          (Φ i x1 x2 ∗ bigSepL2 (fun k => Φ (k + 1 + i)) (l1.drop (i + 1)) (l2.drop (i + 1))) := by
          simp only [hlen1, bigSepL2, Nat.zero_add]; exact Entails.rfl
      _ ⊢ Φ i x1 x2 := sep_elim_r.trans sep_elim_l
  | TCOr.r => (lookup_acc h1 h2).trans sep_elim_l

/-- Insert access pattern: extract element at index i and get a wand to restore with updated values.
    Corresponds to big_sepL2_insert_acc in Rocq. -/
theorem insert_acc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
      iprop(Φ i x1 x2 ∗ (∀ y1, ∀ y2, Φ i y1 y2 -∗
        [∗ list] k ↦ z1;z2 ∈ l1.set i y1;l2.set i y2, Φ k z1 z2)) := by
  -- Following the Coq proof structure:
  -- 1. Rewrite using alt to get ⌜length⌝ ∧ bigSepL over zip
  -- 2. Use pure_elim_l to extract the length condition
  -- 3. Apply BigSepL.insert_acc on the zipped list
  -- 4. Transform the result using the relationship between zip and set

  -- Step 1: Convert to alternative form using zip
  calc bigSepL2 Φ l1 l2
      ⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) :=
        ( alt).1
    _ ⊢ iprop(Φ i x1 x2 ∗ (∀ y1, ∀ y2, Φ i y1 y2 -∗ bigSepL2 Φ (l1.set i y1) (l2.set i y2))) := by
        -- Step 2: Eliminate the pure (length) condition
        apply pure_elim_l
        intro hlen

        -- Step 3: We need to lookup in the zipped list
        -- First establish that (l1.zip l2)[i]? = some (x1, x2)
        have hzip : (l1.zip l2)[i]? = some (x1, x2) := by
          simp only [List.getElem?_zip_eq_some]
          exact ⟨h1, h2⟩

        -- Step 4: Apply BigSepL.insert_acc on the zipped list
        calc iprop(bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2))
            ⊢ iprop(Φ i (x1, x2).1 (x1, x2).2 ∗
                (∀ p, Φ i p.1 p.2 -∗ bigSepL (fun k p => Φ k p.1 p.2) ((l1.zip l2).set i p))) := by
              exact BigSepL.insert_acc hzip
          _ ⊢ iprop(Φ i x1 x2 ∗ (∀ y1, ∀ y2, Φ i y1 y2 -∗
                bigSepL2 Φ (l1.set i y1) (l2.set i y2))) := by
              apply sep_mono_r
              -- Transform ∀ p to ∀ y1, ∀ y2
              apply forall_intro; intro y1
              apply forall_intro; intro y2

              -- Now eliminate the forall with (y1, y2)
              calc iprop(∀ p, Φ i p.1 p.2 -∗ bigSepL (fun k p => Φ k p.1 p.2) ((l1.zip l2).set i p))
                  ⊢ iprop(Φ i (y1, y2).1 (y1, y2).2 -∗ bigSepL (fun k p => Φ k p.1 p.2) ((l1.zip l2).set i (y1, y2))) :=
                    forall_elim (y1, y2)
                _ ⊢ iprop(Φ i y1 y2 -∗ bigSepL2 Φ (l1.set i y1) (l2.set i y2)) := by
                    apply wand_mono_r

                    -- Key insight: (l1.zip l2).set i (y1, y2) = (l1.set i y1).zip (l2.set i y2)
                    have hi1 : i < l1.length := List.getElem?_eq_some_iff.mp h1 |>.1
                    have hi2 : i < l2.length := List.getElem?_eq_some_iff.mp h2 |>.1
                    have hizip : i < (l1.zip l2).length := by
                      simp only [List.length_zip, Nat.min_def]; split <;> omega
                    have hi1' : i < (l1.set i y1).length := by simp only [List.length_set]; exact hi1
                    have hi2' : i < (l2.set i y2).length := by simp only [List.length_set]; exact hi2
                    have hzip_set : (l1.zip l2).set i (y1, y2) = (l1.set i y1).zip (l2.set i y2) := by
                      apply List.ext_getElem?
                      intro k
                      simp only [List.getElem?_set]
                      by_cases hik : i = k
                      · subst hik
                        simp only [hizip, ↓reduceIte]
                        symm
                        rw [List.getElem?_zip_eq_some]
                        simp only [List.getElem?_set, hi1, hi2, ↓reduceIte]
                        trivial
                      · -- Goal: (l1.zip l2)[k]? = ((l1.set i y1).zip (l2.set i y2))[k]?
                        -- Since i ≠ k, setting at i doesn't affect lookup at k
                        simp only [List.zip_eq_zipWith, List.getElem?_zipWith,
                          List.getElem?_set, hik, ↓reduceIte]

                    -- Now we can use the alternative form and length preservation
                    have hlen1 : (l1.set i y1).length = (l2.set i y2).length := by
                      simp only [List.length_set]
                      exact hlen

                    calc iprop(bigSepL (fun k p => Φ k p.1 p.2) ((l1.zip l2).set i (y1, y2)))
                        ⊢ iprop(bigSepL (fun k p => Φ k p.1 p.2) ((l1.set i y1).zip (l2.set i y2))) := by
                          rw [hzip_set]
                          exact Entails.rfl
                      _ ⊢ iprop(⌜(l1.set i y1).length = (l2.set i y2).length⌝ ∧
                          bigSepL (fun k p => Φ k p.1 p.2) ((l1.set i y1).zip (l2.set i y2))) := by
                          apply and_intro
                          · exact pure_intro hlen1
                          · exact Entails.rfl
                      _ ⊢ bigSepL2 Φ (l1.set i y1) (l2.set i y2) :=
                          ( alt).2

/-! ## Higher-Order Lemmas -/

/-- Introduction rule: from a persistent implication, construct bigSepL2.
    Corresponds to big_sepL2_intro in Rocq. -/
theorem intro {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    iprop(⌜l1.length = l2.length⌝ ∧
      □ (∀ k, ∀ x1, ∀ x2, iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2))) ⊢
      ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) := by
  apply pure_elim_l; intro hlen
  -- Use a helper that takes hlen as a Prop argument for the induction
  suffices h : iprop(□ (∀ k, ∀ x1, ∀ x2, iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2))) ⊢
      bigSepL2 Φ l1 l2 from h
  induction l1 generalizing l2 Φ with
  | nil =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact Affine.affine
    | cons => simp at hlen
  | cons y1 ys1 ih =>
    cases l2 with
    | nil => simp at hlen
    | cons y2 ys2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [bigSepL2]
      -- □ P ⊢ □ P ∗ □ P, then use one copy for the head and one for the tail
      have dup : iprop(□ (∀ k, ∀ x1, ∀ x2,
              iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2)))
          ⊢ iprop(□ (∀ k, ∀ x1, ∀ x2,
              iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2)) ∗
              □ (∀ k, ∀ x1, ∀ x2,
              iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))) :=
        ( intuitionistically_sep_idem.symm).1
      have head_step : iprop(□ (∀ k, ∀ x1, ∀ x2,
              iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2)))
          ⊢ Φ 0 y1 y2 := by
        -- Eliminate □, instantiate foralls, use the fact that l[0]? = some y
        calc iprop(□ (∀ k, ∀ x1, ∀ x2,
                iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2)))
            ⊢ iprop(∀ k, ∀ x1, ∀ x2,
                iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2)) :=
              intuitionistically_elim
          _ ⊢ iprop(⌜(y1 :: ys1)[0]? = some y1⌝ → ⌜(y2 :: ys2)[0]? = some y2⌝ → Φ 0 y1 y2) :=
              (forall_elim 0).trans ((forall_elim y1).trans (forall_elim y2))
          _ ⊢ Φ 0 y1 y2 := by
              -- Both premises are ⌜True⌝, so we can use pure_intro and modus ponens
              have h1 : (y1 :: ys1)[0]? = some y1 := rfl
              have h2 : (y2 :: ys2)[0]? = some y2 := rfl
              -- Start from (P1 → P2 → Φ), add ⌜P1⌝ on left, use imp_elim_r, then same for P2
              exact ((and_intro (pure_intro h1) Entails.rfl).trans imp_elim_r).trans
                ((and_intro (pure_intro h2) Entails.rfl).trans imp_elim_r)
      have tail_step : iprop(□ (∀ k, ∀ x1, ∀ x2,
              iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2)))
          ⊢ iprop(□ (∀ k, ∀ x1, ∀ x2,
              iprop(⌜ys1[k]? = some x1⌝ → ⌜ys2[k]? = some x2⌝ → Φ (k + 1) x1 x2))) := by
        apply intuitionistically_mono
        apply forall_intro; intro k
        apply forall_intro; intro z1
        apply forall_intro; intro z2
        calc iprop(∀ k, ∀ x1, ∀ x2,
                iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))
            ⊢ iprop(⌜(y1 :: ys1)[k + 1]? = some z1⌝ → ⌜(y2 :: ys2)[k + 1]? = some z2⌝ → Φ (k + 1) z1 z2) :=
              (forall_elim (k + 1)).trans ((forall_elim z1).trans (forall_elim z2))
          _ ⊢ iprop(⌜ys1[k]? = some z1⌝ → ⌜ys2[k]? = some z2⌝ → Φ (k + 1) z1 z2) := by
              simp only [List.getElem?_cons_succ]
              exact Entails.rfl
      exact dup.trans (sep_mono head_step (tail_step.trans (ih hlen)))

/-- Corresponds to `big_sepL2_wand` in Rocq Iris. -/
theorem wand {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢
      ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 -∗ Ψ k x1 x2) -∗
      ([∗ list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  apply wand_intro
  calc iprop(([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 -∗ Ψ k x1 x2)) l1 l2)
      ⊢ bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 ∗ (Φ k x1 x2 -∗ Ψ k x1 x2))) l1 l2 :=
        ( sep_2).1
    _ ⊢ bigSepL2 Ψ l1 l2 := mono fun _ _ _ _ _ => wand_elim_r

/-! ## impl: Specialized Introduction from Persistent Wand Implication -/

/-- Corresponds to `big_sepL2_impl` in Rocq Iris. -/
theorem impl {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢
      iprop(□ (∀ k, ∀ x1, ∀ x2,
        iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2))) -∗
      ([∗ list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  -- Following Rocq: use idemp on and, extract length, use intro to build wands, combine
  apply wand_intro
  -- We need to show: bigSepL2 Φ l1 l2 ∗ □(∀ k x1 x2, ⌜...⌝ → ⌜...⌝ → Φ -∗ Ψ) ⊢ bigSepL2 Ψ l1 l2
  -- Step 1: Get the length hypothesis from bigSepL2 Φ l1 l2
  -- Use P ⊢ P ∧ P (and_self), then extract length from one copy
  have hlen_extract : ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL2 Φ l1 l2) :=
    ( and_self).2.trans (and_mono_l length)
  calc iprop(([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ □ (∀ k, ∀ x1, ∀ x2,
          iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2)))
      ⊢ iprop((⌜l1.length = l2.length⌝ ∧ bigSepL2 Φ l1 l2) ∗
          □ (∀ k, ∀ x1, ∀ x2,
            iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2))) :=
        sep_mono_l hlen_extract
    _ ⊢ iprop(⌜l1.length = l2.length⌝ ∧ (bigSepL2 Φ l1 l2 ∗
          □ (∀ k, ∀ x1, ∀ x2,
            iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2)))) := by
        -- Need to show (P ∧ Q) ∗ R ⊢ P ∧ (Q ∗ R)
        -- Use P ∧ Q ⊣⊢ <affine> P ∗ Q (persistent_and_affinely_sep_l) then associativity
        calc iprop((⌜l1.length = l2.length⌝ ∧ bigSepL2 Φ l1 l2) ∗
                □ (∀ k, ∀ x1, ∀ x2,
                  iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2)))
            ⊢ iprop((<affine> ⌜l1.length = l2.length⌝ ∗ bigSepL2 Φ l1 l2) ∗
                □ (∀ k, ∀ x1, ∀ x2,
                  iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2))) :=
              sep_mono_l ( persistent_and_affinely_sep_l).1
          _ ⊢ iprop(<affine> ⌜l1.length = l2.length⌝ ∗ (bigSepL2 Φ l1 l2 ∗
                □ (∀ k, ∀ x1, ∀ x2,
                  iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2)))) :=
              ( sep_assoc).1
          _ ⊢ iprop(⌜l1.length = l2.length⌝ ∧ (bigSepL2 Φ l1 l2 ∗
                □ (∀ k, ∀ x1, ∀ x2,
                  iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2)))) :=
              ( persistent_and_affinely_sep_l.symm).1
    _ ⊢ bigSepL2 Ψ l1 l2 := by
        apply pure_elim_l; intro hlen
        -- Now we have: bigSepL2 Φ l1 l2 ∗ □(...) ⊢ bigSepL2 Ψ l1 l2
        -- Use intro to convert □(...) to bigSepL2 of wands
        have hwands : iprop(□ (∀ k, ∀ x1, ∀ x2,
                iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2)))
            ⊢ bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 -∗ Ψ k x1 x2)) l1 l2 :=
          (and_intro (pure_intro hlen) Entails.rfl).trans intro
        calc iprop(([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗
                □ (∀ k, ∀ x1, ∀ x2,
                  iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2)))
            ⊢ iprop(bigSepL2 Φ l1 l2 ∗
                bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 -∗ Ψ k x1 x2)) l1 l2) :=
              sep_mono_r hwands
          _ ⊢ bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 ∗ (Φ k x1 x2 -∗ Ψ k x1 x2))) l1 l2 :=
              ( sep_2).1
          _ ⊢ bigSepL2 Ψ l1 l2 := mono fun _ _ _ _ _ => wand_elim_r

/-- Corresponds to `big_sepL2_forall` in Rocq Iris. -/
theorem forall' [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (hPersistent : ∀ k x1 x2, Persistent (Φ k x1 x2)) :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧
        (∀ k, ∀ x1, ∀ x2, iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2))) := by
  constructor
  · -- Forward direction
    haveI : ∀ k x1 x2, Persistent (Φ k x1 x2) := hPersistent
    apply and_intro
    · exact length
    · apply forall_intro; intro k
      apply forall_intro; intro x1
      apply forall_intro; intro x2
      apply imp_intro'
      apply pure_elim_l; intro h1
      apply imp_intro'
      apply pure_elim_l; intro h2
      exact lookup h1 h2
  · -- Backward direction
    apply pure_elim_l; intro hlen
    -- Use persistent_and_sep_1 pattern: when Φ is persistent, we have P ∧ Q ⊢ P ∗ Q with affine
    -- Following Rocq: induction on l1, l2
    induction l1 generalizing l2 Φ hPersistent with
    | nil =>
      cases l2 with
      | nil => simp only [bigSepL2]; exact Affine.affine
      | cons => simp at hlen
    | cons y1 ys1 ih =>
      cases l2 with
      | nil => simp at hlen
      | cons y2 ys2 =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        simp only [bigSepL2]
        -- Need: ∀ k x1 x2, ⌜...⌝ → ⌜...⌝ → Φ k x1 x2 ⊢ Φ 0 y1 y2 ∗ bigSepL2 (Φ (·+1)) ys1 ys2
        -- When Φ is persistent, we can duplicate it
        haveI : ∀ k x1 x2, Persistent (Φ k x1 x2) := hPersistent
        have head_step : iprop(∀ k, ∀ x1, ∀ x2,
                iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))
            ⊢ Φ 0 y1 y2 := by
          calc iprop(∀ k, ∀ x1, ∀ x2,
                  iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))
              ⊢ iprop(⌜(y1 :: ys1)[0]? = some y1⌝ → ⌜(y2 :: ys2)[0]? = some y2⌝ → Φ 0 y1 y2) :=
                (forall_elim 0).trans ((forall_elim y1).trans (forall_elim y2))
            _ ⊢ Φ 0 y1 y2 := by
                have h1 : (y1 :: ys1)[0]? = some y1 := rfl
                have h2 : (y2 :: ys2)[0]? = some y2 := rfl
                exact ((and_intro (pure_intro h1) Entails.rfl).trans imp_elim_r).trans
                  ((and_intro (pure_intro h2) Entails.rfl).trans imp_elim_r)
        have tail_step : iprop(∀ k, ∀ x1, ∀ x2,
                iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))
            ⊢ iprop(∀ k, ∀ x1, ∀ x2,
                iprop(⌜ys1[k]? = some x1⌝ → ⌜ys2[k]? = some x2⌝ → Φ (k + 1) x1 x2)) := by
          apply forall_intro; intro k
          apply forall_intro; intro z1
          apply forall_intro; intro z2
          calc iprop(∀ k, ∀ x1, ∀ x2,
                  iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))
              ⊢ iprop(⌜(y1 :: ys1)[k + 1]? = some z1⌝ → ⌜(y2 :: ys2)[k + 1]? = some z2⌝ → Φ (k + 1) z1 z2) :=
                (forall_elim (k + 1)).trans ((forall_elim z1).trans (forall_elim z2))
            _ ⊢ iprop(⌜ys1[k]? = some z1⌝ → ⌜ys2[k]? = some z2⌝ → Φ (k + 1) z1 z2) := by
                simp only [List.getElem?_cons_succ]
                exact Entails.rfl
        -- Use persistent_and_sep_1: P ∧ Q ⊢ P ∗ Q when P is Persistent
        calc iprop(∀ k, ∀ x1, ∀ x2,
                iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))
            ⊢ iprop(Φ 0 y1 y2 ∧ (∀ k, ∀ x1, ∀ x2,
                iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))) :=
              ( and_self).2.trans (and_mono_l head_step)
          _ ⊢ iprop(Φ 0 y1 y2 ∗ (∀ k, ∀ x1, ∀ x2,
                iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))) :=
              persistent_and_sep_1
          _ ⊢ iprop(Φ 0 y1 y2 ∗ (∀ k, ∀ x1, ∀ x2,
                iprop(⌜ys1[k]? = some x1⌝ → ⌜ys2[k]? = some x2⌝ → Φ (k + 1) x1 x2))) :=
              sep_mono_r tail_step
          _ ⊢ iprop(Φ 0 y1 y2 ∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2) :=
              sep_mono_r (ih (fun k x1 x2 => hPersistent (k + 1) x1 x2) hlen)

/-! ## Modality Interaction -/

/-- Corresponds to `big_sepL2_persistently` in Rocq Iris. -/
theorem persistently [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    iprop(<pers> [∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      ([∗ list] k ↦ x1;x2 ∈ l1;l2, <pers> Φ k x1 x2) := by
  calc iprop(<pers> [∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2)
      ⊣⊢ iprop(<pers> (⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2))) :=
        persistently_congr alt
    _ ⊣⊢ iprop(<pers> ⌜l1.length = l2.length⌝ ∧ <pers> bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) :=
        persistently_and
    _ ⊣⊢ iprop(⌜l1.length = l2.length⌝ ∧ <pers> bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) :=
        and_congr persistently_pure BiEntails.rfl
    _ ⊣⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => iprop(<pers> Φ k p.1 p.2)) (l1.zip l2)) :=
        and_congr BiEntails.rfl BigSepL.persistently
    _ ⊣⊢ ([∗ list] k ↦ x1;x2 ∈ l1;l2, <pers> Φ k x1 x2) :=
        (alt (Φ := fun k x1 x2 => iprop(<pers> Φ k x1 x2))).symm

/-- Corresponds to `big_sepL2_later_2` in Rocq Iris. -/
theorem later_2 {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, ▷ Φ k x1 x2) ⊢
      iprop(▷ [∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) := by
  calc ([∗ list] k ↦ x1;x2 ∈ l1;l2, ▷ Φ k x1 x2)
      ⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => iprop(▷ Φ k p.1 p.2)) (l1.zip l2)) :=
        ( (alt (Φ := fun k x1 x2 => iprop(▷ Φ k x1 x2)))).1
    _ ⊢ iprop(⌜l1.length = l2.length⌝ ∧ ▷ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) :=
        and_mono Entails.rfl BigSepL.later_2
    _ ⊢ iprop(▷ ⌜l1.length = l2.length⌝ ∧ ▷ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) := by
        apply and_mono _ Entails.rfl
        exact later_intro
    _ ⊢ iprop(▷ (⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2))) := by
        exact ( later_and).2
    _ ⊢ iprop(▷ [∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) := by
        apply later_mono
        exact ( alt).2

/-- Corresponds to `big_sepL2_laterN_2` in Rocq Iris. -/
theorem laterN_2 {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {n : Nat} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, ▷^[n] Φ k x1 x2) ⊢
      iprop(▷^[n] [∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) := by
  induction n with
  | zero => exact Entails.rfl
  | succ m ih =>
    calc ([∗ list] k ↦ x1;x2 ∈ l1;l2, ▷ ▷^[m] Φ k x1 x2)
        ⊢ iprop(▷ [∗ list] k ↦ x1;x2 ∈ l1;l2, ▷^[m] Φ k x1 x2) := later_2
      _ ⊢ iprop(▷ ▷^[m] [∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) := later_mono ih

/- Corresponds to `big_sepL2_later_1` in Rocq Iris.
    Later modality through bigSepL2 (other direction, requires BIAffine and equal lengths).

  TODO: Add except-0 infrastructure (timeless_pure, except0_and, except0_intro)
theorem later_1 [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}:
     iprop(▷ bigSepL2 Φ l1 l2) ⊢ ◇ bigSepL2 (fun k x1 x2 => iprop(▷ Φ k x1 x2)) l1 l2 := by sorry
-/

/- Corresponds to `big_sepL2_later` in Rocq Iris.
    Later distributes over bigSepL2 (equivalence requires BIAffine for emp case).

    TODO: Add except-0 infrastructure
theorem later [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}:
    iprop(▷ bigSepL2 Φ l1 l2) ⊣⊢ ◇ bigSepL2 (fun k x1 x2 => iprop(▷ Φ k x1 x2)) l1 l2 :=
  ⟨later_1, later_2⟩
-/

/- LaterN modality through bigSepL2 (other direction, requires BIAffine).

    TODO: Add except-0 infrastructure
theorem laterN_1 [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {n : Nat}:
    iprop(▷^[n] bigSepL2 Φ l1 l2) ⊢ ◇ bigSepL2 (fun k x1 x2 => iprop(▷^[n] Φ k x1 x2)) l1 l2 := by sorry sorry
-/

/- Corresponds to `big_sepL2_laterN` in Rocq Iris.
    LaterN distributes over bigSepL2 (equivalence requires BIAffine).

    TODO: Add except-0 infrastructure
theorem laterN [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {n : Nat}:
    iprop(▷^[n] bigSepL2 Φ l1 l2) ⊣⊢ bigSepL2 (fun k x1 x2 => iprop(▷^[n] Φ k x1 x2)) l1 l2 :=
  ⟨laterN_1, laterN_2⟩
 -/

/-! ## Interaction with BigSepL -/

/-- Corresponds to `big_sepL2_sepL` in Rocq Iris. -/
theorem sepL {Φ1 : Nat → A → PROP} {Φ2 : Nat → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ1 k x1 ∗ Φ2 k x2) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ (bigSepL Φ1 l1 ∗ bigSepL Φ2 l2)) := by
  calc ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ1 k x1 ∗ Φ2 k x2)
      ⊣⊢ iprop(⌜l1.length = l2.length⌝ ∧
          bigSepL (fun k p => iprop(Φ1 k p.1 ∗ Φ2 k p.2)) (l1.zip l2)) := alt
    _ ⊣⊢ iprop(⌜l1.length = l2.length⌝ ∧ (bigSepL Φ1 l1 ∗ bigSepL Φ2 l2)) := by
        have h : ∀ hlen : l1.length = l2.length,
            bigSepL (fun k p => iprop(Φ1 k p.1 ∗ Φ2 k p.2)) (l1.zip l2) ⊣⊢
              iprop(bigSepL Φ1 l1 ∗ bigSepL Φ2 l2) :=
          fun hlen => BigSepL.sep_zip hlen
        constructor
        · apply pure_elim_l; intro hlen
          exact and_intro (pure_intro hlen) ((h hlen).1)
        · apply pure_elim_l; intro hlen
          exact and_intro (pure_intro hlen) ((h hlen).2)

/-- Corresponds to `big_sepL2_sepL_2` in Rocq Iris. -/
theorem sepL_2 {Φ1 : Nat → A → PROP} {Φ2 : Nat → B → PROP} {l1 : List A} {l2 : List B} :
    iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ1 l1) ⊢ bigSepL Φ2 l2 -∗
      ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ1 k x1 ∗ Φ2 k x2) := by
  apply wand_intro
  -- Goal: (⌜...⌝ ∧ bigSepL Φ1 l1) ∗ bigSepL Φ2 l2 ⊢ bigSepL2 ...
  -- First extract the pure to the left
  have rearrange : iprop((⌜l1.length = l2.length⌝ ∧ bigSepL Φ1 l1) ∗ bigSepL Φ2 l2) ⊢
      iprop(⌜l1.length = l2.length⌝ ∧ (bigSepL Φ1 l1 ∗ bigSepL Φ2 l2)) := by
    calc iprop((⌜l1.length = l2.length⌝ ∧ bigSepL Φ1 l1) ∗ bigSepL Φ2 l2)
        ⊢ iprop((<affine> ⌜l1.length = l2.length⌝ ∗ bigSepL Φ1 l1) ∗ bigSepL Φ2 l2) :=
          sep_mono_l ( persistent_and_affinely_sep_l).1
      _ ⊢ iprop(<affine> ⌜l1.length = l2.length⌝ ∗ (bigSepL Φ1 l1 ∗ bigSepL Φ2 l2)) :=
          ( sep_assoc).1
      _ ⊢ iprop(⌜l1.length = l2.length⌝ ∧ (bigSepL Φ1 l1 ∗ bigSepL Φ2 l2)) :=
          ( persistent_and_affinely_sep_l.symm).1
  exact rearrange.trans sepL.2

/-! ## Reverse Lemmas -/

/-- Corresponds to `big_sepL2_reverse_2` in Rocq Iris. -/
theorem reverse_2 {Φ : A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] _k ↦ x1;x2 ∈ l1;l2, Φ x1 x2) ⊢
      ([∗ list] _k ↦ x1;x2 ∈ l1.reverse;l2.reverse, Φ x1 x2) := by
  -- Extract length from bigSepL2 and use it in the induction
  have h : ∀ hlen : l1.length = l2.length,
      ([∗ list] _k ↦ y1;y2 ∈ l1;l2, Φ y1 y2) ⊢
        ([∗ list] _k ↦ y1;y2 ∈ l1.reverse;l2.reverse, Φ y1 y2) := by
    intro hlen
    induction l1 generalizing l2 with
    | nil =>
      cases l2 with
      | nil => simp only [List.reverse_nil]; exact Entails.rfl
      | cons => simp at hlen
    | cons x1 xs1 ih =>
      cases l2 with
      | nil => simp at hlen
      | cons x2 xs2 =>
        simp only [List.length_cons] at hlen
        have xs_len : xs1.length = xs2.length := Nat.succ.inj hlen
        simp only [bigSepL2, List.reverse_cons]
        -- Have: Φ x1 x2 ∗ bigSepL2 Φ xs1 xs2
        -- Want: bigSepL2 Φ (xs1.reverse ++ [x1]) (xs2.reverse ++ [x2])
        calc iprop(Φ x1 x2 ∗ [∗ list] _n ↦ y1;y2 ∈ xs1;xs2, Φ y1 y2)
            ⊢ iprop(([∗ list] _n ↦ y1;y2 ∈ xs1;xs2, Φ y1 y2) ∗ Φ x1 x2) :=
              ( sep_comm).1
          _ ⊢ iprop(([∗ list] _n ↦ y1;y2 ∈ xs1.reverse;xs2.reverse, Φ y1 y2) ∗ Φ x1 x2) :=
              sep_mono_l (ih xs_len)
          _ ⊢ iprop(([∗ list] _n ↦ y1;y2 ∈ xs1.reverse;xs2.reverse, Φ y1 y2) ∗
                     [∗ list] _n ↦ y1;y2 ∈ [x1];[x2], Φ y1 y2) := by
              apply sep_mono_r
              simp only [bigSepL2]
              exact ( sep_emp).2
          _ ⊢ ([∗ list] _n ↦ y1;y2 ∈ xs1.reverse ++ [x1];xs2.reverse ++ [x2], Φ y1 y2) := by
              -- Use snoc (no length argument needed now!)
              have h := snoc (Φ := fun _ => Φ) (l1 := xs1.reverse) (l2 := xs2.reverse)
                             (x := x1) (y := x2)
              calc iprop(([∗ list] _n ↦ y1;y2 ∈ xs1.reverse;xs2.reverse, Φ y1 y2) ∗
                        [∗ list] _n ↦ y1;y2 ∈ [x1];[x2], Φ y1 y2)
                  ⊢ iprop(([∗ list] _n ↦ y1;y2 ∈ xs1.reverse;xs2.reverse, Φ y1 y2) ∗ Φ x1 x2) := by
                    apply sep_mono_r
                    simp only [bigSepL2]
                    exact ( sep_emp).1
                _ ⊢ iprop(([∗ list] _n ↦ y1;y2 ∈ xs1.reverse;xs2.reverse, Φ y1 y2) ∗
                        (fun _ => Φ) xs1.reverse.length x1 x2) :=
                    Entails.rfl
                _ ⊢ ([∗ list] _n ↦ y1;y2 ∈ xs1.reverse ++ [x1];xs2.reverse ++ [x2], Φ y1 y2) :=
                    ( h).2
  -- Now use pure_elim to derive the result
  calc ([∗ list] _k ↦ y1;y2 ∈ l1;l2, Φ y1 y2)
      ⊢ iprop(⌜l1.length = l2.length⌝ ∧ [∗ list] _k ↦ y1;y2 ∈ l1;l2, Φ y1 y2) :=
        ( and_self).2.trans (and_mono_l length)
    _ ⊢ ([∗ list] _k ↦ y1;y2 ∈ l1.reverse;l2.reverse, Φ y1 y2) := by
        apply pure_elim_l; intro hlen
        exact h hlen

/-- Corresponds to `big_sepL2_reverse` in Rocq Iris. -/
theorem reverse {Φ : A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] _k ↦ x1;x2 ∈ l1.reverse;l2.reverse, Φ x1 x2) ⊣⊢
      ([∗ list] _k ↦ x1;x2 ∈ l1;l2, Φ x1 x2) := by
  constructor
  · -- reverse.reverse = id
    have h1 := reverse_2 (Φ := Φ) (l1 := l1.reverse) (l2 := l2.reverse)
    simp only [List.reverse_reverse] at h1
    exact h1
  · exact reverse_2

/-! ## Replicate Lemmas -/

/-- Corresponds to `big_sepL2_replicate_l` in Rocq Iris. -/
theorem replicate_l {Φ : Nat → A → B → PROP} {l : List B} {x : A} :
    ([∗ list] k ↦ x1;x2 ∈ List.replicate l.length x;l, Φ k x1 x2) ⊣⊢
      bigSepL (fun k x2 => Φ k x x2) l := by
  induction l generalizing Φ with
  | nil =>
    simp only [List.length_nil, List.replicate_zero, bigSepL2, bigSepL, bigOpL]
    exact BiEntails.rfl
  | cons y ys ih =>
    simp only [List.length_cons, List.replicate_succ, bigSepL2, bigSepL, bigOpL]
    exact sep_congr .rfl (ih (Φ := fun n => Φ (n + 1)))

/-- Corresponds to `big_sepL2_replicate_r` in Rocq Iris. -/
theorem replicate_r {Φ : Nat → A → B → PROP} {l : List A} {x : B} :
    ([∗ list] k ↦ x1;x2 ∈ l;List.replicate l.length x, Φ k x1 x2) ⊣⊢
      bigSepL (fun k x1 => Φ k x1 x) l := by
  induction l generalizing Φ with
  | nil =>
    simp only [List.length_nil, List.replicate_zero, bigSepL2, bigSepL, bigOpL]
    exact BiEntails.rfl
  | cons y ys ih =>
    simp only [List.length_cons, List.replicate_succ, bigSepL2, bigSepL, bigOpL]
    exact sep_congr .rfl (ih (Φ := fun n => Φ (n + 1)))

/-! ## App Same Length -/

/-- Corresponds to `big_sepL2_app_same_length` in Rocq Iris. -/
theorem app_same_length {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗ list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊣⊢
      iprop(([∗ list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
            ([∗ list] k ↦ x1;x2 ∈ l1b;l2b, Φ (l1a.length + k) x1 x2)) := by
  have h := app (Φ := Φ) (l1a := l1a) (l2a := l2a) (l1b := l1b) (l2b := l2b) hlen
  calc ([∗ list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2)
      ⊣⊢ iprop(bigSepL2 Φ l1a l2a ∗ bigSepL2 (fun n => Φ (n + l1a.length)) l1b l2b) := h
    _ ⊣⊢ iprop(bigSepL2 Φ l1a l2a ∗ bigSepL2 (fun k => Φ (l1a.length + k)) l1b l2b) := by
        apply sep_congr .rfl
        apply congr
        intro k x1 x2
        simp only [Nat.add_comm]
        exact BiEntails.rfl

/-! ## Const SepL Lemmas -/

/-- No direct Rocq equivalent; when Φ doesn't depend on second argument. -/
theorem const_sepL_l {Φ : Nat → A → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;_x2 ∈ l1;l2, Φ k x1) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ l1) := by
  -- Following Coq: rewrite via alt, then use BigSepL.fmap
  calc ([∗ list] k ↦ x1;_x2 ∈ l1;l2, Φ k x1)
      ⊣⊢ iprop(⌜l1.length = l2.length⌝ ∧
          bigSepL (fun k p => Φ k p.1) (l1.zip l2)) := alt
    _ ⊣⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ l1) := by
        -- Following Coq: apply (anti_symm _), then use pure_elim_l for both directions
        constructor
        · -- Forward: ⌜len⌝ ∧ bigSepL [...] zip ⊢ ⌜len⌝ ∧ bigSepL [...] l1
          apply pure_elim_l; intro hlen
          apply and_intro (pure_intro hlen)
          -- With hlen, (l1.zip l2).map fst = l1, so bigSepL over zip becomes bigSepL over l1
          have fst_zip : (l1.zip l2).map Prod.fst = l1 := by
            clear Φ
            induction l1 generalizing l2 with
            | nil => cases l2; rfl; simp at hlen
            | cons x xs ih =>
              cases l2 with
              | nil => simp at hlen
              | cons y ys =>
                simp only [List.length_cons] at hlen
                simp only [List.zip_cons_cons, List.map_cons]
                congr
                exact ih (Nat.succ.inj hlen)
          -- bigSepL (fun k p => Φ k p.1) (l1.zip l2) ⊢ bigSepL Φ l1
          -- Use: bigSepL Φ (l.map Prod.fst) ⊣⊢ bigSepL (fun k x => Φ k x.fst) l
          have h1 : bigSepL Φ ((l1.zip l2).map Prod.fst) ⊣⊢
                     bigSepL (fun k p => Φ k p.1) (l1.zip l2) :=
            equiv_iff.mp (BigSepL.fmap Prod.fst)
          have h2 : bigSepL Φ ((l1.zip l2).map Prod.fst) ⊣⊢ bigSepL Φ l1 := by
            rw [fst_zip]; exact .rfl
          exact (h1.symm.trans h2).1
        · -- Backward: ⌜len⌝ ∧ bigSepL [...] l1 ⊢ ⌜len⌝ ∧ bigSepL [...] zip
          apply pure_elim_l; intro hlen
          apply and_intro (pure_intro hlen)
          -- With hlen, need to show: bigSepL Φ l1 ⊢ bigSepL (fun k p => Φ k p.1) (l1.zip l2)
          have fst_zip : (l1.zip l2).map Prod.fst = l1 := by
            clear Φ
            induction l1 generalizing l2 with
            | nil => cases l2; rfl; simp at hlen
            | cons x xs ih =>
              cases l2 with
              | nil => simp at hlen
              | cons y ys =>
                simp only [List.length_cons] at hlen
                simp only [List.zip_cons_cons, List.map_cons]
                congr
                exact ih (Nat.succ.inj hlen)
          have h1 : bigSepL Φ l1 ⊣⊢ bigSepL Φ ((l1.zip l2).map Prod.fst) := by
            rw [fst_zip]; exact .rfl
          have h2 : bigSepL Φ ((l1.zip l2).map Prod.fst) ⊣⊢
                     bigSepL (fun k p => Φ k p.1) (l1.zip l2) :=
            equiv_iff.mp (BigSepL.fmap Prod.fst)
          exact (h1.trans h2).1

/-- No direct Rocq equivalent; when Φ doesn't depend on first argument. -/
theorem const_sepL_r {Φ : Nat → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ _x1;x2 ∈ l1;l2, Φ k x2) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ l2) := by
  -- Following Coq: rewrite using flip, then const_sepL_l, then symmetry of equality
  calc ([∗ list] k ↦ _x1;x2 ∈ l1;l2, Φ k x2)
      ⊣⊢ bigSepL2 (fun k x2 _ => Φ k x2) l2 l1 := flip
    _ ⊣⊢ iprop(⌜l2.length = l1.length⌝ ∧ bigSepL Φ l2) := const_sepL_l
    _ ⊣⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ l2) := by
        constructor
        · apply and_mono
          · apply pure_mono; intro h; exact h.symm
          · exact .rfl
        · apply and_mono
          · apply pure_mono; intro h; exact h.symm
          · exact .rfl

/-! ## Sep SepL Lemmas -/

/-- No direct Rocq equivalent; separate term depending only on l1. -/
theorem sep_sepL_l [BIAffine PROP] {Φ : Nat → A → PROP} {Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 ∗ Ψ k x1 x2) ⊣⊢
      iprop(bigSepL Φ l1 ∗ [∗ list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  -- Following Coq: rewrite via sep', const_sepL_l, then use and_elim_r
  calc ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 ∗ Ψ k x1 x2)
      ⊣⊢ iprop(bigSepL2 (fun k x1 _ => Φ k x1) l1 l2 ∗ bigSepL2 Ψ l1 l2) := sep'
    _ ⊣⊢ iprop((⌜l1.length = l2.length⌝ ∧ bigSepL Φ l1) ∗ bigSepL2 Ψ l1 l2) := by
        constructor
        · exact sep_mono ( const_sepL_l).1 .rfl
        · exact sep_mono ( const_sepL_l).2 .rfl
    _ ⊣⊢ iprop(bigSepL Φ l1 ∗ bigSepL2 Ψ l1 l2) := by
        constructor
        · exact sep_mono and_elim_r .rfl
        · calc iprop(bigSepL Φ l1 ∗ bigSepL2 Ψ l1 l2)
              ⊢ iprop(bigSepL Φ l1 ∗ (⌜l1.length = l2.length⌝ ∗ bigSepL2 Ψ l1 l2)) := by
                  apply sep_mono .rfl
                  calc iprop(bigSepL2 Ψ l1 l2)
                      ⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL2 Ψ l1 l2) :=
                          and_intro BigSepL2.length .rfl
                    _ ⊢ iprop(<affine> ⌜l1.length = l2.length⌝ ∗ bigSepL2 Ψ l1 l2) :=
                          ( persistent_and_affinely_sep_l).1
                    _ ⊢ iprop(⌜l1.length = l2.length⌝ ∗ bigSepL2 Ψ l1 l2) :=
                          sep_mono_l affinely_elim
            _ ⊢ iprop((bigSepL Φ l1 ∗ ⌜l1.length = l2.length⌝) ∗ bigSepL2 Ψ l1 l2) :=
                  ( sep_assoc).2
            _ ⊢ iprop((⌜l1.length = l2.length⌝ ∧ bigSepL Φ l1) ∗ bigSepL2 Ψ l1 l2) := by
                  apply sep_mono _ .rfl
                  -- bigSepL Φ l1 ∗ ⌜l1.length = l2.length⌝ ⊢ ⌜l1.length = l2.length⌝ ∧ bigSepL Φ l1
                  -- Use persistently_sep_persistently to duplicate persistent pure
                  apply and_intro
                  · calc iprop(bigSepL Φ l1 ∗ ⌜l1.length = l2.length⌝)
                        ⊢ iprop(⌜l1.length = l2.length⌝ ∗ bigSepL Φ l1) :=
                            ( sep_comm).1
                      _ ⊢ iprop(<pers> ⌜l1.length = l2.length⌝ ∗ bigSepL Φ l1) :=
                            sep_mono_l persistently_intro
                      _ ⊢ iprop(<pers> ⌜l1.length = l2.length⌝) :=
                            persistently_absorb_l
                      _ ⊢ iprop(⌜l1.length = l2.length⌝) :=
                            persistently_elim
                  · exact sep_elim_l

/-- No direct Rocq equivalent; separate term depending only on l2. -/
theorem sep_sepL_r [BIAffine PROP] {Φ : Nat → B → PROP} {Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗ list] k ↦ x1;x2 ∈ l1;l2, Φ k x2 ∗ Ψ k x1 x2) ⊣⊢
      iprop(bigSepL Φ l2 ∗ [∗ list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  -- Following Coq: use flip, sep_comm on each element, sep_sepL_l
  calc bigSepL2 (fun k x1 x2 => iprop(Φ k x2 ∗ Ψ k x1 x2)) l1 l2
      ⊣⊢ bigSepL2 (fun k x1 x2 => iprop(Ψ k x1 x2 ∗ Φ k x2)) l1 l2 := by
          apply congr; intro k x1 x2; exact sep_comm
    _ ⊣⊢ bigSepL2 (fun k x2 x1 => iprop(Ψ k x1 x2 ∗ Φ k x2)) l2 l1 := flip
    _ ⊣⊢ iprop(bigSepL (fun k x2 => Φ k x2) l2 ∗ bigSepL2 Ψ l1 l2) := by
          -- Now (fun k x2 x1 => Ψ k x1 x2 ∗ Φ k x2) matches (fun k x2 _ => Φ k x2) ∗ (fun k x2 x1 => Ψ k x1 x2)
          -- But we need to rewrite to have the pattern for sep_sepL_l
          calc bigSepL2 (fun k x2 x1 => iprop(Ψ k x1 x2 ∗ Φ k x2)) l2 l1
              ⊣⊢ bigSepL2 (fun k x2 x1 => iprop(Φ k x2 ∗ Ψ k x1 x2)) l2 l1 := by
                  apply congr; intro k x2 x1; exact sep_comm
            _ ⊣⊢ iprop(bigSepL (fun k x2 => Φ k x2) l2 ∗ bigSepL2 (fun k x2 x1 => Ψ k x1 x2) l2 l1) :=
                  sep_sepL_l
            _ ⊣⊢ iprop(bigSepL Φ l2 ∗ bigSepL2 (fun k x2 x1 => Ψ k x1 x2) l2 l1) := by
                  apply sep_congr _ .rfl
                  exact .rfl
            _ ⊣⊢ iprop(bigSepL Φ l2 ∗ bigSepL2 Ψ l1 l2) := by
                  apply sep_congr .rfl; exact flip

/-! ## Delete Lemmas -/

/-- Corresponds to `big_sepL2_delete` in Rocq Iris. -/
theorem delete {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat}
    {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
      iprop(Φ i x1 x2 ∗ [∗ list] k ↦ y1;y2 ∈ l1;l2,
        if k = i then emp else Φ k y1 y2) := by
  induction l1 generalizing l2 i Φ with
  | nil => simp at h1
  | cons z1 zs1 ih =>
    cases l2 with
    | nil => simp at h2
    | cons z2 zs2 =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
        subst h1 h2
        simp only [bigSepL2, ↓reduceIte]
        apply sep_congr .rfl
        calc bigSepL2 (fun n => Φ (n + 1)) zs1 zs2
            ⊣⊢ bigSepL2 (fun n y1 y2 => if n + 1 = 0 then emp else Φ (n + 1) y1 y2) zs1 zs2 := by
              apply proper
              intro k x1 x2 _ _
              simp only [Nat.add_one_ne_zero, ↓reduceIte]
              exact BiEntails.rfl
          _ ⊣⊢ emp ∗ bigSepL2 (fun n y1 y2 => if n + 1 = 0 then emp else Φ (n + 1) y1 y2) zs1 zs2 := emp_sep.symm
      | succ j =>
        simp only [List.getElem?_cons_succ] at h1 h2
        simp only [bigSepL2]
        have ih' := ih (i := j) (Φ := fun n => Φ (n + 1)) h1 h2
        calc Φ 0 z1 z2 ∗ bigSepL2 (fun n => Φ (n + 1)) zs1 zs2
            ⊣⊢ Φ 0 z1 z2 ∗ (Φ (j + 1) x1 x2 ∗ bigSepL2 (fun k y1 y2 => if k = j then emp else Φ (k + 1) y1 y2) zs1 zs2) :=
              sep_congr .rfl ih'
          _ ⊣⊢ Φ (j + 1) x1 x2 ∗ (Φ 0 z1 z2 ∗ bigSepL2 (fun k y1 y2 => if k = j then emp else Φ (k + 1) y1 y2) zs1 zs2) := by
              calc Φ 0 z1 z2 ∗ (Φ (j + 1) x1 x2 ∗ bigSepL2 (fun k y1 y2 => if k = j then emp else Φ (k + 1) y1 y2) zs1 zs2)
                  ⊣⊢ (Φ 0 z1 z2 ∗ Φ (j + 1) x1 x2) ∗ bigSepL2 (fun k y1 y2 => if k = j then emp else Φ (k + 1) y1 y2) zs1 zs2 := sep_assoc.symm
                _ ⊣⊢ (Φ (j + 1) x1 x2 ∗ Φ 0 z1 z2) ∗ bigSepL2 (fun k y1 y2 => if k = j then emp else Φ (k + 1) y1 y2) zs1 zs2 := sep_congr sep_comm BiEntails.rfl
                _ ⊣⊢ Φ (j + 1) x1 x2 ∗ (Φ 0 z1 z2 ∗ bigSepL2 (fun k y1 y2 => if k = j then emp else Φ (k + 1) y1 y2) zs1 zs2) := sep_assoc
          _ ⊣⊢ Φ (j + 1) x1 x2 ∗ bigSepL2 (fun k y1 y2 => if k = j + 1 then emp else Φ k y1 y2) (z1 :: zs1) (z2 :: zs2) := by
              apply sep_congr .rfl
              simp only [bigSepL2]
              have hne0 : (0 : Nat) ≠ j + 1 := Nat.zero_ne_add_one j
              simp only [hne0, ↓reduceIte]
              apply sep_congr .rfl
              apply proper
              intro k y1 y2 _ _
              by_cases hkj : k = j
              · subst hkj
                simp only [↓reduceIte]
                exact BiEntails.rfl
              · simp only [hkj, ↓reduceIte]
                have hkj' : k + 1 ≠ j + 1 := by omega
                simp only [hkj', ↓reduceIte]
                exact BiEntails.rfl

/-- Corresponds to `big_sepL2_delete'` in Rocq Iris. -/
theorem delete' [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat}
    {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
      iprop(Φ i x1 x2 ∗ [∗ list] k ↦ y1;y2 ∈ l1;l2, ⌜k ≠ i⌝ → Φ k y1 y2) := by
  -- Following Rocq: rewrite using delete, then convert (if k = i then emp else Φ) to (⌜k ≠ i⌝ → Φ)
  calc ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)
      ⊣⊢ iprop(Φ i x1 x2 ∗ [∗ list] k ↦ y1;y2 ∈ l1;l2, if k = i then emp else Φ k y1 y2) :=
        delete h1 h2
    _ ⊣⊢ iprop(Φ i x1 x2 ∗ [∗ list] k ↦ y1;y2 ∈ l1;l2, ⌜k ≠ i⌝ → Φ k y1 y2) := by
        apply sep_congr .rfl
        apply congr
        intro k y1 y2
        by_cases hki : k = i
        · -- k = i: need emp ⊣⊢ ⌜False⌝ → Φ k y1 y2
          subst hki
          simp only [↓reduceIte, ne_eq, not_true_eq_false]
          constructor
          · -- emp ⊢ ⌜False⌝ → Φ k y1 y2
            apply imp_intro'
            exact (pure_elim_l (φ := False) (R := Φ k y1 y2)
              (fun hf => False.elim hf)).trans Entails.rfl
          · -- ⌜False⌝ → Φ k y1 y2 ⊢ emp
            exact Affine.affine
        · -- k ≠ i: need Φ k y1 y2 ⊣⊢ ⌜True⌝ → Φ k y1 y2
          simp only [hki, ↓reduceIte, ne_eq, not_false_eq_true]
          exact true_imp.symm


/-- Corresponds to `big_sepL2_lookup_acc_impl` in Rocq Iris. -/
theorem lookup_acc_impl {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
      iprop(Φ i x1 x2 ∗ ∀ Ψ, □ (∀ k, ∀ y1, ∀ y2,
        iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
          Φ k y1 y2 -∗ Ψ k y1 y2)) -∗
        Ψ i x1 x2 -∗ bigSepL2 Ψ l1 l2) := by
  -- Use delete to extract element
  have hdel := ( (delete (Φ := Φ) h1 h2)).1
  calc ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)
      ⊢ iprop(Φ i x1 x2 ∗ bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2) := hdel
    _ ⊢ iprop(Φ i x1 x2 ∗ ∀ Ψ, □ (∀ k, ∀ y1, ∀ y2,
          iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
            Φ k y1 y2 -∗ Ψ k y1 y2)) -∗
          Ψ i x1 x2 -∗ bigSepL2 Ψ l1 l2) := by
        apply sep_mono_r
        apply forall_intro; intro Ψ
        apply wand_intro
        apply wand_intro
        -- Goal: (bigSepL2 (if k = i then emp else Φ) l1 l2 ∗ □ (...)) ∗ Ψ i x1 x2 ⊢ bigSepL2 Ψ l1 l2
        -- Strategy: Use delete on Ψ to show we need Ψ i x1 x2 and bigSepL2 (if k = i then emp else Ψ) l1 l2
        have hdel_psi := ( (delete (Φ := Ψ) h1 h2)).2
        calc iprop((bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2 ∗
                  □ (∀ k, ∀ y1, ∀ y2,
                    iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                      Φ k y1 y2 -∗ Ψ k y1 y2))) ∗ Ψ i x1 x2)
            ⊢ iprop(Ψ i x1 x2 ∗ (bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2 ∗
                  □ (∀ k, ∀ y1, ∀ y2,
                    iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                      Φ k y1 y2 -∗ Ψ k y1 y2)))) := by
                have := @sep_comm PROP _
                  iprop((bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2 ∗
                    □ (∀ k, ∀ y1, ∀ y2,
                      iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                        Φ k y1 y2 -∗ Ψ k y1 y2))))
                  iprop(Ψ i x1 x2)
                exact ( this).1
          _ ⊢ iprop(Ψ i x1 x2 ∗ bigSepL2 (fun k y1 y2 => if k = i then emp else Ψ k y1 y2) l1 l2) := by
                apply sep_mono_r
                -- Transform bigSepL2 with Φ to bigSepL2 with Ψ using the □ hypothesis
                -- Following Rocq: use impl (big_sepL2_impl) to transform predicates
                -- For positions k ≠ i: use the hypothesis to transform Φ k y1 y2 to Ψ k y1 y2
                -- For position i: both are emp
                -- Step 1: Extract length from bigSepL2 (if k = i then emp else Φ)
                have hlen_extract :
                    bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2 ⊢
                      iprop(⌜l1.length = l2.length⌝ ∧
                        bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2) :=
                  ( and_self).2.trans (and_mono_l length)
                -- Step 2: Use impl to build the transformation
                have himpl := @impl PROP _ A B
                  (fun k y1 y2 => if k = i then emp else Φ k y1 y2)
                  (fun k y1 y2 => if k = i then emp else Ψ k y1 y2) l1 l2
                -- Now combine: extract length, then use with the □ hypothesis
                calc iprop(bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2 ∗
                      □ (∀ k, ∀ y1, ∀ y2,
                        iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                          Φ k y1 y2 -∗ Ψ k y1 y2)))
                    ⊢ iprop((⌜l1.length = l2.length⌝ ∧
                          bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2) ∗
                        □ (∀ k, ∀ y1, ∀ y2,
                          iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                            Φ k y1 y2 -∗ Ψ k y1 y2))) := sep_mono_l hlen_extract
                  _ ⊢ iprop(⌜l1.length = l2.length⌝ ∧
                        (bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2 ∗
                        □ (∀ k, ∀ y1, ∀ y2,
                          iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                            Φ k y1 y2 -∗ Ψ k y1 y2)))) := by
                      -- (P ∧ Q) ∗ R ⊢ P ∧ (Q ∗ R)
                      calc iprop((⌜l1.length = l2.length⌝ ∧
                              bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2) ∗
                            □ (∀ k, ∀ y1, ∀ y2,
                              iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                                Φ k y1 y2 -∗ Ψ k y1 y2)))
                          ⊢ iprop((<affine> ⌜l1.length = l2.length⌝ ∗
                              bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2) ∗
                            □ (∀ k, ∀ y1, ∀ y2,
                              iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                                Φ k y1 y2 -∗ Ψ k y1 y2))) :=
                            sep_mono_l ( persistent_and_affinely_sep_l).1
                        _ ⊢ iprop(<affine> ⌜l1.length = l2.length⌝ ∗
                            (bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2 ∗
                            □ (∀ k, ∀ y1, ∀ y2,
                              iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                                Φ k y1 y2 -∗ Ψ k y1 y2)))) :=
                            ( sep_assoc).1
                        _ ⊢ iprop(⌜l1.length = l2.length⌝ ∧
                            (bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2 ∗
                            □ (∀ k, ∀ y1, ∀ y2,
                              iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                                Φ k y1 y2 -∗ Ψ k y1 y2)))) :=
                            ( persistent_and_affinely_sep_l.symm).1
                  _ ⊢ bigSepL2 (fun k y1 y2 => if k = i then emp else Ψ k y1 y2) l1 l2 := by
                      apply pure_elim_l; intro hlen
                      -- Now use wand_elim with impl to transform the predicate
                      -- Goal: bigSepL2 (if emp else Φ) ∗ □(...) ⊢ bigSepL2 (if emp else Ψ)
                      -- impl says: bigSepL2 Φ' ⊢ □(∀ k x1 x2, ⌜...⌝ → ⌜...⌝ → Φ' -∗ Ψ') -∗ bigSepL2 Ψ'
                      -- So: bigSepL2 Φ' ∗ □(...) ⊢ bigSepL2 Ψ' via wand_elim
                      -- Build the wand hypothesis transformation
                      have hwand_transform :
                          iprop(□ (∀ k, ∀ y1, ∀ y2,
                              iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                                Φ k y1 y2 -∗ Ψ k y1 y2)))
                          ⊢ iprop(□ (∀ k, ∀ x1, ∀ x2,
                              iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ →
                                (if k = i then emp else Φ k x1 x2) -∗
                                (if k = i then emp else Ψ k x1 x2)))) := by
                        -- Use intuitionistically_intro' so we have □(...) on LHS, which is affine
                        apply intuitionistically_intro'
                        apply forall_intro; intro k
                        apply forall_intro; intro y1
                        apply forall_intro; intro y2
                        apply imp_intro'
                        apply pure_elim_l; intro hk1
                        apply imp_intro'
                        apply pure_elim_l; intro hk2
                        -- Goal: □(∀ k y1 y2, ⌜...⌝ → ⌜...⌝ → ⌜k ≠ i⌝ → Φ -∗ Ψ) ⊢
                        --       (if k=i then emp else Φ) -∗ (if k=i then emp else Ψ)
                        by_cases hki : k = i
                        · -- k = i case: emp -∗ emp
                          subst hki
                          simp only [↓reduceIte]
                          -- Goal: □(...) ⊢ emp -∗ emp
                          -- □(...) is affine, so □(...) ⊢ emp
                          -- Use wand_intro: need emp ∗ □(...) ⊢ emp
                          apply wand_intro
                          -- emp ∗ □(...) ⊢ emp via sep_emp and affine
                          exact ( sep_emp).1.trans Affine.affine
                        · -- k ≠ i case: use the hypothesis
                          simp only [hki, ↓reduceIte]
                          -- Goal: □(∀ k y1 y2, ...) ⊢ Φ k y1 y2 -∗ Ψ k y1 y2
                          -- Use intuitionistically_elim to drop the □, then work with the forall
                          calc iprop(□ (∀ k, ∀ y1, ∀ y2,
                                  iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                                    Φ k y1 y2 -∗ Ψ k y1 y2)))
                              ⊢ iprop(∀ k, ∀ y1, ∀ y2,
                                  iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                                    Φ k y1 y2 -∗ Ψ k y1 y2)) := intuitionistically_elim
                            _ ⊢ iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                                  Φ k y1 y2 -∗ Ψ k y1 y2) :=
                                (forall_elim k).trans ((forall_elim y1).trans (forall_elim y2))
                            _ ⊢ iprop(Φ k y1 y2 -∗ Ψ k y1 y2) := by
                                -- Apply the three pure implications
                                -- We have (⌜P1⌝ → ⌜P2⌝ → ⌜P3⌝ → S) and pure facts P1, P2, P3
                                -- Use and_intro + and_symm + imp_elim_r to eliminate each
                                have h : iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                                      Φ k y1 y2 -∗ Ψ k y1 y2) ⊢
                                    iprop(⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ → Φ k y1 y2 -∗ Ψ k y1 y2) :=
                                  (@and_intro PROP _ _ _ _ Entails.rfl (pure_intro hk1)).trans
                                    (and_symm.trans imp_elim_r)
                                have h2 : iprop(⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ → Φ k y1 y2 -∗ Ψ k y1 y2) ⊢
                                    iprop(⌜k ≠ i⌝ → Φ k y1 y2 -∗ Ψ k y1 y2) :=
                                  (@and_intro PROP _ _ _ _ Entails.rfl (pure_intro hk2)).trans
                                    (and_symm.trans imp_elim_r)
                                have h3 : iprop(⌜k ≠ i⌝ → Φ k y1 y2 -∗ Ψ k y1 y2) ⊢
                                    iprop(Φ k y1 y2 -∗ Ψ k y1 y2) :=
                                  (@and_intro PROP _ _ _ _ Entails.rfl (pure_intro hki)).trans
                                    (and_symm.trans imp_elim_r)
                                exact h.trans (h2.trans h3)
                      -- Now apply: sep_mono_r with hwand_transform, then wand_elim with himpl
                      calc iprop(bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2 ∗
                              □ (∀ k, ∀ y1, ∀ y2,
                                iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                                  Φ k y1 y2 -∗ Ψ k y1 y2)))
                          ⊢ iprop(bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2 ∗
                              □ (∀ k, ∀ x1, ∀ x2,
                                iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ →
                                  (if k = i then emp else Φ k x1 x2) -∗
                                  (if k = i then emp else Ψ k x1 x2)))) :=
                            sep_mono_r hwand_transform
                        _ ⊢ bigSepL2 (fun k y1 y2 => if k = i then emp else Ψ k y1 y2) l1 l2 :=
                            wand_elim himpl
          _ ⊢ bigSepL2 Ψ l1 l2 := hdel_psi

end BigSepL2

namespace BigSepL

/-! ## SepL2 Diagonal -/

/-- No direct Rocq equivalent; diagonal BigSepL to BigSepL2. -/
theorem sepL2_diag {Φ : Nat → A → A → PROP} {l : List A} :
    bigSepL (fun k x => Φ k x x) l ⊢ bigSepL2 Φ l l := by
  -- Key observation: l.zip l = l.map (fun x => (x, x))
  have hzip : l.zip l = l.map (fun x => (x, x)) := by
    induction l with
    | nil => simp
    | cons hd tl ih => simp [ih]
  -- The inner equivalence proof: bigSepL over l equals bigSepL over l.zip l
  have inner_eq : bigSepL (fun k x => Φ k x x) l ⊣⊢
      bigSepL (fun k p => Φ k p.1 p.2) (l.zip l) := by
    rw [hzip]
    -- fmap says: bigSepL Φ (l.map f) ⊣⊢ bigSepL (fun k x => Φ k (f x)) l
    -- We have: bigSepL (fun k p => Φ k p.1 p.2) (l.map (fun x => (x, x)))
    --        ⊣⊢ bigSepL (fun k x => (fun k p => Φ k p.1 p.2) k ((fun x => (x, x)) x)) l
    --        = bigSepL (fun k x => Φ k x x) l
    have h := equiv_iff.mp (BigSepL.fmap (PROP := PROP) (Φ := fun k p => Φ k p.1 p.2)
        (fun x => (x, x)) (l := l))
    -- h : bigSepL (fun k p => Φ k p.1 p.2) (l.map (fun x => (x,x))) ⊣⊢ bigSepL (fun k x => Φ k x x) l
    exact h.symm
  -- Now build the full entailment using inner_eq
  calc bigSepL (fun k x => Φ k x x) l
      ⊢ iprop(⌜l.length = l.length⌝ ∧ bigSepL (fun k x => Φ k x x) l) :=
        and_intro (pure_intro rfl) Entails.rfl
    _ ⊢ iprop(⌜l.length = l.length⌝ ∧ bigSepL (fun k p => Φ k p.1 p.2) (l.zip l)) :=
        and_mono Entails.rfl ( inner_eq).1
    _ ⊢ bigSepL2 Φ l l := ( BigSepL2.alt).2

end BigSepL

/-! ## Missing Lemmas from Rocq Iris

The following lemmas from Rocq Iris are not ported:
- `big_sepL2_proper_2`: Uses OFE structure on A, B (list element types)
- `big_sepL2_closed`: Meta-lemma (direct inductive proofs used instead)
- `big_sepL2_timeless`, `big_sepL2_timeless'`: Requires `sep_timeless` infrastructure
- `big_sepL2_later_1`, `big_sepL2_later`, `big_sepL2_laterN_1`, `big_sepL2_laterN`: Requires except-0 infrastructure (TODO)
-/

end Iris.BI
