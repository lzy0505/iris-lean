/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp
import Iris.BI.BigOpList

namespace Iris.BI

open Iris.Algebra
open BIBase

/-- Bidirectional entailment on separation logic propositions. -/
local macro:25 P:term:29 " ⊣⊢ " Q:term:29 : term => ``(BI.BiEquiv iprop($P) iprop($Q))

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
syntax "[∗ " "list" "] " ident "," ident " ∈ " term "," term ", " term : term
-- Notation for bigSepL2 with index
syntax "[∗ " "list" "] " ident " ↦ " ident "," ident " ∈ " term "," term ", " term : term

macro_rules
  | `([∗ list] $x1:ident,$x2:ident ∈ $l1,$l2, $P) =>
      `(bigSepL2 (fun _ $x1 $x2 => $P) $l1 $l2)
  | `([∗ list] $k:ident ↦ $x1:ident,$x2:ident ∈ $l1,$l2, $P) =>
      `(bigSepL2 (fun $k $x1 $x2 => $P) $l1 $l2)

-- iprop macro rules
macro_rules
  | `(iprop([∗ list] $x1:ident,$x2:ident ∈ $l1,$l2, $P)) =>
      `(bigSepL2 (fun _ $x1 $x2 => iprop($P)) $l1 $l2)
  | `(iprop([∗ list] $k:ident ↦ $x1:ident,$x2:ident ∈ $l1,$l2, $P)) =>
      `(bigSepL2 (fun $k $x1 $x2 => iprop($P)) $l1 $l2)

namespace BigSepL2

/-! ## Basic Structural Lemmas -/

@[simp]
theorem nil {Φ : Nat → A → B → PROP} :
    bigSepL2 Φ ([] : List A) ([] : List B) ⊣⊢ emp := by
  simp only [bigSepL2]
  exact .rfl

theorem nil' {P : PROP} [Affine P] {Φ : Nat → A → B → PROP} :
    P ⊢ bigSepL2 Φ ([] : List A) ([] : List B) := by
  exact Affine.affine.trans (BI.equiv_entails.mp nil.symm).1

theorem nil_inv_l {Φ : Nat → A → B → PROP} {l2 : List B} :
    bigSepL2 Φ [] l2 ⊣⊢ iprop(⌜l2 = []⌝ ∧ emp) := by
  cases l2 with
  | nil =>
    simp only [bigSepL2]
    exact BI.equiv_entails.mpr ⟨and_intro (pure_intro trivial) Entails.rfl, and_elim_r⟩
  | cons y ys =>
    simp only [bigSepL2]
    apply BI.equiv_entails.mpr; constructor
    · exact false_elim
    · exact (and_elim_l.trans (pure_elim' (fun h => nomatch h)))

theorem nil_inv_r {Φ : Nat → A → B → PROP} {l1 : List A} :
    bigSepL2 Φ l1 [] ⊣⊢ iprop(⌜l1 = []⌝ ∧ emp) := by
  cases l1 with
  | nil =>
    simp only [bigSepL2]
    exact BI.equiv_entails.mpr ⟨and_intro (pure_intro trivial) Entails.rfl, and_elim_r⟩
  | cons x xs =>
    simp only [bigSepL2]
    apply BI.equiv_entails.mpr; constructor
    · exact false_elim
    · exact (and_elim_l.trans (pure_elim' (fun h => nomatch h)))

theorem cons {Φ : Nat → A → B → PROP} {x1 : A} {x2 : B} {xs1 : List A} {xs2 : List B} :
    bigSepL2 Φ (x1 :: xs1) (x2 :: xs2) ⊣⊢
      Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2 := by
  simp only [bigSepL2]
  exact .rfl

theorem cons_inv_l {Φ : Nat → A → B → PROP} {x1 : A} {xs1 : List A} {l2 : List B} :
    bigSepL2 Φ (x1 :: xs1) l2 ⊣⊢
      iprop(∃ x2 xs2, ⌜l2 = x2 :: xs2⌝ ∧ (Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2)) := by
  cases l2 with
  | nil =>
    simp only [bigSepL2]
    apply BI.equiv_entails.mpr; constructor
    · exact false_elim
    · exact exists_elim fun _ => exists_elim fun _ =>
        and_elim_l.trans (pure_elim' (fun h => nomatch h))
  | cons y ys =>
    simp only [bigSepL2]
    apply BI.equiv_entails.mpr; constructor
    · exact (and_intro (pure_intro rfl) Entails.rfl).trans
        ((exists_intro (Ψ := fun xs2 => iprop(⌜y :: ys = y :: xs2⌝ ∧
          (Φ 0 x1 y ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2))) ys).trans
        (exists_intro (Ψ := fun x2 => iprop(∃ xs2, ⌜y :: ys = x2 :: xs2⌝ ∧
          (Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2))) y))
    · exact exists_elim fun x2 => exists_elim fun xs2 =>
        pure_elim_l fun h => by cases h; exact Entails.rfl

theorem cons_inv_r {Φ : Nat → A → B → PROP} {l1 : List A} {x2 : B} {xs2 : List B} :
    bigSepL2 Φ l1 (x2 :: xs2) ⊣⊢
      iprop(∃ x1 xs1, ⌜l1 = x1 :: xs1⌝ ∧ (Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2)) := by
  cases l1 with
  | nil =>
    simp only [bigSepL2]
    apply BI.equiv_entails.mpr; constructor
    · exact false_elim
    · exact exists_elim fun _ => exists_elim fun _ =>
        and_elim_l.trans (pure_elim' (fun h => nomatch h))
  | cons x xs =>
    simp only [bigSepL2]
    apply BI.equiv_entails.mpr; constructor
    · exact (and_intro (pure_intro rfl) Entails.rfl).trans
        ((exists_intro (Ψ := fun xs1 => iprop(⌜x :: xs = x :: xs1⌝ ∧
          (Φ 0 x x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2))) xs).trans
        (exists_intro (Ψ := fun x1 => iprop(∃ xs1, ⌜x :: xs = x1 :: xs1⌝ ∧
          (Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2))) x))
    · exact exists_elim fun x1 => exists_elim fun xs1 =>
        pure_elim_l fun h => by cases h; exact Entails.rfl

theorem singleton {Φ : Nat → A → B → PROP} {x : A} {y : B} :
    bigSepL2 Φ [x] [y] ⊣⊢ Φ 0 x y := by
  simp only [bigSepL2]
  exact sep_emp

/-! ## Length Lemma -/

theorem length {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    bigSepL2 Φ l1 l2 ⊢ iprop(⌜l1.length = l2.length⌝) := by
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
      calc iprop(Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2)
          ⊢ iprop(True ∗ ⌜xs1.length = xs2.length⌝) := sep_mono true_intro hlength
        _ ⊢ iprop(⌜xs1.length = xs2.length⌝) := (BI.equiv_entails.mp (true_sep (PROP := PROP))).1
        _ ⊢ iprop(⌜xs1.length + 1 = xs2.length + 1⌝) := pure_mono (congrArg (· + 1))

/-! ## Monotonicity and Congruence -/

theorem mono {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ⊢ Ψ k x1 x2) :
    bigSepL2 Φ l1 l2 ⊢ bigSepL2 Ψ l1 l2 := by
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

theorem proper {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ⊣⊢ Ψ k x1 x2) :
    bigSepL2 Φ l1 l2 ⊣⊢ bigSepL2 Ψ l1 l2 := by
  apply BI.equiv_entails.mpr; constructor
  · apply mono; intro k x1 x2 h1 h2; exact (BI.equiv_entails.mp (h k x1 x2 h1 h2)).1
  · apply mono; intro k x1 x2 h1 h2; exact (BI.equiv_entails.mp (h k x1 x2 h1 h2)).2

theorem congr {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, Φ k x1 x2 ⊣⊢ Ψ k x1 x2) :
    bigSepL2 Φ l1 l2 ⊣⊢ bigSepL2 Ψ l1 l2 := by
  apply proper
  intro k x1 x2 _ _
  exact h k x1 x2

/-- Non-expansiveness: if predicates are n-equivalent pointwise, so are their big seps. -/
theorem ne {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {n : Nat}
    (h : ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ≡{n}≡ Ψ k x1 x2) :
    bigSepL2 Φ l1 l2 ≡{n}≡ bigSepL2 Ψ l1 l2 := by
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

/-- Monotonicity without lookup condition: pointwise entailment lifts to bigSepL2. -/
theorem mono' {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, Φ k x1 x2 ⊢ Ψ k x1 x2) :
    bigSepL2 Φ l1 l2 ⊢ bigSepL2 Ψ l1 l2 :=
  mono (fun k x1 x2 _ _ => h k x1 x2)

/-- Flip monotonicity: pointwise reverse entailment lifts to bigSepL2. -/
theorem flip_mono' {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, Ψ k x1 x2 ⊢ Φ k x1 x2) :
    bigSepL2 Ψ l1 l2 ⊢ bigSepL2 Φ l1 l2 :=
  mono (fun k x1 x2 _ _ => h k x1 x2)

/-! ## Alternative Characterization via Zip -/

theorem alt {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    bigSepL2 Φ l1 l2 ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) := by
  apply BI.equiv_entails.mpr; constructor
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

instance persistent {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    [∀ k x1 x2, Persistent (Φ k x1 x2)] :
    Persistent (bigSepL2 Φ l1 l2) where
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
        have h2 : bigSepL2 (fun n => Φ (n + 1)) xs1 xs2 ⊢
            <pers> bigSepL2 (fun n => Φ (n + 1)) xs1 xs2 := ih
        exact (sep_mono h1 h2).trans persistently_sep_2

instance affine {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    [∀ k x1 x2, Affine (Φ k x1 x2)] :
    Affine (bigSepL2 Φ l1 l2) where
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
        have h2 : bigSepL2 (fun n => Φ (n + 1)) xs1 xs2 ⊢ emp := ih
        exact (sep_mono h1 h2).trans (BI.equiv_entails.mp sep_emp).1

/-! ## Distribution over Sep -/

theorem sep' {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 ∗ Ψ k x1 x2)) l1 l2 ⊣⊢
      bigSepL2 Φ l1 l2 ∗ bigSepL2 Ψ l1 l2 := by
  induction l1 generalizing l2 Φ Ψ with
  | nil =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact emp_sep.symm
    | cons => simp only [bigSepL2]; exact BI.equiv_entails.mpr ⟨false_elim, sep_elim_l.trans false_elim⟩
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact BI.equiv_entails.mpr ⟨false_elim, sep_elim_l.trans false_elim⟩
    | cons x2 xs2 =>
      simp only [bigSepL2]
      calc iprop((Φ 0 x1 x2 ∗ Ψ 0 x1 x2) ∗
              bigSepL2 (fun k x1 x2 => iprop(Φ (k + 1) x1 x2 ∗ Ψ (k + 1) x1 x2)) xs1 xs2)
          ⊣⊢ iprop((Φ 0 x1 x2 ∗ Ψ 0 x1 x2) ∗
              (bigSepL2 (fun n => Φ (n + 1)) xs1 xs2 ∗ bigSepL2 (fun n => Ψ (n + 1)) xs1 xs2)) :=
            sep_congr OFE.Equiv.rfl ih
        _ ⊣⊢ iprop((Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2) ∗
              (Ψ 0 x1 x2 ∗ bigSepL2 (fun n => Ψ (n + 1)) xs1 xs2)) := sep_sep_sep_comm

theorem sep_2 {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    bigSepL2 Φ l1 l2 ∗ bigSepL2 Ψ l1 l2 ⊣⊢
      bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 ∗ Ψ k x1 x2)) l1 l2 :=
  sep'.symm

/-! ## Distribution over And -/

theorem and' {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 ∧ Ψ k x1 x2)) l1 l2 ⊢
      bigSepL2 Φ l1 l2 ∧ bigSepL2 Ψ l1 l2 := by
  apply and_intro
  · exact mono fun k x1 x2 _ _ => and_elim_l
  · exact mono fun k x1 x2 _ _ => and_elim_r

/-! ## Pure Proposition Lemmas -/

theorem pure_1 {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    bigSepL2 (fun k x1 x2 => iprop(⌜φ k x1 x2⌝ : PROP)) l1 l2 ⊢
      iprop(⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) := by
  -- Use alt to convert to bigSepL, then use Iris.BI.BigSepL.pure_1
  calc bigSepL2 (fun k x1 x2 => iprop(⌜φ k x1 x2⌝ : PROP)) l1 l2
      ⊢ iprop(⌜l1.length = l2.length⌝ ∧
          bigSepL (fun k p => iprop(⌜φ k p.1 p.2⌝ : PROP)) (l1.zip l2) : PROP) := (BI.equiv_entails.mp alt).1
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

theorem affinely_pure_2 {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B}
    (hlen : l1.length = l2.length) :
    iprop(<affine> ⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) ⊢
      bigSepL2 (fun k x1 x2 => iprop(<affine> ⌜φ k x1 x2⌝ : PROP)) l1 l2 := by
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
  have step3 : bigSepL (fun k p => iprop(<affine> ⌜φ k p.1 p.2⌝ : PROP)) (l1.zip l2) ⊢
      iprop(⌜l1.length = l2.length⌝ ∧
        bigSepL (fun k p => iprop(<affine> ⌜φ k p.1 p.2⌝ : PROP)) (l1.zip l2) : PROP) :=
    and_intro (pure_intro hlen) Entails.rfl
  have step4 : iprop(⌜l1.length = l2.length⌝ ∧
      bigSepL (fun k p => iprop(<affine> ⌜φ k p.1 p.2⌝ : PROP)) (l1.zip l2) : PROP) ⊢
      bigSepL2 (fun k x1 x2 => iprop(<affine> ⌜φ k x1 x2⌝ : PROP)) l1 l2 :=
    (BI.equiv_entails.mp (alt (Φ := fun k x1 x2 => iprop(<affine> ⌜φ k x1 x2⌝ : PROP))
      (l1 := l1) (l2 := l2)).symm).1
  exact step1.trans (step2.trans (step3.trans step4))

theorem pure [BIAffine PROP] {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    bigSepL2 (fun k x1 x2 => iprop(⌜φ k x1 x2⌝ : PROP)) l1 l2 ⊣⊢
      iprop(⌜l1.length = l2.length ∧
        ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) := by
  apply BI.equiv_entails.mpr; constructor
  · -- Forward direction: combine length and pure_1 using pure_and
    have hlength := @length PROP _ A B (fun k x1 x2 => iprop(⌜φ k x1 x2⌝)) l1 l2
    have hpure1 := @pure_1 PROP _ A B φ l1 l2
    exact (and_intro hlength hpure1).trans (BI.equiv_entails.mp pure_and).1
  · -- Backward direction
    calc iprop(⌜l1.length = l2.length ∧
          ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP)
        ⊢ iprop(⌜l1.length = l2.length⌝ ∧
          ⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) :=
          (BI.equiv_entails.mp pure_and).2
      _ ⊢ bigSepL2 (fun k x1 x2 => iprop(⌜φ k x1 x2⌝ : PROP)) l1 l2 := by
          apply pure_elim_l; intro hlen
          calc iprop(⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP)
              ⊢ iprop(<affine> ⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) :=
                (BI.equiv_entails.mp (affine_affinely (PROP := PROP) _)).2
            _ ⊢ bigSepL2 (fun k x1 x2 => iprop(<affine> ⌜φ k x1 x2⌝ : PROP)) l1 l2 :=
                affinely_pure_2 hlen
            _ ⊢ bigSepL2 (fun k x1 x2 => iprop(⌜φ k x1 x2⌝ : PROP)) l1 l2 := by
                apply mono; intro k x1 x2 _ _
                exact affinely_elim

/-! ## Unit/Emp Lemma -/

theorem emp_l [BIAffine PROP] {l1 : List A} {l2 : List B} :
    bigSepL2 (fun _ _ _ => (emp : PROP)) l1 l2 ⊣⊢ iprop(⌜l1.length = l2.length⌝) := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil =>
      simp only [bigSepL2]
      exact (true_emp (PROP := PROP)).symm.trans (pure_true (PROP := PROP) rfl).symm
    | cons => simp only [bigSepL2]; exact BI.equiv_entails.mpr ⟨false_elim, pure_elim' (fun h => nomatch h)⟩
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact BI.equiv_entails.mpr ⟨false_elim, pure_elim' (fun h => nomatch h)⟩
    | cons x2 xs2 =>
      simp only [bigSepL2, List.length_cons]
      calc iprop(emp ∗ bigSepL2 (fun _ _ _ => emp) xs1 xs2)
          ⊣⊢ bigSepL2 (fun _ _ _ => (emp : PROP)) xs1 xs2 := emp_sep
        _ ⊣⊢ iprop(⌜xs1.length = xs2.length⌝) := ih
        _ ⊣⊢ iprop(⌜xs1.length + 1 = xs2.length + 1⌝) := BI.equiv_entails.mpr ⟨pure_mono (congrArg (· + 1)),
            pure_mono Nat.succ.inj⟩

/-! ## App Lemma -/

/-- bi-entailment version when we know one pair of lengths match. -/
theorem app {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length) :
    bigSepL2 Φ (l1a ++ l1b) (l2a ++ l2b) ⊣⊢
      bigSepL2 Φ l1a l2a ∗ bigSepL2 (fun n => Φ (n + l1a.length)) l1b l2b := by
  induction l1a generalizing l2a Φ with
  | nil =>
    cases l2a with
    | nil =>
      simp only [bigSepL2, List.nil_append, List.length_nil, Nat.add_zero]
      exact emp_sep.symm
    | cons => simp at hlen
  | cons x1 xs1 ih =>
    cases l2a with
    | nil => simp at hlen
    | cons x2 xs2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [bigSepL2, List.cons_append, List.length_cons]
      have ihspec := ih (Φ := fun n => Φ (n + 1)) (l2a := xs2) hlen
      -- ihspec : bigSepL2 (Φ (·+1)) (xs1++l1b) (xs2++l2b) ⊣⊢
      --          bigSepL2 (Φ (·+1)) xs1 xs2 ∗ bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1b l2b
      -- We need to convert between (n + xs1.length + 1) and (n + (xs1.length + 1))
      have hcongr : bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1b l2b ⊣⊢
                   bigSepL2 (fun n => Φ (n + (xs1.length + 1))) l1b l2b :=
        congr fun n _ _ => by simp only [Nat.add_assoc]; exact OFE.Equiv.rfl
      calc iprop(Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) (xs1 ++ l1b) (xs2 ++ l2b))
          ⊣⊢ iprop(Φ 0 x1 x2 ∗ (bigSepL2 (fun n => Φ (n + 1)) xs1 xs2 ∗
              bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1b l2b)) := sep_congr OFE.Equiv.rfl ihspec
        _ ⊣⊢ iprop(Φ 0 x1 x2 ∗ (bigSepL2 (fun n => Φ (n + 1)) xs1 xs2 ∗
              bigSepL2 (fun n => Φ (n + (xs1.length + 1))) l1b l2b)) :=
            sep_congr OFE.Equiv.rfl (sep_congr OFE.Equiv.rfl hcongr)
        _ ⊣⊢ iprop((Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2) ∗
              bigSepL2 (fun n => Φ (n + (xs1.length + 1))) l1b l2b) := sep_assoc.symm

theorem app_inv {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length) :
    bigSepL2 Φ (l1a ++ l1b) (l2a ++ l2b) ⊣⊢
      bigSepL2 Φ l1a l2a ∗ bigSepL2 (fun n => Φ (n + l1a.length)) l1b l2b := by
  exact app hlen

/-! ## Snoc Lemma -/

theorem snoc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {x : A} {y : B}
    (hlen : l1.length = l2.length) :
    bigSepL2 Φ (l1 ++ [x]) (l2 ++ [y]) ⊣⊢
      bigSepL2 Φ l1 l2 ∗ Φ l1.length x y := by
  have h := app (Φ := Φ) (l1b := [x]) (l2b := [y]) hlen
  simp only [bigSepL2] at h
  -- h : bigSepL2 Φ (l1 ++ [x]) (l2 ++ [y]) ⊣⊢ bigSepL2 Φ l1 l2 ∗ (Φ (0 + l1.length) x y ∗ emp)
  calc bigSepL2 Φ (l1 ++ [x]) (l2 ++ [y])
      ⊣⊢ bigSepL2 Φ l1 l2 ∗ (Φ (0 + l1.length) x y ∗ emp) := h
    _ ⊣⊢ bigSepL2 Φ l1 l2 ∗ Φ (0 + l1.length) x y := sep_congr OFE.Equiv.rfl sep_emp
    _ ⊣⊢ bigSepL2 Φ l1 l2 ∗ Φ l1.length x y := by simp only [Nat.zero_add]; exact OFE.Equiv.rfl

/-! ## Fmap Lemmas -/

theorem fmap_l {C : Type _} (f : C → A) {Φ : Nat → A → B → PROP}
    {l1 : List C} {l2 : List B} :
    bigSepL2 Φ (l1.map f) l2 ⊣⊢ bigSepL2 (fun k x y => Φ k (f x) y) l1 l2 := by
  induction l1 generalizing l2 Φ with
  | nil =>
    cases l2 with
    | nil => simp only [List.map_nil, bigSepL2]; exact OFE.Equiv.rfl
    | cons => simp only [List.map_nil, bigSepL2]; exact OFE.Equiv.rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [List.map_cons, bigSepL2]; exact OFE.Equiv.rfl
    | cons x2 xs2 =>
      simp only [List.map_cons, bigSepL2]
      exact sep_congr OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

theorem fmap_r {C : Type _} (f : C → B) {Φ : Nat → A → B → PROP}
    {l1 : List A} {l2 : List C} :
    bigSepL2 Φ l1 (l2.map f) ⊣⊢ bigSepL2 (fun k x y => Φ k x (f y)) l1 l2 := by
  induction l1 generalizing l2 Φ with
  | nil =>
    cases l2 with
    | nil => simp only [List.map_nil, bigSepL2]; exact OFE.Equiv.rfl
    | cons => simp only [List.map_cons, bigSepL2]; exact OFE.Equiv.rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [List.map_nil, bigSepL2]; exact OFE.Equiv.rfl
    | cons x2 xs2 =>
      simp only [List.map_cons, bigSepL2]
      exact sep_congr OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

theorem fmap {C D : Type _} (f : C → A) (g : D → B) {Φ : Nat → A → B → PROP}
    {l1 : List C} {l2 : List D} :
    bigSepL2 Φ (l1.map f) (l2.map g) ⊣⊢ bigSepL2 (fun k x y => Φ k (f x) (g y)) l1 l2 := by
  calc bigSepL2 Φ (l1.map f) (l2.map g)
      ⊣⊢ bigSepL2 (fun k x y => Φ k (f x) y) l1 (l2.map g) := fmap_l f
    _ ⊣⊢ bigSepL2 (fun k x y => Φ k (f x) (g y)) l1 l2 := fmap_r g

/-! ## Flip Lemma -/

theorem flip {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    bigSepL2 (fun k x y => Φ k y x) l2 l1 ⊣⊢ bigSepL2 Φ l1 l2 := by
  induction l1 generalizing l2 Φ with
  | nil =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact OFE.Equiv.rfl
    | cons => simp only [bigSepL2]; exact OFE.Equiv.rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact OFE.Equiv.rfl
    | cons x2 xs2 =>
      simp only [bigSepL2]
      exact sep_congr OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

/-! ## Fst/Snd Lemma -/

theorem fst_snd {Φ : Nat → A → B → PROP} {l : List (A × B)} :
    bigSepL2 Φ (l.map Prod.fst) (l.map Prod.snd) ⊣⊢
      bigSepL (fun k p => Φ k p.1 p.2) l := by
  -- Using big_sepL2_alt and properties of zip and fmap
  calc bigSepL2 Φ (l.map Prod.fst) (l.map Prod.snd)
      ⊣⊢ iprop(⌜(l.map Prod.fst).length = (l.map Prod.snd).length⌝ ∧
          bigSepL (fun k p => Φ k p.1 p.2) ((l.map Prod.fst).zip (l.map Prod.snd))) := alt
    _ ⊣⊢ iprop(⌜l.length = l.length⌝ ∧
          bigSepL (fun k p => Φ k p.1 p.2) ((l.map Prod.fst).zip (l.map Prod.snd))) := by
        simp only [List.length_map]; exact OFE.Equiv.rfl
    _ ⊣⊢ iprop(⌜True⌝ ∧
          bigSepL (fun k p => Φ k p.1 p.2) ((l.map Prod.fst).zip (l.map Prod.snd))) := by
        apply and_congr
        · exact pure_true (PROP := PROP) rfl
        · exact OFE.Equiv.rfl
    _ ⊣⊢ bigSepL (fun k p => Φ k p.1 p.2) ((l.map Prod.fst).zip (l.map Prod.snd)) :=
        true_and (PROP := PROP)
    _ ⊣⊢ bigSepL (fun k p => Φ k p.1 p.2) l := by
        -- Need to show that (l.map fst).zip (l.map snd) = l for pairs
        have : (l.map Prod.fst).zip (l.map Prod.snd) = l := by
          induction l with
          | nil => rfl
          | cons hd tl ih => simp only [List.map_cons, List.zip_cons_cons, ih, Prod.eta]
        rw [this]

/-! ## App Inverse Lemmas -/

/-- When we have bigSepL2 of l1' ++ l1'' with some l2, we can split l2 to match. -/
theorem app_inv_l {Φ : Nat → A → B → PROP} {l1' l1'' : List A} {l2 : List B} :
    bigSepL2 Φ (l1' ++ l1'') l2 ⊢
      iprop(∃ l2' l2'', ⌜l2 = l2' ++ l2''⌝ ∧
        (bigSepL2 Φ l1' l2' ∗ bigSepL2 (fun n => Φ (n + l1'.length)) l1'' l2'')) := by
  -- Introduce existential witnesses: l2' = take (length l1') l2, l2'' = drop (length l1') l2
  -- Then prove the result by induction
  induction l1' generalizing l2 Φ with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    -- Need: bigSepL2 Φ l1'' l2 ⊢ ∃ l2' l2'', ⌜l2 = l2' ++ l2''⌝ ∧ (bigSepL2 Φ [] l2' ∗ bigSepL2 Φ l1'' l2'')
    -- Choose l2' = [], l2'' = l2
    -- Note: bigSepL2 Φ [] [] = emp
    calc bigSepL2 Φ l1'' l2
        ⊢ iprop(emp ∗ bigSepL2 Φ l1'' l2) := (BI.equiv_entails.mp emp_sep.symm).1
      _ ⊢ iprop(bigSepL2 Φ [] [] ∗ bigSepL2 Φ l1'' l2) := sep_mono_l (BI.equiv_entails.mp nil.symm).1
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
            (BI.equiv_entails.mp sep_exists_l).1
        _ ⊢ iprop(∃ l2', ∃ l2'', Φ 0 x1 x2 ∗ (⌜xs2 = l2' ++ l2''⌝ ∧
              (bigSepL2 (fun n => Φ (n + 1)) xs1 l2' ∗
               bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2''))) :=
            exists_mono fun _ => (BI.equiv_entails.mp sep_exists_l).1
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
                    sep_mono_r (BI.equiv_entails.mp persistent_and_affinely_sep_l).1
                _ ⊢ iprop((Φ 0 x1 x2 ∗ <affine> ⌜xs2 = l2'_tail ++ l2''⌝) ∗
                      (bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail ∗
                       bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2'')) :=
                    (BI.equiv_entails.mp sep_assoc.symm).1
                _ ⊢ iprop((<affine> ⌜xs2 = l2'_tail ++ l2''⌝ ∗ Φ 0 x1 x2) ∗
                      (bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail ∗
                       bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2'')) :=
                    sep_mono_l (BI.equiv_entails.mp sep_comm).1
                _ ⊢ iprop(<affine> ⌜xs2 = l2'_tail ++ l2''⌝ ∗
                      (Φ 0 x1 x2 ∗ (bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail ∗
                       bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2''))) :=
                    (BI.equiv_entails.mp sep_assoc).1
                _ ⊢ iprop(<affine> ⌜xs2 = l2'_tail ++ l2''⌝ ∗
                      ((Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail) ∗
                       bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2'')) :=
                    sep_mono_r (BI.equiv_entails.mp sep_assoc.symm).1
                _ ⊢ iprop(⌜xs2 = l2'_tail ++ l2''⌝ ∧
                      ((Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 l2'_tail) ∗
                       bigSepL2 (fun n => Φ (n + xs1.length + 1)) l1'' l2'')) :=
                    (BI.equiv_entails.mp persistent_and_affinely_sep_l.symm).1
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
    bigSepL2 Φ l1 (l2' ++ l2'') ⊢
      iprop(∃ l1' l1'', ⌜l1 = l1' ++ l1''⌝ ∧
        (bigSepL2 Φ l1' l2' ∗ bigSepL2 (fun n => Φ (n + l2'.length)) l1'' l2'')) := by
  -- By symmetry with app_inv_l, using flip
  calc bigSepL2 Φ l1 (l2' ++ l2'')
      ⊢ bigSepL2 (fun k x y => Φ k y x) (l2' ++ l2'') l1 := (BI.equiv_entails.mp flip.symm).1
    _ ⊢ iprop(∃ l1' l1'', ⌜l1 = l1' ++ l1''⌝ ∧
          (bigSepL2 (fun k x y => Φ k y x) l2' l1' ∗
           bigSepL2 (fun n x y => Φ (n + l2'.length) y x) l2'' l1'')) := app_inv_l
    _ ⊢ iprop(∃ l1' l1'', ⌜l1 = l1' ++ l1''⌝ ∧
          (bigSepL2 Φ l1' l2' ∗ bigSepL2 (fun n => Φ (n + l2'.length)) l1'' l2'')) := by
        apply exists_mono; intro l1'
        apply exists_mono; intro l1''
        apply and_mono Entails.rfl
        apply sep_mono
        · exact (BI.equiv_entails.mp flip).1
        · exact (BI.equiv_entails.mp flip).1

/-! ## Lookup/Access Lemmas -/

/-- Lookup access pattern: extract element at index i and get a wand to restore. -/
theorem lookup_acc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    bigSepL2 Φ l1 l2 ⊢
      iprop(Φ i x1 x2 ∗ (Φ i x1 x2 -∗ bigSepL2 Φ l1 l2)) := by
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
        exact sep_mono_r (wand_intro ((BI.equiv_entails.mp sep_comm).1))
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
              (BI.equiv_entails.mp sep_assoc.symm).1
          _ ⊢ iprop((Φ (j + 1) x1 x2 ∗ Φ 0 y1 y2) ∗
                (Φ (j + 1) x1 x2 -∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2)) :=
              sep_mono_l (BI.equiv_entails.mp sep_comm).1
          _ ⊢ iprop(Φ (j + 1) x1 x2 ∗ (Φ 0 y1 y2 ∗
                (Φ (j + 1) x1 x2 -∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2))) :=
              (BI.equiv_entails.mp sep_assoc).1
          _ ⊢ iprop(Φ (j + 1) x1 x2 ∗
                (Φ (j + 1) x1 x2 -∗ (Φ 0 y1 y2 ∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2))) := by
              apply sep_mono_r
              apply wand_intro
              calc iprop((Φ 0 y1 y2 ∗ (Φ (j + 1) x1 x2 -∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2)) ∗
                      Φ (j + 1) x1 x2)
                  ⊢ iprop(Φ 0 y1 y2 ∗ ((Φ (j + 1) x1 x2 -∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2) ∗
                      Φ (j + 1) x1 x2)) := (BI.equiv_entails.mp sep_assoc).1
                _ ⊢ iprop(Φ 0 y1 y2 ∗ (Φ (j + 1) x1 x2 ∗
                      (Φ (j + 1) x1 x2 -∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2))) :=
                    sep_mono_r (BI.equiv_entails.mp sep_comm).1
                _ ⊢ iprop(Φ 0 y1 y2 ∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2) :=
                    sep_mono_r wand_elim_r

/-- Lookup lemma with Absorbing: extract element at index i (discarding the wand). -/
theorem lookup_absorbing {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    [Absorbing (Φ i x1 x2)]
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    bigSepL2 Φ l1 l2 ⊢ Φ i x1 x2 :=
  (lookup_acc h1 h2).trans sep_elim_l

/-- Lookup lemma with BIAffine: extract element at index i (discarding the wand). -/
theorem lookup [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    bigSepL2 Φ l1 l2 ⊢ Φ i x1 x2 :=
  (lookup_acc h1 h2).trans sep_elim_l

/-- Insert access pattern: extract element at index i and get a wand to restore with updated values.
    Corresponds to big_sepL2_insert_acc in Rocq. -/
theorem insert_acc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    bigSepL2 Φ l1 l2 ⊢
      iprop(Φ i x1 x2 ∗ (∀ y1, ∀ y2, Φ i y1 y2 -∗ bigSepL2 Φ (l1.set i y1) (l2.set i y2))) := by
  -- Following the Coq proof structure:
  -- 1. Rewrite using alt to get ⌜length⌝ ∧ bigSepL over zip
  -- 2. Use pure_elim_l to extract the length condition
  -- 3. Apply BigSepL.insert_acc on the zipped list
  -- 4. Transform the result using the relationship between zip and set

  -- Step 1: Convert to alternative form using zip
  calc bigSepL2 Φ l1 l2
      ⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) :=
        (BI.equiv_entails.mp alt).1
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
                          (BI.equiv_entails.mp alt).2

/-! ## Higher-Order Lemmas -/

/-- Introduction rule: from a persistent implication, construct bigSepL2.
    Corresponds to big_sepL2_intro in Rocq. -/
theorem intro {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (hlen : l1.length = l2.length) :
    iprop(□ (∀ k, ∀ x1, ∀ x2, iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2))) ⊢
      bigSepL2 Φ l1 l2 := by
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
        (BI.equiv_entails.mp intuitionistically_sep_idem.symm).1
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

theorem wand {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    bigSepL2 Φ l1 l2 ⊢ bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 -∗ Ψ k x1 x2)) l1 l2 -∗
      bigSepL2 Ψ l1 l2 := by
  apply wand_intro
  calc iprop(bigSepL2 Φ l1 l2 ∗ bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 -∗ Ψ k x1 x2)) l1 l2)
      ⊢ bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 ∗ (Φ k x1 x2 -∗ Ψ k x1 x2))) l1 l2 :=
        (BI.equiv_entails.mp sep_2).1
    _ ⊢ bigSepL2 Ψ l1 l2 := mono fun _ _ _ _ _ => wand_elim_r

/-! ## impl: Specialized Introduction from Persistent Wand Implication -/

theorem impl {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    bigSepL2 Φ l1 l2 ⊢ iprop(□ (∀ k, ∀ x1, ∀ x2,
        iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2))) -∗
      bigSepL2 Ψ l1 l2 := by
  -- Following Rocq: use idemp on and, extract length, use intro to build wands, combine
  apply wand_intro
  -- We need to show: bigSepL2 Φ l1 l2 ∗ □(∀ k x1 x2, ⌜...⌝ → ⌜...⌝ → Φ -∗ Ψ) ⊢ bigSepL2 Ψ l1 l2
  -- Step 1: Get the length hypothesis from bigSepL2 Φ l1 l2
  -- Use P ⊢ P ∧ P (and_self), then extract length from one copy
  have hlen_extract : bigSepL2 Φ l1 l2 ⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL2 Φ l1 l2) :=
    (BI.equiv_entails.mp and_self).2.trans (and_mono_l length)
  calc iprop(bigSepL2 Φ l1 l2 ∗ □ (∀ k, ∀ x1, ∀ x2,
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
              sep_mono_l (BI.equiv_entails.mp persistent_and_affinely_sep_l).1
          _ ⊢ iprop(<affine> ⌜l1.length = l2.length⌝ ∗ (bigSepL2 Φ l1 l2 ∗
                □ (∀ k, ∀ x1, ∀ x2,
                  iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2)))) :=
              (BI.equiv_entails.mp sep_assoc).1
          _ ⊢ iprop(⌜l1.length = l2.length⌝ ∧ (bigSepL2 Φ l1 l2 ∗
                □ (∀ k, ∀ x1, ∀ x2,
                  iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2)))) :=
              (BI.equiv_entails.mp persistent_and_affinely_sep_l.symm).1
    _ ⊢ bigSepL2 Ψ l1 l2 := by
        apply pure_elim_l; intro hlen
        -- Now we have: bigSepL2 Φ l1 l2 ∗ □(...) ⊢ bigSepL2 Ψ l1 l2
        -- Use intro to convert □(...) to bigSepL2 of wands
        have hwands : iprop(□ (∀ k, ∀ x1, ∀ x2,
                iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2)))
            ⊢ bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 -∗ Ψ k x1 x2)) l1 l2 :=
          intro hlen
        calc iprop(bigSepL2 Φ l1 l2 ∗
                □ (∀ k, ∀ x1, ∀ x2,
                  iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2)))
            ⊢ iprop(bigSepL2 Φ l1 l2 ∗
                bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 -∗ Ψ k x1 x2)) l1 l2) :=
              sep_mono_r hwands
          _ ⊢ bigSepL2 (fun k x1 x2 => iprop(Φ k x1 x2 ∗ (Φ k x1 x2 -∗ Ψ k x1 x2))) l1 l2 :=
              (BI.equiv_entails.mp sep_2).1
          _ ⊢ bigSepL2 Ψ l1 l2 := mono fun _ _ _ _ _ => wand_elim_r

/-- bigSepL2 of persistent propositions is equivalent to a conjunction of length and forall. -/
theorem forall' [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    [∀ k x1 x2, Persistent (Φ k x1 x2)] :
    bigSepL2 Φ l1 l2 ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧
        (∀ k, ∀ x1, ∀ x2, iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2))) := by
  apply BI.equiv_entails.mpr; constructor
  · -- Forward direction
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
        -- Need: ∀ k x1 x2, ⌜...⌝ → ⌜...⌝ → Φ k x1 x2 ⊢ Φ 0 y1 y2 ∗ bigSepL2 (Φ (·+1)) ys1 ys2
        -- When Φ is persistent, we can duplicate it
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
              (BI.equiv_entails.mp and_self).2.trans (and_mono_l head_step)
          _ ⊢ iprop(Φ 0 y1 y2 ∗ (∀ k, ∀ x1, ∀ x2,
                iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))) :=
              persistent_and_sep_1
          _ ⊢ iprop(Φ 0 y1 y2 ∗ (∀ k, ∀ x1, ∀ x2,
                iprop(⌜ys1[k]? = some x1⌝ → ⌜ys2[k]? = some x2⌝ → Φ (k + 1) x1 x2))) :=
              sep_mono_r tail_step
          _ ⊢ iprop(Φ 0 y1 y2 ∗ bigSepL2 (fun n => Φ (n + 1)) ys1 ys2) :=
              sep_mono_r (ih hlen)

/-! ## Modality Interaction -/

/-- Persistently modality distributes over bigSepL2. -/
theorem persistently [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    iprop(<pers> bigSepL2 Φ l1 l2) ⊣⊢ bigSepL2 (fun k x1 x2 => iprop(<pers> Φ k x1 x2)) l1 l2 := by
  calc iprop(<pers> bigSepL2 Φ l1 l2)
      ⊣⊢ iprop(<pers> (⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2))) :=
        persistently_congr alt
    _ ⊣⊢ iprop(<pers> ⌜l1.length = l2.length⌝ ∧ <pers> bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) :=
        persistently_and
    _ ⊣⊢ iprop(⌜l1.length = l2.length⌝ ∧ <pers> bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) :=
        and_congr persistently_pure OFE.Equiv.rfl
    _ ⊣⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => iprop(<pers> Φ k p.1 p.2)) (l1.zip l2)) :=
        and_congr OFE.Equiv.rfl BigSepL.persistently
    _ ⊣⊢ bigSepL2 (fun k x1 x2 => iprop(<pers> Φ k x1 x2)) l1 l2 :=
        OFE.Equiv.symm (alt (Φ := fun k x1 x2 => iprop(<pers> Φ k x1 x2)))

/-- Later modality through bigSepL2 (one direction, no BIAffine needed). -/
theorem later_2 {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    bigSepL2 (fun k x1 x2 => iprop(▷ Φ k x1 x2)) l1 l2 ⊢ iprop(▷ bigSepL2 Φ l1 l2) := by
  calc bigSepL2 (fun k x1 x2 => iprop(▷ Φ k x1 x2)) l1 l2
      ⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => iprop(▷ Φ k p.1 p.2)) (l1.zip l2)) :=
        (BI.equiv_entails.mp (alt (Φ := fun k x1 x2 => iprop(▷ Φ k x1 x2)))).1
    _ ⊢ iprop(⌜l1.length = l2.length⌝ ∧ ▷ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) :=
        and_mono Entails.rfl BigSepL.later_2
    _ ⊢ iprop(▷ ⌜l1.length = l2.length⌝ ∧ ▷ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) := by
        apply and_mono _ Entails.rfl
        exact later_intro
    _ ⊢ iprop(▷ (⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2))) := by
        exact (BI.equiv_entails.mp later_and).2
    _ ⊢ iprop(▷ bigSepL2 Φ l1 l2) := by
        apply later_mono
        exact (BI.equiv_entails.mp alt).2

/-- LaterN modality through bigSepL2 (one direction, no BIAffine needed). -/
theorem laterN_2 {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {n : Nat} :
    bigSepL2 (fun k x1 x2 => iprop(▷^[n] Φ k x1 x2)) l1 l2 ⊢ iprop(▷^[n] bigSepL2 Φ l1 l2) := by
  induction n with
  | zero => exact Entails.rfl
  | succ m ih =>
    calc bigSepL2 (fun k x1 x2 => iprop(▷ ▷^[m] Φ k x1 x2)) l1 l2
        ⊢ iprop(▷ bigSepL2 (fun k x1 x2 => iprop(▷^[m] Φ k x1 x2)) l1 l2) := later_2
      _ ⊢ iprop(▷ ▷^[m] bigSepL2 Φ l1 l2) := later_mono ih

/-! ## Interaction with BigSepL -/

/-- BigSepL2 over separated predicates is equivalent to separating two BigSepLs. -/
theorem sepL {Φ1 : Nat → A → PROP} {Φ2 : Nat → B → PROP} {l1 : List A} {l2 : List B}
    (hlen : l1.length = l2.length) :
    bigSepL2 (fun k x1 x2 => iprop(Φ1 k x1 ∗ Φ2 k x2)) l1 l2 ⊣⊢
      bigSepL Φ1 l1 ∗ bigSepL Φ2 l2 := by
  calc bigSepL2 (fun k x1 x2 => iprop(Φ1 k x1 ∗ Φ2 k x2)) l1 l2
      ⊣⊢ iprop(⌜l1.length = l2.length⌝ ∧
          bigSepL (fun k p => iprop(Φ1 k p.1 ∗ Φ2 k p.2)) (l1.zip l2)) := alt
    _ ⊣⊢ bigSepL (fun k p => iprop(Φ1 k p.1 ∗ Φ2 k p.2)) (l1.zip l2) := by
        apply BI.equiv_entails.mpr; constructor
        · exact and_elim_r
        · exact and_intro (pure_intro hlen) Entails.rfl
    _ ⊣⊢ bigSepL Φ1 l1 ∗ bigSepL Φ2 l2 := BigSepL.sep_zip hlen

/-- BigSepL2 can be constructed from two BigSepLs. -/
theorem sepL_2 {Φ1 : Nat → A → PROP} {Φ2 : Nat → B → PROP} {l1 : List A} {l2 : List B}
    (hlen : l1.length = l2.length) :
    ⊢ bigSepL Φ1 l1 -∗ bigSepL Φ2 l2 -∗
      bigSepL2 (fun k x1 x2 => iprop(Φ1 k x1 ∗ Φ2 k x2)) l1 l2 := by
  apply entails_wand
  apply wand_intro'
  calc iprop(bigSepL Φ2 l2 ∗ bigSepL Φ1 l1)
      ⊢ iprop(bigSepL Φ1 l1 ∗ bigSepL Φ2 l2) := (BI.equiv_entails.mp sep_comm).1
    _ ⊢ bigSepL2 (fun k x1 x2 => iprop(Φ1 k x1 ∗ Φ2 k x2)) l1 l2 := (BI.equiv_entails.mp (sepL hlen)).2

/-! ## Reverse Lemmas -/

/-- BigSepL2 over reversed lists (one direction).
    Note: This lemma requires that the lists have equal length, which is implicit in
    the well-formedness of bigSepL2. -/
theorem reverse_2 {Φ : A → B → PROP} {l1 : List A} {l2 : List B}
    (hlen : l1.length = l2.length) :
    bigSepL2 (fun _ x1 x2 => Φ x1 x2) l1 l2 ⊢
      bigSepL2 (fun _ x1 x2 => Φ x1 x2) l1.reverse l2.reverse := by
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
      calc iprop(Φ x1 x2 ∗ bigSepL2 (fun _ => Φ) xs1 xs2)
          ⊢ iprop(bigSepL2 (fun _ => Φ) xs1 xs2 ∗ Φ x1 x2) :=
            (BI.equiv_entails.mp sep_comm).1
        _ ⊢ iprop(bigSepL2 (fun _ => Φ) xs1.reverse xs2.reverse ∗ Φ x1 x2) :=
            sep_mono_l (ih xs_len)
        _ ⊢ iprop(bigSepL2 (fun _ => Φ) xs1.reverse xs2.reverse ∗
                   bigSepL2 (fun _ => Φ) [x1] [x2]) := by
            apply sep_mono_r
            simp only [bigSepL2]
            exact (BI.equiv_entails.mp sep_emp).2
        _ ⊢ bigSepL2 (fun _ => Φ) (xs1.reverse ++ [x1]) (xs2.reverse ++ [x2]) := by
            -- Use snoc with equal lengths
            have rev_len : xs1.reverse.length = xs2.reverse.length := by
              simp only [List.length_reverse, xs_len]
            have h := snoc (Φ := fun _ => Φ) (l1 := xs1.reverse) (l2 := xs2.reverse)
                           (x := x1) (y := x2) rev_len
            calc iprop(bigSepL2 (fun _ => Φ) xs1.reverse xs2.reverse ∗
                      bigSepL2 (fun _ => Φ) [x1] [x2])
                ⊢ iprop(bigSepL2 (fun _ => Φ) xs1.reverse xs2.reverse ∗ Φ x1 x2) := by
                  apply sep_mono_r
                  simp only [bigSepL2]
                  exact (BI.equiv_entails.mp sep_emp).1
              _ ⊢ iprop(bigSepL2 (fun _ => Φ) xs1.reverse xs2.reverse ∗
                      (fun _ => Φ) xs1.reverse.length x1 x2) :=
                  Entails.rfl
              _ ⊢ bigSepL2 (fun _ => Φ) (xs1.reverse ++ [x1]) (xs2.reverse ++ [x2]) :=
                  (BI.equiv_entails.mp h).2

/-- BigSepL2 over reversed lists (equivalence). -/
theorem reverse {Φ : A → B → PROP} {l1 : List A} {l2 : List B}
    (hlen : l1.length = l2.length) :
    bigSepL2 (fun _ x1 x2 => Φ x1 x2) l1.reverse l2.reverse ⊣⊢
      bigSepL2 (fun _ x1 x2 => Φ x1 x2) l1 l2 := by
  apply BI.equiv_entails.mpr; constructor
  · -- reverse.reverse = id
    have rev_len : l1.reverse.length = l2.reverse.length := by
      simp only [List.length_reverse, hlen]
    have h1 := reverse_2 (Φ := Φ) (l1 := l1.reverse) (l2 := l2.reverse) rev_len
    simp only [List.reverse_reverse] at h1
    exact h1
  · exact reverse_2 hlen

/-! ## Replicate Lemmas -/

/-- BigSepL2 with replicate on the left reduces to BigSepL. -/
theorem replicate_l {Φ : Nat → A → B → PROP} {l : List B} {x : A} {n : Nat}
    (hlen : l.length = n) :
    bigSepL2 Φ (List.replicate n x) l ⊣⊢ bigSepL (fun k x2 => Φ k x x2) l := by
  subst hlen
  induction l generalizing Φ with
  | nil =>
    simp only [List.length_nil, List.replicate_zero, bigSepL2, bigSepL, bigOpL]
    exact OFE.Equiv.rfl
  | cons y ys ih =>
    simp only [List.length_cons, List.replicate_succ, bigSepL2, bigSepL, bigOpL]
    exact sep_congr OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

/-- BigSepL2 with replicate on the right reduces to BigSepL. -/
theorem replicate_r {Φ : Nat → A → B → PROP} {l : List A} {x : B} {n : Nat}
    (hlen : l.length = n) :
    bigSepL2 Φ l (List.replicate n x) ⊣⊢ bigSepL (fun k x1 => Φ k x1 x) l := by
  subst hlen
  induction l generalizing Φ with
  | nil =>
    simp only [List.length_nil, List.replicate_zero, bigSepL2, bigSepL, bigOpL]
    exact OFE.Equiv.rfl
  | cons y ys ih =>
    simp only [List.length_cons, List.replicate_succ, bigSepL2, bigSepL, bigOpL]
    exact sep_congr OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

/-! ## App Same Length -/

/-- App lemma with explicit same-length hypothesis (simplified version). -/
theorem app_same_length {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length) :
    bigSepL2 Φ (l1a ++ l1b) (l2a ++ l2b) ⊣⊢
      iprop(bigSepL2 Φ l1a l2a ∗ bigSepL2 (fun k => Φ (l1a.length + k)) l1b l2b) := by
  have h := app (Φ := Φ) (l1a := l1a) (l2a := l2a) (l1b := l1b) (l2b := l2b) hlen
  calc bigSepL2 Φ (l1a ++ l1b) (l2a ++ l2b)
      ⊣⊢ iprop(bigSepL2 Φ l1a l2a ∗ bigSepL2 (fun n => Φ (n + l1a.length)) l1b l2b) := h
    _ ⊣⊢ iprop(bigSepL2 Φ l1a l2a ∗ bigSepL2 (fun k => Φ (l1a.length + k)) l1b l2b) := by
        apply sep_congr OFE.Equiv.rfl
        apply congr
        intro k x1 x2
        simp only [Nat.add_comm]
        exact OFE.Equiv.rfl

/-! ## Const SepL Lemmas -/

/-- When Φ doesn't depend on the second argument, relate to BigSepL. -/
theorem const_sepL_l {Φ : Nat → A → PROP} {l1 : List A} {l2 : List B} :
    bigSepL2 (fun k x1 _ => Φ k x1) l1 l2 ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ l1) := by
  -- Following Coq: rewrite via alt, then use BigSepL.fmap
  calc bigSepL2 (fun k x1 _ => Φ k x1) l1 l2
      ⊣⊢ iprop(⌜l1.length = l2.length⌝ ∧
          bigSepL (fun k p => Φ k p.1) (l1.zip l2)) := alt
    _ ⊣⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ l1) := by
        -- Following Coq: apply (anti_symm _), then use pure_elim_l for both directions
        apply BI.equiv_entails.mpr; constructor
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
            BigSepL.fmap Prod.fst
          have h2 : bigSepL Φ ((l1.zip l2).map Prod.fst) ⊣⊢ bigSepL Φ l1 := by
            rw [fst_zip]
          exact (BI.equiv_entails.mp (h1.symm.trans h2)).1
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
            rw [fst_zip]
          have h2 : bigSepL Φ ((l1.zip l2).map Prod.fst) ⊣⊢
                     bigSepL (fun k p => Φ k p.1) (l1.zip l2) :=
            BigSepL.fmap Prod.fst
          exact (BI.equiv_entails.mp (h1.trans h2)).1

/-- When Φ doesn't depend on the first argument, relate to BigSepL. -/
theorem const_sepL_r {Φ : Nat → B → PROP} {l1 : List A} {l2 : List B} :
    bigSepL2 (fun k _ x2 => Φ k x2) l1 l2 ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ l2) := by
  -- Following Coq: rewrite using flip, then const_sepL_l, then symmetry of equality
  calc bigSepL2 (fun k _ x2 => Φ k x2) l1 l2
      ⊣⊢ bigSepL2 (fun k x2 _ => Φ k x2) l2 l1 := flip
    _ ⊣⊢ iprop(⌜l2.length = l1.length⌝ ∧ bigSepL Φ l2) := const_sepL_l
    _ ⊣⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ l2) := by
        apply BI.equiv_entails.mpr; constructor
        · apply and_mono
          · apply pure_mono; intro h; exact h.symm
          · exact .rfl
        · apply and_mono
          · apply pure_mono; intro h; exact h.symm
          · exact .rfl

/-! ## Sep SepL Lemmas -/

/-- Separate a term that only depends on l1 from a BigSepL2. -/
theorem sep_sepL_l [BIAffine PROP] {Φ : Nat → A → PROP} {Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    bigSepL2 (fun k x1 x2 => iprop(Φ k x1 ∗ Ψ k x1 x2)) l1 l2 ⊣⊢
      iprop(bigSepL Φ l1 ∗ bigSepL2 Ψ l1 l2) := by
  -- Following Coq: rewrite via sep', const_sepL_l, then use and_elim_r
  calc bigSepL2 (fun k x1 x2 => iprop(Φ k x1 ∗ Ψ k x1 x2)) l1 l2
      ⊣⊢ iprop(bigSepL2 (fun k x1 _ => Φ k x1) l1 l2 ∗ bigSepL2 Ψ l1 l2) := sep'
    _ ⊣⊢ iprop((⌜l1.length = l2.length⌝ ∧ bigSepL Φ l1) ∗ bigSepL2 Ψ l1 l2) := by
        apply BI.equiv_entails.mpr; constructor
        · exact sep_mono (BI.equiv_entails.mp const_sepL_l).1 .rfl
        · exact sep_mono (BI.equiv_entails.mp const_sepL_l).2 .rfl
    _ ⊣⊢ iprop(bigSepL Φ l1 ∗ bigSepL2 Ψ l1 l2) := by
        apply BI.equiv_entails.mpr; constructor
        · exact sep_mono and_elim_r .rfl
        · calc iprop(bigSepL Φ l1 ∗ bigSepL2 Ψ l1 l2)
              ⊢ iprop(bigSepL Φ l1 ∗ (⌜l1.length = l2.length⌝ ∗ bigSepL2 Ψ l1 l2)) := by
                  apply sep_mono .rfl
                  calc iprop(bigSepL2 Ψ l1 l2)
                      ⊢ iprop(⌜l1.length = l2.length⌝ ∧ bigSepL2 Ψ l1 l2) :=
                          and_intro BigSepL2.length .rfl
                    _ ⊢ iprop(<affine> ⌜l1.length = l2.length⌝ ∗ bigSepL2 Ψ l1 l2) :=
                          (BI.equiv_entails.mp persistent_and_affinely_sep_l).1
                    _ ⊢ iprop(⌜l1.length = l2.length⌝ ∗ bigSepL2 Ψ l1 l2) :=
                          sep_mono_l affinely_elim
            _ ⊢ iprop((bigSepL Φ l1 ∗ ⌜l1.length = l2.length⌝) ∗ bigSepL2 Ψ l1 l2) :=
                  (BI.equiv_entails.mp sep_assoc).2
            _ ⊢ iprop((⌜l1.length = l2.length⌝ ∧ bigSepL Φ l1) ∗ bigSepL2 Ψ l1 l2) := by
                  apply sep_mono _ .rfl
                  -- bigSepL Φ l1 ∗ ⌜l1.length = l2.length⌝ ⊢ ⌜l1.length = l2.length⌝ ∧ bigSepL Φ l1
                  -- Use persistently_sep_persistently to duplicate persistent pure
                  apply and_intro
                  · calc iprop(bigSepL Φ l1 ∗ ⌜l1.length = l2.length⌝)
                        ⊢ iprop(⌜l1.length = l2.length⌝ ∗ bigSepL Φ l1) :=
                            (BI.equiv_entails.mp sep_comm).1
                      _ ⊢ iprop(<pers> ⌜l1.length = l2.length⌝ ∗ bigSepL Φ l1) :=
                            sep_mono_l persistently_intro
                      _ ⊢ iprop(<pers> ⌜l1.length = l2.length⌝) :=
                            persistently_absorb_l
                      _ ⊢ iprop(⌜l1.length = l2.length⌝) :=
                            persistently_elim
                  · exact sep_elim_l

/-- Separate a term that only depends on l2 from a BigSepL2. -/
theorem sep_sepL_r [BIAffine PROP] {Φ : Nat → B → PROP} {Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    bigSepL2 (fun k x1 x2 => iprop(Φ k x2 ∗ Ψ k x1 x2)) l1 l2 ⊣⊢
      iprop(bigSepL Φ l2 ∗ bigSepL2 Ψ l1 l2) := by
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
                  apply BigSepL.congr; intro k x; exact .rfl
            _ ⊣⊢ iprop(bigSepL Φ l2 ∗ bigSepL2 Ψ l1 l2) := by
                  apply sep_congr .rfl; exact flip

/-! ## Delete Lemmas -/

/-- Delete lemma: extract an element at index i with conditional on remaining elements.
    Following Rocq: uses take_drop_middle and app_same_length. -/
theorem delete {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat}
    {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    bigSepL2 Φ l1 l2 ⊣⊢
      iprop(Φ i x1 x2 ∗ bigSepL2 (fun k y1 y2 =>
        if k = i then emp else Φ k y1 y2) l1 l2) := by
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
        apply sep_congr OFE.Equiv.rfl
        calc bigSepL2 (fun n => Φ (n + 1)) zs1 zs2
            ⊣⊢ bigSepL2 (fun n y1 y2 => if n + 1 = 0 then emp else Φ (n + 1) y1 y2) zs1 zs2 := by
              apply proper
              intro k x1 x2 _ _
              simp only [Nat.add_one_ne_zero, ↓reduceIte]
              exact OFE.Equiv.rfl
          _ ⊣⊢ emp ∗ bigSepL2 (fun n y1 y2 => if n + 1 = 0 then emp else Φ (n + 1) y1 y2) zs1 zs2 := emp_sep.symm
      | succ j =>
        simp only [List.getElem?_cons_succ] at h1 h2
        simp only [bigSepL2]
        have ih' := ih (i := j) (Φ := fun n => Φ (n + 1)) h1 h2
        calc Φ 0 z1 z2 ∗ bigSepL2 (fun n => Φ (n + 1)) zs1 zs2
            ⊣⊢ Φ 0 z1 z2 ∗ (Φ (j + 1) x1 x2 ∗ bigSepL2 (fun k y1 y2 => if k = j then emp else Φ (k + 1) y1 y2) zs1 zs2) :=
              sep_congr OFE.Equiv.rfl ih'
          _ ⊣⊢ Φ (j + 1) x1 x2 ∗ (Φ 0 z1 z2 ∗ bigSepL2 (fun k y1 y2 => if k = j then emp else Φ (k + 1) y1 y2) zs1 zs2) := by
              calc Φ 0 z1 z2 ∗ (Φ (j + 1) x1 x2 ∗ bigSepL2 (fun k y1 y2 => if k = j then emp else Φ (k + 1) y1 y2) zs1 zs2)
                  ⊣⊢ (Φ 0 z1 z2 ∗ Φ (j + 1) x1 x2) ∗ bigSepL2 (fun k y1 y2 => if k = j then emp else Φ (k + 1) y1 y2) zs1 zs2 := sep_assoc.symm
                _ ⊣⊢ (Φ (j + 1) x1 x2 ∗ Φ 0 z1 z2) ∗ bigSepL2 (fun k y1 y2 => if k = j then emp else Φ (k + 1) y1 y2) zs1 zs2 := sep_congr sep_comm OFE.Equiv.rfl
                _ ⊣⊢ Φ (j + 1) x1 x2 ∗ (Φ 0 z1 z2 ∗ bigSepL2 (fun k y1 y2 => if k = j then emp else Φ (k + 1) y1 y2) zs1 zs2) := sep_assoc
          _ ⊣⊢ Φ (j + 1) x1 x2 ∗ bigSepL2 (fun k y1 y2 => if k = j + 1 then emp else Φ k y1 y2) (z1 :: zs1) (z2 :: zs2) := by
              apply sep_congr OFE.Equiv.rfl
              simp only [bigSepL2]
              have hne0 : (0 : Nat) ≠ j + 1 := Nat.zero_ne_add_one j
              simp only [hne0, ↓reduceIte]
              apply sep_congr OFE.Equiv.rfl
              apply proper
              intro k y1 y2 _ _
              by_cases hkj : k = j
              · subst hkj
                simp only [↓reduceIte]
                exact OFE.Equiv.rfl
              · simp only [hkj, ↓reduceIte]
                have hkj' : k + 1 ≠ j + 1 := by omega
                simp only [hkj', ↓reduceIte]
                exact OFE.Equiv.rfl

/-- Delete' lemma using pure implication instead of conditional emp (BiAffine version).
    Corresponds to big_sepL2_delete' in Rocq. -/
theorem delete' [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat}
    {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    bigSepL2 Φ l1 l2 ⊣⊢
      iprop(Φ i x1 x2 ∗ bigSepL2 (fun k y1 y2 => iprop(⌜k ≠ i⌝ → Φ k y1 y2)) l1 l2) := by
  -- Following Rocq: rewrite using delete, then convert (if k = i then emp else Φ) to (⌜k ≠ i⌝ → Φ)
  calc bigSepL2 Φ l1 l2
      ⊣⊢ iprop(Φ i x1 x2 ∗ bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2) :=
        delete h1 h2
    _ ⊣⊢ iprop(Φ i x1 x2 ∗ bigSepL2 (fun k y1 y2 => iprop(⌜k ≠ i⌝ → Φ k y1 y2)) l1 l2) := by
        apply sep_congr OFE.Equiv.rfl
        apply congr
        intro k y1 y2
        by_cases hki : k = i
        · -- k = i: need emp ⊣⊢ ⌜False⌝ → Φ k y1 y2
          subst hki
          simp only [↓reduceIte, ne_eq, not_true_eq_false]
          apply BI.equiv_entails.mpr
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


/-- Lookup with ability to change predicate when restoring.
    This is the most general form: extract element, then restore with a different predicate.
    Corresponds to big_sepL2_lookup_acc_impl in Rocq. -/
theorem lookup_acc_impl {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    bigSepL2 Φ l1 l2 ⊢
      iprop(Φ i x1 x2 ∗ ∀ Ψ, □ (∀ k, ∀ y1, ∀ y2,
        iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
          Φ k y1 y2 -∗ Ψ k y1 y2)) -∗
        Ψ i x1 x2 -∗ bigSepL2 Ψ l1 l2) := by
  -- Use delete to extract element
  have hdel := (BI.equiv_entails.mp (delete (Φ := Φ) h1 h2)).1
  calc bigSepL2 Φ l1 l2
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
        have hdel_psi := (BI.equiv_entails.mp (delete (Φ := Ψ) h1 h2)).2
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
                exact (BI.equiv_entails.mp this).1
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
                  (BI.equiv_entails.mp and_self).2.trans (and_mono_l length)
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
                            sep_mono_l (BI.equiv_entails.mp persistent_and_affinely_sep_l).1
                        _ ⊢ iprop(<affine> ⌜l1.length = l2.length⌝ ∗
                            (bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2 ∗
                            □ (∀ k, ∀ y1, ∀ y2,
                              iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                                Φ k y1 y2 -∗ Ψ k y1 y2)))) :=
                            (BI.equiv_entails.mp sep_assoc).1
                        _ ⊢ iprop(⌜l1.length = l2.length⌝ ∧
                            (bigSepL2 (fun k y1 y2 => if k = i then emp else Φ k y1 y2) l1 l2 ∗
                            □ (∀ k, ∀ y1, ∀ y2,
                              iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
                                Φ k y1 y2 -∗ Ψ k y1 y2)))) :=
                            (BI.equiv_entails.mp persistent_and_affinely_sep_l.symm).1
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
                          exact (BI.equiv_entails.mp sep_emp).1.trans Affine.affine
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

/-- BigSepL over diagonal (l, l) relates to BigSepL2. -/
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
    have h := BigSepL.fmap (PROP := PROP) (Φ := fun k p => Φ k p.1 p.2)
        (fun x => (x, x)) (l := l)
    -- h : bigSepL (fun k p => Φ k p.1 p.2) (l.map (fun x => (x,x))) ⊣⊢ bigSepL (fun k x => Φ k x x) l
    exact h.symm
  -- Now build the full entailment using inner_eq
  calc bigSepL (fun k x => Φ k x x) l
      ⊢ iprop(⌜l.length = l.length⌝ ∧ bigSepL (fun k x => Φ k x x) l) :=
        and_intro (pure_intro rfl) Entails.rfl
    _ ⊢ iprop(⌜l.length = l.length⌝ ∧ bigSepL (fun k p => Φ k p.1 p.2) (l.zip l)) :=
        and_mono Entails.rfl (BI.equiv_entails.mp inner_eq).1
    _ ⊢ bigSepL2 Φ l l := (BI.equiv_entails.mp BigSepL2.alt).2

end BigSepL

end Iris.BI
