/-
Copyright (c) 2026 TODO: fill in author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TODO: fill in author
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.BigOp
public import Batteries.Data.List.Basic
public import Batteries.Data.List.Perm
meta import Iris.Std.RocqPorting

/-!
# OFE structure on lists

The type `List α` carries an OFE whenever `α` does, with the `n`-step
distance lifted pointwise via `List.Forall₂`. Common list operations
(`cons`, `++`, `take`, `drop`, `head?`, `tail`, `lookup`, `reverse`,
`replicate`, `map`, `flatMap`, `flatten`, `zipWith`, ...) are non-expansive
in this OFE. The file also provides the OFE functor `ListOF` and shows that
it is contractive whenever its argument is.
-/

@[expose] public section

/-- `Forall₂` is monotone in its relation argument. -/
theorem List.Forall₂.imp {R S : α → β → Prop} (H : ∀ ⦃x y⦄, R x y → S x y)
    {l : List α} {k : List β} (h : List.Forall₂ R l k) : List.Forall₂ S l k := by
  induction h with | nil => exact .nil | cons hx _ ih => exact .cons (H hx) ih

/-- `Forall₂` of an equivalence relation is itself an equivalence relation. -/
theorem List.Forall₂.equivalence {R : α → α → Prop} (H : Equivalence R) :
    Equivalence (List.Forall₂ R) where
  refl l := by induction l with | nil => exact .nil | cons _ _ ih => exact .cons (H.1 _) ih
  symm h := by induction h with | nil => exact .nil | cons hx _ ih => exact .cons (H.2 hx) ih
  trans {_ _ z} h₁ h₂ := by
    induction h₁ generalizing z with
    | nil => exact h₂
    | cons hx _ ih => let .cons hy hz := h₂; exact .cons (H.3 hx hy) (ih hz)

namespace Iris

open OFE Iris.Algebra

section ofe
variable {α : Type _} [OFE α]

#rocq_ignore list_dist "Inlined into the `OFE (List α)` instance below"

@[rocq_alias list_ofe_mixin]
instance List.instOFE : OFE (List α) where
  Equiv l k := List.Forall₂ Equiv l k
  Dist n l k := List.Forall₂ (Dist n) l k
  dist_eqv := List.Forall₂.equivalence dist_eqv
  equiv_dist {l k} := by
    refine ⟨fun h n => h.imp fun _ _ => Equiv.dist, fun h => ?_⟩
    induction l generalizing k with
    | nil => let .nil := h 0; exact .nil
    | cons _ _ ih =>
      let .cons _ _ := h 0
      exact .cons (equiv_dist.mpr fun n => let .cons hx _ := h n; hx)
        (ih fun n => let .cons _ hl := h n; hl)
  dist_lt h hm := h.imp fun _ _ hd => hd.lt hm

/-- `n`-equivalence on lists is pointwise via `List.Forall₂`. -/
@[rocq_alias list_dist_Forall2]
theorem List.dist_forall₂ {n} {l k : List α} : l ≡{n}≡ k ↔ List.Forall₂ (Dist n) l k := .rfl

#rocq_ignore listO "Use `List` with typeclass inference"

@[rocq_alias cons_ne]
instance List.cons_ne : NonExpansive₂ (List.cons : α → List α → List α) where
  ne _ _ _ hx _ _ hy := List.Forall₂.cons hx hy

@[rocq_alias app_ne]
instance List.append_ne : NonExpansive₂ (HAppend.hAppend : List α → List α → List α) where
  ne _ _ _ hx _ _ hy := by
    induction hx with
    | nil => exact hy
    | cons hh _ ih => exact .cons hh ih

/-- The length of a list is preserved under `n`-equivalence. -/
@[rocq_alias length_ne]
theorem List.length_eq_of_dist {n} {l k : List α} (h : l ≡{n}≡ k) : l.length = k.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

@[rocq_alias tail_ne]
instance List.tail_ne : NonExpansive (List.tail : List α → List α) where
  ne _ _ _ h := by cases h with | nil => exact .nil | cons _ ht => exact ht

@[rocq_alias take_ne]
instance List.take_ne (n : Nat) : NonExpansive (List.take n : List α → List α) where
  ne _ _ _ h := by
    induction h generalizing n with
    | nil => simp
    | cons hh _ ih => cases n with | zero => exact .nil | succ k => exact .cons hh (ih (n := k))

@[rocq_alias drop_ne]
instance List.drop_ne (n : Nat) : NonExpansive (List.drop n : List α → List α) where
  ne _ _ _ h := by
    induction h generalizing n with
    | nil => simp
    | cons hh ht ih => cases n with | zero => exact .cons hh ht | succ k => exact ih (n := k)

@[rocq_alias head_ne]
instance List.head?_ne : NonExpansive (List.head? : List α → Option α) where
  ne _ _ _ h := by cases h with | nil => trivial | cons hh _ => exact hh

@[rocq_alias list_lookup_ne]
instance List.getElem?_ne (i : Nat) : NonExpansive (fun l : List α => l[i]?) where
  ne _ _ _ h := by
    induction h generalizing i with
    | nil => trivial
    | cons hh _ ih => cases i with | zero => exact hh | succ k => exact ih (i := k)

/-- Pointwise characterization of `n`-equivalence on lists via `getElem?`. -/
@[rocq_alias list_dist_lookup]
theorem List.dist_lookup {n} {l₁ l₂ : List α} :
    l₁ ≡{n}≡ l₂ ↔ ∀ i : Nat, l₁[i]? ≡{n}≡ l₂[i]? := by
  refine ⟨fun h i => List.getElem?_ne i |>.ne h, fun h => ?_⟩
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with | nil => exact .nil | cons _ _ => exact (h 0).elim
  | cons _ _ ih =>
    cases l₂ with
    | nil => exact (h 0).elim
    | cons _ _ => exact .cons (h 0) (ih fun i => h (i + 1))

@[rocq_alias list_lookup_total_ne]
instance List.getElem!_ne [Inhabited α] (i : Nat) :
    NonExpansive (fun l : List α => l[i]!) where
  ne _ _ _ h := by
    induction h generalizing i with
    | nil => exact .of_eq rfl
    | cons hh _ ih =>
      cases i with
      | zero => simpa using hh
      | succ k => simpa using ih (i := k)

@[rocq_alias list_insert_ne]
instance List.set_ne (i : Nat) :
    NonExpansive₂ (fun (l : List α) (a : α) => l.set i a) where
  ne _ _ _ hl _ _ ha := by
    induction hl generalizing i with
    | nil => exact .nil
    | cons hh _ ih =>
      cases i with
      | zero => exact .cons ha ‹_›
      | succ k => exact .cons hh (ih (i := k))

@[rocq_alias list_delete_ne]
instance List.eraseIdx_ne (i : Nat) :
    NonExpansive (fun l : List α => l.eraseIdx i) where
  ne _ _ _ hl := by
    induction hl generalizing i with
    | nil => exact .nil
    | cons hh ht ih =>
      cases i with
      | zero => exact ht
      | succ k => exact .cons hh (ih (i := k))

@[rocq_alias option_list_ne]
instance Option.toList_ne : NonExpansive (Option.toList : Option α → List α) where
  ne _ x y h := by cases x <;> cases y <;> simp_all [Option.toList, Option.Forall₂, Dist]

@[rocq_alias last_ne]
instance List.getLast?_ne : NonExpansive (List.getLast? : List α → Option α) where
  ne _ _ _ h := by
    induction h with
    | nil => trivial
    | cons hh ht ih =>
      cases ht with
      | nil => exact hh
      | cons _ _ => simpa using ih

@[rocq_alias replicate_ne]
instance List.replicate_ne (n : Nat) : NonExpansive (List.replicate n : α → List α) where
  ne _ _ _ h := by
    induction n with
    | zero => exact .nil
    | succ _ ih => exact .cons h ih

@[rocq_alias reverse_ne]
instance List.reverse_ne : NonExpansive (List.reverse : List α → List α) where
  ne _ _ _ h := by
    induction h with
    | nil => exact .nil
    | cons hh _ ih =>
      rw [List.reverse_cons, List.reverse_cons]
      exact List.append_ne.ne ih (.cons hh .nil)

@[rocq_alias list_alter_ne]
theorem List.modify_dist {n} (i : Nat) {f₁ f₂ : α → α}
    (hf : ∀ ⦃x y⦄, x ≡{n}≡ y → f₁ x ≡{n}≡ f₂ y)
    {l₁ l₂ : List α} (hl : l₁ ≡{n}≡ l₂) :
    l₁.modify i f₁ ≡{n}≡ l₂.modify i f₂ := by
  induction hl generalizing i with
  | nil => cases i <;> exact .nil
  | cons hh _ ih =>
    cases i with
    | zero => exact .cons (hf hh) ‹_›
    | succ k => exact .cons hh (ih (i := k))

@[rocq_alias list_filter_ne]
theorem List.filter_dist {n} {P₁ P₂ : α → Bool}
    (hP : ∀ ⦃x y⦄, x ≡{n}≡ y → P₁ x = P₂ y)
    {l₁ l₂ : List α} (hl : l₁ ≡{n}≡ l₂) :
    l₁.filter P₁ ≡{n}≡ l₂.filter P₂ := by
  induction hl with
  | nil => exact .nil
  | cons hh _ ih =>
    rw [List.filter_cons, List.filter_cons, hP hh]
    split
    · exact .cons hh ih
    · exact ih

@[rocq_alias cons_dist_inj]
theorem List.cons_injN {n} {x y : α} {l k : List α}
    (h : (x :: l) ≡{n}≡ (y :: k)) : x ≡{n}≡ y ∧ l ≡{n}≡ k :=
  let .cons hx hl := h; ⟨hx, hl⟩

@[rocq_alias nil_dist_eq]
theorem List.nil_dist_eq {n} {l : List α} : l ≡{n}≡ [] ↔ l = [] := by
  refine ⟨fun h => let .nil := h; rfl, ?_⟩
  rintro rfl; exact .nil

@[rocq_alias cons_dist_eq]
theorem List.cons_dist_eq {n} {l k : List α} {y : α} :
    l ≡{n}≡ y :: k → ∃ x l', x ≡{n}≡ y ∧ l' ≡{n}≡ k ∧ l = x :: l' := by
  intro h
  cases l with
  | nil => cases h
  | cons x l' => let .cons hx hl := h; exact ⟨x, l', hx, hl, rfl⟩

@[rocq_alias app_dist_eq]
theorem List.append_dist_eq {n} {l k₁ k₂ : List α} :
    l ≡{n}≡ k₁ ++ k₂ ↔ ∃ k₁' k₂', l = k₁' ++ k₂' ∧ k₁' ≡{n}≡ k₁ ∧ k₂' ≡{n}≡ k₂ := by
  refine ⟨fun h => ?_, fun ⟨_, _, hl, hk₁, hk₂⟩ => hl ▸ List.append_ne.ne hk₁ hk₂⟩
  induction k₁ generalizing l with
  | nil => exact ⟨[], l, rfl, .nil, h⟩
  | cons _ _ ih =>
    obtain ⟨x, l', hx, hl, rfl⟩ := List.cons_dist_eq h
    obtain ⟨a, b, rfl, ha, hb⟩ := ih hl
    exact ⟨x :: a, b, rfl, .cons hx ha, hb⟩

@[rocq_alias list_singleton_dist_eq]
theorem List.singleton_dist_eq {n} {l : List α} {x : α} :
    l ≡{n}≡ [x] ↔ ∃ x', l = [x'] ∧ x' ≡{n}≡ x := by
  refine ⟨fun h => ?_, fun ⟨_, hl, hx⟩ => hl ▸ .cons hx .nil⟩
  obtain ⟨x', _, hx, hl, rfl⟩ := List.cons_dist_eq h
  let .nil := hl
  exact ⟨x', rfl, hx⟩

@[rocq_alias list_ofe_discrete]
instance List.instDiscrete [Discrete α] : Discrete (List α) where
  discrete_0 h := by
    induction h with
    | nil => exact .nil
    | cons hh _ ih => exact .cons (discrete_0 hh) ih

@[rocq_alias nil_discrete]
instance List.nil_discrete : DiscreteE (([] : List α)) where
  discrete h := by cases h; exact .nil

@[rocq_alias cons_discrete]
instance List.cons_discrete {x : α} {l : List α} [DiscreteE x] [DiscreteE l] :
    DiscreteE (x :: l) where
  discrete h := by
    let .cons hx hl := h
    exact .cons (DiscreteE.discrete hx) (DiscreteE.discrete (x := l) hl)

@[rocq_alias dist_Permutation]
theorem List.dist_perm {n} {l₁ l₂ l₃ : List α}
    (heq : l₁ ≡{n}≡ l₂) (hperm : l₂.Perm l₃) :
    ∃ l₂', l₁.Perm l₂' ∧ l₂' ≡{n}≡ l₃ := by
  induction hperm generalizing l₁ with
  | nil => exact ⟨l₁, .refl _, heq⟩
  | cons _ _ ih =>
    obtain ⟨x', _, hx, hl, rfl⟩ := List.cons_dist_eq heq
    obtain ⟨_, hp, hd⟩ := ih hl
    exact ⟨x' :: _, .cons _ hp, .cons hx hd⟩
  | swap _ _ _ =>
    obtain ⟨y', _, hy, hh, rfl⟩ := List.cons_dist_eq heq
    obtain ⟨x', _, hx, hl, rfl⟩ := List.cons_dist_eq hh
    exact ⟨x' :: y' :: _, .swap _ _ _, .cons hx (.cons hy hl)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨_, hp1, hd1⟩ := ih1 heq
    obtain ⟨_, hp2, hd2⟩ := ih2 hd1
    exact ⟨_, hp1.trans hp2, hd2⟩

end ofe

/-! ## Non-expansiveness of higher-order list functions -/

@[rocq_alias list_fmap_ne]
theorem List.map_dist {α β : Type _} [OFE α] [OFE β] {n}
    {f₁ f₂ : α → β} (hf : ∀ ⦃x y⦄, x ≡{n}≡ y → f₁ x ≡{n}≡ f₂ y)
    {l₁ l₂ : List α} (hl : l₁ ≡{n}≡ l₂) : l₁.map f₁ ≡{n}≡ l₂.map f₂ := by
  induction hl with
  | nil => exact .nil
  | cons hh _ ih => exact .cons (hf hh) ih

@[rocq_alias list_bind_ne]
theorem List.flatMap_dist {α β : Type _} [OFE α] [OFE β] {n}
    {f₁ f₂ : α → List β} (hf : ∀ ⦃x y⦄, x ≡{n}≡ y → f₁ x ≡{n}≡ f₂ y)
    {l₁ l₂ : List α} (hl : l₁ ≡{n}≡ l₂) : l₁.flatMap f₁ ≡{n}≡ l₂.flatMap f₂ := by
  induction hl with
  | nil => exact .nil
  | cons hh _ ih => exact List.append_ne.ne (hf hh) ih

@[rocq_alias list_join_ne]
instance List.flatten_ne {α : Type _} [OFE α] :
    NonExpansive (List.flatten : List (List α) → List α) where
  ne _ _ _ h := by
    induction h with
    | nil => exact .nil
    | cons hh _ ih => exact List.append_ne.ne hh ih

@[rocq_alias list_omap_ne]
theorem List.filterMap_dist {α β : Type _} [OFE α] [OFE β] {n}
    {f₁ f₂ : α → Option β} (hf : ∀ ⦃x y⦄, x ≡{n}≡ y → f₁ x ≡{n}≡ f₂ y)
    {l₁ l₂ : List α} (hl : l₁ ≡{n}≡ l₂) :
    l₁.filterMap f₁ ≡{n}≡ l₂.filterMap f₂ := by
  induction hl with
  | nil => exact .nil
  | cons hh _ ih =>
    rw [List.filterMap_cons, List.filterMap_cons]
    have hxy := hf hh
    revert hxy
    generalize f₁ _ = o₁; generalize f₂ _ = o₂
    cases o₁ <;> cases o₂ <;> intro hxy <;>
      first | exact ih | exact .cons hxy ih | exact hxy.elim

@[rocq_alias imap_ne]
theorem List.mapIdx_dist {α β : Type _} [OFE α] [OFE β] {n}
    {f₁ f₂ : Nat → α → β} (hf : ∀ i ⦃x y⦄, x ≡{n}≡ y → f₁ i x ≡{n}≡ f₂ i y)
    {l₁ l₂ : List α} (hl : l₁ ≡{n}≡ l₂) :
    l₁.mapIdx f₁ ≡{n}≡ l₂.mapIdx f₂ := by
  induction hl generalizing f₁ f₂ with
  | nil => exact .nil
  | cons hh _ ih =>
    rw [List.mapIdx_cons, List.mapIdx_cons]
    exact .cons (hf 0 hh) (ih (f₁ := fun i => f₁ (i + 1)) (f₂ := fun i => f₂ (i + 1))
      (fun i _ _ hxy => hf (i + 1) hxy))

@[rocq_alias zip_with_ne]
theorem List.zipWith_dist {α β γ : Type _} [OFE α] [OFE β] [OFE γ] {n}
    {f₁ f₂ : α → β → γ} (hf : ∀ ⦃x y⦄, x ≡{n}≡ y → ∀ ⦃u v⦄, u ≡{n}≡ v → f₁ x u ≡{n}≡ f₂ y v)
    {l₁ l₂ : List α} (hl : l₁ ≡{n}≡ l₂)
    {k₁ k₂ : List β} (hk : k₁ ≡{n}≡ k₂) : List.zipWith f₁ l₁ k₁ ≡{n}≡ List.zipWith f₂ l₂ k₂ := by
  induction hl generalizing k₁ k₂ with
  | nil => simp
  | cons hh _ ih =>
    cases hk with
    | nil => simp
    | cons hhk _ => exact .cons (hf hh hhk) (ih ‹_›)

@[rocq_alias list_fmap_dist_inj]
theorem List.map_injN {α β : Type _} [OFE α] [OFE β] {n} {f : α → β}
    (hf : ∀ ⦃x y⦄, f x ≡{n}≡ f y → x ≡{n}≡ y) :
    ∀ ⦃l₁ l₂ : List α⦄, l₁.map f ≡{n}≡ l₂.map f → l₁ ≡{n}≡ l₂ := by
  intro l₁ l₂ h
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with | nil => exact .nil | cons _ _ => cases h
  | cons _ _ ih =>
    cases l₂ with
    | nil => cases h
    | cons _ _ => let .cons hh hl := h; exact .cons (hf hh) (ih hl)

/-! ## Functor -/

@[rocq_alias list_fmap_ext_ne]
theorem List.map_ext_dist {α : Type _} {β : Type _} [OFE β] {n}
    (f g : α → β) (l : List α) (h : ∀ x, f x ≡{n}≡ g x) :
    l.map f ≡{n}≡ l.map g := by
  induction l with
  | nil => exact .nil
  | cons x _ ih => exact .cons (h x) ih

/-- Lift a non-expansive function to lists. -/
@[rocq_alias listO_map]
def listMap {α β : Type _} [OFE α] [OFE β] (f : α -n> β) : List α -n> List β where
  f l := l.map f
  ne := ⟨fun _ _ _ h => List.map_dist (fun _ _ hx => f.ne.ne hx) h⟩

@[rocq_alias listO_map_ne]
instance listMap_ne {α β : Type _} [OFE α] [OFE β] :
    NonExpansive (@listMap α β _ _) where
  ne _ _ _ h _ := List.map_ext_dist _ _ _ h

@[rocq_alias listOF]
abbrev ListOF (F : COFE.OFunctorPre) : COFE.OFunctorPre :=
  fun A B _ _ => List (F A B)

instance ListOF.instOFunctor {F} [COFE.OFunctor F] : COFE.OFunctor (ListOF F) where
  cofe := inferInstance
  map f g := listMap (COFE.OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy l := by
    induction l with
    | nil => exact .nil
    | cons _ _ ih => exact .cons (COFE.OFunctor.map_ne.ne Hx Hy _) ih
  map_id l := by
    induction l with
    | nil => exact .nil
    | cons _ _ ih => exact .cons (COFE.OFunctor.map_id _) ih
  map_comp _ _ _ _ l := by
    induction l with
    | nil => exact .nil
    | cons _ _ ih => exact .cons (COFE.OFunctor.map_comp ..) ih

@[rocq_alias listOF_contractive]
instance ListOF.instOFunctorContractive {F} [COFE.OFunctorContractive F] :
    COFE.OFunctorContractive (ListOF F) where
  map_contractive.distLater_dist H l := by
    induction l with
    | nil => exact .nil
    | cons _ _ ih =>
      exact .cons ((COFE.OFunctorContractive.map_contractive (F := F)).distLater_dist H _) ih

end Iris

/-! ## Big operators on lists -/

namespace Iris.Algebra.BigOpL

open Iris OFE MonoidOps

/-- Pointwise non-expansiveness for `bigOpL`, allowing the function and the
list to vary together. -/
@[rocq_alias big_opL_ne_2]
theorem bigOpL_dist_2 {M : Type u} {α : Type v} [OFE M] [OFE α]
    {op : M → M → M} {unit : M} [MonoidOps op unit]
    {f g : Nat → α → M} {l₁ l₂ : List α} {n : Nat}
    (hl : l₁ ≡{n}≡ l₂)
    (hf : ∀ ⦃k y₁ y₂⦄,
      l₁[k]? = some y₁ → l₂[k]? = some y₂ → y₁ ≡{n}≡ y₂ → f k y₁ ≡{n}≡ g k y₂) :
    ([^op list] k ↦ y ∈ l₁, f k y) ≡{n}≡ ([^op list] k ↦ y ∈ l₂, g k y) := by
  refine bigOpL_gen_proper_2 (· ≡{n}≡ ·) .rfl op_dist
    (List.length_eq_of_dist hl) fun {i _ _} h₁ h₂ =>
      hf h₁ h₂ (h₁ ▸ h₂ ▸ List.dist_lookup.mp hl i :)

end Iris.Algebra.BigOpL
