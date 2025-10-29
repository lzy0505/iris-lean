/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

-- import Iris.Std.DepRewrite
import Iris.BI
import Iris.Algebra
import Iris.Instances.UPred
namespace Iris

open COFE

/-- Apply an OFunctor at a fixed type -/
abbrev COFE.OFunctorPre.ap (F : OFunctorPre) (T : Type _) [OFE T] :=
  F T T

/-- Apply a list of OFunctors at a fixed type and index -/
abbrev BundledGFunctors.api (FF : BundledGFunctors) (τ : GType) (T : Type _) [OFE T] :=
  FF τ |>.fst |>.ap T


section ElemG
-- This section provides the core infrastructure for bundling and unbundling
-- elements.

open OFE

class ElemG (FF : BundledGFunctors) (F : OFunctorPre) [RFunctorContractive F] where
  τ : GType
  transp : FF τ = ⟨F, ‹_›⟩

def ElemG.Bundle {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T] : F.ap T → GF.api E.τ T :=
  (congrArg (OFunctorPre.ap · T) (Sigma.mk.inj E.transp).left).mpr

def ElemG.Unbundle {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T] : GF.api E.τ T → F.ap T :=
  (congrArg (OFunctorPre.ap · T) (Sigma.mk.inj E.transp).left).mp

theorem ElemG.transp_OFE {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T] : F.ap T = GF.api E.τ T := by
  unfold OFunctorPre.ap
  unfold BundledGFunctors.api
  rw [E.transp]


-- Casting lemmas for RFunctors
-- These transfer properties (dist, op, pcore, validN) across type equalities
theorem OFE.cast_dist_from_RFunctor_mpr {F₁ F₂ : OFunctorPre}
    [RF₁ : RFunctorContractive F₁] [RF₂ : RFunctorContractive F₂]
    {T : Type u} [OFE T]
    (h_fun : F₁ = F₂)
    (h_inst : HEq RF₁ RF₂)
    {n : Nat} {x y : F₁ T T}
    (H : x ≡{n}≡ y) :
    (congrArg (OFunctorPre.ap · T) h_fun.symm).mpr x ≡{n}≡ (congrArg (OFunctorPre.ap · T) h_fun.symm).mpr y := by
  cases h_fun; cases eq_of_heq h_inst; exact H

-- Version for .mp (opposite direction)
theorem OFE.cast_dist_from_RFunctor_mp {F₁ F₂ : OFunctorPre}
    [RF₁ : RFunctorContractive F₁] [RF₂ : RFunctorContractive F₂]
    {T : Type u} [OFE T]
    (h_fun : F₁ = F₂)
    (h_inst : HEq RF₁ RF₂)
    {n : Nat} {x y : F₂ T T}
    (H : x ≡{n}≡ y) :
    (congrArg (OFunctorPre.ap · T) h_fun.symm).mp x ≡{n}≡ (congrArg (OFunctorPre.ap · T) h_fun.symm).mp y := by
  cases h_fun; cases eq_of_heq h_inst; exact H

-- CMRA operation preservation for casts from RFunctor

-- .mpr preserves op for RFunctor casts
theorem OFE.cast_op_from_RFunctor_mpr {F₁ F₂ : OFunctorPre}
    [RF₁ : RFunctorContractive F₁] [RF₂ : RFunctorContractive F₂]
    {T : Type u} [OFE T]
    (h_fun : F₁ = F₂)
    (h_inst : HEq RF₁ RF₂)
    {x y : F₁ T T} :
    (congrArg (OFunctorPre.ap · T) h_fun.symm).mpr (x • y) ≡
    (congrArg (OFunctorPre.ap · T) h_fun.symm).mpr x • (congrArg (OFunctorPre.ap · T) h_fun.symm).mpr y := by
  cases h_fun; cases eq_of_heq h_inst; rfl

-- .mp preserves op for RFunctor casts
theorem OFE.cast_op_from_RFunctor_mp {F₁ F₂ : OFunctorPre}
    [RF₁ : RFunctorContractive F₁] [RF₂ : RFunctorContractive F₂]
    {T : Type u} [OFE T]
    (h_fun : F₁ = F₂)
    (h_inst : HEq RF₁ RF₂)
    {x y : F₂ T T} :
    (congrArg (OFunctorPre.ap · T) h_fun.symm).mp (x • y) ≡
    (congrArg (OFunctorPre.ap · T) h_fun.symm).mp x • (congrArg (OFunctorPre.ap · T) h_fun.symm).mp y := by
  cases h_fun; cases eq_of_heq h_inst; rfl

-- .mpr preserves pcore for RFunctor casts
theorem OFE.cast_pcore_from_RFunctor_mpr {F₁ F₂ : OFunctorPre}
    [RF₁ : RFunctorContractive F₁] [RF₂ : RFunctorContractive F₂]
    {T : Type u} [OFE T]
    (h_fun : F₁ = F₂)
    (h_inst : HEq RF₁ RF₂)
    {x : F₁ T T} :
    (CMRA.pcore x).map (congrArg (OFunctorPre.ap · T) h_fun.symm).mpr ≡
    CMRA.pcore ((congrArg (OFunctorPre.ap · T) h_fun.symm).mpr x) := by
  cases h_fun; cases eq_of_heq h_inst
  simp [Equiv, Option.Forall₂]; cases CMRA.pcore x <;> simp [Equiv.rfl]

-- .mp preserves pcore for RFunctor casts
theorem OFE.cast_pcore_from_RFunctor_mp {F₁ F₂ : OFunctorPre}
    [RF₁ : RFunctorContractive F₁] [RF₂ : RFunctorContractive F₂]
    {T : Type u} [OFE T]
    (h_fun : F₁ = F₂)
    (h_inst : HEq RF₁ RF₂)
    {x : F₂ T T} :
    (CMRA.pcore x).map (congrArg (OFunctorPre.ap · T) h_fun.symm).mp ≡
    CMRA.pcore ((congrArg (OFunctorPre.ap · T) h_fun.symm).mp x) := by
  cases h_fun; cases eq_of_heq h_inst
  simp [Equiv, Option.Forall₂]; cases CMRA.pcore x <;> simp [Equiv.rfl]

-- .mpr preserves validN for RFunctor casts
theorem OFE.cast_validN_from_RFunctor_mpr {F₁ F₂ : OFunctorPre}
    [RF₁ : RFunctorContractive F₁] [RF₂ : RFunctorContractive F₂]
    {T : Type u} [OFE T]
    (h_fun : F₁ = F₂)
    (h_inst : HEq RF₁ RF₂)
    {n : Nat} {x : F₁ T T} :
    ✓{n} x → ✓{n} ((congrArg (OFunctorPre.ap · T) h_fun.symm).mpr x) := by
  cases h_fun
  have : RF₁ = RF₂ := eq_of_heq h_inst
  cases this
  intro H
  exact H

-- .mp preserves validN for RFunctor casts (inverse direction)
theorem OFE.cast_validN_from_RFunctor_mp {F₁ F₂ : OFunctorPre}
    [RF₁ : RFunctorContractive F₁] [RF₂ : RFunctorContractive F₂]
    {T : Type u} [OFE T]
    (h_fun : F₁ = F₂)
    (h_inst : HEq RF₁ RF₂)
    {n : Nat} {x : F₁ T T} :
    ✓{n} x → ✓{n} ((congrArg (OFunctorPre.ap · T) h_fun).mp x) := by
  cases h_fun
  have : RF₁ = RF₂ := eq_of_heq h_inst
  cases this
  intro H
  exact H

-- Bundle/Unbundle preserve CMRA operations
-- KEY: CMRA (F.ap T) comes from RFunctorContractive F, not from T itself
-- So these lemmas apply even when T = IProp GF (which has no CMRA instance)
theorem ElemG.Bundle_op {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T]
    (x y : F.ap T) :
    E.Bundle (x • y) ≡ E.Bundle x • E.Bundle y := by
  unfold Bundle
  have h_fun : (GF E.τ).fst = F := (Sigma.mk.inj E.transp).left
  have h_inst : HEq (GF E.τ).snd ‹RFunctorContractive F› := (Sigma.mk.inj E.transp).right
  exact OFE.cast_op_from_RFunctor_mpr h_fun.symm h_inst.symm

-- Bundle preserves pcore
theorem ElemG.Bundle_pcore {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T]
    (x : F.ap T) :
    (CMRA.pcore x).map E.Bundle ≡ CMRA.pcore (E.Bundle x) := by
  unfold Bundle
  have h_fun : (GF E.τ).fst = F := (Sigma.mk.inj E.transp).left
  have h_inst : HEq (GF E.τ).snd ‹RFunctorContractive F› := (Sigma.mk.inj E.transp).right
  exact OFE.cast_pcore_from_RFunctor_mpr h_fun.symm h_inst.symm

-- Unbundle preserves op
theorem ElemG.Unbundle_op {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T]
    (x y : GF.api E.τ T) :
    E.Unbundle (x • y) ≡ E.Unbundle x • E.Unbundle y := by
  unfold Unbundle
  have h_fun : (GF E.τ).fst = F := (Sigma.mk.inj E.transp).left
  have h_inst : HEq (GF E.τ).snd ‹RFunctorContractive F› := (Sigma.mk.inj E.transp).right
  exact OFE.cast_op_from_RFunctor_mp h_fun.symm h_inst.symm

-- Bundle preserves validN
theorem ElemG.Bundle_validN {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T]
    {n : Nat} (x : F.ap T) :
    ✓{n} x → ✓{n} (E.Bundle x) := by
  unfold Bundle
  have h_fun : (GF E.τ).fst = F := (Sigma.mk.inj E.transp).left
  have h_inst : HEq (GF E.τ).snd ‹RFunctorContractive F› := (Sigma.mk.inj E.transp).right
  exact OFE.cast_validN_from_RFunctor_mpr h_fun.symm h_inst.symm

-- Unbundle preserves validN
theorem ElemG.Unbundle_validN {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T]
    {n : Nat} (x : GF.api E.τ T) :
    ✓{n} x → ✓{n} (E.Unbundle x) := by
  unfold Unbundle
  have h_fun : (GF E.τ).fst = F := (Sigma.mk.inj E.transp).left
  have h_inst : HEq (GF E.τ).snd ‹RFunctorContractive F› := (Sigma.mk.inj E.transp).right
  exact OFE.cast_validN_from_RFunctor_mp h_fun h_inst

-- Unbundle preserves pcore
theorem ElemG.Unbundle_pcore {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T]
    (x : GF.api E.τ T) :
    (CMRA.pcore x).map E.Unbundle ≡ CMRA.pcore (E.Unbundle x) := by
  unfold Unbundle
  have h_fun : (GF E.τ).fst = F := (Sigma.mk.inj E.transp).left
  have h_inst : HEq (GF E.τ).snd ‹RFunctorContractive F› := (Sigma.mk.inj E.transp).right
  exact OFE.cast_pcore_from_RFunctor_mp h_fun.symm h_inst.symm

-- Bundle and Unbundle are inverses
theorem ElemG.Bundle_Unbundle {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T]
    (x : GF.api E.τ T) :
    E.Bundle (E.Unbundle x) ≡ x := by
  unfold Bundle Unbundle
  simp [Equiv]

theorem ElemG.Unbundle_Bundle {GF F} [RFunctorContractive F] (E : ElemG GF F) [OFE T]
    (x : F.ap T) :
    E.Unbundle (E.Bundle x) ≡ x := by
  unfold Bundle Unbundle
  simp [Equiv]

instance ElemG.Bundle.ne {GF F} [RFunctorContractive F] {E : ElemG GF F} [OFE T] :
    OFE.NonExpansive (E.Bundle (T := T)) where
  ne {n x1 x2} H := by
    unfold Bundle
    have h_fun : (GF E.τ).fst = F := (Sigma.mk.inj E.transp).left
    have h_inst : HEq (GF E.τ).snd ‹RFunctorContractive F› := (Sigma.mk.inj E.transp).right
    exact @OFE.cast_dist_from_RFunctor_mpr F (GF E.τ).fst ‹RFunctorContractive F› (GF E.τ).snd
          T ‹OFE T› h_fun.symm h_inst.symm n x1 x2 H

instance ElemG.UnBundle.ne {GF F} [RFunctorContractive F] {E : ElemG GF F} [OFE T] :
    OFE.NonExpansive (E.Unbundle (T := T)) where
  ne {n x1 x2} H := by
    unfold Unbundle
    have h_fun : (GF E.τ).fst = F := (Sigma.mk.inj E.transp).left
    have h_inst : HEq (GF E.τ).snd ‹RFunctorContractive F› := (Sigma.mk.inj E.transp).right
    exact @OFE.cast_dist_from_RFunctor_mp F (GF E.τ).fst ‹RFunctorContractive F› (GF E.τ).snd
          T ‹OFE T› h_fun.symm h_inst.symm n x1 x2 H

end ElemG

section Fold
-- This section provides folding and unfolding operations for IProp
open Iris COFE UPred

variable {FF : BundledGFunctors}

/-- Isorecursive unfolding for each projection of FF. -/
def IProp.unfoldi : FF.api τ (IProp FF) -n> FF.api τ (IPre FF) :=
  OFunctor.map (IProp.fold FF) (IProp.unfold FF)

/-- Isorecursive folding for each projection of FF. -/
def IProp.foldi : FF.api τ (IPre FF) -n> FF.api τ (IProp FF) :=
  OFunctor.map (IProp.unfold FF) (IProp.fold FF)

theorem IProp.unfoldi_foldi (x : FF.api τ (IPre FF)) : unfoldi (foldi x) ≡ x := by
  refine .trans (OFunctor.map_comp (F := FF τ |>.fst) ..).symm ?_
  refine .trans ?_ (OFunctor.map_id (F := FF τ |>.fst) x)
  apply OFunctor.map_ne.eqv <;> intro _ <;> simp [IProp.unfold, IProp.fold]

-- foldi ∘ unfoldi ≈ id (clearer name than proj_fold_unfold)
theorem IProp.foldi_unfoldi_comp (x : FF.api τ (IProp FF)) : foldi (unfoldi x) ≡ x := by
  simp only [foldi, unfoldi, OFunctor.map]
  letI : RFunctor (FF τ).fst := (FF τ).snd.toRFunctor
  refine .trans (OFunctor.map_comp (F := FF τ |>.fst) ..).symm ?_
  refine .trans ?_ (OFunctor.map_id (F := FF τ |>.fst) x)
  apply OFunctor.map_ne.eqv <;> intro _ <;> simp [IProp.unfold, IProp.fold]

-- foldi is a CMRA homomorphism (preserves operations)
theorem IProp.foldi_op (x y : FF.api τ (IPre FF)) : foldi (x • y) ≡ foldi x • foldi y := by
  simp only [foldi, OFunctor.map]
  letI : RFunctor (FF τ).fst := (FF τ).snd.toRFunctor
  exact (RFunctor.map (IProp.unfold FF) (IProp.fold FF)).op _ _

-- foldi preserves validity (morphism property)
theorem IProp.foldi_validN {n : Nat} (x : FF.api τ (IPre FF)) :
    ✓{n} x → ✓{n} (foldi x) := by
  intro H
  simp only [foldi, OFunctor.map]
  letI : RFunctor (FF τ).fst := (FF τ).snd.toRFunctor
  exact (RFunctor.map (IProp.unfold FF) (IProp.fold FF)).validN H

-- unfoldi preserves validity (morphism property)
theorem IProp.unfoldi_validN {n : Nat} (x : FF.api τ (IProp FF)) :
    ✓{n} x → ✓{n} (unfoldi x) := by
  intro H
  simp only [unfoldi, OFunctor.map]
  letI : RFunctor (FF τ).fst := (FF τ).snd.toRFunctor
  exact (RFunctor.map (IProp.fold FF) (IProp.unfold FF)).validN H

-- Helper: mapping preserves Option.Forall₂
theorem Option.map_forall₂ {α β : Type _} [OFE α] [OFE β] (f : α → β) [hf : OFE.NonExpansive f]
    {o1 o2 : Option α} (h : o1 ≡ o2) : o1.map f ≡ o2.map f := by
  cases o1 <;> cases o2
  · simp [Option.Forall₂]
  · simp [Option.Forall₂] at h
  · simp [Option.Forall₂] at h
  · simp [Option.Forall₂] at h ⊢
    exact hf.eqv h

end Fold


section iSingleton
open IProp OFE UPred

def iSingleton {GF} F [RFunctorContractive F] [E : ElemG GF F] (γ : GName) (v : F.ap (IProp GF)) : IResUR GF :=
  fun τ' => ⟨fun γ' =>
    if H : (τ' = E.τ ∧ γ' = γ)
      then some (H.1 ▸ (unfoldi <| E.Bundle v))
      else none⟩

theorem IResUR_op_eval {GF} (c1 c2 : IResUR GF) : (c1 • c2) τ' γ' = (c1 τ' γ') • (c2 τ' γ') := by
    simp [CMRA.op, optionOp]

instance {γ : GName} [RFunctorContractive F] [E : ElemG GF F] :
    OFE.NonExpansive (iSingleton F γ (GF := GF))  where
  ne {n x1 x2} H τ' γ' := by
    simp [iSingleton]
    split <;> try rfl
    simp [optionOp]
    rename_i h; rcases h with ⟨h1, h2⟩; subst h1; subst h2; simp
    exact NonExpansive.ne (NonExpansive.ne H)

theorem iSingleton_op {γ : GName} [RFunctorContractive F] [E : ElemG GF F]
    (x y : F.ap (IProp GF)) :
    (iSingleton F γ x) • iSingleton F γ y ≡ iSingleton F γ (x • y) := by
  intro τ' γ'
  unfold iSingleton
  simp [CMRA.op]
  split <;> try rfl
  simp [optionOp]
  rename_i h; rcases h with ⟨h1, h2⟩; subst h1 h2; simp [IProp.unfoldi]
  -- Strategy: Use Bundle_op and map.op (CMRA homomorphism)
  have h_bundle := ElemG.Bundle_op E x y
  have h_map : ∀ (a b : GF.api E.τ (IProp GF)),
      OFunctor.map (IProp.fold GF) (IProp.unfold GF) (a • b) ≡
      OFunctor.map (IProp.fold GF) (IProp.unfold GF) a •
      OFunctor.map (IProp.fold GF) (IProp.unfold GF) b :=
    fun a b => (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).op a b
  exact ((OFE.NonExpansive.eqv h_bundle).trans (h_map (E.Bundle x) (E.Bundle y))).symm

-- Helper lemmas for iSingleton validity and freedom properties

-- iSingleton is free at all keys except γ
theorem iSingleton_free_at_ne {GF F} [RFunctorContractive F] [E : ElemG GF F]
    (γ : GName) (v : F.ap (IProp GF)) (γ' : GName) (h : γ' ≠ γ) :
    (iSingleton F γ v E.τ).car γ' = none := by
  simp [iSingleton, h]

-- iSingleton at a single key has infinitely many free keys
theorem iSingleton_infinite_free {GF F} [RFunctorContractive F] [E : ElemG GF F]
    (γ : GName) (v : F.ap (IProp GF)) :
    Infinite (IsFree (iSingleton F γ v E.τ).car) := by
  refine ⟨Poke id γ, ?_, ?_⟩
  · intro n
    simp [IsFree, Poke]
    split
    · rename_i h; exact iSingleton_free_at_ne γ v n (Nat.ne_of_lt h)
    · rename_i h; exact iSingleton_free_at_ne γ v (n + 1) (Nat.ne_of_gt (Nat.lt_succ_of_le (Nat.ge_of_not_lt h)))
  · intro n m; simp [Poke]; split <;> split <;> omega

-- iSingleton at τ' ≠ E.τ is the unit
theorem iSingleton_ne_eq_unit {GF F} [RFunctorContractive F] [E : ElemG GF F]
    (γ : GName) (v : F.ap (IProp GF)) (τ' : GType) (h : τ' ≠ E.τ) :
    (iSingleton F γ v τ').car = (UCMRA.unit : GenMap Nat _).car := by
  ext γ'; simp [iSingleton, h]

-- Composing with iSingleton preserves freedom at keys ≠ γ
theorem iSingleton_op_free_at_ne {GF F} [RFunctorContractive F] [E : ElemG GF F]
    (γ : GName) (v : F.ap (IProp GF)) (m : GenMap GName (GF.api E.τ (IPre GF)))
    (γ' : GName) (h_ne : γ' ≠ γ) (h_free : m.car γ' = none) :
    ((iSingleton F γ v E.τ) • m).car γ' = none := by
  simp [CMRA.op, optionOp, iSingleton, h_ne, h_free]

-- Composing with iSingleton preserves infinite free keys
theorem iSingleton_preserves_infinite_free {GF F} [RFunctorContractive F] [E : ElemG GF F]
    (γ : GName) (v : F.ap (IProp GF)) (m : GenMap GName (GF.api E.τ (IPre GF)))
    (h_inf : Infinite (IsFree m.car)) :
    Infinite (IsFree ((iSingleton F γ v E.τ) • m).car) := by
  rcases h_inf with ⟨enum, h_enum_free, h_enum_inj⟩
  by_cases h_gamma_in : ∃ n₀, enum n₀ = γ
  · -- If γ appears in enum, use Poke to skip it
    rcases h_gamma_in with ⟨n₀, h_n₀⟩
    refine ⟨Poke enum n₀, ?_, ?_⟩
    · intro n; simp [IsFree, Poke]; split
      · rename_i h; apply iSingleton_op_free_at_ne
        · intro heq; exact absurd (h_enum_inj (heq.trans h_n₀.symm)) (Nat.ne_of_lt h)
        · exact h_enum_free
      · rename_i h; apply iSingleton_op_free_at_ne
        · intro heq; exact absurd (h_enum_inj (heq.trans h_n₀.symm)) (by omega)
        · exact h_enum_free
    · intro n m h_eq; simp [Poke] at h_eq
      split at h_eq <;> split at h_eq <;> rename_i hn hm
      · exact h_enum_inj h_eq
      · have : n = m + 1 := h_enum_inj h_eq; omega
      · have : n + 1 = m := h_enum_inj h_eq; omega
      · have : n + 1 = m + 1 := h_enum_inj h_eq; omega
  · -- If γ not in enum, all enumerated keys remain free
    refine ⟨enum, ?_, h_enum_inj⟩
    intro n; simp [IsFree]
    apply iSingleton_op_free_at_ne
    · intro heq; exact h_gamma_in ⟨n, heq⟩
    · exact h_enum_free

end iSingleton

def iOwn {GF F} [RFunctorContractive F] [E : ElemG GF F] (γ : GName) (v : F.ap (IProp GF)) : IProp GF :=
  UPred.ownM <| iSingleton F γ v


section iOwn
-- This section defines resource ownership and its properties
open IProp OFE UPred

variable {GF F} [RFunctorContractive F] [E : ElemG GF F]

-- Subsection: Basic properties

instance iOwn_ne : NonExpansive (iOwn τ : F.ap (IProp GF) → IProp GF) where
  ne {n x1 x2} H := by unfold iOwn; exact NonExpansive.ne (NonExpansive.ne H)

theorem iOwn_op {a1 a2 : F.ap (IProp GF)} : iOwn γ (a1 • a2) ⊣⊢ iOwn γ a1 ∗ iOwn γ a2 :=
  UPred.ownM_eqv (iSingleton_op _ _).symm |>.trans (UPred.ownM_op _ _)

theorem iOwn_mono {a1 a2 : F.ap (IProp GF)} (H : a2 ≼ a1) : iOwn γ a1 ⊢ iOwn γ a2 := by
  rcases H with ⟨ac, Hac⟩
  rintro n x Hv ⟨clos, Hclos⟩
  -- Basically the heaps proof, want some other lemmas
  refine ⟨iSingleton F γ ac • clos, Hclos.trans ?_⟩
  intros τ' γ'
  refine .trans ?_ CMRA.op_assocN.symm
  rw [IResUR_op_eval]
  unfold iSingleton
  simp
  split
  · rename_i h
    rcases h with ⟨h_τ, h_γ⟩
    subst h_τ h_γ
    refine Dist.op_l ?_
    simp [CMRA.op, optionOp]
    -- Show unfoldi (E.Bundle a1) ≡{n}≡ unfoldi (E.Bundle a2) • unfoldi (E.Bundle ac)
    -- using that unfoldi and E.Bundle are morphisms
    have h1 : E.Bundle a1 ≡{n}≡ E.Bundle (a2 • ac) := NonExpansive.ne Hac.dist
    have h2 := ElemG.Bundle_op E a2 ac
    have h3 : E.Bundle a1 ≡{n}≡ E.Bundle a2 • E.Bundle ac := h1.trans h2.dist
    have h4 : IProp.unfoldi (E.Bundle a2 • E.Bundle ac) ≡{n}≡
              IProp.unfoldi (E.Bundle a2) • IProp.unfoldi (E.Bundle ac) := by
      simp [IProp.unfoldi]
      exact (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).op _ _ |>.dist
    exact (NonExpansive.ne h3).trans h4
  · simp [CMRA.op, optionOp]

theorem iOwn_cmraValid {a : F.ap (IProp GF)} : iOwn γ a ⊢ UPred.cmraValid a := by
  refine .trans (UPred.ownM_valid _) ?_
  refine UPred.valid_entails (fun n H => ?_)
  -- Strategy: Extract validity from iSingleton at (E.τ, γ), work backwards through unfoldi and Bundle
  rcases H E.τ with ⟨h_valid, _⟩
  have h_at_γ : ✓{n} (((iSingleton F γ a) E.τ).car γ) := h_valid γ
  simp [iSingleton, CMRA.ValidN, optionValidN] at h_at_γ
  -- h_at_γ : ✓{n} (unfoldi (E.Bundle a))
  -- Work backwards: unfoldi → Bundle → a
  have h_bundle_valid : ✓{n} (E.Bundle a) := by
    apply CMRA.validN_ne (IProp.foldi_unfoldi_comp (E.Bundle a)).dist
    exact IProp.foldi_validN (IProp.unfoldi (E.Bundle a)) h_at_γ
  apply CMRA.validN_ne (ElemG.Unbundle_Bundle E a).dist
  exact ElemG.Unbundle_validN E (E.Bundle a) h_bundle_valid

theorem iOwn_cmraValid_op {a1 a2 : F.ap (IProp GF)} : iOwn γ a1 ∗ iOwn γ a2 ⊢ UPred.cmraValid (a1 • a2) :=
  iOwn_op.mpr.trans iOwn_cmraValid

theorem iOwn_valid_r {a : F.ap (IProp GF)} : iOwn γ a ⊢ iOwn γ a ∗ UPred.cmraValid a :=
  BI.persistent_entails_l iOwn_cmraValid

theorem iOwn_valid_l {a : F.ap (IProp GF)} : iOwn γ a ⊢ UPred.cmraValid a ∗ iOwn γ a :=
  BI.persistent_entails_r iOwn_cmraValid

-- Subsection: Persistence

-- Helper lemma: unfoldi ∘ E.Bundle preserves CoreId
theorem unfoldi_Bundle_coreId {a : F.ap (IProp GF)} [CMRA.CoreId a] :
    CMRA.CoreId (unfoldi (E.Bundle a)) := by
  constructor
  -- Strategy: Use that both Bundle and RFunctor.map preserve pcore
  simp only [unfoldi, OFunctor.map]
  letI : RFunctor (GF E.τ).fst := (GF E.τ).snd.toRFunctor
  have bundle_coreId : CMRA.CoreId (E.Bundle a) := by
    constructor
    calc CMRA.pcore (E.Bundle a)
      ≡ (CMRA.pcore a).map E.Bundle := (ElemG.Bundle_pcore E a).symm
      _ ≡ (some a).map E.Bundle := by
        have : CMRA.pcore a ≡ some a := CMRA.CoreId.core_id
        rcases h : CMRA.pcore a with (_ | ca)
        · rw [h] at this; simp [Option.Forall₂] at this
        · rw [h] at this; simp [Option.Forall₂, Option.map] at this ⊢
          exact OFE.NonExpansive.eqv this
      _ ≡ some (E.Bundle a) := by simp [Option.map, Option.Forall₂, OFE.Equiv.rfl]
  calc CMRA.pcore ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a))
    ≡ (CMRA.pcore (E.Bundle a)).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f :=
      (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).pcore (E.Bundle a) |>.symm
    _ ≡ (some (E.Bundle a)).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f := by
      have : CMRA.pcore (E.Bundle a) ≡ some (E.Bundle a) := bundle_coreId.core_id
      rcases h : CMRA.pcore (E.Bundle a) with (_ | c)
      · rw [h] at this; simp [Option.Forall₂] at this
      · rw [h] at this; simp [Option.Forall₂, Option.map] at this ⊢
        exact OFE.NonExpansive.eqv this
    _ ≡ some ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a)) := by
      simp [Option.map, Option.Forall₂, OFE.Equiv.rfl]

instance {a : F.ap (IProp GF)} [CMRA.CoreId a] : BI.Persistent (iOwn γ a) where
  persistent := by
    simp [iOwn]
    refine .trans (UPred.persistently_ownM_core _) ?_
    refine BI.persistently_mono ?_
    refine BI.equiv_iff.mp ?_ |>.mp
    refine OFE.NonExpansive.eqv ?_
    -- Strategy: Show iSingleton F γ a has CoreId, then use core_eqv_self
    haveI : CMRA.CoreId (iSingleton F γ a) := by
      constructor
      unfold iSingleton
      simp only [CMRA.pcore, cmraDiscreteFunO]
      intro τ'
      simp only [instCMRA_GenMap, Option.map]
      intro γ'
      simp only [GenMap.mk, CMRA.core, CMRA.pcore, cmraDiscreteFunO, Option.getD, Option.map]
      split
      · -- At (τ' = E.τ, γ' = γ): use that cast preserves CoreId
        rename_i h
        simp only [CMRA.core, optionCore, Option.bind]
        have bundle_coreId : CMRA.CoreId (unfoldi (E.Bundle a)) := unfoldi_Bundle_coreId
        have : CMRA.CoreId (h.1 ▸ unfoldi (E.Bundle a)) := by cases h.1; exact bundle_coreId
        exact this.core_id
      · rfl
    apply CMRA.core_eqv_self

-- Subsection: Allocation

theorem iOwn_alloc_strong_dep {f : GName → F.ap (IProp GF)} {P : GName → Prop}
    (HI : Infinite P) (Hv : ∀ γ, P γ → ✓ (f γ)) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ iOwn γ (f γ) := by
  refine .trans (Q := iprop(|==> ∃ m : IResUR GF, ⌜∃ γ, P γ ∧ m = iSingleton _ γ (f γ)⌝ ∧ UPred.ownM m)) ?_ ?_
  · refine .trans (UPred.ownM_unit _) <| BI.intuitionistically_elim.trans ?_
    refine UPred.ownM_updateP _ (fun n mz Hvalid => ?_)
    -- Key insight: pick γ based on the frame mz
    -- For each frame, we need γ ∈ P such that γ is free in that frame
    cases mz with
    | none =>
      -- No frame: any element from P works
      rcases HI with ⟨PE, HPE⟩
      refine ⟨iSingleton F (PE 0) (f (PE 0)), ⟨_, HPE.inc, rfl⟩, ?_⟩
      -- Validity is trivial for empty frame
      intro γ; constructor
      · intro γ'
        simp [CMRA.ValidN, optionValidN, CMRA.op?, iSingleton]
        rcases Classical.em (γ = ElemG.τ GF F ∧ γ' = PE 0) with (⟨h1, h2⟩ | h)
        · subst h1 h2
          simp [iSingleton]
          have hvn : ✓{n} (f (PE 0)) := (Hv (PE 0) HPE.inc).validN
          have hb : ✓{n} (E.Bundle (f (PE 0))) := ElemG.Bundle_validN E (f (PE 0)) hvn
          exact IProp.unfoldi_validN (E.Bundle (f (PE 0))) hb
        · simp_all only [↓reduceDIte]
      · -- IsFree: show that after allocating at PE 0, infinitely many remain free
        -- Use Poke to shift the enumeration, skipping PE 0
        refine ⟨Poke PE 0, ?_, ?_⟩
        · intro n'
          -- After allocation at PE 0, Poke PE 0 enumerates the remaining free positions
          simp [IsFree, iSingleton, CMRA.op?]
          intro h hcontra
          -- Poke PE 0 n' = PE (n' + 1) ≠ PE 0 by injectivity
          simp only [Poke] at hcontra
          split at hcontra
          · next hn => have := HPE.inj hcontra; omega
          · next hn => have := HPE.inj hcontra; omega
        · intro n' m' h
          -- Poke is injective when the base enumeration is injective
          simp only [Poke] at h
          by_cases hn : n' < 0 <;> by_cases hm : m' < 0
          · rw [if_pos hn, if_pos hm] at h; exact HPE.inj h
          · rw [if_pos hn, if_neg hm] at h; have := HPE.inj h; omega
          · rw [if_neg hn, if_pos hm] at h; have := HPE.inj h; omega
          · rw [if_neg hn, if_neg hm] at h; have := HPE.inj h; omega
    | some z =>
      -- Have frame z: pick γ ∈ P that's free in z
      -- Use Infinite.inter_nonempty_nat to find such a γ
      have Hvalid_z : ✓{n} ((UCMRA.unit : IResUR GF) • z) := by
        simp [CMRA.op?] at Hvalid; exact Hvalid
      have Hinf_free : Infinite (IsFree (z E.τ).car) := by
        -- Extract the infinity condition from validity of the GenMap at type E.τ
        have h := Hvalid_z E.τ
        -- The validity of a GenMap includes Infinite (IsFree ...)
        rcases h with ⟨_, Hinf⟩
        -- Now show (unit • z) E.τ has the same IsFree as z E.τ
        refine Infinite.mono Hinf (fun a => ?_)
        simp [IsFree, CMRA.op]
        have : ((UCMRA.unit : IResUR GF) E.τ).car a = none := by simp [UCMRA.unit]
        simp [this, optionOp]
      have h_inter : ∃ n, P n ∧ IsFree (z E.τ).car n := by
        -- FIXME: unprovable
        sorry
      rcases h_inter with ⟨γ_fresh, Hγ_P, Hγ_free⟩
      refine ⟨iSingleton F γ_fresh (f γ_fresh), ⟨γ_fresh, Hγ_P, rfl⟩, ?_⟩
      -- Now prove validity with γ_fresh which is free in the frame
      intro γ; constructor
      · intro γ'
        simp [CMRA.ValidN, optionValidN, CMRA.op?, iSingleton]
        rcases Classical.em (γ = ElemG.τ GF F ∧ γ' = γ_fresh) with (⟨h1, h2⟩ | h)
        · -- At the allocated position: γ = E.τ and γ' = γ_fresh
          subst h1 h2
          -- After subst, γ_fresh becomes γ'
          simp [iSingleton, CMRA.op, optionOp]
          -- γ' is free in z, so z E.τ γ' = none
          simp [IsFree] at Hγ_free
          rw [Hγ_free]
          simp [optionOp]
          -- Now show validity of unfoldi (E.Bundle (f γ'))
          have hvn : ✓{n} (f γ') := (Hv γ' Hγ_P).validN
          have hb : ✓{n} (E.Bundle (f γ')) := ElemG.Bundle_validN E (f γ') hvn
          exact IProp.unfoldi_validN (E.Bundle (f γ')) hb
        · -- Away from allocated position: use validity of z
          -- Since h : ¬(γ = E.τ ∧ γ' = γ_fresh), iSingleton at (γ, γ') is none
          have h_if_false : ¬(γ = ElemG.τ GF F ∧ γ' = γ_fresh) := h
          simp [CMRA.op, iSingleton]
          rw [dif_neg h_if_false]
          simp [optionOp]
          -- Now just the validity from z
          -- Note: (unit • z) γ = z γ since unit is left identity
          have h_unit_z : (((UCMRA.unit : IResUR GF) • z) γ).car = (z γ).car := by
            simp [CMRA.op, UCMRA.unit, optionOp]
          have := Hvalid_z γ
          rcases this with ⟨Hv_z, _⟩
          simp [CMRA.ValidN] at Hv_z
          rw [h_unit_z] at Hv_z
          exact Hv_z γ'
      · -- IsFree: show infinitely many remain free after allocation
        rcases Classical.em (γ = ElemG.τ GF F) with (h_eq | h_ne)
        · -- Case: γ = E.τ, use alter_isFree_infinite
          subst h_eq
          simp [CMRA.op?, CMRA.op, iSingleton]
          -- The goal is: Infinite (IsFree (fun x => optionOp (if x = γ_fresh then ... else none) ((z E.τ).car x)))
          -- We know γ_fresh is free in (z E.τ).car, i.e., (z E.τ).car γ_fresh = none
          simp [IsFree] at Hγ_free
          -- Now show this matches alter pattern
          suffices h : (fun x => optionOp (if x = γ_fresh then some (unfoldi (E.Bundle (f γ_fresh))) else none) ((z (ElemG.τ GF F)).car x)) =
                       alter (z (ElemG.τ GF F)).car γ_fresh (some (unfoldi (E.Bundle (f γ_fresh)))) by
            rw [h]; exact alter_isFree_infinite Hinf_free
          funext x
          simp only [alter, optionOp]
          by_cases h : x = γ_fresh
          · subst h
            rw [if_pos rfl, if_pos rfl]
            rw [Hγ_free]
          · rw [if_neg h, if_neg (Ne.symm h)]
            cases (z (ElemG.τ GF F)).car x <;> rfl
        · -- Case: γ ≠ E.τ, iSingleton doesn't affect this type
          simp [CMRA.op?, CMRA.op, iSingleton]
          -- The dif_neg applies because γ ≠ E.τ
          have : ∀ x, ¬(γ = ElemG.τ GF F ∧ x = γ_fresh) := fun x ⟨h1, _⟩ => h_ne h1
          simp [this]
          -- Now (z γ).car still has infinite free elements
          have := Hvalid_z γ
          exact this.2
  · refine BIUpdate.mono ?_
    refine BI.exists_elim (fun m => ?_)
    refine BI.pure_elim (φ := ∃ γ, P γ ∧ m = iSingleton F γ (f γ)) BI.and_elim_l ?_
    refine fun ⟨γ, HP, Hm⟩ => BI.and_elim_r' ?_
    refine BI.exists_intro' γ ?_
    refine BI.emp_sep.mpr.trans (BI.sep_mono ?_ ?_)
    · exact BI.pure_intro HP
    · rw [Hm]; exact .rfl

theorem iOwn_alloc_dep (f : GName → F.ap (IProp GF)) (Ha : ∀ γ, ✓ (f γ)) :
    ⊢ |==> ∃ γ, iOwn γ (f γ) :=
  (iOwn_alloc_strong_dep .Nat_True (fun _ => Ha ·)).trans <|
  BIUpdate.mono <| BI.exists_mono fun _ => BI.sep_elim_r

theorem iOwn_alloc (a : F.ap (IProp GF)) : ✓ a → ⊢ |==> ∃ γ, iOwn γ a :=
  fun Ha => iOwn_alloc_dep _ (fun _ => Ha)

-- Subsection: Updates

theorem iOwn_updateP {P γ a} (Hupd : a ~~>: P) :
    iOwn γ a ⊢ |==> ∃ a' : F.ap (IProp GF), ⌜P a'⌝ ∗ iOwn γ a' := by
  refine .trans (Q := iprop(|==> ∃ m, ⌜ ∃ a', m = (iSingleton F γ a') ∧ P a' ⌝ ∧ UPred.ownM m)) ?_ ?_
  · apply UPred.ownM_updateP
    -- Need to prove: iSingleton F γ a ~~>: fun y => ∃ a', y = iSingleton F γ a' ∧ P a'
    intro n mz Hv
    -- The frame mz is optional, and Hv tells us that iSingleton F γ a •? mz is valid
    -- The iSingleton at E.τ, γ contains unfoldi (E.Bundle a)
    -- We need to extract the frame's value at E.τ, γ and "unwrap" it to get the frame for a

    -- Derive validity and apply the update by case analysis on mz
    cases mz with
    | none =>
      -- No frame case
      -- First derive ✓{n} a from Hv
      have h_a_valid : ✓{n} a := by
        -- From Hv, at position E.τ and key γ, we have ✓{n} some (unfoldi (E.Bundle a))
        have h_valid_at_tau : ✓{n} ((iSingleton F γ a) E.τ) := Hv E.τ
        rcases h_valid_at_tau with ⟨h_pointwise, _⟩
        have h_at_gamma : ✓{n} (((iSingleton F γ a) E.τ).car γ) := h_pointwise γ
        simp [iSingleton] at h_at_gamma
        simp [CMRA.ValidN, optionValidN] at h_at_gamma
        -- h_at_gamma : ✓{n} (unfoldi (E.Bundle a))
        -- Use foldi to go back: foldi (unfoldi (E.Bundle a)) ≡ E.Bundle a
        have h_fold_unfold := IProp.foldi_unfoldi_comp (E.Bundle a)
        have h_bundle_valid : ✓{n} (E.Bundle a) := by
          apply CMRA.validN_ne h_fold_unfold.dist
          exact IProp.foldi_validN (IProp.unfoldi (E.Bundle a)) h_at_gamma
        -- Use Unbundle to go back: Unbundle (Bundle a) ≡ a
        have h_unbundle_bundle := ElemG.Unbundle_Bundle E a
        apply CMRA.validN_ne h_unbundle_bundle.dist
        exact ElemG.Unbundle_validN E (E.Bundle a) h_bundle_valid

      -- Apply update with none frame
      obtain ⟨a', Ha'_P, Ha'_valid⟩ := Hupd n none (by simp [CMRA.op?]; exact h_a_valid)

      refine ⟨iSingleton F γ a', ⟨a', rfl, Ha'_P⟩, ?_⟩
      -- Show ✓{n} (iSingleton F γ a')
      simp [CMRA.op?]
      intro τ'
      by_cases h_tau : τ' = E.τ
      · -- At τ' = E.τ: need to show the GenMap is valid
        subst h_tau
        refine ⟨?_, ?_⟩
        · -- Pointwise validity
          intro γ'
          simp [iSingleton]
          by_cases h_gamma : γ' = γ
          · -- At key γ: need ✓{n} (some (unfoldi (E.Bundle a')))
            simp [h_gamma, CMRA.ValidN, optionValidN]
            -- From Ha'_valid : ✓{n} a', we need ✓{n} (unfoldi (E.Bundle a'))
            simp [CMRA.op?] at Ha'_valid
            -- Apply Bundle
            have h_bundle_valid : ✓{n} (E.Bundle a') := ElemG.Bundle_validN E a' Ha'_valid
            -- Apply unfoldi
            exact IProp.unfoldi_validN (E.Bundle a') h_bundle_valid
          · -- At other keys: none is always valid
            simp [h_gamma, CMRA.ValidN, optionValidN]
        · -- Infinite free keys: all keys except γ are free
          refine ⟨Poke id γ, ?_, ?_⟩
          · intro n; simp [IsFree, iSingleton, Poke]; split <;> omega
          · intro n m; simp [Poke]; split <;> split <;> omega
      · -- At τ' ≠ E.τ: iSingleton is the unit
        simp [iSingleton, h_tau]
        exact (UCMRA.unit_valid : ✓ (UCMRA.unit : GenMap Nat ((GF τ').fst (IPre GF) (IPre GF)))).validN

    | some mz' =>
      -- With frame case
      cases h_mz_gamma : (mz' E.τ).car γ with
      | none =>
        -- Frame has none at γ, similar to none case
        have h_a_valid : ✓{n} a := by
          have h_valid_at_tau : ✓{n} ((iSingleton F γ a •? some mz') E.τ) := Hv E.τ
          simp [CMRA.op?] at h_valid_at_tau
          rcases h_valid_at_tau with ⟨h_pointwise, _⟩
          have h_at_gamma : ✓{n} ((((iSingleton F γ a) • mz') E.τ).car γ) := h_pointwise γ
          simp [iSingleton, CMRA.op, optionOp, h_mz_gamma] at h_at_gamma
          simp [CMRA.ValidN, optionValidN] at h_at_gamma
          have h_fold_unfold := IProp.foldi_unfoldi_comp (E.Bundle a)
          have h_bundle_valid : ✓{n} (E.Bundle a) := by
            apply CMRA.validN_ne h_fold_unfold.dist
            exact IProp.foldi_validN (IProp.unfoldi (E.Bundle a)) h_at_gamma
          have h_unbundle_bundle := ElemG.Unbundle_Bundle E a
          apply CMRA.validN_ne h_unbundle_bundle.dist
          exact ElemG.Unbundle_validN E (E.Bundle a) h_bundle_valid

        obtain ⟨a', Ha'_P, Ha'_valid⟩ := Hupd n none (by simp [CMRA.op?]; exact h_a_valid)

        refine ⟨iSingleton F γ a', ⟨a', rfl, Ha'_P⟩, ?_⟩
        -- Show ✓{n} (iSingleton F γ a' •? some mz')
        simp [CMRA.op?]
        intro τ'
        by_cases h_tau : τ' = E.τ
        · -- At τ' = E.τ
          subst h_tau
          refine ⟨?_, ?_⟩
          · -- Pointwise validity
            intro γ'
            simp [CMRA.op]
            by_cases h_gamma : γ' = γ
            · -- At key γ: frame has none, so just need validity of singleton
              simp [h_gamma, iSingleton, optionOp, h_mz_gamma, CMRA.ValidN, optionValidN]
              simp [CMRA.op?] at Ha'_valid
              have h_bundle_valid : ✓{n} (E.Bundle a') := ElemG.Bundle_validN E a' Ha'_valid
              exact IProp.unfoldi_validN (E.Bundle a') h_bundle_valid
            · -- At other keys: just propagate frame validity
              simp [h_gamma, iSingleton, optionOp]
              have h_frame_valid := Hv E.τ
              simp [CMRA.op?] at h_frame_valid
              rcases h_frame_valid with ⟨h_pointwise, _⟩
              have h_at_gamma' := h_pointwise γ'
              simp [CMRA.op, iSingleton, h_gamma, optionOp] at h_at_gamma'
              exact h_at_gamma'
          · -- Infinite free keys
            have h_frame_inf := Hv E.τ
            simp [CMRA.op?] at h_frame_inf
            rcases h_frame_inf with ⟨_, h_inf⟩
            -- The frame has infinite free keys when composed with the old singleton
            -- We need to show it still has infinite free keys with the new singleton
            -- Since both singletons only occupy key γ, the free keys are the same
            apply Infinite.mono h_inf
            intro k h_free
            simp [IsFree, CMRA.op, iSingleton, optionOp] at h_free ⊢
            by_cases h_k : k = γ
            · simp [h_k, h_mz_gamma, optionOp] at h_free
            · simp [h_k, optionOp] at h_free ⊢
              exact h_free
        · -- At τ' ≠ E.τ: both singleton and composition are well-behaved
          have h_frame_valid := Hv τ'
          simp [CMRA.op?, CMRA.op, iSingleton, h_tau] at h_frame_valid ⊢
          exact h_frame_valid

      | some v =>
        -- Frame has some v at γ
        have h_a_valid : ✓{n} (a • E.Unbundle (IProp.foldi v)) := by
          have h_valid_at_tau : ✓{n} ((iSingleton F γ a •? some mz') E.τ) := Hv E.τ
          simp [CMRA.op?] at h_valid_at_tau
          rcases h_valid_at_tau with ⟨h_pointwise, _⟩
          have h_at_gamma : ✓{n} ((((iSingleton F γ a) • mz') E.τ).car γ) := h_pointwise γ
          simp [iSingleton, CMRA.op, optionOp, h_mz_gamma] at h_at_gamma
          simp [CMRA.ValidN, optionValidN] at h_at_gamma
          -- h_at_gamma : ✓{n} (unfoldi (E.Bundle a) • v)
          -- Need: ✓{n} (a • E.Unbundle (foldi v))
          -- Strategy: Apply foldi (which is a CMRA homomorphism)
          simp [IProp.foldi, IProp.unfoldi] at h_at_gamma ⊢
          letI : RFunctor (GF E.τ).fst := (GF E.τ).snd.toRFunctor
          -- foldi preserves validity
          have h_foldi_valid : ✓{n} ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f
              ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a) • v)) := by
            exact IProp.foldi_validN _ h_at_gamma
          -- foldi is a homomorphism
          have h_foldi_hom := (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).op
              ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a)) v
          have h_after_hom : ✓{n} ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f
              ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a)) •
              (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v) := by
            apply CMRA.validN_ne h_foldi_hom.dist
            exact h_foldi_valid
          -- Use foldi_unfoldi_comp
          have h_comp : (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f
              ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a)) ≡ E.Bundle a := by
            refine .trans (OFunctor.map_comp (F := GF E.τ |>.fst) ..).symm ?_
            refine .trans ?_ (OFunctor.map_id (F := GF E.τ |>.fst) (E.Bundle a))
            apply OFunctor.map_ne.eqv <;> intro _ <;> simp [IProp.unfold, IProp.fold]
          have h_bundle_foldi_v : ✓{n} (E.Bundle a • (RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v) := by
            apply CMRA.validN_ne (h_comp.op_l).dist
            exact h_after_hom
          -- Apply Unbundle
          have h_unbundle_hom := ElemG.Unbundle_op E (E.Bundle a) ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v)
          have h_after_unbundle : ✓{n} (E.Unbundle (E.Bundle a) • E.Unbundle ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v)) := by
            apply CMRA.validN_ne h_unbundle_hom.dist
            exact ElemG.Unbundle_validN E _ h_bundle_foldi_v
          -- Use Unbundle_Bundle
          have h_unbundle_bundle := ElemG.Unbundle_Bundle E a
          apply CMRA.validN_ne (h_unbundle_bundle.op_l).dist
          exact h_after_unbundle

        obtain ⟨a', Ha'_P, Ha'_valid⟩ := Hupd n (some (E.Unbundle (IProp.foldi v))) (by simp [CMRA.op?]; exact h_a_valid)

        refine ⟨iSingleton F γ a', ⟨a', rfl, Ha'_P⟩, ?_⟩
        -- Show ✓{n} (iSingleton F γ a' •? some mz')
        -- This is the reverse of extracting h_a_valid from Hv
        simp [CMRA.op?]
        intro τ'
        by_cases h_tau : τ' = E.τ
        · -- At τ' = E.τ
          subst h_tau
          refine ⟨?_, ?_⟩
          · -- Pointwise validity
            intro γ'
            simp [CMRA.op]
            by_cases h_gamma : γ' = γ
            · -- At key γ: need to go from Ha'_valid to validity of singleton • frame
              simp [h_gamma, iSingleton, optionOp, h_mz_gamma, CMRA.ValidN, optionValidN]
              -- Ha'_valid : ✓{n} (a' • E.Unbundle (foldi v))
              -- Need: ✓{n} (unfoldi (E.Bundle a') • v)
              simp [CMRA.op?] at Ha'_valid
              -- Reverse of what we did before
              letI : RFunctor (GF E.τ).fst := (GF E.τ).snd.toRFunctor
              -- From ✓{n} (a' • E.Unbundle (foldi v))
              -- Apply Bundle
              have h_bundle_valid : ✓{n} (E.Bundle a' • E.Bundle (E.Unbundle (foldi v))) := by
                have h_bundle_op := ElemG.Bundle_op E a' (E.Unbundle (foldi v))
                apply CMRA.validN_ne h_bundle_op.dist
                exact ElemG.Bundle_validN E _ Ha'_valid
              -- Use Bundle_Unbundle
              have h_bundle_unbundle := ElemG.Bundle_Unbundle E (foldi v)
              have h_bundle_foldi_v : ✓{n} (E.Bundle a' • foldi v) := by
                apply CMRA.validN_ne (h_bundle_unbundle.op_r).dist
                exact h_bundle_valid
              -- Apply unfoldi
              simp [IProp.unfoldi, IProp.foldi] at h_bundle_foldi_v ⊢
              have h_unfoldi_op := (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).op (E.Bundle a') ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v)
              have h_after_unfoldi : ✓{n} ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f (E.Bundle a') •
                  (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f ((RFunctor.map (IProp.unfold GF) (IProp.fold GF)).toHom.f v)) := by
                apply CMRA.validN_ne h_unfoldi_op.dist
                exact IProp.unfoldi_validN _ h_bundle_foldi_v
              -- Use unfoldi_foldi
              have h_unfoldi_foldi := IProp.unfoldi_foldi v
              apply CMRA.validN_ne (h_unfoldi_foldi.op_r).dist
              exact h_after_unfoldi
            · -- At other keys: propagate frame validity
              simp [h_gamma, iSingleton, optionOp]
              have h_frame_valid := Hv E.τ
              simp [CMRA.op?] at h_frame_valid
              rcases h_frame_valid with ⟨h_pointwise, _⟩
              have h_at_gamma' := h_pointwise γ'
              simp [CMRA.op, iSingleton, h_gamma, optionOp] at h_at_gamma'
              exact h_at_gamma'
          · -- Infinite free keys
            have h_frame_inf := Hv E.τ
            simp [CMRA.op?] at h_frame_inf
            rcases h_frame_inf with ⟨_, h_inf⟩
            apply Infinite.mono h_inf
            intro k h_free
            simp [IsFree, CMRA.op, iSingleton, optionOp] at h_free ⊢
            by_cases h_k : k = γ
            · simp [h_k, h_mz_gamma, optionOp] at h_free
            · simp [h_k, optionOp] at h_free ⊢
              exact h_free
        · -- At τ' ≠ E.τ
          have h_frame_valid := Hv τ'
          simp [CMRA.op?, CMRA.op, iSingleton, h_tau] at h_frame_valid ⊢
          exact h_frame_valid
  · refine BIUpdate.mono (BI.exists_elim (fun m => BI.pure_elim_l (fun ⟨a', Hm, HP⟩ => ?_)))
    subst Hm
    exact BI.exists_intro' a' (BI.persistent_entails_r (BI.pure_intro HP))

theorem iOwn_update {γ} {a a' : F.ap (IProp GF)} (Hupd : a ~~> a') : iOwn γ a ⊢ |==> iOwn γ a' := by
  refine .trans (iOwn_updateP <| UpdateP.of_update Hupd) ?_
  refine BIUpdate.mono ?_
  refine BI.exists_elim (fun m => ?_)
  refine BI.pure_elim (a' = m) BI.sep_elim_l ?_
  rintro rfl
  exact BI.sep_elim_r

-- Helper lemmas for iOwn_unit

-- Bundle preserves unit structure
theorem ElemG.Bundle_unit {GF F} [RFunctorContractive F] (E : ElemG GF F)
    {ε : F.ap (IProp GF)} [IsUnit ε] :
    IsUnit (E.Bundle ε) := by
  refine { unit_valid := ?_, unit_left_id := ?_, pcore_unit := ?_ }
  · -- Validity: use Bundle_validN
    refine CMRA.valid_iff_validN.mpr fun n => ?_
    exact ElemG.Bundle_validN E ε IsUnit.unit_valid.validN
  · -- Left identity: Strategy: apply Unbundle to both sides, use that ε is unit, then Bundle back
    intro x
    have h1 : E.Unbundle (E.Bundle ε • x) ≡ E.Unbundle x := by
      calc E.Unbundle (E.Bundle ε • x)
        _ ≡ E.Unbundle (E.Bundle ε) • E.Unbundle x := ElemG.Unbundle_op E _ _
        _ ≡ ε • E.Unbundle x := (ElemG.Unbundle_Bundle E ε).op_l
        _ ≡ E.Unbundle x := IsUnit.unit_left_id
    calc E.Bundle ε • x
      ≡ E.Bundle (E.Unbundle (E.Bundle ε • x)) := (ElemG.Bundle_Unbundle E _).symm
      _ ≡ E.Bundle (E.Unbundle x) := OFE.NonExpansive.eqv h1
      _ ≡ x := ElemG.Bundle_Unbundle E x
  · -- Pcore
    calc CMRA.pcore (E.Bundle ε)
      ≡ (CMRA.pcore ε).map E.Bundle := (ElemG.Bundle_pcore E ε).symm
      _ ≡ Option.map E.Bundle (some ε) := by
         rename_i unit
         have := unit.pcore_unit
         rcases eqn: CMRA.pcore ε
         · rw [eqn] at this; simp [Option.Forall₂] at this
         · rw [eqn] at this; simp [Option.Forall₂, Option.map] at this ⊢
           exact NonExpansive.eqv this
      _ ≡ E.Bundle ε := by rfl

-- unfoldi preserves unit structure
theorem IProp.unfoldi_unit {GF : BundledGFunctors} {τ : GType}
    {x : GF.api τ (IProp GF)} [IsUnit x] :
    IsUnit (unfoldi x) := by
  refine { unit_valid := ?_, unit_left_id := ?_, pcore_unit := ?_ }
  · -- Validity
    refine CMRA.valid_iff_validN.mpr fun n => IProp.unfoldi_validN x IsUnit.unit_valid.validN
  · -- Left identity: unfoldi x • y ≡ y
    intro y
    have h : foldi (unfoldi x • y) ≡ foldi y := by
      calc foldi (unfoldi x • y)
        _ ≡ foldi (unfoldi x) • foldi y := foldi_op _ _
        _ ≡ x • foldi y := (foldi_unfoldi_comp x).op_l
        _ ≡ foldi y := IsUnit.unit_left_id
    calc unfoldi x • y
      _ ≡ unfoldi (foldi (unfoldi x • y)) := (IProp.unfoldi_foldi _).symm
      _ ≡ unfoldi (foldi y) := OFE.NonExpansive.eqv h
      _ ≡ y := IProp.unfoldi_foldi y
  · -- pcore_unit
    simp only [unfoldi, OFunctor.map]
    letI : RFunctor (GF τ).fst := (GF τ).snd.toRFunctor
    calc CMRA.pcore ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f x)
      _ ≡ (CMRA.pcore x).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f :=
        (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).pcore x |>.symm
      _ ≡ (some x).map (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f :=
        Option.map_forall₂ _ IsUnit.pcore_unit
      _ ≡ some ((RFunctor.map (IProp.fold GF) (IProp.unfold GF)).toHom.f x) := by
        simp [Option.map, Option.Forall₂, OFE.Equiv.rfl]

-- Subsection: Unit allocation (with helpers)

-- Helper: UCMRA.unit composes neutrally with any map at type τ
theorem unit_op_eq {GF : BundledGFunctors} (τ : GType) (m : GenMap GName (GF.api τ (IPre GF))) :
    ((UCMRA.unit : IResUR GF) τ) • m ≡ m := by
  simp [OFE.Equiv, CMRA.op, UCMRA.unit, optionOp, Option.Forall₂]
  intro k; cases m.car k <;> simp [OFE.Equiv.rfl]

-- Helper: unfoldi of Bundle of unit is a unit
theorem unfoldi_bundle_unit {GF F} [RFunctorContractive F] (E : ElemG GF F)
    {ε : F.ap (IProp GF)} [IsUnit ε] : IsUnit (IProp.unfoldi (E.Bundle ε)) :=
  haveI : IsUnit (E.Bundle ε) := ElemG.Bundle_unit E
  IProp.unfoldi_unit

-- Helper: validity of unfoldi (Bundle ε) at level n
theorem unfoldi_bundle_validN {GF F} [RFunctorContractive F] (E : ElemG GF F)
    {ε : F.ap (IProp GF)} [IsUnit ε] (n : Nat) : ✓{n} (IProp.unfoldi (E.Bundle ε)) := by
  have h1 : ✓{n} (E.Bundle ε) := ElemG.Bundle_validN E ε IsUnit.unit_valid.validN
  simp [IProp.unfoldi]
  letI : RFunctor (GF E.τ).fst := (GF E.τ).snd.toRFunctor
  exact (RFunctor.map (IProp.fold GF) (IProp.unfold GF)).validN h1

-- Helper: extract validity of element at key from unit-composed frame
theorem extract_frame_validN {GF : BundledGFunctors} (τ : GType) (n : Nat)
    (mz' : IResUR GF)
    (h_valid : ✓{n} ((UCMRA.unit : IResUR GF) τ • mz' τ).car)
    (γ : GName) (v : GF.api τ (IPre GF)) (h_at : (mz' τ).car γ = some v) :
    ✓{n} v := by
  have := h_valid γ
  simp [CMRA.op, UCMRA.unit, optionOp, CMRA.ValidN, optionValidN, h_at] at this
  exact this

theorem iOwn_unit {γ} {ε : F.ap (IProp GF)} [Hε : IsUnit ε] : ⊢ |==> iOwn γ ε := by
  unfold iOwn

  -- First, use ownM_unit to get emp ⊢ □ ownM ε
  refine .trans (UPred.ownM_unit _) ?_
  refine BI.intuitionistically_elim.trans ?_

  -- Now we need to show: ownM (UCMRA.unit : IResUR GF) ⊢ |==> ownM (iSingleton F γ ε)
  -- This requires a CMRA update: UCMRA.unit ~~> iSingleton F γ ε
  have Hupd : (UCMRA.unit : IResUR GF) ~~>: (iSingleton F γ ε = ·) := by
    intro n mz Hv
    refine ⟨iSingleton F γ ε, rfl, ?_⟩
    -- Show ✓{n} (iSingleton F γ ε •? mz)
    intro τ'
    by_cases Heq : τ' = E.τ
    · -- At τ' = E.τ: need to show validity at the allocated index
      subst Heq
      refine ⟨?_, ?_⟩
      · -- Pointwise validity at each key
        intro γ'
        unfold iSingleton
        simp [CMRA.op?, CMRA.ValidN, optionValidN]
        cases mz with
        | none =>
          -- No frame: just need validity of the singleton
          simp [CMRA.op, optionOp]
          by_cases h_key : γ' = γ
          · simp [h_key]; exact unfoldi_bundle_validN E n
          · simp [h_key]
        | some mz' =>
          -- With frame: use that unfoldi (Bundle ε) is a unit
          simp [CMRA.op, optionOp]
          have Hv' := Hv E.τ
          simp [CMRA.op?] at Hv'
          rcases Hv' with ⟨h_valid, _⟩
          by_cases h_key : γ' = γ
          · -- At the key γ where we're allocating
            simp [h_key]
            rcases h_at : (mz' E.τ).car γ with (⟨⟩ | v)
            · simp [optionOp]; exact unfoldi_bundle_validN E n
            · simp [optionOp]
              haveI h_unit : IsUnit (IProp.unfoldi (E.Bundle ε)) := unfoldi_bundle_unit E
              have h_v_valid := extract_frame_validN E.τ n mz' h_valid γ v h_at
              exact CMRA.validN_ne h_unit.unit_left_id.dist.symm h_v_valid
          · -- At other keys: propagate frame validity
            simp [h_key]
            rcases h_at : (mz' E.τ).car γ' with (⟨⟩ | v)
            · trivial
            · simp [optionOp]; exact extract_frame_validN E.τ n mz' h_valid γ' v h_at
      · -- Infinite free keys: allocation doesn't consume free keys
        cases mz with
        | none => exact iSingleton_infinite_free γ ε
        | some mz' =>
          have ⟨_, h_inf⟩ := Hv E.τ; simp [CMRA.op?] at h_inf
          have h_inf_mz : Infinite (IsFree (mz' E.τ).car) := by
            apply Infinite.mono h_inf
            intro k h_free; simp [IsFree, CMRA.op, UCMRA.unit, optionOp] at h_free ⊢; exact h_free
          exact iSingleton_preserves_infinite_free γ ε (mz' E.τ) h_inf_mz
    · -- At τ' ≠ E.τ: iSingleton is unit, so it composes neutrally
      have h_is_unit := iSingleton_ne_eq_unit γ ε τ' Heq
      cases mz with
      | none =>
        simp [CMRA.op?, CMRA.op, h_is_unit]
        show ✓{n} (⟨fun γ' => if _ : τ' = E.τ ∧ γ' = γ then _ else none⟩ : GenMap Nat _)
        simp [Heq]
        exact (UCMRA.unit_valid : ✓ (UCMRA.unit : GenMap Nat ((GF τ').fst (IPre GF) (IPre GF)))).validN
      | some mz' =>
        have Hv' := Hv τ'; simp [CMRA.op?] at Hv'
        have h_eq : ((UCMRA.unit : IResUR GF) • mz') τ' ≡ (iSingleton F γ ε •? some mz') τ' := by
          simp only [CMRA.op?, CMRA.op, h_is_unit, OFE.Equiv]
          intro k
          simp [UCMRA.unit, optionOp, Option.Forall₂]
          cases (mz' τ').car k <;> simp [OFE.Equiv.rfl]
        exact CMRA.validN_ne h_eq.dist Hv'

  refine .trans (UPred.ownM_updateP _ Hupd) ?_

  -- Clean up the assertion
  refine BIUpdate.mono ?_
  refine BI.exists_elim (fun y => ?_)
  refine BI.pure_elim (iSingleton F γ ε = y) BI.and_elim_l ?_
  rintro rfl
  exact BI.and_elim_r

/-
(** ** Allocation *)
(* TODO: This also holds if we just have ✓ a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
Lemma own_alloc_strong_dep (f : gname → A) (P : gname → Prop) :
  pred_infinite P →
  (∀ γ, P γ → ✓ (f γ)) →
  ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ (f γ).
Proof.
  intros HPinf Hf.
  rewrite -(bupd_mono (∃ m, ⌜∃ γ, P γ ∧ m = iRes_singleton γ (f γ)⌝ ∧ uPred_ownM m)%I).
  - rewrite /bi_emp_valid (ownM_unit emp).
    apply bupd_ownM_updateP, (discrete_fun_singleton_updateP_empty _ (λ m, ∃ γ,
      m = {[ γ := inG_unfold (cmra_transport inG_prf (f γ)) ]} ∧ P γ));
      [|naive_solver].
    apply (alloc_updateP_strong_dep _ P _ (λ γ,
      inG_unfold (cmra_transport inG_prf (f γ)))); [done| |naive_solver].
    intros γ _ ?.
    by apply (cmra_morphism_valid inG_unfold), cmra_transport_valid, Hf.
  - apply exist_elim=>m; apply pure_elim_l=>-[γ [Hfresh ->]].
    by rewrite !own_eq /own_def -(exist_intro γ) pure_True // left_id.
Qed.
Lemma own_alloc_cofinite_dep (f : gname → A) (G : gset gname) :
  (∀ γ, γ ∉ G → ✓ (f γ)) → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ (f γ).
Proof.
  intros Ha.
  apply (own_alloc_strong_dep f (λ γ, γ ∉ G))=> //.
  apply (pred_infinite_set (C:=gset gname)).
  intros E. set (γ := fresh (G ∪ E)).
  exists γ. apply not_elem_of_union, is_fresh.
Qed.
Lemma own_alloc_dep (f : gname → A) :
  (∀ γ, ✓ (f γ)) → ⊢ |==> ∃ γ, own γ (f γ).
Proof.
  intros Ha. rewrite /bi_emp_valid (own_alloc_cofinite_dep f ∅) //; [].
  apply bupd_mono, exist_mono=>?. apply: sep_elim_r.
Qed.

Lemma own_alloc_strong a (P : gname → Prop) :
  pred_infinite P →
  ✓ a → ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ a.
Proof. intros HP Ha. eapply (own_alloc_strong_dep (λ _, a)); eauto. Qed.
Lemma own_alloc_cofinite a (G : gset gname) :
  ✓ a → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ a.
Proof. intros Ha. eapply (own_alloc_cofinite_dep (λ _, a)); eauto. Qed.
Lemma own_alloc a : ✓ a → ⊢ |==> ∃ γ, own γ a.
Proof. intros Ha. eapply (own_alloc_dep (λ _, a)); eauto. Qed.
-/



end iOwn
end Iris
