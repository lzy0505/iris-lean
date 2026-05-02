/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Markus de Medeiros
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.LocalUpdates
meta import Iris.Std.RocqPorting

/-! ## Numbers CMRA
Simple CMRA's for commutative monoids.

There are three variants:
- "Constant core": the core is a fixed value such as 0 (eg. (ℕ, +))
- "Universal core": every element is a core (eg. (ℕ, max))
- "No core": there is no core (eg. (PNat, +))
-/

@[expose] public section

open Std

class IdentityFree (α : Type _) [Add α] where
  id_free {a b : α} : ¬ Add.add a b = a

class LeftCancelAdd (α : Type _) [Add α] where
  cancel_left {x₁ x₂ y : α} : y + x₁ = y + x₂ → x₁ = x₂

open Add Commutative in
theorem LeftCancelAdd.cancel_right {x₁ x₂ y : α} [Add α] [LeftCancelAdd α]
    [Commutative (add (α := α))] (h : add x₁ y = add x₂ y) : x₁ = x₂ := by
  refine cancel_left (y := y) ?_
  rw [← add_eq_hAdd, comm (op := Add.add) y x₁, h, comm (op := Add.add)]

/- Constant core -/
namespace CommMonoidLike

open Iris Iris.OFE Add Zero One Associative Commutative LawfulLeftIdentity CMRA

variable [OFE α] [Discrete α] [Leibniz α]
variable [Add α] [Associative (add (α := α))] [Commutative (add (α := α))]
variable [Zero α] [LawfulLeftIdentity (add (α := α)) zero]
variable {x y x' y' : α}

scoped instance : CMRA α where
  pcore _ := some zero
  op := add
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by rw [eq_of_eqv (discrete h)]
  pcore_ne _ := dist_some ∘ Dist.of_eq
  validN_ne _ _ := .intro
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left := id
  assoc {_ _ _} := by rw [assoc (op := add)]
  comm {_ _} := by rw [comm (op := add)]
  pcore_op_left {_ _} := by rintro ⟨rfl⟩; rw [left_id (op := add) _]
  pcore_idem := by simp
  pcore_op_mono {_ _} := by
    rintro ⟨rfl⟩ _
    exists zero
    rw [left_id (op := add) _]
  extend _ h := ⟨_, _, discrete h, .rfl, .rfl⟩

scoped instance : CMRA.Discrete α where
  discrete_valid := id

scoped instance : UCMRA α where
  unit := zero
  unit_valid := trivial
  unit_left_id := pcore_op_left rfl
  pcore_unit := .symm .rfl

scoped instance [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ eq_of_eqv ∘ discrete

/-- Sufficient condition for a local update on a LeftCancelAdd structure, such as (ℕ, +) -/
theorem leftCancelAdd_local_update [LeftCancelAdd α] (h : add x y' = add x' y) :
    (x, y) ~l~> (x', y') := by
  refine leibniz_discrete_unital_triv_local_update (fun _ => trivial) @fun z hz => ?_
  refine LeftCancelAdd.cancel_right (y := y) ?_
  calc
    add x' y = add x y' := h.symm
    _ = add (add y z) y' := by rw [hz]; rfl
    _ = add y' (add y z) := by rw [comm (op := add)]
    _ = add y' (add z y) := by rw [comm (op := add) z]
    _ = add (add y' z) y := by rw [assoc (op := add)]

scoped instance {a : α} : DiscreteE a := ⟨fun H => discrete H⟩

scoped instance : CoreId (α := α) 0 where
  core_id := by rfl

end CommMonoidLike

/- Universal core -/
namespace OrdCommMonoidLike

open Iris Iris.OFE Add Zero One Associative Commutative LawfulLeftIdentity CMRA IdempotentOp

variable [OFE α] [OFE.Discrete α] [Leibniz α]
variable [Add α] [Associative (add (α := α))] [Commutative (add (α := α))]
variable [IdempotentOp (add (α := α))]
variable [Zero α]
variable {x y x' y' : α}

scoped instance : CMRA α where
  pcore := some
  op := add
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by rw [eq_of_eqv (discrete h)]
  pcore_ne {_ y _ _} h := by
    rintro ⟨rfl⟩
    exact ⟨y, congrArg _ <| leibniz.mp (discrete h.symm), .rfl⟩
  validN_ne _ _ := .intro
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left := id
  assoc {_ _ _} := by rw [assoc (op := add)]
  comm {_ _} := by rw [comm (op := add)]
  pcore_op_left {_ _} := by
    rintro ⟨rfl⟩
    refine .of_eq <| idempotent _
  pcore_idem := by simp
  pcore_op_mono {a b} := by
    rintro ⟨rfl⟩ z
    exists z
  extend _ h := ⟨_, _, discrete h, .rfl, .rfl⟩

scoped instance : CMRA.Discrete α where
  discrete_valid := id

scoped instance (a : α) : CMRA.CoreId a where
  core_id := by simp [pcore]

scoped instance [LawfulLeftIdentity (add (α := α)) zero] : UCMRA α where
  unit := zero
  unit_valid := trivial
  unit_left_id := .of_eq <| left_id _
  pcore_unit := .symm .rfl

scoped instance [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ eq_of_eqv ∘ discrete

end OrdCommMonoidLike

/- NoCore core -/
namespace PosCommMonoidLike

open Iris Iris.OFE Add Zero One Associative Commutative LawfulLeftIdentity CMRA IdempotentOp

variable [OFE α] [OFE.Discrete α] [Leibniz α]
variable [Add α] [Associative (add (α := α))] [Commutative (add (α := α))]
variable [IdempotentOp (add (α := α))]

variable {x y x' y' : α}

scoped instance : CMRA α where
  pcore _ := none
  op := add
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by rw [eq_of_eqv (discrete h)]
  pcore_ne _ := by rintro ⟨rfl⟩
  validN_ne _ _ := .intro
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left := id
  assoc {_ _ _} := by rw [assoc (op := add)]
  comm {_ _} := by rw [comm (op := add)]
  pcore_op_left {_ _} := by rintro ⟨rfl⟩
  pcore_idem := by simp
  pcore_op_mono {_ _} := by rintro ⟨rfl⟩
  extend _ h := ⟨_, _, discrete h, .rfl, .rfl⟩

scoped instance : CMRA.Discrete α where
  discrete_valid := id

scoped instance [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ eq_of_eqv ∘ discrete

scoped instance [IdentityFree α] {a : α} : CMRA.IdFree a where
  id_free0_r _ _ h := IdentityFree.id_free (α := α) <| leibniz.mp (discrete h)

end PosCommMonoidLike

/-! ## `MaxNat` -/

namespace Iris

@[rocq_alias max_nat]
structure MaxNat where
  car : Nat

namespace MaxNat

@[reducible] instance : Add MaxNat := ⟨fun x y => ⟨x.car.max y.car⟩⟩
@[reducible] instance : Zero MaxNat := ⟨⟨0⟩⟩

scoped instance : Associative (Add.add (α := MaxNat)) where
  assoc := fun {x y z} => by
    simp only [Add.add]
    exact congrArg MaxNat.mk (Nat.max_assoc ..)
scoped instance : Commutative (Add.add (α := MaxNat)) where
  comm := fun {x y} => by
    simp only [Add.add]
    exact congrArg MaxNat.mk (Nat.max_comm ..)
scoped instance : IdempotentOp (Add.add (α := MaxNat)) where
  idempotent x := by
    simp only [Add.add]
    cases x
    exact congrArg MaxNat.mk (Nat.max_self _)
scoped instance : @LeftIdentity MaxNat MaxNat Add.add (Zero.zero : MaxNat) where
scoped instance : @LawfulLeftIdentity MaxNat MaxNat Add.add (Zero.zero : MaxNat) where
  left_id := fun {x} => by
    simp only [Add.add]
    cases x
    exact congrArg MaxNat.mk (Nat.zero_max _)

scoped instance : Iris.COFE MaxNat := Iris.COFE.ofDiscrete _ Iris.Eq_Equivalence
scoped instance : Iris.OFE.Discrete MaxNat := ⟨id⟩
scoped instance : Iris.OFE.Leibniz MaxNat := ⟨id⟩

open scoped OrdCommMonoidLike

scoped instance : Iris.UCMRA MaxNat := inferInstance
scoped instance : Iris.CMRA.Discrete MaxNat := inferInstance
scoped instance (a : MaxNat) : Iris.CMRA.CoreId a := inferInstance

@[rocq_alias max_nat_op]
theorem op (x y : Nat) : (MaxNat.mk x) • (MaxNat.mk y) = MaxNat.mk (x.max y) := rfl

@[rocq_alias max_nat_included]
theorem included {x y : MaxNat} : x ≼ y ↔ x.car ≤ y.car := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨z⟩, h⟩
    rw [op] at h
    cases h
    exact Nat.le_max_left _ _
  · intro h
    refine ⟨y, ?_⟩
    cases x; cases y
    rw [op]
    exact congrArg MaxNat.mk (Nat.max_eq_right h).symm

@[rocq_alias max_nat_local_update]
theorem local_update {x y x' : MaxNat} (h : x.car ≤ x'.car) :
    (x, y) ~l~> (x', x') := by
  refine (local_update_unital_discrete x y x' x').mpr fun ⟨z⟩ _ he => ?_
  refine ⟨trivial, ?_⟩
  rcases x with ⟨xc⟩; rcases x' with ⟨xc'⟩; cases y
  simp only [op] at he
  cases he
  refine .of_eq (congrArg MaxNat.mk ?_)
  show xc' = xc'.max z
  simp only at h
  exact (Nat.max_eq_left (Nat.le_trans (Nat.le_max_right _ _) h)).symm

#rocq_ignore max_natO "Use the MaxNat type and inferred OFE/COFE instances"
#rocq_ignore max_natR "Use the MaxNat type and OrdCommMonoidLike CMRA instance"
#rocq_ignore max_natUR "Use the MaxNat type and OrdCommMonoidLike UCMRA instance"

#rocq_ignore max_nat_unit_instance "Provided by OrdCommMonoidLike.instUCMRA"
#rocq_ignore max_nat_valid_instance "Provided by OrdCommMonoidLike.instCMRA"
#rocq_ignore max_nat_validN_instance "Provided by OrdCommMonoidLike.instCMRA"
#rocq_ignore max_nat_pcore_instance "Provided by OrdCommMonoidLike.instCMRA"
#rocq_ignore max_nat_op_instance "Use the Add instance and OrdCommMonoidLike.instCMRA"

#rocq_ignore max_nat_ra_mixin "Subsumed by OrdCommMonoidLike.instCMRA"
#rocq_ignore max_nat_cmra_discrete "Provided by OrdCommMonoidLike.instDiscrete"
#rocq_ignore max_nat_ucmra_mixin "Subsumed by OrdCommMonoidLike.instUCMRA"
#rocq_ignore max_nat_core_id "Provided by OrdCommMonoidLike.instCoreId"

end MaxNat

/-! ## `MaxZ` -/

@[rocq_alias max_Z]
structure MaxZ where
  car : Int

namespace MaxZ

@[reducible] instance : Add MaxZ := ⟨fun x y => ⟨max x.car y.car⟩⟩
/-- Required by the `OrdCommMonoidLike` CMRA scaffold. `MaxZ` is **not** a UCMRA — `0`
is not the bottom element under `Int.max` — so no `LawfulLeftIdentity` instance is
provided. `MonoZ` therefore wraps `MaxZ` in `Option` to obtain a unit. -/
@[reducible] instance : Zero MaxZ := ⟨⟨0⟩⟩

scoped instance : Associative (Add.add (α := MaxZ)) where
  assoc := fun {x _ _} => by
    simp only [Add.add]
    exact congrArg MaxZ.mk (Int.max_assoc ..)
scoped instance : Commutative (Add.add (α := MaxZ)) where
  comm := fun {x y} => by
    simp only [Add.add]
    exact congrArg MaxZ.mk (Int.max_comm x.car y.car)
scoped instance : IdempotentOp (Add.add (α := MaxZ)) where
  idempotent x := by
    simp only [Add.add]
    cases x
    exact congrArg MaxZ.mk (Int.max_self _)

scoped instance : Iris.COFE MaxZ := Iris.COFE.ofDiscrete _ Iris.Eq_Equivalence
scoped instance : Iris.OFE.Discrete MaxZ := ⟨id⟩
scoped instance : Iris.OFE.Leibniz MaxZ := ⟨id⟩

open scoped OrdCommMonoidLike

scoped instance : Iris.CMRA MaxZ := inferInstance
scoped instance : Iris.CMRA.Discrete MaxZ := inferInstance
scoped instance (a : MaxZ) : Iris.CMRA.CoreId a := inferInstance

scoped instance : Iris.CMRA.IsTotal MaxZ where
  total x := ⟨x, rfl⟩

/-- Every `some (MaxZ.mk n)` is `CoreId` because `MaxZ` is a universal-core CMRA.
Useful when wrapping `MaxZ` in `Option` to obtain a UCMRA (e.g. for `MonoZ`). -/
scoped instance some_core_id (n : Int) : Iris.CMRA.CoreId (some (MaxZ.mk n)) where
  core_id := show some (some (MaxZ.mk n)) ≡ some (some (MaxZ.mk n)) from .rfl

@[rocq_alias max_Z_op]
theorem op (x y : Int) : (MaxZ.mk x) • (MaxZ.mk y) = MaxZ.mk (max x y) := rfl

@[rocq_alias max_Z_included]
theorem included {x y : MaxZ} : x ≼ y ↔ x.car ≤ y.car := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨z⟩, h⟩
    rw [op] at h
    cases h
    exact Int.le_max_left _ _
  · intro h
    refine ⟨y, ?_⟩
    cases x; cases y
    rw [op]
    exact congrArg MaxZ.mk (Int.max_eq_right h).symm

@[rocq_alias max_Z_local_update]
theorem local_update {x y x' : MaxZ} (h : x.car ≤ x'.car) :
    (x, y) ~l~> (x', x') := by
  refine (LocalUpdate.discrete x y x' x').mpr ?_
  rintro mz _ he
  refine ⟨trivial, ?_⟩
  rcases x with ⟨xc⟩; rcases x' with ⟨xc'⟩; cases y
  match mz, he with
  | none, _ => exact .rfl
  | some ⟨z⟩, he =>
    simp only [CMRA.op?, op] at he
    cases (OFE.eq_of_eqv he : _ = _)
    refine .of_eq (congrArg MaxZ.mk ?_)
    show xc' = max xc' z
    exact (Int.max_eq_left (Int.le_trans (Int.le_max_right _ _) h)).symm

#rocq_ignore max_ZO "Use the MaxZ type and inferred OFE/COFE instances"
#rocq_ignore max_ZR "Use the MaxZ type and OrdCommMonoidLike CMRA instance"

#rocq_ignore max_Z_unit_instance "Carrier is not a UCMRA; MonoZ wraps it in Option"
#rocq_ignore max_Z_valid_instance "Provided by OrdCommMonoidLike.instCMRA"
#rocq_ignore max_Z_validN_instance "Provided by OrdCommMonoidLike.instCMRA"
#rocq_ignore max_Z_pcore_instance "Provided by OrdCommMonoidLike.instCMRA"
#rocq_ignore max_Z_op_instance "Use the Add instance and OrdCommMonoidLike.instCMRA"

#rocq_ignore max_Z_ra_mixin "Subsumed by OrdCommMonoidLike.instCMRA"
#rocq_ignore max_Z_cmra_total "Provided by OrdCommMonoidLike (CMRA has total core)"
#rocq_ignore max_Z_cmra_discrete "Provided by OrdCommMonoidLike.instDiscrete"
#rocq_ignore max_Z_core_id "Provided by OrdCommMonoidLike.instCoreId"

end MaxZ

end Iris
