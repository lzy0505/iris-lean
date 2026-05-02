/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers
public import Iris.Algebra.Updates
public import Iris.Algebra.Frac
meta import Iris.Std.RocqPorting

/-! # Authoritative CMRA over `MaxNat` -/

@[expose] public section

namespace Iris

open OFE COFE CMRA UCMRA Auth

open scoped MaxNat MaxZ OrdCommMonoidLike

namespace MonoNat

@[rocq_alias mono_nat]
abbrev MonoNat := Auth PNat MaxNat

#rocq_ignore mono_natR "Use the MonoNat type and View.instCMRA typeclass"
#rocq_ignore mono_natUR "Use the MonoNat type and View.instUCMRA typeclass"

@[rocq_alias mono_nat_auth]
def auth (dq : DFrac PNat) (n : Nat) : MonoNat :=
  Auth.auth dq (MaxNat.mk n) • Auth.frag (MaxNat.mk n)

@[rocq_alias mono_nat_lb]
def lb (n : Nat) : MonoNat := Auth.frag (MaxNat.mk n)

scoped notation "●MN{" dq "} " n => MonoNat.auth dq n
scoped notation "●MN " n => MonoNat.auth (DFrac.own One.one) n
scoped notation "●MN□ " n => MonoNat.auth DFrac.discard n
scoped notation "◯MN " n => MonoNat.lb n

@[rocq_alias mono_nat_lb_core_id]
instance lb_core_id (n : Nat) : CoreId (◯MN n) :=
  show CoreId (Auth.frag (MaxNat.mk n)) from inferInstance

@[rocq_alias mono_nat_auth_core_id]
instance auth_core_id (n : Nat) : CoreId (●MN□ n) :=
  show CoreId ((Auth.auth DFrac.discard (MaxNat.mk n) : MonoNat) • Auth.frag (MaxNat.mk n)) from
    inferInstance

@[rocq_alias mono_nat_auth_dfrac_op]
theorem auth_dfrac_op {dq1 dq2 : DFrac PNat} {n : Nat} :
    (●MN{dq1 • dq2} n) ≡ (●MN{dq1} n) • (●MN{dq2} n) := by
  let A1 : MonoNat := Auth.auth dq1 (MaxNat.mk n)
  let A2 : MonoNat := Auth.auth dq2 (MaxNat.mk n)
  let F  : MonoNat := Auth.frag (MaxNat.mk n)
  calc (Auth.auth (dq1 • dq2) (MaxNat.mk n) • F : MonoNat)
      ≡ (A1 • A2) • F           := Auth.auth_dfrac_op.op_l
    _ ≡ (A1 • A2) • (F • F)     := (CMRA.op_self _).symm.op_r
    _ ≡ ((A1 • A2) • F) • F     := CMRA.assoc
    _ ≡ (A1 • (A2 • F)) • F     := CMRA.assoc.symm.op_l
    _ ≡ (A1 • (F • A2)) • F     := CMRA.comm.op_r.op_l
    _ ≡ ((A1 • F) • A2) • F     := CMRA.assoc.op_l
    _ ≡ (A1 • F) • (A2 • F)     := CMRA.assoc.symm

@[rocq_alias mono_nat_lb_op]
theorem lb_op {n1 n2 : Nat} : (◯MN (n1.max n2)) = (◯MN n1) • (◯MN n2) :=
  Auth.frag_op

@[rocq_alias mono_nat_auth_lb_op]
theorem auth_lb_op {dq : DFrac PNat} {n : Nat} :
    (●MN{dq} n) ≡ (●MN{dq} n) • (◯MN n) :=
  (CMRA.op_self _).symm.op_r |>.trans CMRA.assoc

@[rocq_alias mono_nat_lb_op_le_l]
theorem lb_op_le_l {n n' : Nat} (h : n' ≤ n) : (◯MN n) = (◯MN n') • (◯MN n) := by
  rw [← lb_op]
  show (◯MN n) = ◯MN (max n' n)
  rw [Nat.max_eq_right h]

@[rocq_alias mono_nat_auth_dfrac_valid]
theorem auth_dfrac_valid {dq : DFrac PNat} {n : Nat} : (✓ ●MN{dq} n) ↔ ✓ dq := by
  show ✓ (Auth.auth dq (MaxNat.mk n) • Auth.frag (MaxNat.mk n) : MonoNat) ↔ ✓ dq
  rw [Auth.both_dfrac_valid_discrete]
  exact ⟨(·.1), fun h => ⟨h, CMRA.inc_refl _, trivial⟩⟩

@[rocq_alias mono_nat_auth_valid]
theorem auth_valid {n : Nat} : ✓ (●MN n) := auth_dfrac_valid.mpr DFrac.valid_own_one

@[rocq_alias mono_nat_auth_dfrac_op_valid]
theorem auth_dfrac_op_valid {dq1 dq2 : DFrac PNat} {n1 n2 : Nat} :
    (✓ (●MN{dq1} n1) • (●MN{dq2} n2)) ↔ ✓ (dq1 • dq2) ∧ n1 = n2 := by
  refine ⟨?_, ?_⟩
  · intro h
    let A1 : MonoNat := Auth.auth dq1 (MaxNat.mk n1)
    let A2 : MonoNat := Auth.auth dq2 (MaxNat.mk n2)
    let F1 : MonoNat := Auth.frag (MaxNat.mk n1)
    let F2 : MonoNat := Auth.frag (MaxNat.mk n2)
    have hauth : ✓ (A1 • A2 : MonoNat) := CMRA.valid_op_left <| CMRA.valid_of_eqv
      (calc (A1 • F1) • (A2 • F2)
          ≡ ((A1 • F1) • A2) • F2 := CMRA.assoc
        _ ≡ (A1 • (F1 • A2)) • F2 := CMRA.assoc.symm.op_l
        _ ≡ (A1 • (A2 • F1)) • F2 := CMRA.comm.op_r.op_l
        _ ≡ ((A1 • A2) • F1) • F2 := CMRA.assoc.op_l
        _ ≡ (A1 • A2) • (F1 • F2) := CMRA.assoc.symm) h
    have ⟨hdq, hne, _⟩ := Auth.auth_dfrac_op_valid.mp hauth
    exact ⟨hdq, congrArg MaxNat.car (OFE.eq_of_eqv hne)⟩
  · rintro ⟨hdq, rfl⟩
    exact CMRA.valid_of_eqv (auth_dfrac_op (dq1 := dq1) (dq2 := dq2) (n := n1))
      (auth_dfrac_valid.mpr hdq)

@[rocq_alias mono_nat_auth_op_valid]
theorem auth_op_valid {n1 n2 : Nat} : (✓ (●MN n1) • (●MN n2)) ↔ False :=
  ⟨fun h => UFraction.one_whole.2 (DFrac.valid_op_own (auth_dfrac_op_valid.mp h).1), False.elim⟩

@[rocq_alias mono_nat_both_dfrac_valid]
theorem both_dfrac_valid {dq : DFrac PNat} {n m : Nat} :
    (✓ (●MN{dq} n) • (◯MN m)) ↔ ✓ dq ∧ m ≤ n := by
  have hreassoc :
      ((●MN{dq} n) • (◯MN m) : MonoNat) ≡
        Auth.auth dq (MaxNat.mk n) • Auth.frag (MaxNat.mk (n.max m)) :=
    CMRA.assoc.symm.trans <| CMRA.op_right_eqv _ <| .of_eq <|
      show ((Auth.frag (MaxNat.mk n) : MonoNat) • Auth.frag (MaxNat.mk m)) =
           Auth.frag (MaxNat.mk (n.max m)) from Auth.frag_op.symm
  rw [CMRA.valid_iff hreassoc, Auth.both_dfrac_valid_discrete, MaxNat.included]
  refine ⟨fun ⟨h, hinc, _⟩ => ⟨h, Nat.le_trans (Nat.le_max_right _ _) hinc⟩, ?_⟩
  rintro ⟨h, hle⟩
  exact ⟨h, Nat.max_le.mpr ⟨Nat.le_refl _, hle⟩, trivial⟩

@[rocq_alias mono_nat_both_valid]
theorem both_valid {n m : Nat} : (✓ (●MN n) • (◯MN m)) ↔ m ≤ n :=
  ⟨fun h => (both_dfrac_valid.mp h).2, fun h => both_dfrac_valid.mpr ⟨DFrac.valid_own_one, h⟩⟩

@[rocq_alias mono_nat_lb_mono]
theorem lb_mono {n1 n2 : Nat} (h : n1 ≤ n2) : (◯MN n1) ≼ (◯MN n2) :=
  Auth.frag_inc_of_inc (MaxNat.included.mpr h)

@[rocq_alias mono_nat_included]
theorem included {dq : DFrac PNat} {n : Nat} : (◯MN n) ≼ (●MN{dq} n) :=
  CMRA.inc_op_right _ _

@[rocq_alias mono_nat_update]
theorem update {n n' : Nat} (h : n ≤ n') : (●MN n) ~~> (●MN n') :=
  Auth.auth_update (MaxNat.local_update h)

@[rocq_alias mono_nat_auth_persist]
theorem auth_persist {dq : DFrac PNat} {n : Nat} : (●MN{dq} n) ~~> (●MN□ n) :=
  Update.op (Auth.auth_update_auth_persist (a := MaxNat.mk n)) Update.id

@[rocq_alias mono_nat_auth_unpersist]
theorem auth_unpersist [IsSplitFraction PNat] {n : Nat} :
    (●MN□ n) ~~>: fun k => ∃ q, k = ●MN{DFrac.own q} n :=
  UpdateP.weaken Auth.auth_updateP_both_unpersist fun _ => id

end MonoNat

/-! # Authoritative CMRA over `MaxZ`

The authoritative element is a monotonically increasing `Int`, while a fragment is a lower
bound. Because `MaxZ` has no absolute bottom under `Int.max`, the underlying CMRA is
`Option MaxZ` so that `none` plays the role of the unit. -/

namespace MonoZ

@[rocq_alias mono_Z]
abbrev MonoZ := Auth PNat (Option MaxZ)

#rocq_ignore mono_ZR "Use the MonoZ type and View.instCMRA typeclass"
#rocq_ignore mono_ZUR "Use the MonoZ type and View.instUCMRA typeclass"

@[rocq_alias mono_Z_auth]
def auth (dq : DFrac PNat) (n : Int) : MonoZ :=
  Auth.auth dq (some (MaxZ.mk n)) • Auth.frag (some (MaxZ.mk n))

@[rocq_alias mono_Z_lb]
def lb (n : Int) : MonoZ := Auth.frag (some (MaxZ.mk n))

scoped notation "●MZ{" dq "} " n => MonoZ.auth dq n
scoped notation "●MZ " n => MonoZ.auth (DFrac.own One.one) n
scoped notation "●MZ□ " n => MonoZ.auth DFrac.discard n
scoped notation "◯MZ " n => MonoZ.lb n

@[rocq_alias mono_Z_lb_core_id]
instance lb_core_id (n : Int) : CoreId (◯MZ n) :=
  show CoreId (Auth.frag (some (MaxZ.mk n))) from inferInstance

@[rocq_alias mono_Z_auth_core_id]
instance auth_core_id (n : Int) : CoreId (●MZ□ n) :=
  show CoreId
    ((Auth.auth DFrac.discard (some (MaxZ.mk n)) : MonoZ) • Auth.frag (some (MaxZ.mk n))) from
    inferInstance

@[rocq_alias mono_Z_auth_dfrac_op]
theorem auth_dfrac_op {dq1 dq2 : DFrac PNat} {n : Int} :
    (●MZ{dq1 • dq2} n) ≡ (●MZ{dq1} n) • (●MZ{dq2} n) := by
  let A1 : MonoZ := Auth.auth dq1 (some (MaxZ.mk n))
  let A2 : MonoZ := Auth.auth dq2 (some (MaxZ.mk n))
  let F  : MonoZ := Auth.frag (some (MaxZ.mk n))
  calc (Auth.auth (dq1 • dq2) (some (MaxZ.mk n)) • F : MonoZ)
      ≡ (A1 • A2) • F           := Auth.auth_dfrac_op.op_l
    _ ≡ (A1 • A2) • (F • F)     := (CMRA.op_self _).symm.op_r
    _ ≡ ((A1 • A2) • F) • F     := CMRA.assoc
    _ ≡ (A1 • (A2 • F)) • F     := CMRA.assoc.symm.op_l
    _ ≡ (A1 • (F • A2)) • F     := CMRA.comm.op_r.op_l
    _ ≡ ((A1 • F) • A2) • F     := CMRA.assoc.op_l
    _ ≡ (A1 • F) • (A2 • F)     := CMRA.assoc.symm

@[rocq_alias mono_Z_lb_op]
theorem lb_op {n1 n2 : Int} : (◯MZ (max n1 n2)) = (◯MZ n1) • (◯MZ n2) := by
  show (Auth.frag (some (MaxZ.mk (max n1 n2))) : MonoZ) =
       (Auth.frag (some (MaxZ.mk n1)) : MonoZ) • Auth.frag (some (MaxZ.mk n2))
  rw [← Auth.frag_op]; rfl

@[rocq_alias mono_Z_auth_lb_op]
theorem auth_lb_op {dq : DFrac PNat} {n : Int} :
    (●MZ{dq} n) ≡ (●MZ{dq} n) • (◯MZ n) :=
  (CMRA.op_self _).symm.op_r |>.trans CMRA.assoc

@[rocq_alias mono_Z_lb_op_le_l]
theorem lb_op_le_l {n n' : Int} (h : n' ≤ n) : (◯MZ n) = (◯MZ n') • (◯MZ n) := by
  rw [← lb_op]
  show (◯MZ n) = ◯MZ (max n' n)
  rw [Int.max_eq_right h]

@[rocq_alias mono_Z_auth_dfrac_valid]
theorem auth_dfrac_valid {dq : DFrac PNat} {n : Int} : (✓ ●MZ{dq} n) ↔ ✓ dq := by
  show ✓ (Auth.auth dq (some (MaxZ.mk n)) • Auth.frag (some (MaxZ.mk n)) : MonoZ) ↔ ✓ dq
  rw [Auth.both_dfrac_valid_discrete]
  exact ⟨(·.1), fun h => ⟨h, CMRA.inc_refl _, trivial⟩⟩

@[rocq_alias mono_Z_auth_valid]
theorem auth_valid {n : Int} : ✓ (●MZ n) := auth_dfrac_valid.mpr DFrac.valid_own_one

@[rocq_alias mono_Z_auth_dfrac_op_valid]
theorem auth_dfrac_op_valid {dq1 dq2 : DFrac PNat} {n1 n2 : Int} :
    (✓ (●MZ{dq1} n1) • (●MZ{dq2} n2)) ↔ ✓ (dq1 • dq2) ∧ n1 = n2 := by
  refine ⟨?_, ?_⟩
  · intro h
    let A1 : MonoZ := Auth.auth dq1 (some (MaxZ.mk n1))
    let A2 : MonoZ := Auth.auth dq2 (some (MaxZ.mk n2))
    let F1 : MonoZ := Auth.frag (some (MaxZ.mk n1))
    let F2 : MonoZ := Auth.frag (some (MaxZ.mk n2))
    have hauth : ✓ (A1 • A2 : MonoZ) := CMRA.valid_op_left <| CMRA.valid_of_eqv
      (calc (A1 • F1) • (A2 • F2)
          ≡ ((A1 • F1) • A2) • F2 := CMRA.assoc
        _ ≡ (A1 • (F1 • A2)) • F2 := CMRA.assoc.symm.op_l
        _ ≡ (A1 • (A2 • F1)) • F2 := CMRA.comm.op_r.op_l
        _ ≡ ((A1 • A2) • F1) • F2 := CMRA.assoc.op_l
        _ ≡ (A1 • A2) • (F1 • F2) := CMRA.assoc.symm) h
    have ⟨hdq, hne, _⟩ := Auth.auth_dfrac_op_valid.mp hauth
    exact ⟨hdq, MaxZ.mk.injEq .. |>.mp <|
      Option.some.injEq .. |>.mp (OFE.eq_of_eqv hne)⟩
  · rintro ⟨hdq, rfl⟩
    exact CMRA.valid_of_eqv (auth_dfrac_op (dq1 := dq1) (dq2 := dq2) (n := n1))
      (auth_dfrac_valid.mpr hdq)

@[rocq_alias mono_Z_auth_op_valid]
theorem auth_op_valid {n1 n2 : Int} : (✓ (●MZ n1) • (●MZ n2)) ↔ False :=
  ⟨fun h => UFraction.one_whole.2 (DFrac.valid_op_own (auth_dfrac_op_valid.mp h).1), False.elim⟩

@[rocq_alias mono_Z_both_dfrac_valid]
theorem both_dfrac_valid {dq : DFrac PNat} {n m : Int} :
    (✓ (●MZ{dq} n) • (◯MZ m)) ↔ ✓ dq ∧ m ≤ n := by
  have hreassoc :
      ((●MZ{dq} n) • (◯MZ m) : MonoZ) ≡
        Auth.auth dq (some (MaxZ.mk n)) • Auth.frag (some (MaxZ.mk (max n m))) :=
    CMRA.assoc.symm.trans <| CMRA.op_right_eqv _ <| .of_eq <|
      show ((Auth.frag (some (MaxZ.mk n)) : MonoZ) • Auth.frag (some (MaxZ.mk m))) =
           Auth.frag (some (MaxZ.mk (max n m))) from Auth.frag_op.symm
  rw [CMRA.valid_iff hreassoc, Auth.both_dfrac_valid_discrete]
  refine ⟨fun ⟨h, hinc, _⟩ => ⟨h, Int.le_trans (Int.le_max_right _ _)
    (MaxZ.included.mp (Option.some_inc_some_iff_isTotal.mp hinc))⟩, ?_⟩
  rintro ⟨h, hle⟩
  exact ⟨h, Option.some_inc_some_iff_isTotal.mpr
    (MaxZ.included.mpr (Int.max_le.mpr ⟨Int.le_refl _, hle⟩)), trivial⟩

@[rocq_alias mono_Z_both_valid]
theorem both_valid {n m : Int} : (✓ (●MZ n) • (◯MZ m)) ↔ m ≤ n :=
  ⟨fun h => (both_dfrac_valid.mp h).2, fun h => both_dfrac_valid.mpr ⟨DFrac.valid_own_one, h⟩⟩

@[rocq_alias mono_Z_lb_mono]
theorem lb_mono {n1 n2 : Int} (h : n1 ≤ n2) : (◯MZ n1) ≼ (◯MZ n2) :=
  Auth.frag_inc_of_inc (Option.some_inc_some_iff_isTotal.mpr (MaxZ.included.mpr h))

@[rocq_alias mono_Z_included]
theorem included {dq : DFrac PNat} {n : Int} : (◯MZ n) ≼ (●MZ{dq} n) :=
  CMRA.inc_op_right _ _

@[rocq_alias mono_Z_update]
theorem update {n n' : Int} (h : n ≤ n') : (●MZ n) ~~> (●MZ n') :=
  Auth.auth_update (LocalUpdate.option (MaxZ.local_update h))

@[rocq_alias mono_Z_auth_persist]
theorem auth_persist {dq : DFrac PNat} {n : Int} : (●MZ{dq} n) ~~> (●MZ□ n) :=
  Update.op (Auth.auth_update_auth_persist (a := some (MaxZ.mk n))) Update.id

@[rocq_alias mono_Z_auth_unpersist]
theorem auth_unpersist [IsSplitFraction PNat] {n : Int} :
    (●MZ□ n) ~~>: fun k => ∃ q, k = ●MZ{DFrac.own q} n :=
  UpdateP.weaken Auth.auth_updateP_both_unpersist fun _ => id

end MonoZ

end Iris
