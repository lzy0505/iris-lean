/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.Frac
import Iris.Algebra.LocalUpdates
meta import Iris.Std.RocqPorting

/-!
# Unbounded Fractional Authoritative Camera

Authoritative camera with fragments fractioned by an unbounded additive fraction
type, allowing fractions arbitrarily greater than the "whole". The authoritative
element `●U{p} a` and the fragment `◯U{q} a` both carry an arbitrary fraction
`p, q : G` from a `Fraction` instance whose validity is total: every fraction is
proper.

The two distinguishing rules from the bounded `FracAuth`:

* A "surplus" allocation is permitted:
  `✓ (a • b) → ●U{p} a ~~> ●U{p + q} (a • b) • ◯U{q} b`.
* `◯U{1} a` is **not** exclusive: combining `◯U{1} a` with `◯U{q} b` is not
  vacuous.
-/

@[expose] public section

namespace Iris

open OFE CMRA UCMRA Auth Option Fraction

/-! ## Definitions -/

/-- Unbounded fractional authoritative camera carrier.

`F` is the discardable-fraction parameter for the outer `Auth`; `G` is an
unbounded `Fraction` carrier (intended to have `Proper := True`) used by the
inner ufrac elements. -/
@[rocq_alias ufrac_authR]
public abbrev UFracAuth (F : Type _) (G : Type _) (A : Type _)
    [UFraction F] [Fraction G] [CMRA A] :=
  Auth F (Option (Frac G × A))

@[rocq_alias ufrac_authUR]
public abbrev UFracAuthU (F : Type _) (G : Type _) (A : Type _)
    [UFraction F] [Fraction G] [CMRA A] :=
  Auth F (Option (Frac G × A))

namespace UFracAuth

variable {F G A : Type _} [UFraction F] [Fraction G] [CMRA A]

@[rocq_alias ufrac_auth_auth]
public abbrev auth (q : G) (a : A) : UFracAuth F G A :=
  Auth.auth (DFrac.own One.one) (some (⟨q⟩, a))

@[rocq_alias ufrac_auth_frag]
public abbrev frag (q : G) (a : A) : UFracAuth F G A :=
  Auth.frag (some (⟨q⟩, a))

scoped notation "●U{" q "} " a => UFracAuth.auth q a
scoped notation "◯U{" q "} " a => UFracAuth.frag q a

#rocq_ignore ufrac_auth_auth_proper "Derivable from auth_ne with NonExpansive.eqv"
#rocq_ignore ufrac_auth_frag_proper "Derivable from frag_ne with NonExpansive.eqv"

/-! ## NonExpansive instances -/

@[rocq_alias ufrac_auth_auth_ne]
instance auth_ne {q : G} : NonExpansive (auth (F := F) q : A → UFracAuth F G A) where
  ne _ _ _ h := Auth.auth_ne.ne (some_dist_some.mpr ⟨.rfl, h⟩)

@[rocq_alias ufrac_auth_frag_ne]
instance frag_ne {q : G} : NonExpansive (frag (F := F) q : A → UFracAuth F G A) where
  ne _ _ _ h := Auth.frag_ne.ne (some_dist_some.mpr ⟨.rfl, h⟩)

/-! ## Discrete instances -/

@[rocq_alias ufrac_auth_auth_discrete]
instance auth_discrete {q : G} {a : A} [ha: DiscreteE a] :
    DiscreteE (●U{q} a : UFracAuth F G A) :=
  Auth.auth_discrete (some_is_discrete (prod.is_discrete ⟨discrete_0⟩ ha)) none_is_discrete

@[rocq_alias ufrac_auth_frag_discrete]
instance frag_discrete {q : G} {a : A} [ha : DiscreteE a] :
    DiscreteE (◯U{q} a : UFracAuth F G A) :=
  Auth.frag_discrete (some_is_discrete (prod.is_discrete ⟨discrete_0⟩ ha))

/-! ## Validity -/

@[rocq_alias ufrac_auth_validN]
theorem validN {n : Nat} {p : G} {a : A} (hp : Fraction.Proper p) (ha : ✓{n} a) :
    ✓{n} (●U{p} a : UFracAuth F G A) • ◯U{p} a :=
  both_validN.mpr ⟨.rfl, hp, ha⟩

@[rocq_alias ufrac_auth_valid]
theorem valid {p : G} {a : A} (hp : Fraction.Proper p) (ha : ✓ a) :
    ✓ (●U{p} a : UFracAuth F G A) • ◯U{p} a :=
  auth_both_valid_2 ⟨valid_iff_validN.mpr fun _ => hp, ha⟩ ⟨none, .rfl⟩

/-! ## Agreement -/

@[rocq_alias ufrac_auth_agreeN]
theorem agreeN {n : Nat} {p : G} {a b : A}
    (h : ✓{n} (●U{p} a : UFracAuth F G A) • ◯U{p} b) : a ≡{n}≡ b := by
  obtain ⟨hinc, _⟩ := both_validN.mp h
  rcases some_incN_some_iff.mp hinc with heq | hinc
  · exact (dist_snd heq).symm
  · obtain ⟨z, hz⟩ := (Prod.incN_iff (n := n) _ _ _ _).mpr hinc |>.1
    exact absurd (LeibnizO.eqv_inj hz) (add_ne ∘ (Fraction.add_comm (α := G) _ _ ▸ ·))

@[rocq_alias ufrac_auth_agree]
theorem agree {p : G} {a b : A}
    (h : ✓ (●U{p} a : UFracAuth F G A) • ◯U{p} b) : a ≡ b :=
  equiv_dist.mpr fun n => agreeN (valid_iff_validN.mp h n)

@[rocq_alias ufrac_auth_agree_L]
theorem agree_L [Leibniz A] {p : G} {a b : A}
    (h : ✓ (●U{p} a : UFracAuth F G A) • ◯U{p} b) : a = b :=
  eq_of_eqv (agree h)

/-! ## Inclusion -/

@[rocq_alias ufrac_auth_includedN]
theorem includedN {n : Nat} {p q : G} {a b : A}
    (h : ✓{n} (●U{p} a : UFracAuth F G A) • ◯U{q} b) : some b ≼{n} some a := by
  obtain ⟨⟨mc, hmc⟩, _⟩ := both_validN.mp h
  match mc with
  | none => exact ⟨none, dist_snd hmc⟩
  | some (_, cr) => exact ⟨some cr, dist_snd hmc⟩

@[rocq_alias ufrac_auth_included]
theorem included [CMRA.Discrete A] {p q : G} {a b : A}
    (h : ✓ (●U{p} a : UFracAuth F G A) • ◯U{q} b) : some b ≼ some a := by
  obtain ⟨_, ⟨mc, hmc⟩, _⟩ := both_dfrac_valid_discrete.mp h
  match mc with
  | none => exact ⟨none, equiv_snd hmc⟩
  | some (_, cr) => exact ⟨some cr, equiv_snd hmc⟩

@[rocq_alias ufrac_auth_includedN_total]
theorem includedN_total [IsTotal A] {n : Nat} {p q : G} {a b : A}
    (h : ✓{n} (●U{p} a : UFracAuth F G A) • ◯U{q} b) : b ≼{n} a :=
  some_incN_some_iff_isTotal.mp (includedN h)

@[rocq_alias ufrac_auth_included_total]
theorem included_total [CMRA.Discrete A] [IsTotal A] {p q : G} {a b : A}
    (h : ✓ (●U{p} a : UFracAuth F G A) • ◯U{q} b) : b ≼ a :=
  inc_of_some_inc_some (included h)

/-! ## Auth-only validity -/

@[rocq_alias ufrac_auth_auth_validN]
theorem auth_validN {n : Nat} {q : G} {a : A} :
    (✓{n} (●U{q} a : UFracAuth F G A)) ↔ Fraction.Proper q ∧ ✓{n} a := by
  rw [Auth.auth_validN]; rfl

@[rocq_alias ufrac_auth_auth_valid]
theorem auth_valid {q : G} {a : A} :
    (✓ (●U{q} a : UFracAuth F G A)) ↔ Fraction.Proper q ∧ ✓ a := by
  simp only [valid_iff_validN]
  refine ⟨fun h => ⟨(auth_validN.mp (h 0)).1, fun n => (auth_validN.mp (h n)).2⟩,
    fun ⟨hp, ha⟩ n => auth_validN.mpr ⟨hp, ha n⟩⟩

/-! ## Fragment-only validity -/

@[rocq_alias ufrac_auth_frag_validN]
theorem frag_validN {n : Nat} {q : G} {a : A} :
    (✓{n} (◯U{q} a : UFracAuth F G A)) ↔ Fraction.Proper q ∧ ✓{n} a := by
  rw [Auth.frag_validN]; rfl

@[rocq_alias ufrac_auth_frag_valid]
theorem frag_valid {q : G} {a : A} :
    (✓ (◯U{q} a : UFracAuth F G A)) ↔ Fraction.Proper q ∧ ✓ a := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hq, ha⟩ => ?_⟩
  · exact (frag_validN.mp (valid_iff_validN.mp h 0)).1
  · exact valid_iff_validN.mpr fun n => (frag_validN.mp (valid_iff_validN.mp h n)).2
  · exact valid_iff_validN.mpr fun n => frag_validN.mpr ⟨hq, valid_iff_validN.mp ha n⟩

/-! ## Operations -/

@[rocq_alias ufrac_auth_frag_op]
theorem frag_op {q1 q2 : G} {a1 a2 : A} :
    (◯U{q1 + q2} (a1 • a2) : UFracAuth F G A) ≡ (◯U{q1} a1) • ◯U{q2} a2 := .rfl

@[rocq_alias ufrac_auth_frag_op_validN]
theorem frag_op_validN {n : Nat} {q1 q2 : G} {a b : A} :
    (✓{n} (◯U{q1} a : UFracAuth F G A) • ◯U{q2} b) ↔ Fraction.Proper (q1 + q2) ∧ ✓{n} (a • b) := by
  show ✓{n} (◯U{q1 + q2} (a • b) : UFracAuth F G A) ↔ _
  exact frag_validN

@[rocq_alias ufrac_auth_frag_op_valid]
theorem frag_op_valid {q1 q2 : G} {a b : A} :
    (✓ (◯U{q1} a : UFracAuth F G A) • ◯U{q2} b) ↔ Fraction.Proper (q1 + q2) ∧ ✓ (a • b) := by
  show ✓ (◯U{q1 + q2} (a • b) : UFracAuth F G A) ↔ _
  exact frag_valid

/-! ## Updates -/

@[rocq_alias ufrac_auth_update]
theorem update {p q : G} {a b a' b' : A} (h : (a, b) ~l~> (a', b')) :
    ((●U{p} a : UFracAuth F G A) • ◯U{q} b) ~~> (●U{p} a') • ◯U{q} b' :=
  auth_update (.option (.prod_2 _ _ h))

@[rocq_alias ufrac_auth_update_surplus]
theorem update_surplus {p q : G} {a b : A} (hp : Fraction.Proper (p + q)) (hv : ✓ (a • b)) :
    (●U{p} a : UFracAuth F G A) ~~> (●U{p + q} (a • b)) • ◯U{q} b := by
  refine auth_update_alloc (local_update_unital.mpr fun n mz _ heq => ?_)
  refine ⟨⟨hp, hv.validN⟩, ?_⟩
  have heq' : some ((⟨p⟩ : Frac G), a) ≡{n}≡ mz :=
    heq.trans (CMRA.unit_left_id_dist mz)
  match mz, heq' with
  | none, heq' => cases heq'
  | some (qa, av), heq' =>
    have hpair : ((⟨p⟩ : Frac G), a) ≡{n}≡ (qa, av) := heq'
    exact ⟨.of_eq <| LeibnizO.ext <| (Fraction.add_comm p q).trans
      (congrArg (q + ·) (LeibnizO.eqv_inj (dist_fst hpair))),
      CMRA.op_commN.trans (CMRA.op_right_dist b (dist_snd hpair))⟩

@[rocq_alias ufrac_auth_update_surplus_cancel]
theorem update_surplus_cancel {p q : G} {a b : A} [Cancelable b] :
    ((●U{p + q} (a • b) : UFracAuth F G A) • ◯U{q} b) ~~> ●U{p} a := by
  refine auth_update_dealloc (local_update_unital.mpr fun n mz hv heq => ?_)
  have ⟨hpq, hab⟩ : Fraction.Proper (p + q) ∧ ✓{n} (a • b) := hv
  have hp : Fraction.Proper p := Fraction.proper_add_mono_left hpq
  refine ⟨⟨hp, CMRA.validN_op_left hab⟩, ?_⟩
  refine .trans ?_ (CMRA.unit_left_id_dist mz).symm
  match mz, heq with
  | none, heq =>
    exact absurd (LeibnizO.eqv_inj (dist_fst (heq : ((⟨p + q⟩ : Frac G), a • b) ≡{n}≡ _))).symm
      Fraction.add_ne
  | some (qa, av), heq =>
    have hpair : ((⟨p + q⟩ : Frac G), a • b) ≡{n}≡ (⟨q⟩ + qa, b • av) := heq
    exact ⟨.of_eq <| LeibnizO.ext <| Fraction.add_left_cancel (a := q)
      (Fraction.add_comm q p ▸ Fraction.add_comm q qa.car ▸
        (LeibnizO.eqv_inj (dist_fst hpair) : p + q = q + qa.car)),
      cancelableN (x := b) (CMRA.comm.dist.validN.mp hab)
        (CMRA.op_commN.symm.trans (dist_snd hpair))⟩

/-! ## Functors -/

@[rocq_alias ufrac_authURF]
abbrev UFracAuthURF (G : Type _) [Fraction G] (T : COFE.OFunctorPre) [RFunctor T] :
    COFE.OFunctorPre :=
  AuthURF (F := F) (OptionOF (ProdOF (constOF (Frac G)) T))

@[rocq_alias ufrac_authRF]
abbrev UFracAuthRF (G : Type _) [Fraction G] (T : COFE.OFunctorPre) [RFunctor T] :
    COFE.OFunctorPre :=
  AuthRF (F := F) (OptionOF (ProdOF (constOF (Frac G)) T))

#rocq_ignore ufrac_authURF_contractive
  "Derived automatically from contractivity of the underlying functors."
#rocq_ignore ufrac_authRF_contractive
  "Derived automatically from contractivity of the underlying functors."

end UFracAuth
end Iris
