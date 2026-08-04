/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers
public import Iris.BI.Lib.MonoNat
public import Iris.Instances.Lib.Invariants
public import Iris.ProofMode.Instances
public import Iris.ProgramLogic.WeakestPre
public import Iris.HeapLang.Notation
public import Iris.HeapLang.Instances
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

namespace Counter

open Std ProofMode Auth

/- `MaxNat` is an `abbrev` for `Nat`, so its `Add` instance (which is `max`, the CMRA op) also
applies to `Nat` and shadows `instAddNat`. Erase it here so that `+` means addition. -/
attribute [-instance] instAddMaxNat

@[rocq_alias heap_lang.newcounter]
def newcounter := hl_val% λ _, ref(#0)
@[rocq_alias heap_lang.incr]
def incr := hl_val%
  rec incr l :=
    let n := !l;
    if snd(cmpXchg(l, n, #1 + n))
      then #()
      else incr l
@[rocq_alias heap_lang.read]
def read := hl_val% λ l, !l


@[rocq_alias heap_lang.mcounterG]
class MCounterG (GF : BundledGFunctors) extends MonoNatG GF

section MonoProofs

variable [HeapLangGS hlc GF] [MCounterG GF] (N : Namespace)

open MonoNat

@[rocq_alias heap_lang.mcounter_inv]
def mcounter_inv (γ : GName) (l : Loc) : IProp GF := iprop%
  ∃ n : Nat, (γ ↪●MN n) ∗ (l ↦ hl_val(#n))

@[rocq_alias heap_lang.mcounter]
def mcounter (l : Loc) (n : Nat) : IProp GF := iprop%
  ∃ γ, inv N (mcounter_inv γ l) ∧ (γ ↪◯MN n)

@[rocq_alias heap_lang.mcounter_persistent]
instance instMCounterPersistent (l : Loc) (n : Nat) : Persistent (mcounter N l n : IProp GF) := by
  unfold mcounter; infer_instance

@[rocq_alias heap_lang.newcounter_mono_spec]
theorem newcounter_mono_spec :
  ⊢@{IProp GF} {{ True }} hl(&newcounter #()) {{ l, RET hl_val(#l); mcounter N l 0 }} := by
  unfold newcounter; iintro %Φ - HΦ; wp_lam; wp_alloc l with Hl
  imod (MonoNat.own_alloc 0) with ⟨%γ, Hγ, Hγ'⟩
  imod (inv_alloc N _ (mcounter_inv γ l)) $$ [Hl Hγ]
  · inext; unfold mcounter_inv; iexists 0; iframe
  imodintro; iapply HΦ; unfold mcounter; iframe

@[rocq_alias heap_lang.incr_mono_spec]
theorem incr_mono_spec l n :
  ⊢@{IProp GF} {{ mcounter N l n }} hl(&incr #l) {{ RET hl_val(#()); mcounter N l (1 + n) }} := by
  iintro %Φ Hl HΦ
  iloeb as IH
  wp_rec
  rw (occs := [3]) [mcounter]
  icases Hl with ⟨%γ, #_, Hγf⟩
  wp_bind (! _)
  unfold mcounter_inv
  iinv N with ⟨%c, >⟨Hγ, Hl⟩⟩
  · exact ⟨by simp, by infer_instance⟩
  wp_load
  imodintro
  isplitl [Hl Hγ]
  · inext
    iexists c
    iframe
  wp_pures
  wp_bind (cmpXchg(_, _, _))
  iinv N with ⟨%c', >⟨Hγ, Hl⟩⟩
  · exact ⟨by simp, by infer_instance⟩
  by_cases (c' = c)
  · subst c'
    icombine Hγ Hγf gives ⟨-, %_⟩
    imod MonoNat.own_update (1 + c) $$ Hγ with ⟨Hγ, Hγf⟩
    · simp
    wp_cmpxchg_suc
    imodintro
    isplitl [Hl Hγ]
    · inext
      iexists (1 + c)
      push_cast
      iframe
    wp_pures
    iapply HΦ
    imodintro
    unfold mcounter mcounter_inv
    iexists γ
    iframe #
    iapply MonoNat.lb_own_le $$ Hγf
    grind
  · wp_cmpxchg_fail
    · grind
    imodintro
    isplitl [Hl Hγ]
    · inext
      iexists c'
      iframe
    wp_pures
    iapply IH $$ [Hγf] [$HΦ]
    rw (occs := [3]) [mcounter]; unfold mcounter_inv
    iexists γ; iframe # Hγf

@[rocq_alias heap_lang.read_mono_spec]
theorem read_mono_spec l j :
  ⊢@{IProp GF} {{ mcounter N l j }} hl(&read #l) {{ i, RET hl_val(#i); ⌜j ≤ i⌝ ∧ mcounter N l i }} := by
  iintro %Φ Hc HΦ
  rw (occs := [1]) [mcounter]; unfold mcounter_inv
  icases Hc with ⟨%γ, #Hinv, Hγf⟩
  unfold read
  wp_lam
  iinv N with ⟨%c, >⟨Hγ, Hl⟩⟩
  · exact ⟨by simp, by infer_instance⟩
  wp_load
  icombine Hγ Hγf gives ⟨-, %_⟩
  imod MonoNat.own_update c $$ Hγ with ⟨Hγ, Hγf⟩
  · simp
  imodintro
  isplitl [Hl Hγ]
  · inext
    iexists c
    iframe
  iapply HΦ $$ [-]
  rw [mcounter]; unfold mcounter_inv
  iframe % # Hγf

end MonoProofs
end Counter
