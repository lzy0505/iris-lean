module

public import Iris.Instances.IProp
public import Iris.Std.HeapInstances
public import Iris.BI.Lib.Fractional
public import Iris.Algebra.BigOp
public import Iris.BI.BigOp.BigOp
public import Iris.BI.BigOp.BigSepMUpdates

namespace Iris

open Iris Std HeapView PartialMap LawfulPartialMap Iris.Algebra BI ProofMode

-- Local @[grind] annotations on PartialMap lemmas so `grind` can discharge the pure
-- map-pointwise equalities that arise after the `OFE.Equiv.of_eq` bridge.
attribute [local grind =] get?_empty get?_insert_eq get?_insert_ne
  get?_delete_eq get?_delete_ne Std.LawfulPartialMap.get?_map
  Std.LawfulPartialMap.get?_union Std.LawfulPartialMap.get?_difference

class GhostMapG (GF : BundledGFunctors) (F: outParam (Type _))
    (K V: Type _)(H : outParam <| Type _ → Type _)
    [UFraction F][LawfulPartialMap H K] where
  elem: ElemG GF (constOF (HeapView F K (Agree (LeibnizO V)) H))

attribute [reducible, instance] GhostMapG.elem

section definitions

variable [UFraction F][LawfulPartialMap H K][hgm: GhostMapG GF F K V H]

public def ghost_map_auth (γ : GName) (dq : DFrac F) (m : H V): IProp GF :=
  iOwn (E := hgm.elem) γ
    (HeapView.Auth dq (Iris.Std.PartialMap.map (fun x ↦ toAgree ⟨x⟩) m))

public def ghost_map_elem (γ : GName) (dq : DFrac F) (k: K) (v: V): IProp GF :=
  iOwn (E := hgm.elem) γ (HeapView.Frag k dq (toAgree ⟨v⟩))

end definitions

notation γ " ↪●MAP{" dq "} " m => ghost_map_auth γ dq m
notation γ " ↪●MAP " m => ghost_map_auth γ (DFrac.own 1) m
notation γ " ↪◯MAP[" k "]{" dq "} " v => ghost_map_elem γ dq k v
notation γ " ↪◯MAP[" k "] " v => ghost_map_elem γ (DFrac.own 1) k v

section lemmas

variable {F K V : Type _} {H : Type _ → Type _} [UFraction F] [LawfulPartialMap H K]
variable [hgm: GhostMapG GF F K V H]

@[rocq_alias ghost_map_elem_timeless]
instance (γ : GName)(k: K)(dq: DFrac F)(v: V): BI.Timeless (PROP := IProp GF) (γ ↪◯MAP[k]{dq} v) :=
  iOwn_timeless (E := hgm.elem)

@[rocq_alias ghost_map_elem_persistent]
instance (γ : GName)(k: K)(v: V): BI.Persistent (PROP := IProp GF) (γ ↪◯MAP[k]{.discard} v) := by
  unfold ghost_map_elem
  exact instPersistentIPropIOwnOfCoreIdAp (E := hgm.elem)

@[rocq_alias ghost_map_elem_fractional]
instance (γ : GName)(k: K)(v: V)
    : Fractional (PROP := IProp GF) iprop(fun q: F => γ ↪◯MAP[k]{.own q} v) where
  fractional p q := by
    unfold ghost_map_elem
    let ta := @toAgree (LeibnizO V) { car := v }
    have :
        Frag (H := H) k (DFrac.own (p + q)) (ta • ta) ≡
        Frag k (DFrac.own (p + q)) ta
      := OFE.NonExpansive.eqv Iris.Agree.idemp
    have := frag_add_op_equiv.symm.trans this
    have := (@iOwn_ne GF _ _ GhostMapG.elem γ).eqv this
    have := (BI.equiv_iff (PROP := IProp GF)).mp this
    exact this.symm.trans <| iOwn_op (E := GhostMapG.elem)

@[rocq_alias ghost_map_elem_as_fractional]
instance (γ : GName) (k : K) (v : V) (q : F) :
    AsFractional (PROP := IProp GF) (γ ↪◯MAP[k]{.own q} v)
      (fun q : F => γ ↪◯MAP[k]{.own q} v) q where
  as_fractional := .rfl

-- ghost_map_elems_unseal is a `Local Lemma` in Rocq; deferred to big_op_lemmas section
-- below where [LawfulFiniteMap H K] is in scope without diamonding with [LawfulPartialMap H K].

@[rocq_alias ghost_map_elem_valid]
theorem ghost_map_elem_valid (γ : GName) (k : K) (dq: DFrac F) (v: V) :
  ⊢@{IProp GF} (γ ↪◯MAP[k]{dq} v) -∗ ⌜✓ dq⌝ := by
  unfold ghost_map_elem
  iintro H
  ihave H := iOwn_cmraValid $$ H
  icases internalCmraValid_discrete $$ H with %H
  ipure_intro; exact (HeapView.frag_valid_iff.mp H).1

@[rocq_alias ghost_map_elem_valid_2]
theorem ghost_map_elem_valid_2 (γ : GName) (k : K) (dq1: DFrac F) (dq2: DFrac F) (v1: V) (v2: V) :
  ⊢@{IProp GF} (γ ↪◯MAP[k]{dq1} v1) -∗ (γ ↪◯MAP[k]{dq2} v2) -∗ ⌜✓ (dq1 • dq2) ∧ v1 = v2⌝ := by
  unfold ghost_map_elem
  iintro H1 H2
  ihave H := iOwn_cmraValid_op $$ [$H1 $H2]
  icases internalCmraValid_discrete (A := HeapView _ _ _ _) $$ H with %H
  ipure_intro
  obtain ⟨Hdq, Hv⟩ := HeapView.frag_op_valid_iff.mp H
  exact ⟨Hdq, LeibnizO.mk.injEq .. |>.mp <| Iris.toAgree_op_valid_iff_eq.mp Hv⟩

@[rocq_alias ghost_map_elem_agree]
theorem ghost_map_elem_agree (γ : GName) (k : K) (dq1 : DFrac F) (dq2 : DFrac F) (v1 : V) (v2 : V) :
  ⊢@{IProp GF} (γ ↪◯MAP[k]{dq1} v1) -∗ (γ ↪◯MAP[k]{dq2} v2) -∗ ⌜v1 = v2⌝ := by
  iintro H1 H2
  ihave %H := ghost_map_elem_valid_2 γ k dq1 dq2 v1 v2 $$ H1 H2
  ipure_intro
  exact H.2

@[rocq_alias ghost_map_elem_combine_gives]
instance ghost_map_elem_combine_sep_gives (γ : GName) (k : K) (v1 : V) (dq1 : DFrac F)
    (v2 : V) (dq2 : DFrac F) :
    CombineSepGives iprop(γ ↪◯MAP[k]{dq1} v1) iprop(γ ↪◯MAP[k]{dq2} v2)
      (iprop(⌜✓ (dq1 • dq2) ∧ v1 = v2⌝) : IProp GF) where
  combine_sep_gives := by
    iintro ⟨H1, H2⟩
    ihave %H := ghost_map_elem_valid_2 γ k dq1 dq2 v1 v2 $$ H1 H2
    imodintro
    ipure_intro
    exact H

@[rocq_alias ghost_map_elem_combine]
theorem ghost_map_elem_combine (γ : GName) (k : K) (dq1 : DFrac F) (dq2 : DFrac F) (v1 : V) (v2 : V) :
  ⊢@{IProp GF} (γ ↪◯MAP[k]{dq1} v1) -∗
  (γ ↪◯MAP[k]{dq2} v2) -∗
  (γ ↪◯MAP[k]{dq1 • dq2} v1) ∗ ⌜v1 = v2⌝ := by
  iintro H1 H2
  ihave %Heq := ghost_map_elem_agree γ k dq1 dq2 v1 v2 $$ H1 H2
  subst Heq
  isplit
  · unfold ghost_map_elem
    ihave Hop := iOwn_op.mpr $$ [$H1 $H2]
    have hEq :
        (HeapView.Frag (H := H) (V := Agree (LeibnizO V)) k dq1 (toAgree ⟨v1⟩) •
            HeapView.Frag k dq2 (toAgree (⟨v1⟩ : LeibnizO V))) ≡
        HeapView.Frag k (dq1 • dq2) (toAgree ⟨v1⟩) :=
      HeapView.frag_op_equiv.symm.trans
        (OFE.NonExpansive.eqv (f := HeapView.Frag k (dq1 • dq2)) Iris.Agree.idemp)
    iapply (BI.equiv_iff.mp (iOwn_ne.eqv hEq)).mp $$ Hop
  · ipure_intro; rfl

-- Lower priority so a future Fractional-based CombineSepAs instance can take precedence.
@[rocq_alias ghost_map_elem_combine_as]
instance (priority := default - 10) ghost_map_elem_combine_sep_as (k : K) (γ : GName)
    (dq1 dq2 : DFrac F) (v1 v2 : V) :
    CombineSepAs iprop(γ ↪◯MAP[k]{dq1} v1) iprop(γ ↪◯MAP[k]{dq2} v2)
      (iprop(γ ↪◯MAP[k]{dq1 • dq2} v1) : IProp GF) where
  combine_sep_as := by
    iintro ⟨H1, H2⟩
    icases ghost_map_elem_combine γ k dq1 dq2 v1 v2 $$ H1 H2 with ⟨H, _⟩
    iexact H

@[rocq_alias ghost_map_elem_frac_ne]
theorem ghost_map_elem_frac_ne γ (k1 : K) (k2 : K) (dq1 : DFrac F) (dq2 : DFrac F) (v1 : V) (v2 : V) :
    ¬ ✓ (dq1 • dq2) →
    ⊢@{IProp GF} (γ ↪◯MAP[k1]{dq1} v1) -∗ (γ ↪◯MAP[k2]{dq2} v2) -∗ ⌜k1 ≠ k2⌝ := by
  intro Hdq
  iintro H1 H2
  by_cases h : k1 = k2
  · subst h
    ihave %Hv := ghost_map_elem_valid_2 γ k1 dq1 dq2 v1 v2 $$ H1 H2
    exact (Hdq Hv.1).elim
  · ipure_intro; exact h

@[rocq_alias ghost_map_elem_ne]
theorem ghost_map_elem_ne γ (k1 : K) (k2 : K) (dq2 : DFrac F) (v1 : V) (v2 : V) :
    ⊢@{IProp GF} (γ ↪◯MAP[k1] v1) -∗ (γ ↪◯MAP[k2]{dq2} v2) -∗ ⌜k1 ≠ k2⌝ :=
  ghost_map_elem_frac_ne γ k1 k2 _ dq2 v1 v2 fun Hv =>
    (DFrac.own_whole_exclusive UFraction.one_whole).exclusive0_l _
      (CMRA.valid_iff_validN.mp Hv 0)

@[rocq_alias ghost_map_elem_persist]
theorem ghost_map_elem_persist (γ : GName) (k : K) (dq : DFrac F) (v : V) :
    ⊢@{IProp GF} (γ ↪◯MAP[k]{dq} v) ==∗ (γ ↪◯MAP[k]{.discard} v) := by
  unfold ghost_map_elem
  iintro Hel
  iapply iOwn_update HeapView.update_frag_discard $$ Hel

@[rocq_alias ghost_map_elem_unpersist]
theorem ghost_map_elem_unpersist [IsSplitFraction F] (γ : GName) (k : K) (v : V) :
    ⊢@{IProp GF} (γ ↪◯MAP[k]{.discard} v) ==∗ ∃ q, (γ ↪◯MAP[k]{.own q} v) := by
  unfold ghost_map_elem
  iintro Hel
  imod iOwn_updateP HeapView.update_frag_acquire $$ Hel with ⟨%a, %Ha, Hel⟩
  obtain ⟨q, rfl⟩ := Ha
  imodintro
  iexists q
  iexact Hel

@[rocq_alias ghost_map_auth_timeless]
instance (γ : GName) (dq : DFrac F) (m : H V) : Timeless (PROP := IProp GF) (γ ↪●MAP{dq} m) :=
  iOwn_timeless

@[rocq_alias ghost_map_persistent]
instance (γ : GName) (m : H V) : Timeless (PROP := IProp GF) (γ ↪●MAP{.discard} m) :=
  iOwn_timeless

@[rocq_alias ghost_map_auth_fractional]
instance (γ : GName) (m : H V) :
    Fractional (PROP := IProp GF) (fun q : F => γ ↪●MAP{.own q} m) where
  fractional p q := by
    unfold ghost_map_auth
    let am : H (Agree (LeibnizO V)) := Iris.Std.PartialMap.map (fun x => toAgree ⟨x⟩) m
    have hEq : HeapView.Auth (H := H) (DFrac.own p • DFrac.own q) am ≡
        HeapView.Auth (.own p) am • HeapView.Auth (.own q) am :=
      HeapView.auth_dfrac_op_equiv
    have := (OFE.NonExpansive.eqv (f := iOwn (E := hgm.elem) γ) hEq)
    have := (BI.equiv_iff (PROP := IProp GF)).mp this
    exact this.trans iOwn_op

@[rocq_alias ghost_map_auth_valid]
theorem ghost_map_auth_valid γ (dq : DFrac F) (m : H V) :
    ⊢@{IProp GF} (γ ↪●MAP{dq} m) -∗ ⌜✓ dq⌝ := by
  unfold ghost_map_auth
  iintro Hauth
  ihave Hauth := iOwn_cmraValid $$ Hauth
  icases internalCmraValid_discrete (A := HeapView _ _ _ _) $$ Hauth with %Hauth
  ipure_intro
  exact HeapView.auth_valid_iff.mp Hauth

-- TODO: deferred until `ExtensionalPartialMap extends LawfulPartialMap` lands;
-- the injectivity of `map (toAgree ∘ LeibnizO.mk)` on the underlying carrier needs
-- pointwise-extensional equality of partial maps that the current `LawfulPartialMap`
-- class does not provide.
@[rocq_alias ghost_map_auth_valid_2]
theorem ghost_map_auth_valid_2 γ (dq1 : DFrac F) (dq2 : DFrac F) (m1 : H V) (m2 : H V) :
  ⊢@{IProp GF} (γ ↪●MAP{dq1} m1) -∗ (γ ↪●MAP{dq2} m2) -∗ ⌜✓ (dq1 • dq2) ∧ m1 = m2⌝ := sorry

-- TODO: derived from `ghost_map_auth_valid_2`; deferred for the same reason.
@[rocq_alias ghost_map_auth_agree]
theorem ghost_map_auth_agree γ (dq1 : DFrac F) (dq2 : DFrac F) (m1 : H V) (m2 : H V) :
  ⊢@{IProp GF} (γ ↪●MAP{dq1} m1) -∗ (γ ↪●MAP{dq2} m2) -∗ ⌜m1 = m2⌝ := sorry

@[rocq_alias ghost_map_auth_persist]
theorem ghost_map_auth_persist γ (dq : DFrac F) (m : H V) :
    ⊢@{IProp GF} (γ ↪●MAP{dq} m) ==∗ γ ↪●MAP{.discard} m := by
  unfold ghost_map_auth
  iintro Hauth
  iapply iOwn_update HeapView.auth_dfrac_discard $$ Hauth

@[rocq_alias ghost_map_auth_unpersist]
theorem ghost_map_auth_unpersist [IsSplitFraction F] γ (m : H V) :
    ⊢@{IProp GF} (γ ↪●MAP{.discard} m) ==∗ ∃ q, γ ↪●MAP{.own q} m := by
  unfold ghost_map_auth
  iintro Hauth
  imod iOwn_updateP HeapView.auth_dfrac_acquire $$ Hauth with ⟨%_, %Ha, Hauth⟩
  obtain ⟨q, rfl⟩ := Ha
  imodintro
  iexists _
  iexact Hauth

/-- Primitive bridge at the `iOwn (HeapView.Auth dq ·)` level when the underlying carrier
agrees pointwise. Two `NonExpansive.eqv` applications (for `HeapView.Auth dq` and `iOwn γ`)
plus `BI.equiv_iff.mp` to get an `⊣⊢`. -/
private theorem iOwn_heapView_auth_equiv_of_pointwise
    {γ : GName} {dq : DFrac F} {X Y : H (Agree (LeibnizO V))}
    (h : X ≡ Y) :
    (iOwn (E := hgm.elem) γ (HeapView.Auth dq X) : IProp GF) ⊣⊢
    iOwn (E := hgm.elem) γ (HeapView.Auth dq Y) :=
  BI.equiv_iff.mp (OFE.NonExpansive.eqv (OFE.NonExpansive.eqv h))

/-- Bridge two `ghost_map_auth γ dq ·` propositions when the underlying maps agree pointwise. -/
private theorem ghost_map_auth_equiv_of_pointwise
    {γ : GName} {dq : DFrac F} {m₁ m₂ : H V} (h : ∀ j, get? m₁ j = get? m₂ j) :
    (γ ↪●MAP{dq} m₁ : IProp GF) ⊣⊢ (γ ↪●MAP{dq} m₂) :=
  iOwn_heapView_auth_equiv_of_pointwise (fun j => by
    refine OFE.Equiv.of_eq ?_; grind)

@[rocq_alias ghost_map_lookup]
theorem ghost_map_lookup {γ} {dq : DFrac F} {m : H V} {k : K} {dq' : DFrac F} {v : V} :
    ⊢@{IProp GF} (γ ↪●MAP{dq} m) -∗ (γ ↪◯MAP[k]{dq'} v) -∗ ⌜get? m k = some v⌝ := by
  unfold ghost_map_auth ghost_map_elem
  iintro Hauth Hel
  ihave Hop := iOwn_cmraValid_op $$ [$Hauth $Hel]
  icases internalCmraValid_discrete (A := HeapView _ _ _ _) $$ Hop with %Hop
  ipure_intro
  obtain ⟨_, _, _, Hlookup, _, Hincl⟩ := HeapView.auth_op_frag_valid_total_discrete_iff Hop
  rw [get?_map] at Hlookup
  match h : get? m k, Hlookup with
  | some b, Hlookup =>
    simp only [Option.map_some, Option.some.injEq] at Hlookup
    subst Hlookup
    have hvb : v = b := LeibnizO.eqv_inj (Iris.Agree.toAgree_included.mp Hincl)
    rw [hvb]

@[rocq_alias ghost_map_lookup_combine_gives_1]
instance ghost_map_lookup_combine_sep_gives_1 {γ : GName} {dq : DFrac F} {m : H V}
    {k : K} {dq' : DFrac F} {v : V} :
    CombineSepGives iprop(γ ↪●MAP{dq} m) iprop(γ ↪◯MAP[k]{dq'} v)
      (iprop(⌜get? m k = some v⌝) : IProp GF) where
  combine_sep_gives := by
    iintro ⟨Hauth, Hel⟩
    ihave %H := ghost_map_lookup $$ Hauth Hel
    ipure_intro; exact H

@[rocq_alias ghost_map_lookup_combine_gives_2]
instance ghost_map_lookup_combine_sep_gives_2 {γ : GName} {dq : DFrac F} {m : H V}
    {k : K} {dq' : DFrac F} {v : V} :
    CombineSepGives iprop(γ ↪◯MAP[k]{dq'} v) iprop(γ ↪●MAP{dq} m)
      (iprop(⌜get? m k = some v⌝) : IProp GF) where
  combine_sep_gives :=
    sep_comm.mp.trans ghost_map_lookup_combine_sep_gives_1.combine_sep_gives

private theorem toAgree_LeibnizO_valid (v : V) : ✓ (toAgree (LeibnizO.mk v)) :=
  CMRA.valid_op_left
    (Iris.Agree.toAgree_op_valid_iff_equiv.mpr (OFE.Equiv.rfl : LeibnizO.mk v ≡ LeibnizO.mk v))

@[rocq_alias ghost_map_insert]
theorem ghost_map_insert {γ} {m : H V} (k : K) (v : V) (Hfresh : get? m k = none) :
    ⊢@{IProp GF} (γ ↪●MAP m) ==∗ (γ ↪●MAP insert m k v) ∗ γ ↪◯MAP[k] v := by
  unfold ghost_map_auth ghost_map_elem
  iintro Hauth
  imod iOwn_update (HeapView.update_one_alloc (by rw [get?_map, Hfresh]; rfl)
      DFrac.valid_own_one (toAgree_LeibnizO_valid v)) $$ Hauth with Hauth
  icases iOwn_op $$ Hauth with ⟨Hauth', Hfrag⟩
  iframe
  iapply (iOwn_heapView_auth_equiv_of_pointwise (fun j => ?_)).mp $$ Hauth'
  refine OFE.Equiv.of_eq ?_
  by_cases hjk : k = j <;> grind

@[rocq_alias ghost_map_insert_persist]
theorem ghost_map_insert_persist {γ} {m : H V} (k : K) (v : V) (Hfresh : get? m k = none) :
    ⊢@{IProp GF} (γ ↪●MAP m) ==∗ (γ ↪●MAP insert m k v) ∗ (γ ↪◯MAP[k]{.discard} v) := by
  iintro Hauth
  imod ghost_map_insert k v Hfresh $$ Hauth with ⟨Hauth, Helem⟩
  imod ghost_map_elem_persist $$ Helem with Helem
  iframe

@[rocq_alias ghost_map_delete]
theorem ghost_map_delete {γ} {m : H V} {k : K} {v : V} :
    ⊢@{IProp GF} (γ ↪●MAP m) -∗ (γ ↪◯MAP[k] v) ==∗ γ ↪●MAP delete m k := by
  unfold ghost_map_auth ghost_map_elem
  iintro Hauth Hel
  ihave Hop := iOwn_op.mpr $$ [$Hauth $Hel]
  imod iOwn_update HeapView.update_one_delete $$ Hop with Hauth
  imodintro
  iapply (iOwn_heapView_auth_equiv_of_pointwise (fun j => ?_)).mp $$ Hauth
  refine OFE.Equiv.of_eq ?_
  by_cases hjk : k = j <;> grind

@[rocq_alias ghost_map_update]
theorem ghost_map_update {γ} {m : H V} {k : K} {v : V} (w : V) :
    ⊢@{IProp GF} (γ ↪●MAP m) -∗ (γ ↪◯MAP[k] v) ==∗ (γ ↪●MAP insert m k w) ∗ γ ↪◯MAP[k] w := by
  unfold ghost_map_auth ghost_map_elem
  iintro Hauth Hel
  ihave Hop := iOwn_op.mpr $$ [$Hauth $Hel]
  imod iOwn_update (HeapView.update_replace (toAgree_LeibnizO_valid w)) $$ Hop with Hauth
  icases iOwn_op $$ Hauth with ⟨Hauth', Hfrag⟩
  imodintro
  iframe
  · iapply (iOwn_heapView_auth_equiv_of_pointwise (fun j => ?_)).mp $$ Hauth'
    refine OFE.Equiv.of_eq ?_
    by_cases hjk : k = j <;> grind

end lemmas

section big_op_lemmas

variable {F K V : Type _} {H : Type _ → Type _} [UFraction F] [LawfulFiniteMap H K]
variable [hgm: GhostMapG GF F K V H]

@[rocq_alias ghost_map_lookup_big]
theorem ghost_map_lookup_big {γ} {dq : DFrac F} {m : H V} {dq' : DFrac F}
    (m0 : H V) :
    ⊢@{IProp GF} (γ ↪●MAP{dq} m) -∗
      ([∗map] k ↦ v ∈ m0, γ ↪◯MAP[k]{dq'} v) -∗ ⌜m0 ⊆ m⌝ := by
  iintro Hauth Hfrag
  simp only [Subset, submap]
  iintro %k %v %Hm0
  icases BigSepM.bigSepM_lookup Hm0 $$ Hfrag with Helem
  iapply ghost_map_lookup $$ Hauth Helem

/-- Bridge between a raw `iOwn (HeapView.Auth ⋯ X)` and `ghost_map_auth γ q m` when their
underlying carriers agree pointwise after the `map (toAgree ∘ LeibnizO.mk)` conversion. -/
private theorem iOwn_ghost_map_auth_equiv_of_pointwise
    {γ : GName} {q : F} {X : H (Agree (LeibnizO V))} {m : H V}
    (h : ∀ j, get? X j ≡
      Option.map (fun x : V => toAgree (LeibnizO.mk x)) (get? m j)) :
    (iOwn (E := hgm.elem) γ (HeapView.Auth (.own q) X) : IProp GF) ⊣⊢
      γ ↪●MAP{.own q} m := by
  unfold ghost_map_auth
  refine iOwn_heapView_auth_equiv_of_pointwise
    (Y := Iris.Std.PartialMap.map (fun x => toAgree ⟨x⟩) m) (fun j => by grind)

variable [DecidableEq K]

@[rocq_alias ghost_map_elems_unseal]
theorem ghost_map_elems_unseal (γ : GName) (m : H V) (dq : DFrac F) :
    ⊢@{IProp GF} ([∗map] k ↦ v ∈ m, γ ↪◯MAP[k]{dq} v) ==∗
      iOwn (E := GhostMapG.elem) γ ([^ CMRA.op map] k ↦ v ∈ m, Frag k dq (toAgree ⟨v⟩)) := by
  induction m using LawfulFiniteMap.induction_on (M := H) with
  | hequiv m₁ m₂ heqv hP =>
    iintro Hbig
    imod hP $$ [Hbig] with Hrest
    iapply (Iris.Algebra.BigOpM.bigOpM_equiv_of_perm _ heqv) $$ Hbig
    imodintro
    iapply (equiv_iff.mp <| iOwn_ne.eqv <| Iris.Algebra.BigOpM.bigOpM_equiv_of_perm _ heqv).mp $$ Hrest
  | hemp =>
    rw [show ([^ CMRA.op map] k ↦ v ∈ (PartialMap.empty : H V),
            Frag (H := H) (V := Agree (LeibnizO V)) k dq (toAgree ⟨v⟩)) =
          (UCMRA.unit : HeapView F K (Agree (LeibnizO V)) H) from
        Iris.Algebra.BigOpM.bigOpM_empty (fun k v => Frag k dq (toAgree (⟨v⟩ : LeibnizO V)))]
    iintro _
    iapply iOwn_unit
  | hins i x m' hfresh ihP =>
    iintro Hbig
    icases (BigSepM.bigSepM_insert hfresh).mp $$ Hbig with ⟨Helem, Hrest⟩
    imod ihP $$ Hrest with Hrest
    imodintro
    unfold ghost_map_elem
    ihave Hop := iOwn_op.mpr $$ [$Helem $Hrest]
    iapply (BI.equiv_iff.mp (iOwn_ne.eqv
      (Iris.Algebra.BigOpM.bigOpM_insert_equiv _ _ hfresh).symm)).mp $$ Hop

/-- Reverse of `ghost_map_elems_unseal`: `iOwn (bigOpM Frag m)` resolves to a `[∗map]` of
ghost-map elements (modulo a `|==>` needed in the empty case to escape `iOwn UCMRA.unit`). -/
private theorem ghost_map_elems_reseal (γ : GName) (m : H V) (dq : DFrac F) :
    (iOwn (E := GhostMapG.elem) γ
        ([^ CMRA.op map] k ↦ v ∈ m, Frag (H := H) k dq (toAgree ⟨v⟩)) : IProp GF) ⊢
      |==> ([∗map] k ↦ v ∈ m, γ ↪◯MAP[k]{dq} v) := by
  induction m using LawfulFiniteMap.induction_on (M := H) with
  | hequiv m₁ m₂ heqv hP =>
    have hlhs : ([^ CMRA.op map] k ↦ v ∈ m₁,
          Frag (H := H) (V := Agree (LeibnizO V)) k dq (toAgree ⟨v⟩)) ≡
        ([^ CMRA.op map] k ↦ v ∈ m₂,
          Frag (H := H) (V := Agree (LeibnizO V)) k dq (toAgree ⟨v⟩)) :=
      Iris.Algebra.BigOpM.bigOpM_equiv_of_perm _ heqv
    have hrhs : ([∗map] k ↦ v ∈ m₁, (γ ↪◯MAP[k]{dq} v) : IProp GF) ⊣⊢
        ([∗map] k ↦ v ∈ m₂, (γ ↪◯MAP[k]{dq} v)) :=
      BI.equiv_iff.mp (Iris.Algebra.BigOpM.bigOpM_equiv_of_perm _ heqv)
    exact (BI.equiv_iff.mp (iOwn_ne.eqv hlhs.symm)).mp.trans
      (hP.trans (BIUpdate.mono hrhs.mp))
  | hemp =>
    rw [show ([^ CMRA.op map] k ↦ v ∈ (PartialMap.empty : H V),
            Frag (H := H) (V := Agree (LeibnizO V)) k dq (toAgree ⟨v⟩)) =
          (UCMRA.unit : HeapView F K (Agree (LeibnizO V)) H) from
        Iris.Algebra.BigOpM.bigOpM_empty (fun k v => Frag k dq (toAgree (⟨v⟩ : LeibnizO V)))]
    iintro _
    imodintro
    iapply BigSepM.bigSepM_empty.mpr
    iemp_intro
  | hins i x m' hfresh ihP =>
    refine .trans ((BI.equiv_iff.mp (iOwn_ne.eqv
      (Iris.Algebra.BigOpM.bigOpM_insert_equiv
        (fun k v => Frag (H := H) (V := Agree (LeibnizO V)) k dq (toAgree ⟨v⟩))
        _ hfresh))).mp.trans iOwn_op.mp) ?_
    refine (BI.sep_mono_r ihP).trans <| bupd_frame_l.trans <| BIUpdate.mono ?_
    exact (BigSepM.bigSepM_insert (Φ := fun k v => iprop(γ ↪◯MAP[k]{dq} v)) hfresh).mpr

@[rocq_alias ghost_map_alloc_strong]
theorem ghost_map_alloc_strong (P : GName → Prop) (m : H V)
    (HP : ∀ N, ∃ k, N ≤ k ∧ P k) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ (γ ↪●MAP m) ∗ [∗map] k ↦ v ∈ m, γ ↪◯MAP[k] v := by
  imod iOwn_alloc_strong (E := GhostMapG.elem)
      (HeapView.Auth (.own (One.one : F))
        (Iris.Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) (∅ : H V))) P HP
      (HeapView.auth_valid_iff.mpr DFrac.valid_own_one) with ⟨%γ, %HPγ, Hauth⟩
  imod iOwn_update
    (.equiv_right
      (.op
        (OFE.NonExpansive.eqv (f := HeapView.Auth (.own (One.one : F)))
          (eqv_of_Equiv fun k => by
            show Std.PartialMap.get? (PartialMap.union
                (Iris.Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) m)
                (Iris.Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) (∅ : H V))) k =
              Std.PartialMap.get?
                (Iris.Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) m) k
            rw [Std.LawfulPartialMap.get?_union, Std.LawfulPartialMap.get?_map,
              Std.LawfulPartialMap.get?_map,
              show Std.PartialMap.get? (∅ : H V) k = none from
                Std.LawfulPartialMap.get?_empty _]
            cases Std.PartialMap.get? m k <;> rfl))
        (BigOpM.bigOpM_map_equiv (fun x : V => toAgree (LeibnizO.mk x))
          (fun k v => HeapView.Frag (H := H) k (.own (One.one : F)) v) m))
      (HeapView.update_alloc_big (Iris.Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) m)
        (LawfulPartialMap.disjoint_map.mpr (Std.LawfulPartialMap.disjoint_empty_left m))
        (LawfulPartialMap.all_map.mpr (fun _ v _ => toAgree_LeibnizO_valid v))))
    $$ Hauth with Hauth
  icases iOwn_op $$ Hauth with ⟨Hauth, Hfrag⟩
  imod ghost_map_elems_reseal γ m (.own (One.one : F)) $$ Hfrag with Hfrag
  imodintro; iexists γ; isplit
  · ipure_intro; exact HPγ
  · unfold ghost_map_auth; iframe

@[rocq_alias ghost_map_alloc_strong_empty]
theorem ghost_map_alloc_strong_empty (P : GName → Prop) (HP : ∀ N, ∃ k, N ≤ k ∧ P k) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ (γ ↪●MAP (∅ : H V)) := by
  imod ghost_map_alloc_strong P (∅ : H V) HP with ⟨%γ, %HPγ, Hauth, _⟩
  imodintro; iexists γ; isplit
  · ipure_intro; exact HPγ
  · iassumption

@[rocq_alias ghost_map_alloc]
theorem ghost_map_alloc (m : H V) :
    ⊢@{IProp GF} |==> ∃ γ, (γ ↪●MAP m) ∗ [∗map] k ↦ v ∈ m, γ ↪◯MAP[k] v := by
  imod ghost_map_alloc_strong (fun _ => True) m (fun N => ⟨N, Nat.le_refl _, trivial⟩)
    with ⟨%γ, _, Hauth, Hbig⟩
  imodintro
  iexists _
  iframe

@[rocq_alias ghost_map_alloc_empty]
theorem ghost_map_alloc_empty :
    ⊢@{IProp GF} |==> ∃ γ, (γ ↪●MAP (∅ : H V)) := by
  imod ghost_map_alloc (∅ : H V) with ⟨%γ, Hauth, _⟩
  imodintro; iexists γ; iassumption

@[rocq_alias ghost_map_insert_big]
theorem ghost_map_insert_big {γ} {m : H V} (m' : H V) (Hdisj : m' ##ₘ m) :
    ⊢@{IProp GF} (γ ↪●MAP m) ==∗
      (γ ↪●MAP (m' ∪ m)) ∗ [∗map] k ↦ v ∈ m', γ ↪◯MAP[k] v := by
  iintro Hauth
  unfold ghost_map_auth
  imod iOwn_update
    (.equiv_right
      (.op
        (OFE.NonExpansive.eqv (f := HeapView.Auth (.own (One.one : F)))
          (eqv_of_Equiv
            (LawfulPartialMap.map_union (f := fun x : V => toAgree (LeibnizO.mk x)))).symm)
        (BigOpM.bigOpM_map_equiv (fun x : V => toAgree (LeibnizO.mk x))
          (fun k v => HeapView.Frag (H := H) k (.own (One.one : F)) v) m'))
      (HeapView.update_alloc_big (Iris.Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) m')
        (LawfulPartialMap.disjoint_map.mpr (PartialMap.disjoint_comm Hdisj))
        (LawfulPartialMap.all_map.mpr (fun _ v _ => toAgree_LeibnizO_valid v))))
    $$ Hauth with Hauth
  icases iOwn_op $$ Hauth with ⟨Hauth, Hfrag⟩
  imod ghost_map_elems_reseal γ m' (.own (One.one : F)) $$ Hfrag with Hfrag
  imodintro; iframe

@[rocq_alias ghost_map_insert_persist_big]
theorem ghost_map_insert_persist_big {γ} {m : H V} (m' : H V) (Hdisj : m' ##ₘ m) :
    ⊢@{IProp GF} (γ ↪●MAP m) ==∗
      (γ ↪●MAP (m' ∪ m)) ∗ [∗map] k ↦ v ∈ m', γ ↪◯MAP[k]{.discard} v := by
  iintro Hauth
  imod ghost_map_insert_big m' Hdisj $$ Hauth with ⟨Hauth, Helem⟩
  iframe
  iapply BigSepM.bigSepM_bupd
  iapply (BigSepM.bigSepM_mono (Φ := fun k v => iprop(γ ↪◯MAP[k] v))
    (Ψ := fun k v => iprop(|==> γ ↪◯MAP[k]{.discard} v))
    (m := m') (fun _ => BI.wand_entails (ghost_map_elem_persist γ _ _ _))) $$ Helem

@[rocq_alias ghost_map_delete_big]
theorem ghost_map_delete_big {γ} {m : H V} (m0 : H V) :
    ⊢@{IProp GF} (γ ↪●MAP m) -∗ ([∗map] k ↦ v ∈ m0, γ ↪◯MAP[k] v) ==∗ γ ↪●MAP (m \ m0) := by
  iintro Hauth Hfrag
  imod ghost_map_elems_unseal γ m0 _ $$ Hfrag with Hfrag
  unfold ghost_map_auth
  ihave Hop := iOwn_op.mpr $$ [$Hauth $Hfrag]
  iapply iOwn_update
    (.equiv_left
      (CMRA.op_right_eqv _ (BigOpM.bigOpM_map_equiv (fun x : V => toAgree (LeibnizO.mk x))
        (fun k v => HeapView.Frag (H := H) k (.own (One.one : F)) v) m0))
      (.equiv_right
        (OFE.NonExpansive.eqv (f := HeapView.Auth (.own (One.one : F)))
          (eqv_of_Equiv
            (LawfulPartialMap.map_difference (f := fun x : V => toAgree (LeibnizO.mk x)))).symm)
        (HeapView.update_delete_big
          (Iris.Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) m0))))
    $$ Hop

@[rocq_alias ghost_map_update_big]
theorem ghost_map_update_big {γ} {m : H V} (m0 m1 : H V) (Hdom : dom m0 = dom m1) :
    ⊢@{IProp GF} (γ ↪●MAP m) -∗ ([∗map] k ↦ v ∈ m0, γ ↪◯MAP[k] v) ==∗
      (γ ↪●MAP (m1 ∪ m)) ∗ [∗map] k ↦ v ∈ m1, γ ↪◯MAP[k] v := by
  iintro Hauth Hfrag
  imod ghost_map_elems_unseal γ m0 _ $$ Hfrag with Hfrag
  unfold ghost_map_auth
  ihave Hop := iOwn_op.mpr $$ [$Hauth $Hfrag]
  have hDomMap :
      Std.PartialMap.dom (Iris.Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) m0) =
      Std.PartialMap.dom (Iris.Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) m1) := by
    funext k
    simp only [Std.PartialMap.dom, Std.LawfulPartialMap.get?_map, Option.isSome_map]
    exact congrFun Hdom k
  imod iOwn_update
    (.equiv_left
      (CMRA.op_right_eqv _ (BigOpM.bigOpM_map_equiv (fun x : V => toAgree (LeibnizO.mk x))
        (fun k v => HeapView.Frag (H := H) k (.own (One.one : F)) v) m0))
      (.equiv_right
        (.op
          (OFE.NonExpansive.eqv (f := HeapView.Auth (.own (One.one : F)))
            (eqv_of_Equiv
              (LawfulPartialMap.map_union (f := fun x : V => toAgree (LeibnizO.mk x)))).symm)
          (BigOpM.bigOpM_map_equiv (fun x : V => toAgree (LeibnizO.mk x))
            (fun k v => HeapView.Frag (H := H) k (.own (One.one : F)) v) m1))
        (HeapView.update_replace_big
          (Iris.Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) m1)
          (Iris.Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) m0)
          hDomMap
          (LawfulPartialMap.all_map.mpr (fun _ v _ => toAgree_LeibnizO_valid v)))))
    $$ Hop with Hres
  icases iOwn_op $$ Hres with ⟨Hauth, Hfrag⟩
  imod ghost_map_elems_reseal γ m1 (.own (One.one : F)) $$ Hfrag with Hfrag
  imodintro; iframe

end big_op_lemmas
