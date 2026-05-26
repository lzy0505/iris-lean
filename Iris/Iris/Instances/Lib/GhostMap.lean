module

public import Iris.Instances.IProp
public import Iris.Std.HeapInstances
public import Iris.BI.Lib.Fractional
public import Iris.Algebra.BigOp
public import Iris.BI.BigOp.BigOp

namespace Iris

open Iris Std HeapView PartialMap LawfulPartialMap Iris.Algebra BI ProofMode

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
    exact this.symm.trans <| iOwn_op (E := hgm.elem)

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
  icases internalCmraValid_discrete (A := HeapView _ _ _ _) $$ H with %H
  ipure_intro
  exact (HeapView.frag_valid_iff.mp H).1

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

-- * lemmas about [ghost_map_auth]

@[rocq_alias ghost_map_auth_timeless]
instance (γ : GName) (dq : DFrac F) (m : H V) :
    BI.Timeless (PROP := IProp GF) (γ ↪●MAP{dq} m) :=
  iOwn_timeless

@[rocq_alias ghost_map_persistent]
instance (γ : GName) (m : H V) :
    BI.Timeless (PROP := IProp GF) (γ ↪●MAP{.discard} m) :=
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
  imod iOwn_updateP HeapView.auth_dfrac_acquire $$ Hauth with ⟨%a, %Ha, Hauth⟩
  obtain ⟨q, rfl⟩ := Ha
  imodintro
  iexists q
  iexact Hauth

-- * lemmas about the interaction of [ghost_map_auth] with the elements

/-- Bridge two `ghost_map_auth γ dq ·` propositions when the underlying maps agree pointwise. -/
private theorem ghost_map_auth_equiv_of_pointwise
    {γ : GName} {dq : DFrac F} {m₁ m₂ : H V} (h : ∀ j, get? m₁ j = get? m₂ j) :
    (γ ↪●MAP{dq} m₁ : IProp GF) ⊣⊢ (γ ↪●MAP{dq} m₂) := by
  unfold ghost_map_auth
  apply BI.equiv_iff.mp
  refine OFE.NonExpansive.eqv (f := iOwn (E := hgm.elem) γ) ?_
  refine OFE.NonExpansive.eqv (f := HeapView.Auth dq) (fun j => ?_)
  simp [get?_map, h j]

/-- Primitive bridge at the `iOwn (HeapView.Auth dq ·)` level when the underlying carrier
agrees pointwise. -/
private theorem iOwn_heapView_auth_equiv_of_pointwise
    {γ : GName} {dq : DFrac F} {X Y : H (Agree (LeibnizO V))}
    (h : X ≡ Y) :
    (iOwn (E := hgm.elem) γ (HeapView.Auth dq X) : IProp GF) ⊣⊢
    iOwn (E := hgm.elem) γ (HeapView.Auth dq Y) :=
  BI.equiv_iff.mp (OFE.NonExpansive.eqv (OFE.NonExpansive.eqv h))

@[rocq_alias ghost_map_lookup]
theorem ghost_map_lookup {γ} {dq : DFrac F} {m : H V} {k : K} {dq' : DFrac F} {v : V} :
    ⊢@{IProp GF} (γ ↪●MAP{dq} m) -∗ (γ ↪◯MAP[k]{dq'} v) -∗ ⌜get? m k = some v⌝ := by
  unfold ghost_map_auth ghost_map_elem
  iintro Hauth Hel
  ihave Hop := iOwn_cmraValid_op $$ [$Hauth $Hel]
  icases internalCmraValid_discrete (A := HeapView _ _ _ _) $$ Hop with %Hop
  ipure_intro
  obtain ⟨av', _, _, Hlookup, _, Hincl⟩ := HeapView.auth_op_frag_valid_total_discrete_iff Hop
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
    imodintro
    ipure_intro
    exact H

@[rocq_alias ghost_map_lookup_combine_gives_2]
instance ghost_map_lookup_combine_sep_gives_2 {γ : GName} {dq : DFrac F} {m : H V}
    {k : K} {dq' : DFrac F} {v : V} :
    CombineSepGives iprop(γ ↪◯MAP[k]{dq'} v) iprop(γ ↪●MAP{dq} m)
      (iprop(⌜get? m k = some v⌝) : IProp GF) where
  combine_sep_gives :=
    sep_comm.mp.trans ghost_map_lookup_combine_sep_gives_1.combine_sep_gives

/-- Validity of `toAgree`-encoded singletons. Derived by `idemp`-reflection. -/
private theorem toAgree_LeibnizO_valid (v : V) : ✓ (toAgree (LeibnizO.mk v)) :=
  CMRA.valid_op_left
    (Iris.Agree.toAgree_op_valid_iff_equiv.mpr (OFE.Equiv.rfl : LeibnizO.mk v ≡ LeibnizO.mk v))

@[rocq_alias ghost_map_insert]
theorem ghost_map_insert {γ} {m : H V} (k : K) (v : V) (Hfresh : get? m k = none) :
    ⊢@{IProp GF} (γ ↪●MAP m) ==∗ (γ ↪●MAP insert m k v) ∗ γ ↪◯MAP[k] v := by
  unfold ghost_map_auth ghost_map_elem
  iintro Hauth
  imod iOwn_update (HeapView.update_one_alloc (k := k) (dq := DFrac.own One.one)
      (by rw [get?_map, Hfresh]; rfl)
      DFrac.valid_own_one (toAgree_LeibnizO_valid v)) $$ Hauth with Hauth
  icases iOwn_op $$ Hauth with ⟨Hauth', Hfrag⟩
  imodintro
  iframe
  · iapply (iOwn_heapView_auth_equiv_of_pointwise (fun j => ?_)).mp $$ Hauth'
    by_cases hjk : k = j
    · simp [get?_insert_eq hjk, get?_map]
    · simp [get?_insert_ne hjk, get?_map]

@[rocq_alias ghost_map_insert_persist]
theorem ghost_map_insert_persist {γ} {m : H V} (k : K) (v : V) (Hfresh : get? m k = none) :
    ⊢@{IProp GF} (γ ↪●MAP m) ==∗ (γ ↪●MAP insert m k v) ∗ (γ ↪◯MAP[k]{.discard} v) := by
  iintro Hauth
  imod ghost_map_insert k v Hfresh $$ Hauth with ⟨Hauth, Helem⟩
  imod ghost_map_elem_persist γ k (DFrac.own (One.one : F)) v $$ Helem with Helem
  imodintro
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
  by_cases hjk : k = j
  · simp [get?_delete_eq hjk, get?_map]
  · simp [get?_delete_ne hjk, get?_map]

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
    by_cases hjk : k = j
    · simp [get?_insert_eq hjk, get?_map]
    · simp [get?_insert_ne hjk, get?_map]

end lemmas

section big_op_lemmas

variable {F K V : Type _} {H : Type _ → Type _} [UFraction F] [LawfulFiniteMap H K]
variable [hgm: GhostMapG GF F K V H]

--  Big-op versions of above lemmas
@[rocq_alias ghost_map_lookup_big]
theorem ghost_map_lookup_big {γ} {dq : DFrac F} {m : H V} {dq' : DFrac F}
    (m0 : H V) :
    ⊢@{IProp GF} (γ ↪●MAP{dq} m) -∗
      ([∗map] k ↦ v ∈ m0, γ ↪◯MAP[k]{dq'} v) -∗ ⌜m0 ⊆ m⌝ := by
  iintro Hauth Hfrag
  iapply BI.pure_mono (φ1 := ∀ k v, get? m0 k = some v → get? m k = some v)
    (φ2 := m0 ⊆ m) (fun h k v hk => h k v hk)
  iintro %k %v %Hm0
  icases BigSepM.bigSepM_lookup (Φ := fun k v => iprop(γ ↪◯MAP[k]{dq'} v))
    Hm0 $$ Hfrag with Helem
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
    (Y := Iris.Std.PartialMap.map (fun x => toAgree ⟨x⟩) m) (fun j => ?_)
  rw [get?_map]
  exact h j

variable [DecidableEq K]

@[rocq_alias ghost_map_elems_unseal]
theorem ghost_map_elems_unseal (γ : GName) (m : H V) (dq : DFrac F) :
    ⊢@{IProp GF} ([∗map] k ↦ v ∈ m, γ ↪◯MAP[k]{dq} v) ==∗
      iOwn (E := hgm.elem) γ ([^ CMRA.op map] k ↦ v ∈ m,
        Frag (V := Agree (LeibnizO V)) k dq (toAgree ⟨v⟩)) := by
  induction m using LawfulFiniteMap.induction_on (M := H) with
  | hequiv m₁ m₂ heqv hP =>
    have hlhs :
        (([∗map] k ↦ v ∈ m₁, γ ↪◯MAP[k]{dq} v) : IProp GF) ⊣⊢
        ([∗map] k ↦ v ∈ m₂, γ ↪◯MAP[k]{dq} v) :=
      BI.equiv_iff.mp (Iris.Algebra.BigOpM.bigOpM_equiv_of_perm _ heqv)
    have hrhs :
        ([^ CMRA.op map] k ↦ v ∈ m₁, Frag (H := H) (V := Agree (LeibnizO V)) k dq (toAgree ⟨v⟩)) ≡
        ([^ CMRA.op map] k ↦ v ∈ m₂, Frag (H := H) (V := Agree (LeibnizO V)) k dq (toAgree ⟨v⟩)) :=
      Iris.Algebra.BigOpM.bigOpM_equiv_of_perm _ heqv
    iintro Hbig
    icases hlhs.mpr $$ Hbig with Hbig
    imod hP $$ Hbig with Hrest
    imodintro
    iapply (BI.equiv_iff.mp (iOwn_ne.eqv hrhs)).mp $$ Hrest
  | hemp =>
    rw [show ([^ CMRA.op map] k ↦ v ∈ (PartialMap.empty : H V),
            Frag (H := H) (V := Agree (LeibnizO V)) k dq (toAgree ⟨v⟩)) =
          (UCMRA.unit : HeapView F K (Agree (LeibnizO V)) H) from
        Iris.Algebra.BigOpM.bigOpM_empty (fun k v => Frag k dq (toAgree (⟨v⟩ : LeibnizO V)))]
    iintro _
    iapply iOwn_unit (E := hgm.elem) (γ := γ) (ε := UCMRA.unit)
  | hins i x m' hfresh ihP =>
    iintro Hbig
    icases (BigSepM.bigSepM_insert (Φ := fun k v => iprop(γ ↪◯MAP[k]{dq} v)) hfresh).mp $$ Hbig
      with ⟨Helem, Hrest⟩
    imod ihP $$ Hrest with Hrest
    imodintro
    have hElem :
        (γ ↪◯MAP[i]{dq} x : IProp GF) ⊣⊢
        iOwn (E := hgm.elem) γ
          (Frag (V := Agree (LeibnizO V)) (H := H) i dq (toAgree (⟨x⟩ : LeibnizO V))) :=
      BIBase.BiEntails.rfl
    icases hElem.mp $$ Helem with Helem
    ihave Hop := iOwn_op.mpr $$ [$Helem $Hrest]
    iapply (BI.equiv_iff.mp (iOwn_ne.eqv
      (Iris.Algebra.BigOpM.bigOpM_insert_equiv _ _ hfresh).symm)).mp $$ Hop

/-- Insert-shaped induction skeleton shared by the various big-op insert lemmas. Given a
per-element "allocate one fresh key as `Φ k v`" step, lift it to a whole disjoint sub-map. -/
private theorem ghost_map_insert_big_induct (γ : GName) (Φ : K → V → IProp GF)
    (h_step : ∀ {m_acc : H V} (i : K) (x : V), get? m_acc i = none →
        ⊢@{IProp GF} (γ ↪●MAP m_acc) ==∗ (γ ↪●MAP (insert m_acc i x)) ∗ Φ i x)
    (m m' : H V) (Hdisj : m' ##ₘ m) :
    (γ ↪●MAP m : IProp GF) ⊢ |==> ((γ ↪●MAP (m' ∪ m)) ∗ [∗map] k ↦ v ∈ m', Φ k v) := by
  revert Hdisj
  refine LawfulFiniteMap.induction_on
    (P := fun m' =>
      m' ##ₘ m →
      (γ ↪●MAP m : IProp GF) ⊢ |==> ((γ ↪●MAP (m' ∪ m)) ∗ [∗map] k ↦ v ∈ m', Φ k v))
    ?_ ?_ ?_ m'
  · intro m₁ m₂ heqv hP Hdisj
    have hdisj' : m₁ ##ₘ m :=
      fun k ⟨h1, h2⟩ => Hdisj k ⟨(heqv k) ▸ h1, h2⟩
    have hunion :=
      ghost_map_auth_equiv_of_pointwise (GF := GF) (γ := γ) (dq := DFrac.own (One.one : F))
        (m₁ := m₁ ∪ m) (m₂ := m₂ ∪ m)
        (fun j => by
          show get? (union m₁ m) j = get? (union m₂ m) j
          rw [get?_union, get?_union, heqv j])
    have hbig :
        ([∗map] k ↦ v ∈ m₁, Φ k v : IProp GF) ⊣⊢ ([∗map] k ↦ v ∈ m₂, Φ k v) :=
      BI.equiv_iff.mp (Iris.Algebra.BigOpM.bigOpM_equiv_of_perm _ heqv)
    iintro Hauth
    iapply (hP hdisj').trans (BIUpdate.mono (BI.sep_mono hunion.mp hbig.mp)) $$ Hauth
  · intro _
    iintro Hauth
    imodintro
    isplitl [Hauth]
    · iapply (ghost_map_auth_equiv_of_pointwise (GF := GF) (γ := γ) (dq := DFrac.own (One.one : F))
        (m₁ := (∅ : H V) ∪ m) (m₂ := m)
        (fun j => by
          show get? (union (∅ : H V) m) j = _
          rw [get?_union, show get? (∅ : H V) j = none from get?_empty _]; rfl)).mpr $$ Hauth
    · iapply (BigSepM.bigSepM_empty (Φ := Φ) (M := H)).mpr
      iemp_intro
  · intro i x m'' hfresh ihP Hdisj
    have hfresh_in_m : get? m i = none := by
      cases h : get? m i with
      | none => rfl
      | some v =>
        exfalso
        refine Hdisj i ⟨?_, ?_⟩
        · rw [get?_insert_eq (rfl : i = i)]; rfl
        · rw [h]; rfl
    have hdisj' : m'' ##ₘ m := fun k ⟨h1, h2⟩ => by
      by_cases hik : i = k
      · subst hik
        refine Hdisj i ⟨?_, h2⟩
        rw [get?_insert_eq (rfl : i = i)]
        rfl
      · refine Hdisj k ⟨?_, h2⟩
        rw [get?_insert_ne hik]
        exact h1
    have hinner :
        ((γ ↪●MAP (m'' ∪ m)) ∗ [∗map] k ↦ v ∈ m'', Φ k v : IProp GF) ⊢
        |==> ((γ ↪●MAP (insert m'' i x ∪ m)) ∗
          [∗map] k ↦ v ∈ insert m'' i x, Φ k v) := by
      iintro ⟨Hauth, Hbig⟩
      have hfresh_union : get? (m'' ∪ m) i = none := by
        show get? (union m'' m) i = none
        rw [get?_union, hfresh, hfresh_in_m]; rfl
      imod h_step i x hfresh_union $$ Hauth with Hres
      icases Hres with ⟨Hauth', Helem⟩
      imodintro
      have hunion :=
        ghost_map_auth_equiv_of_pointwise (GF := GF) (γ := γ) (dq := DFrac.own (One.one : F))
          (m₁ := insert (m'' ∪ m) i x)
          (m₂ := insert m'' i x ∪ m)
          (fun j => by
            show get? (insert (union m'' m) i x) j = get? (union (insert m'' i x) m) j
            by_cases hij : i = j
            · rw [get?_insert_eq hij, get?_union, get?_insert_eq hij]; rfl
            · rw [get?_insert_ne hij, get?_union, get?_union, get?_insert_ne hij])
      isplitl [Hauth']
      · iapply hunion.mp $$ Hauth'
      · iapply (BigSepM.bigSepM_insert (Φ := Φ) hfresh).mpr
        iframe
    exact (ihP hdisj').trans <| (BIUpdate.mono hinner).trans BIUpdate.trans

/-- Allocate the elements of `m` one-by-one starting from `Auth γ 1 ∅`. -/
private theorem ghost_map_alloc_aux (γ : GName) (m : H V) :
    (γ ↪●MAP (∅ : H V) : IProp GF) ⊢
      iprop(|==> ((γ ↪●MAP m) ∗ [∗map] k ↦ v ∈ m, γ ↪◯MAP[k] v)) := by
  have h :=
    ghost_map_insert_big_induct (GF := GF) γ (fun k v => iprop(γ ↪◯MAP[k] v))
      (fun {m_acc} i x hfresh => ghost_map_insert (γ := γ) (m := m_acc) i x hfresh)
      (∅ : H V) m (disjoint_empty_right _)
  have hunion :=
    ghost_map_auth_equiv_of_pointwise (GF := GF) (γ := γ) (dq := DFrac.own (One.one : F))
      (m₁ := m ∪ (∅ : H V)) (m₂ := m)
      (fun j => by
        show get? (union m (∅ : H V)) j = _
        rw [get?_union, show get? (∅ : H V) j = none from get?_empty _]
        cases get? m j <;> rfl)
  exact h.trans (BIUpdate.mono (BI.sep_mono_l hunion.mp))

@[rocq_alias ghost_map_alloc_strong]
theorem ghost_map_alloc_strong (P : GName → Prop) (m : H V)
    (HP : ∀ N, ∃ k, N ≤ k ∧ P k) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ (γ ↪●MAP m) ∗ [∗map] k ↦ v ∈ m, γ ↪◯MAP[k] v := by
  imod iOwn_alloc_strong (E := hgm.elem)
      (HeapView.Auth (.own (One.one : F)) (∅ : H (Agree (LeibnizO V)))) P HP
      (HeapView.auth_valid_iff.mpr DFrac.valid_own_one) with ⟨%γ, %HPγ, Hauth⟩
  ihave Hauth := (iOwn_ghost_map_auth_equiv_of_pointwise (m := (∅ : H V))
    (fun j => by
      rw [show get? (∅ : H (Agree (LeibnizO V))) j = none from get?_empty _,
        show get? (∅ : H V) j = none from get?_empty _]; rfl)).mp $$ Hauth
  imod ghost_map_alloc_aux γ m $$ Hauth with Hres
  icases Hres with ⟨Hauth, Hbig⟩
  imodintro
  iexists γ
  isplit
  · ipure_intro; exact HPγ
  · isplitl [Hauth] <;> iassumption

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
  iexists γ
  isplitl [Hauth] <;> iassumption

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
  iapply ghost_map_insert_big_induct γ (fun k v => iprop(γ ↪◯MAP[k] v))
    (fun {m_acc} i x hfresh => ghost_map_insert (γ := γ) (m := m_acc) i x hfresh)
    m m' Hdisj $$ Hauth

@[rocq_alias ghost_map_insert_persist_big]
theorem ghost_map_insert_persist_big {γ} {m : H V} (m' : H V) (Hdisj : m' ##ₘ m) :
    ⊢@{IProp GF} (γ ↪●MAP m) ==∗
      (γ ↪●MAP (m' ∪ m)) ∗ [∗map] k ↦ v ∈ m', γ ↪◯MAP[k]{.discard} v := by
  iintro Hauth
  iapply ghost_map_insert_big_induct γ (fun k v => iprop(γ ↪◯MAP[k]{.discard} v))
    (fun {m_acc} i x hfresh => ghost_map_insert_persist (γ := γ) (m := m_acc) i x hfresh)
    m m' Hdisj $$ Hauth

/-- From `Auth γ 1 m` + `[∗map] m0 frag`, derive `|==> Auth γ 1 (m \ m0)` by inducting on `m0`. -/
private theorem ghost_map_delete_big_aux (γ : GName) (m0 : H V) :
    ∀ m : H V,
      ((γ ↪●MAP m) ∗ [∗map] k ↦ v ∈ m0, γ ↪◯MAP[k] v : IProp GF) ⊢
        |==> γ ↪●MAP (m \ m0) := by
  refine LawfulFiniteMap.induction_on
    (P := fun m0 =>
      ∀ m : H V,
        ((γ ↪●MAP m) ∗ [∗map] k ↦ v ∈ m0, γ ↪◯MAP[k] v : IProp GF) ⊢
          |==> γ ↪●MAP (m \ m0))
    ?_ ?_ ?_ m0
  · intro m₁ m₂ heqv hP m
    have hbig :
        ([∗map] k ↦ v ∈ m₁, (γ ↪◯MAP[k] v) : IProp GF) ⊣⊢
        ([∗map] k ↦ v ∈ m₂, (γ ↪◯MAP[k] v)) :=
      BI.equiv_iff.mp (Iris.Algebra.BigOpM.bigOpM_equiv_of_perm _ heqv)
    have hdiff :=
      ghost_map_auth_equiv_of_pointwise (GF := GF) (γ := γ) (dq := DFrac.own (One.one : F))
        (m₁ := m \ m₁) (m₂ := m \ m₂)
        (fun j => by rw [get?_difference, get?_difference, heqv j])
    iintro ⟨Hauth, Hbig⟩
    iapply (BI.sep_mono_r hbig.mpr).trans
      ((hP m).trans (BIUpdate.mono hdiff.mp)) $$ [$Hauth $Hbig]
  · intro m
    iintro ⟨Hauth, _⟩
    imodintro
    iapply (ghost_map_auth_equiv_of_pointwise (GF := GF) (γ := γ) (dq := DFrac.own (One.one : F))
      (m₁ := m) (m₂ := m \ (∅ : H V))
      (fun j => by
        rw [get?_difference, show get? (∅ : H V) j = none from get?_empty _]; rfl)).mp $$ Hauth
  · intro i x m0 hfresh ihP m
    iintro ⟨Hauth, Hbig⟩
    icases (BigSepM.bigSepM_insert (Φ := fun k v => iprop(γ ↪◯MAP[k] v)) hfresh).mp $$ Hbig
      with ⟨Helem, Hbig⟩
    ihave %Hlookup := ghost_map_lookup $$ Hauth Helem
    imod ghost_map_delete $$ Hauth Helem with Hauth
    have hdiff :=
      ghost_map_auth_equiv_of_pointwise (GF := GF) (γ := γ) (dq := DFrac.own (One.one : F))
        (m₁ := delete m i \ m0)
        (m₂ := m \ insert m0 i x)
        (fun j => by
          rw [get?_difference, get?_difference]
          by_cases hij : i = j
          · subst hij
            rw [get?_insert_eq (rfl : i = i), get?_delete_eq (rfl : i = i)]
            simp
          · rw [get?_insert_ne hij, get?_delete_ne hij])
    iapply (ihP (delete m i)).trans (BIUpdate.mono hdiff.mp) $$ [$Hauth $Hbig]

@[rocq_alias ghost_map_delete_big]
theorem ghost_map_delete_big {γ} {m : H V} (m0 : H V) :
    ⊢@{IProp GF} (γ ↪●MAP m) -∗ ([∗map] k ↦ v ∈ m0, γ ↪◯MAP[k] v) ==∗ γ ↪●MAP (m \ m0) := by
  iintro Hauth Hfrag
  iapply ghost_map_delete_big_aux γ m0 m $$ [$Hauth $Hfrag]

@[rocq_alias ghost_map_update_big]
theorem ghost_map_update_big {γ} {m : H V} (m0 m1 : H V) (Hdom : dom m0 = dom m1) :
    ⊢@{IProp GF} (γ ↪●MAP m) -∗ ([∗map] k ↦ v ∈ m0, γ ↪◯MAP[k] v) ==∗
      (γ ↪●MAP (m1 ∪ m)) ∗ [∗map] k ↦ v ∈ m1, γ ↪◯MAP[k] v := by
  iintro Hauth Hfrag
  have hisSome : ∀ j, (get? m0 j).isSome ↔ (get? m1 j).isSome :=
    fun j => Iff.of_eq (congrFun Hdom j)
  have hdisj : m1 ##ₘ (m \ m0) := by
    intro k ⟨h1, h2⟩
    rw [get?_difference] at h2
    simp [(hisSome k).mpr h1] at h2
  imod ghost_map_delete_big m0 $$ Hauth Hfrag with Hauth
  imod ghost_map_insert_big m1 hdisj $$ Hauth with Hres
  icases Hres with ⟨Hauth, Hbig⟩
  imodintro
  isplitl [Hauth]
  · iapply (ghost_map_auth_equiv_of_pointwise (GF := GF) (γ := γ) (dq := DFrac.own (One.one : F))
      (m₁ := m1 ∪ (m \ m0)) (m₂ := m1 ∪ m) (fun j => by
        show get? (union m1 (m \ m0)) j = get? (union m1 m) j
        rw [get?_union, get?_union, get?_difference]
        cases hm1 : get? m1 j with
        | none =>
          have hm0 : get? m0 j = none :=
            Option.not_isSome_iff_eq_none.mp fun h => by
              have := (hisSome j).mp h; rw [hm1] at this; cases this
          simp [hm0]
        | some _ => rfl)).mp $$ Hauth
  · iexact Hbig

end big_op_lemmas
