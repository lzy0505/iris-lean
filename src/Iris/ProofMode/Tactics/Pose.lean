/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Tactics.Cases
import Iris.ProofMode.Tactics.Specialize

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem pose {PROP} [BI PROP] {P Q R : PROP}
    (H1 : P ∗ □ Q ⊢ R) (H2 : ⊢ Q) : P ⊢ R :=
  (BI.equiv_entails.mp sep_emp).2.trans <| (sep_mono_r ((BI.equiv_entails.mp intuitionistically_emp).2.trans (intuitionistically_mono H2))).trans H1

/-- Pose a hypothesis `Q` from the Iris context, keeping its persistence flag. -/
theorem pose_hyp [BI PROP] {P P' : PROP} {p : Bool} {Q R : PROP}
    (H1 : P ⊢ P' ∗ □?p Q) (H2 : P' ∗ □?p Q ⊢ R) : P ⊢ R :=
  H1.trans H2

/-! ## iPoseLean -/

/-- Convert a Lean hypothesis `⊢ P` into the form `e ⊢ e ∗ □ P`.
    This allows treating Lean hypotheses uniformly with Iris hypotheses. -/
theorem pose_lean [BI PROP] {e P : PROP} (h : ⊢ P) : e ⊢ e ∗ □ P :=
  (BI.equiv_entails.mp sep_emp).2.trans <| sep_mono_r <| (BI.equiv_entails.mp intuitionistically_emp).2.trans (intuitionistically_mono h)

theorem emp_wand {PROP} [BI PROP] {P : PROP}: (emp ⊢ P) → (⊢ P) := by
 intros H
 assumption

/-- Instantiate Iris-level forall with `x`. -/
theorem pose_forall [BI PROP] (x : α) (P : α → PROP) {Q : PROP}
    [H1 : IntoForall Q P] (H2 : ⊢ Q) : ⊢ P x :=
  Entails.trans H2 <| H1.into_forall.trans <| forall_elim x

/-- Instantiate Iris-level foralls in `hyp` with the given `terms`. -/
partial def instantiateForalls {prop : Q(Type u)} (bi : Q(BI $prop)) (hyp : Q($prop))
    (pf : Expr) (terms : List Term) : TacticM (Expr × Expr) := do
  if let some t := terms.head? then
    let texpr ← mkAppM' (← elabTerm t none) #[]
    let ⟨_, ttype, texpr⟩ ← inferTypeQ texpr
    let Φ ← mkFreshExprMVarQ q($ttype → $prop)
    let _ ← synthInstanceQ q(IntoForall $hyp $Φ)
    let res ← mkAppM' Φ #[texpr]
    let pf' ← mkAppM ``pose_forall #[texpr, Φ, pf]
    return ← instantiateForalls bi res pf' terms.tail
  else
    let pf'Ty ← inferType pf
    if let some #[_, _, hh, (P : Q($prop))] := (← whnfR pf'Ty).appM? ``Entails then
      if (← whnfR hh).isAppOfArity ``BI.emp 2 then
        -- special case for `emp ⊢ P`
        let pf' : Expr ← mkAppM ``emp_wand #[pf]
        let pf ← mkAppM ``as_emp_valid_1 #[P, pf']
        return ⟨P, pf⟩
      else
      -- case for `P ⊢ Q`
      let pf ← mkAppM ``as_emp_valid_1 #[hyp, pf]
      return ⟨hyp, pf⟩
    else
      -- case for `⊢ P`
      let pf ← mkAppM ``as_emp_valid_1 #[hyp, pf]
      return ⟨hyp, pf⟩

/-- Process Lean-level foralls/implications in the type of `val`. -/
partial def handleDependentArrows {prop : Q(Type u)} (bi : Q(BI $prop)) (val : Expr) (goals : IO.Ref (Array MVarId)) : TacticM (Expr × Q(Prop)) := do
  let p : Q(Prop) ← inferType val
  if let .forallE _ binderType _ _ := p then
    let m ← mkFreshExprMVar binderType
    let val' := mkApp val m
    let binderTypeType ← inferType binderType
    -- Only add as goal if binderType is Prop (i.e., this is a Lean implication)
    if binderTypeType.isProp then
      goals.modify (·.push m.mvarId!)
    return ← handleDependentArrows bi val' goals
  else
    return (val, p)

/-- Synthesize an `IntoEmpValid φ P` instance, recursively handling implications and foralls. -/
partial def synthIntoEmpValid {prop : Q(Type u)} (bi : Q(BI $prop))
    (φ : Q(Prop)) (P : Q($prop)) (goals : IO.Ref (Array MVarId)) : MetaM Expr := do
  let φReduced ← whnf φ

  -- Check for implication (non-dependent arrow): φ → ψ
  if let .forallE _name binderType body .default := φReduced then
    if !body.hasLooseBVars then
      let φ' := binderType
      let ψ := body
      let hφ ← mkFreshExprMVar φ'
      goals.modify (·.push hφ.mvarId!)
      let innerInst ← synthIntoEmpValid bi ψ P goals
      return ← mkAppOptM ``intoEmpValid_impl #[prop, bi, P, φ', ψ, hφ, innerInst]

  -- Check for forall (dependent): ∀ x : A, φ x
  if let .forallE name binderType body _ := φReduced then
    let A := binderType
    let x ← mkFreshExprMVar A
    let φx := body.instantiate1 x
    let innerInst ← synthIntoEmpValid bi φx P goals
    let φFn := Expr.lam name binderType body .default
    return ← mkAppOptM ``intoEmpValid_forall #[prop, bi, P, A, φFn, x, innerInst]

  -- Base case: try to synthesize directly
  try
    synthInstance q(@IntoEmpValid $φ $prop $P $bi)
  catch _ =>
    throwError "ipose: cannot find IntoEmpValid instance for {φ}"

/-- Convert a Lean proof to an Iris hypothesis. Returns `(hyp, pf : ⊢ hyp)`. -/
def iPoseLean {prop : Q(Type u)} (bi : Q(BI $prop)) (val : Expr) (terms : List Term)
    (goals : IO.Ref (Array MVarId)) : TacticM (Q($prop) × Expr) := do
  let hyp ← mkFreshExprMVarQ q($prop)
  let (v, p) ← handleDependentArrows bi val goals
  let _ ← synthIntoEmpValid bi p hyp goals
  let ⟨hyp, pf⟩ ← instantiateForalls bi hyp v terms
  return ⟨hyp, pf⟩

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
/-- Pose a hypothesis from the Iris context. -/
def iPoseHypCore {e : Q($prop)}
    (hyps : Hyps bi e) (uniq : Name) (terms : List Term) (spats : List SpecPat)
    (addGoal : ∀ {e'}, Name → Hyps bi e' → (goal : Q($prop)) → MetaM Q($e' ⊢ $goal)) :
    TacticM (SpecializeState bi e) := do
  let ⟨e', hyps', _out, out', b, _, pf⟩ := hyps.remove false uniq
  let state : SpecializeState bi e := { e := e', hyps := hyps', b, out := out', pf := q((BI.equiv_entails.mp $pf).1) }
  let state ← liftM <| terms.foldlM SpecializeState.process1 state
  let state ← state.processSpats spats addGoal
  return state

/-- Core logic for posing a Lean proof as an Iris hypothesis. -/
def iPoseLeanCore {prop : Q(Type u)} (bi : Q(BI $prop)) {e : Q($prop)}
    (hyps : Hyps bi e) (val : Expr) (terms : List Term) (spats : List SpecPat)
    (goals : IO.Ref (Array MVarId))
    (addGoal : ∀ {e'}, Name → Hyps bi e' → (goal : Q($prop)) → MetaM Q($e' ⊢ $goal)) :
    TacticM (SpecializeState bi e) := do
  let ⟨(hyp : Q($prop)), (pf : Q(⊢ $hyp))⟩ ← iPoseLean bi val terms goals
  let state : SpecializeState bi e := {
    e := e, hyps := hyps, b := q(true), out := hyp, pf := q(pose_lean $pf)
  }
  let state ← state.processSpats spats addGoal
  return state

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
/-- Unified core logic for `ipose`: handles both Lean and Iris context hypotheses. -/
def iPoseCore {e : Q($prop)}
    (hyps : Hyps bi e) (pmt : PMTerm) (goals : IO.Ref (Array MVarId)) :
    TacticM (SpecializeState bi e) := do
  if let some uniq ← try? do pure (← hyps.findWithInfo ⟨pmt.term⟩) then
    iPoseHypCore hyps uniq pmt.terms pmt.spats (goalTracker goals)
  else
    let val ← elabTerm pmt.term none true
    let val ← instantiateMVars val
    iPoseLeanCore bi hyps val pmt.terms pmt.spats goals (goalTracker goals)

elab "ipose" colGt pmt:pmTerm "as" pat:(colGt icasesPat) : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  let pat ← liftMacroM <| iCasesPat.parse pat
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

    let goals ← IO.mkRef #[]

    -- Both Lean and Iris hypotheses now return SpecializeState
    let { hyps := hyps', b, out, pf, .. } ← iPoseCore hyps pmt goals
    let ⟨ehyp, _⟩ := mkIntuitionisticIf bi b out
    let m ← iCasesCore bi hyps' goal b ehyp out ⟨⟩ pat
      (fun hyps => goalTracker goals .anonymous hyps goal)
    mvar.assign q(pose_hyp $pf $m)

    replaceMainGoal (← goals.get).toList
