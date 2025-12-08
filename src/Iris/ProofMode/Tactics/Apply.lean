/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Split
import Iris.ProofMode.Tactics.Pose

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem apply' [BI PROP] {P Q1 Q2 R : PROP} (p : Bool)
    (inst : IntoWand p false R Q1 Q2) (h : P ⊢ Q1) : P ∗ □?p R ⊢ Q2 :=
  (sep_mono h inst.1).trans wand_elim_r

theorem rec_apply' [BI PROP] {P Q P' Q' Q1 Q2 R : PROP} (p : Bool)
    (inst : IntoWand p false Q Q1 Q2) (h1 : P ⊣⊢ P' ∗ Q') (h2 : Q' ⊢ Q1) (h3 : P' ∗ Q2 ⊢ R)
    : P ∗ □?p Q ⊢ R :=
  (sep_congr h1 .rfl).mp.trans <| sep_assoc.mp.trans <| (sep_mono_r <| apply' p inst h2).trans h3

theorem apply_lean [BI PROP] {P Q R : PROP} (h1 : ⊢ Q) (h2 : P ∗ Q ⊢ R) : P ⊢ R :=
  sep_emp.mpr.trans <| (sep_mono_r h1).trans h2

/-- Connect the result of `iPoseCore` (which gives `e ⊢ e' ∗ □?b out`) with `iApplyCore`
    (which gives `e' ∗ □?b out ⊢ goal`). -/
theorem apply_pose [BI PROP] {e e' : PROP} {b : Bool} {out goal : PROP}
    (h1 : e ⊢ e' ∗ □?b out) (h2 : e' ∗ □?b out ⊢ goal) : e ⊢ goal :=
  h1.trans h2

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
/--
Resolves a goal using the first specialization pattern.

If the specialization pattern is an identifier and the current context `e`
can directly prove `A1` via `FromAssumption p`, use that proof directly.
Otherwise, delegate to `addGoal` to create a new subgoal.

## Parameters
- `goal`: The goal to prove
- `p`: `e` is persistent or not
- `hyps`: The structured representation of the hypothesis `e`
- `spats`: Specialization patterns provided by the user
- `addGoal`: Callback to create a new subgoal when direct proof isn't possible

TODO: handle more cases of spec patterns

## Returns
A proof term of type `e ⊢ goal`
-/
def specPatGoal
    (goal : Q($prop)) (p : Bool) (hyps : Hyps bi e) (spats : List SpecPat)
    (addGoal : ∀ {e}, Name → Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal)) :
    MetaM Q($e ⊢ $goal) := do
  return ← if let (some <| .ident _, some inst) := (spats.head?,
      ← try? (synthInstanceQ q(FromAssumption $p $e $goal))) then
    match p with
    | false => pure q(($inst).from_assumption)
    | true => do
      let _intInst ← synthInstanceQ q(Intuitionistic $e)
      pure q(intuitionistic.trans ($inst).from_assumption)
  else
    addGoal (headName spats) hyps goal

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
/--
Splits the hypothesis context based on specialization patterns and resolves the goal.

This function processes specialization patterns to determine which hypotheses should be
used to prove a goal `goal`. It splits the input hypotheses `hypsl` into two parts:
- Hypotheses matching the specialization pattern (used to prove `goal`)
- Remaining hypotheses (returned for further proof construction)

## Parameters
- `goal`: The goal to prove using the matched hypotheses
- `p`: Whether the context is persistent
- `hypsl`: The input hypothesis context to split
- `spats`: Specialization patterns specifying which hypotheses to use
- `addGoal`: Callback to create a new subgoal when direct proof isn't possible

## Returns
A tuple containing:
- `el'`: The remaining hypotheses (not used for `goal`)
- `er'`: The hypotheses used to prove `goal`
- A proof term of type `er' ⊢ goal`
- The structured representation of remaining hypotheses
- A proof that `el ⊣⊢ el' ∗ er'`
-/
def processSpecPats
    (goal : Q($prop)) (p: Bool) (hypsl : Hyps bi el) (spats : List SpecPat)
    (addGoal : ∀ {e}, Name → Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal)) :
    MetaM ((el' er' : Q($prop)) × Q($er' ⊢ $goal) × Hyps bi el' × Q($el ⊣⊢ $el' ∗ $er')) := do
  let splitPat := fun name _ => match spats.head? with
    | some <| .ident bIdent => binderIdentHasName name bIdent
    | some <| .idents bIdents _ => bIdents.any <| binderIdentHasName name
    | _ => false

  let ⟨el', er', hypsl', hypsr', h'⟩ := Hyps.split bi splitPat hypsl
  let m ← specPatGoal goal p hypsr' spats addGoal
  return ⟨el', er', m, hypsl', h'⟩

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
/--
Core implementation of `iapply` tactic. Applies a hypothesis `er` to prove `goal`,
consuming spatial hypotheses as needed.

## Parameters
- `goal`: The proposition to prove
- `el`: The "left" context (spatial hypotheses not being applied)
- `er`: The hypothesis being applied (the "right" part of the separating conjunction)
- `hypsl`: The structured representation of hypotheses in `el`
- `spats`: Specialization patterns for instantiating arguments
- `addGoal`: Callback to create new subgoals when arguments need to be provided

## Returns
A proof term of type `el ∗ er ⊢ goal`
-/
partial def iApplyCore
    (goal el er : Q($prop)) (hypsl : Hyps bi el) (spats : List SpecPat)
    (addGoal : ∀ {e}, Name → Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal)) :
    MetaM (Q($el ∗ $er ⊢ $goal)) := do
  let _ ← isDefEq er goal

  -- Case: `er` is persistent (`□ R`)
  if let some pf ← observing? do
        let R ← mkFreshExprMVarQ q($prop)
        guard (← isDefEq er q(intuitionisticallyIf true $R))
        let R ← instantiateMVarsQ R
        let _er : Q($prop) := q(intuitionisticallyIf true $R)

        -- iexact (p = true): `R` directly entails `goal` via `FromAssumption true`
        if let (some _, some _) := (← try? <| synthInstanceQ q(FromAssumption true $R $goal),
                                    ← try? <| synthInstanceQ q(TCOr (Affine $el) (Absorbing $goal))) then
          return (q(assumption (p := true) (P' := $el) (A := $R) .rfl) : Q($el ∗ $_er ⊢ $goal))

        let A1 ← mkFreshExprMVarQ q($prop)

        -- iapply base case (p = true): `R` decomposes as `A1 -∗ goal` via `IntoWand true`
        if let some inst ← try? <| synthInstanceQ q(IntoWand true false $R $A1 $goal) then
          let m ← specPatGoal A1 true hypsl spats addGoal
          return (q(apply' true $inst $m) : Q($el ∗ $_er ⊢ $goal))

        let A2 ← mkFreshExprMVarQ q($prop)
        -- iapply recursive case (p = true): `R` is `A1 -∗ A2` where `A2 ≠ goal`

        let inst ← synthInstanceQ q(IntoWand true false $R $A1 $A2)
        let ⟨el', _, m, hypsl', h'⟩ ← processSpecPats A1 true hypsl spats addGoal
        let res : Q($el' ∗ $A2 ⊢ $goal) ← iApplyCore goal el' A2 hypsl' spats.tail addGoal
        pure (q(rec_apply' true $inst $h' $m $res) : Q($el ∗ $_er ⊢ $goal))
  then return pf

  -- Case: `er` is not persistent
  -- iexact (p = false): `er` directly entails `goal` via `FromAssumption false`
  if let (some _, some _) := (← try? <| synthInstanceQ q(FromAssumption false $er $goal),
                              ← try? <| synthInstanceQ q(TCOr (Affine $el) (Absorbing $goal))) then
    return q(assumption (p := false) .rfl)

  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)

  -- iapply base case (p = false): `er` decomposes as `A1 -∗ goal` via `IntoWand false`
  if let some inst ← try? <| synthInstanceQ q(IntoWand false false $er $A1 $goal) then
    let m ← specPatGoal A1 false hypsl spats addGoal
    return q(apply' false $inst $m)

  -- iapply recursive case (p = false): `er` is `A1 -∗ A2` where `A2 ≠ goal`
  if let some inst ← try? <| synthInstanceQ q(IntoWand false false $er $A1 $A2) then
    let ⟨el', _, m, hypsl', h'⟩ ← processSpecPats A1 false hypsl spats addGoal
    let res : Q($el' ∗ $A2 ⊢ $goal) ← iApplyCore goal el' A2 hypsl' spats.tail addGoal
    return q(rec_apply' false $inst $h' $m $res)

  throwError "iapply: cannot apply {er} to {goal}"

theorem apply_forall [BI PROP] (x : α) (P : α → PROP) {Q : PROP}
    [H1 : IntoForall Q P] (H2 : E ⊢ E' ∗ Q) : E ⊢ E' ∗ P x :=
  Entails.trans H2 <| sep_mono_r <| H1.into_forall.trans <| forall_elim x

/--
Instantiates universal quantifiers in a hypothesis with provided terms.

Given a proof `pf : e ⊢ e' ∗ out` where `out` may be a universally quantified proposition,
this function repeatedly applies `apply_forall` to instantiate the quantifiers with the
provided terms, producing a specialized hypothesis.

## Parameters
- `e`: The full hypothesis context
- `e'`: The "left" part of the separating conjunction (unchanged)
- `bi`: The BI instance
- `out`: The current proposition being specialized (initially may have ∀ quantifiers)
- `pf`: The current proof of `e ⊢ e' ∗ out`
- `terms`: The list of terms to instantiate the quantifiers with

## Returns
A pair `(out', pf')` where:
- `out'`: The specialized proposition after instantiating all provided terms
- `pf'`: A proof of `e ⊢ e' ∗ out'`
-/
partial def instantiateForalls' {prop : Q(Type u)} (e e' : Q($prop)) (bi : Q(BI $prop))
    (out : Q($prop)) (pf : Q($e ⊢ $e' ∗ $out)) (terms : List Term) :
    TacticM (Expr × Expr) := do
  if let some t := terms.head? then
    let texpr ← mkAppM' (← elabTerm t none) #[]
    let ⟨_, ttype, texpr⟩ ← inferTypeQ texpr
    let Φ ← mkFreshExprMVarQ q($ttype → $prop)
    let _ ← synthInstanceQ q(IntoForall $out $Φ)
    let res ← mkAppM' Φ #[texpr]
    let pf' ← mkAppM ``apply_forall #[texpr, Φ, pf]
    return ← instantiateForalls' e e' bi res pf' terms.tail
  else
    return ⟨out, pf⟩

elab "iapply" colGt pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { prop, e, bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

    let goals ← IO.mkRef #[]

    if let some uniq ← try? do pure (← hyps.findWithInfo ⟨pmt.term⟩) then
      -- Iris context hypothesis: use iPoseHypCore for forall instantiation
      let { e := e', hyps := hyps', b, out, pf } ← iPoseHypCore hyps uniq pmt.terms [] (goalTracker goals)

      -- Construct □?b out for iApplyCore
      let ⟨ehyp, _⟩ := mkIntuitionisticIf bi b out
      let res ← iApplyCore goal e' ehyp hyps' pmt.spats <| goalTracker goals

      mvar.assign q(apply_pose $pf $res)
      replaceMainGoal (← goals.get).toList
    else
      -- Lean context lemma: use expected type for better inference
      let A1 ← mkFreshExprMVarQ q($prop)
      let A2 ← mkFreshExprMVarQ q($prop)

      let expected : Q(Prop) := if let some _ := ← try? <|
        synthInstanceQ q(IntoWand false false $goal $A1 $A2)
        then q($e ⊢ $A1 -∗ $A2) else q($e ⊢ $goal)

      let expr ← mkAppM' (← elabTerm pmt.term (some expected)) #[]
      let ⟨hyp, pf⟩ ← iPoseLean bi expr pmt.terms goals

      let res ← iApplyCore goal e hyp hyps pmt.spats <| goalTracker goals
      mvar.assign <| ← mkAppM ``apply_lean #[pf, res]
      replaceMainGoal (← goals.get).toList
