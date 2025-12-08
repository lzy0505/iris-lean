/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove
import Iris.ProofMode.Tactics.Split
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Instances
import Iris.Std

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

structure SpecializeState {prop : Q(Type u)} (bi : Q(BI $prop)) (orig : Q($prop)) where
  (e : Q($prop)) (hyps : Hyps bi e) (b : Q(Bool)) (out : Q($prop))
  pf : Q($orig ⊢ $e ∗ □?$b $out)

theorem specialize_wand [BI PROP] {q p : Bool} {A1 A2 A3 Q P1 P2 : PROP}
    (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊣⊢ A3 ∗ □?p P1)
    [inst : IntoWand q p Q P1 P2] : A1 ⊢ A3 ∗ □?(p && q) P2 := by
  refine h1.trans <| (sep_mono_l h2.1).trans <| sep_assoc.1.trans (sep_mono_r ?_)
  cases p with
  | false => exact (sep_mono_r inst.1).trans wand_elim_r
  | true => exact
    (sep_mono intuitionisticallyIf_intutitionistically.2 intuitionisticallyIf_idem.2).trans <|
    intuitionisticallyIf_sep_2.trans <| intuitionisticallyIf_mono <| wand_elim' inst.1

theorem specialize_forall [BI PROP] {p : Bool} {A1 A2 P : PROP} {α : Sort _} {Φ : α → PROP}
    [inst : IntoForall P Φ] (h : A1 ⊢ A2 ∗ □?p P) (a : α) : A1 ⊢ A2 ∗ □?p (Φ a) := by
  refine h.trans <| sep_mono_r <| intuitionisticallyIf_mono <| inst.1.trans (forall_elim a)

/-- Specialize a wand by splitting context to provide the argument.

    Given:
    - `h1 : orig ⊢ e ∗ □?p R` where `R` is a wand (via IntoWand)
    - `h2 : e ⊣⊢ e' ∗ er` (split the context)
    - `h3 : er ⊢ P` (proof of the wand argument from the split-off part)

    Produces: `orig ⊢ e' ∗ □?p Q` -/
theorem specialize_wand_split [BI PROP] {p : Bool} {orig e e' er R P Q : PROP}
    (h1 : orig ⊢ e ∗ □?p R) (h2 : e ⊣⊢ e' ∗ er) (h3 : er ⊢ P)
    [inst : IntoWand p false R P Q] : orig ⊢ e' ∗ □?p Q := by
  -- inst.into_wand : □?p R ⊢ P -∗ Q
  refine h1.trans <| (sep_mono_l h2.1).trans <| sep_assoc.1.trans <| sep_mono_r ?_
  -- Goal: er ∗ □?p R ⊢ □?p Q
  cases p with
  | false =>
    -- Goal: er ∗ R ⊢ Q
    -- inst.into_wand : R ⊢ P -∗ Q
    exact (sep_mono h3 inst.into_wand).trans wand_elim_r
  | true =>
    -- Goal: er ∗ □ R ⊢ □ Q
    sorry

def SpecializeState.process1 :
    @SpecializeState u prop bi orig → Term → TermElabM (SpecializeState bi orig)
  | { e, hyps, b, out, pf }, arg => do
    let uniq ← match arg with
      | `($x:ident) => try? (hyps.findWithInfo x)
      | _ => pure none
    if let some uniq := uniq then
      -- if the argument is a hypothesis then specialize the wand
      let ⟨e', hyps', out₁, out₁', b1, _, pf'⟩ := hyps.remove false uniq
      let b2 := if b1.constName! == ``true then b else q(false)
      have : $out₁ =Q iprop(□?$b1 $out₁') := ⟨⟩
      have : $b2 =Q ($b1 && $b) := ⟨⟩

      let out₂ ← mkFreshExprMVarQ prop
      let _ ← synthInstanceQ q(IntoWand $b $b1 $out $out₁' $out₂)
      let pf := q(specialize_wand $pf $pf')
      return { e := e', hyps := hyps', b := b2, out := out₂, pf }
    else
      -- otherwise specialize the universal quantifier
      let v ← mkFreshLevelMVar
      let α : Q(Sort v) ← mkFreshExprMVarQ q(Sort v)
      let Φ : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
      let _ ← synthInstanceQ q(IntoForall $out $Φ)
      let x ← elabTermEnsuringTypeQ (u := .succ .zero) arg α
      have out' : Q($prop) := Expr.headBeta q($Φ $x)
      have : $out' =Q $Φ $x := ⟨⟩
      return { e, hyps, b, out := out', pf := q(specialize_forall $pf $x) }

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
/-- Resolve a goal using a specialization pattern, following the pattern from Apply.lean.

    If the spec pattern is an identifier and the context `e` can directly prove `goal`
    via `FromAssumption p`, use that proof directly. Otherwise, delegate to `addGoal`. -/
def specPatGoal'
    (goal : Q($prop)) (p : Bool) (hyps : Hyps bi e) (spats : List SpecPat)
    (addGoal : ∀ {e}, Name → Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal)) :
    MetaM Q($e ⊢ $goal) := do
  if let (some <| .ident _, some inst) := (spats.head?,
      ← try? (synthInstanceQ q(FromAssumption $p $e $goal))) then
    match p with
    | false => pure q(($inst).from_assumption)
    | true => do
      let _intInst ← synthInstanceQ q(Intuitionistic $e)
      pure q(intuitionistic.trans ($inst).from_assumption)
  else
    addGoal (headName spats) hyps goal

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
/-- Process specialization patterns to specialize a wand in a SpecializeState.

    Given the current state with `out` being a wand `P -∗ Q`, this function:
    1. Splits the context based on the first spec pattern
    2. Uses those hypotheses (or creates a subgoal) to prove `P`
    3. Returns updated state with `out = Q`

    Follows the same pattern as `processSpecPats` in Apply.lean. -/
def SpecializeState.processSpat {orig : Q($prop)}
    (state : SpecializeState bi orig) (spats : List SpecPat)
    (addGoal : ∀ {e}, Name → Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal)) :
    MetaM (SpecializeState bi orig) := do
  let { hyps, b, out, pf, .. } := state

  -- Determine which hypotheses to split off based on the first pattern
  let splitPat := fun name _ => match spats.head? with
    | some <| .ident bIdent => binderIdentHasName name bIdent
    | some <| .idents bIdents _ => bIdents.any <| binderIdentHasName name
    | _ => false

  -- Split context: e ⊣⊢ e' ∗ er
  let ⟨e', er, hyps', hypsr, splitPf⟩ := Hyps.split bi splitPat hyps

  -- Synthesize IntoWand to decompose `out` as `P -∗ Q`
  let P ← mkFreshExprMVarQ q($prop)
  let Q ← mkFreshExprMVarQ q($prop)
  let p : Bool := b.constName! == ``true
  let _inst ← synthInstanceQ q(IntoWand $b false $out $P $Q)

  -- Get proof of the argument using specPatGoal' pattern
  let argPf : Q($er ⊢ $P) ← specPatGoal' P p hypsr spats addGoal

  -- Apply the theorem to get the new state
  let pf' := q(specialize_wand_split $pf $splitPf $argPf)

  return { e := e', hyps := hyps', b, out := Q, pf := pf' }

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
/-- Process multiple specialization patterns to specialize a chain of wands.

    Repeatedly applies `processSpat` for each pattern in the list. -/
def SpecializeState.processSpats {orig : Q($prop)}
    (state : SpecializeState bi orig) (spats : List SpecPat)
    (addGoal : ∀ {e}, Name → Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal)) :
    MetaM (SpecializeState bi orig) := do
  match spats with
  | [] => pure state
  | _ :: tail => do
    let state' ← state.processSpat spats addGoal
    state'.processSpats tail addGoal

elab "ispecialize" hyp:ident args:(colGt term:max)* " as " name:binderIdent : tactic => do
  let (mvar, { prop, bi, e, hyps, goal, .. }) ← istart (← getMainGoal)
  mvar.withContext do

  -- find hypothesis index
  let uniq ← hyps.findWithInfo hyp
  let (nameTo, nameRef) ← getFreshName name
  let ⟨_, hyps', _, out', b, _, pf⟩ := hyps.remove (hyp.getId == nameTo) uniq

  let state := { hyps := hyps', out := out', b, pf := q(($pf).1), .. }

  -- specialize hypothesis using process1 (handles both forall and wand args)
  let { e := ehyps, hyps, out, b, pf } ← liftM <| args.foldlM SpecializeState.process1 state

  let ⟨ehyp1, _⟩ := mkIntuitionisticIf bi b out
  let uniq' ← mkFreshId
  let hyp1 := .mkHyp bi nameTo uniq' b out ehyp1
  addHypInfo nameRef nameTo uniq' prop out (isBinder := true)
  let hyps' := hyps.mkSep hyp1
  have pf : Q($e ⊢ $ehyps ∗ $ehyp1) := pf
  let m : Q($ehyps ∗ $ehyp1 ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps := hyps', goal, .. }
  mvar.assign q(($pf).trans $m)
  replaceMainGoal [m.mvarId!]

macro "ispecialize" hyp:ident args:(colGt term:max)* : tactic =>
  `(tactic| ispecialize $hyp $args* as $hyp:ident)
