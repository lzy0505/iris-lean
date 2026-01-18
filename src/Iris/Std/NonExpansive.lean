/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu

Tactics for proving NonExpansive instances automatically.

This file provides tactics similar to Coq's `solve_proper` and `f_equiv` for
automatically proving that functions preserve OFE relations (NonExpansive).
-/
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Simp
import Iris.Algebra.OFE
import Iris.BI.DerivedLaws

namespace Iris.Std.NonExpansiveTactic
open Lean Lean.Elab.Tactic Lean.Meta Iris

/-!
The `f_nonexp` tactic automatically proves goals about relation preservation.
It works on goals of the form:
- `f x₁ ≡{n}≡ f x₂` (given `x₁ ≡{n}≡ x₂`)
- `f x₁ y₁ ≡{n}≡ f x₂ y₂` (given `x₁ ≡{n}≡ x₂` and `y₁ ≡{n}≡ y₂`)
- Similar patterns for OFE equivalence `≡`

The tactic tries to:
1. Apply reflexivity if both sides are identical
2. Apply NonExpansive instances to decompose the goal
3. Use assumptions from the context
4. Recursively solve subgoals
-/

/-- Try to apply reflexivity using the rfl tactic -/
def tryRefl (goal : MVarId) : MetaM (Option (List MVarId)) := do
  try
    goal.refl
    return some []
  catch _ =>
    return none

/-- Try to apply Dist.rfl explicitly -/
def tryDistRefl (goal : MVarId) : MetaM (Option (List MVarId)) := do
  try
    let newGoals ← goal.apply (← mkConstWithFreshMVarLevels ``Iris.OFE.Dist.rfl)
    return some newGoals
  catch _ =>
    return none

/-- Try to apply symmetry -/
def trySymm (goal : MVarId) : MetaM (Option MVarId) := do
  try
    let goalNew ← goal.applySymm
    return some goalNew
  catch _ =>
    return none

/-- Check if expression is an OFE Dist relation `_ ≡{_}≡ _` -/
def isDistRel (e : Expr) : MetaM Bool := do
  let type ← inferType e
  return type.isAppOf ``Iris.OFE.Dist

/-- Check if expression is an OFE Equiv relation `_ ≡ _` -/
def isEquivRel (e : Expr) : MetaM Bool := do
  let type ← inferType e
  return type.isAppOf ``Iris.OFE.Equiv

/-- Try to find a NonExpansive₂ instance by inspecting the goal structure -/
def tryApplyNonExpansive₂ForOp (goal : MVarId) : MetaM (Option (List MVarId)) := do
  goal.withContext do
    try
      -- Get the goal type
      let goalType ← goal.getType'
      -- Try to match against `Dist n lhs rhs` pattern (≡{n}≡)
      -- The goalType is `Dist n lhs rhs` where Dist takes implicit OFE args
      let (_, args) := goalType.getAppFnArgs
      -- We expect at least 3 args: n, lhs, rhs (plus potentially implicit OFE args)
      if args.size < 3 then return none
      let lhs := args[args.size - 2]!
      let rhs := args[args.size - 1]!

      -- Reduce/unfold the lhs and rhs to get past any macro expansions
      let lhs ← Meta.reduce lhs (skipTypes := false) (skipProofs := false)
      let rhs ← Meta.reduce rhs (skipTypes := false) (skipProofs := false)

      -- Check if lhs and rhs have the same head function (binary operator)
      let lhsFn := lhs.getAppFn
      let rhsFn := rhs.getAppFn
      -- If both sides have the same head and it's applied to at least 2 args, try NonExpansive₂
      if lhsFn == rhsFn && lhs.getAppNumArgs >= 2 && rhs.getAppNumArgs >= 2 then
        -- Build the type `NonExpansive₂ op`
        let ne2Type := mkApp (← mkConstWithFreshMVarLevels ``Iris.OFE.NonExpansive₂) lhsFn
        -- Try to synthesize the instance
        let ne2Inst ← try synthInstance ne2Type catch _ => return none
        -- Apply the .ne field
        let neField := mkProj ``Iris.OFE.NonExpansive₂ 0 ne2Inst
        let newGoals ← goal.apply neField
        return some newGoals
      return none
    catch _ =>
      return none

/-- Try to find a NonExpansive instance and apply it -/
def applyNonExpansive (goal : MVarId) : MetaM (Option (List MVarId)) := do
  goal.withContext do
    -- First try the smart approach for binary operators
    if let some goals := ← tryApplyNonExpansive₂ForOp goal then
      return some goals

    -- Try NonExpansive.ne for unary functions
    try
      let newGoals ← goal.apply (← mkConstWithFreshMVarLevels ``Iris.OFE.NonExpansive.ne)
      return some newGoals
    catch _ => pure ()

    -- Try NonExpansive₂.ne for binary functions (generic approach)
    try
      let newGoals ← goal.apply (← mkConstWithFreshMVarLevels ``Iris.OFE.NonExpansive₂.ne)
      return some newGoals
    catch _ => pure ()

    return none

/-- Try to apply OFE.Equiv.dist to convert ≡ to ≡{n}≡ -/
def applyEquivDist (goal : MVarId) : MetaM (Option (List MVarId)) := do
  try
    let newGoals ← goal.apply (← mkConstWithFreshMVarLevels ``Iris.OFE.Equiv.dist)
    return some newGoals
  catch _ =>
    return none

/-- Try to apply `constructor` to break down NonExpansive goals -/
def tryConstructor (goal : MVarId) : MetaM (Option (List MVarId)) := do
  try
    let newGoals ← goal.constructor
    return some newGoals
  catch _ =>
    return none

/-- Try to solve goal using typeclass inference -/
def tryInferInstance (goal : MVarId) : MetaM (Option (List MVarId)) := do
  try
    goal.inferInstance
    return some []
  catch _ =>
    return none

/-- Try to use an assumption from the context -/
def tryAssumption (goal : MVarId) : MetaM (Option (List MVarId)) := do
  try
    goal.assumption
    return some []
  catch _ =>
    return none

/-- Try to apply assumptions that might be universally quantified -/
def tryApplyAssumptions (goal : MVarId) : MetaM (Option (List MVarId)) := do
  goal.withContext do
    let lctx ← getLCtx
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      try
        let newGoals ← goal.apply ldecl.toExpr
        return some newGoals
      catch _ => continue
    return none

/-- Try to apply forall_ne for goals involving forall quantifiers -/
def tryForallNe (goal : MVarId) : MetaM (Option (List MVarId)) := do
  try
    let newGoals ← goal.apply (← mkConstWithFreshMVarLevels ``Iris.BI.forall_ne)
    return some newGoals
  catch _ =>
    return none

/-- Try to apply NonExpansive.ne and let typeclass inference fill in the instance -/
def applyNonExpansiveNe (goal : MVarId) : MetaM (Option (List MVarId)) := do
  try
    let newGoals ← goal.apply (← mkConstWithFreshMVarLevels ``Iris.OFE.NonExpansive.ne)
    return some newGoals
  catch _ =>
    return none


/-- Check if goal is an Equiv (≡) relation, not Dist (≡{n}≡) -/
def isEquivGoal (goal : MVarId) : MetaM Bool := do
  let goalType ← goal.getType
  -- Check if it's of the form `x ≡ y` (Equiv)
  return goalType.isAppOf ``Iris.OFE.Equiv


/-- Main recursive solver for f_nonexp -/
partial def solveNonExpansiveCore (maxDepth : Nat) (goal : MVarId) : MetaM (List MVarId) := do
  if maxDepth = 0 then
    return [goal]

  -- Try reflexivity first (fast path)
  if let some goals := ← tryRefl goal then
    return goals

  -- Try Dist.rfl explicitly (for cases where goal.refl doesn't work)
  if let some goals := ← tryDistRefl goal then
    return goals

  -- Try using an assumption
  if let some goals := ← tryAssumption goal then
    return goals

  -- Try applying assumptions (for universally quantified hypotheses)
  if let some goals := ← tryApplyAssumptions goal then
    let mut remainingGoals := []
    for g in goals do
      remainingGoals := remainingGoals ++ (← solveNonExpansiveCore (maxDepth - 1) g)
    return remainingGoals

  -- Try typeclass inference
  if let some goals := ← tryInferInstance goal then
    return goals

  -- Try constructor for NonExpansive goals
  if let some goals := ← tryConstructor goal then
    let mut remainingGoals := []
    for g in goals do
      remainingGoals := remainingGoals ++ (← solveNonExpansiveCore (maxDepth - 1) g)
    return remainingGoals

  -- Try applying NonExpansive.ne (for goals like `f x ≡{n}≡ f y`)
  if let some goals := ← applyNonExpansiveNe goal then
    let mut remainingGoals := []
    for g in goals do
      remainingGoals := remainingGoals ++ (← solveNonExpansiveCore (maxDepth - 1) g)
    return remainingGoals

  -- Try applying NonExpansive₂.ne for binary operators
  if let some goals := ← applyNonExpansive goal then
    let mut remainingGoals := []
    for g in goals do
      remainingGoals := remainingGoals ++ (← solveNonExpansiveCore (maxDepth - 1) g)
    return remainingGoals

  -- Try applying forall_ne for forall quantifiers, then intro the quantified variable
  if let some goals := ← tryForallNe goal then
    let mut remainingGoals := []
    for g in goals do
      -- After applying forall_ne, we need to introduce the quantified variable
      let (_, g') ← try g.intro1 catch _ => pure (default, g)
      remainingGoals := remainingGoals ++ (← solveNonExpansiveCore (maxDepth - 1) g')
    return remainingGoals

  -- Try converting ≡ to ≡{n}≡ - ONLY if the goal is actually ≡, not ≡{n}≡
  -- This prevents converting solvable ≡{n}≡ goals into unsolvable ≡ goals
  if ← isEquivGoal goal then
    if let some goals := ← applyEquivDist goal then
      let mut remainingGoals := []
      for g in goals do
        remainingGoals := remainingGoals ++ (← solveNonExpansiveCore (maxDepth - 1) g)
      return remainingGoals

  -- If nothing works, return the goal unsolved
  return [goal]

/-- Tactic entry point for f_nonexp -/
def fNonexpTactic (maxDepth : Nat := 10) : TacticM Unit := do
  let goal ← getMainGoal
  let remainingGoals ← solveNonExpansiveCore maxDepth goal
  setGoals remainingGoals

/-!
The `solve_nonexp` tactic is a more aggressive version of `f_nonexp` that:
1. Tries to apply constructor if goal is NonExpansive
2. Introduces all variables and hypotheses
3. Applies f_nonexp repeatedly
4. Fails if it cannot completely solve the goal

Note: This tactic only works on NonExpansive goals. If there are multiple goals,
it will only attempt to solve the NonExpansive ones and leave others unchanged.
-/
def solveNonexpTactic (maxDepth : Nat := 20) : TacticM Unit := do
  -- Get all current goals
  let allGoals ← getGoals
  let mut remainingGoals := []

  -- Process each goal
  for goal in allGoals do
    let goalType ← goal.getType

    -- Check if this goal is a NonExpansive instance
    if goalType.isAppOf ``Iris.OFE.NonExpansive then
      -- This is a NonExpansive goal - try to solve it
      goal.withContext do
        -- Try applying constructor
        let goals ← try
          goal.constructor
        catch _ =>
          pure [goal]

        -- Introduce all variables for the constructor subgoals
        let mut introedGoals := []
        for g in goals do
          let g' ← g.intros
          introedGoals := introedGoals ++ [g'.2]

        -- Apply the core solver to all subgoals
        let mut finalGoals := []
        for g in introedGoals do
          let remaining ← solveNonExpansiveCore maxDepth g
          finalGoals := finalGoals ++ remaining

        -- Check if we successfully solved all NonExpansive subgoals
        if finalGoals.length > 0 then
          throwError "solve_nonexp: could not completely solve NonExpansive goal"
        -- If solved, don't add to remaining goals
    else
      -- Not a NonExpansive goal - leave it unchanged
      remainingGoals := remainingGoals ++ [goal]

  -- Set the remaining goals (non-NonExpansive goals)
  setGoals remainingGoals

end Iris.Std.NonExpansiveTactic

namespace Lean.Elab.Tactic

/-- Tactic for proving NonExpansive goals by decomposition -/
syntax "f_nonexp" : tactic
elab_rules : tactic
  | `(tactic| f_nonexp) => Iris.Std.NonExpansiveTactic.fNonexpTactic

/-- Tactic for solving NonExpansive instances completely -/
syntax "solve_nonexp" : tactic
elab_rules : tactic
  | `(tactic| solve_nonexp) => Iris.Std.NonExpansiveTactic.solveNonexpTactic

end Lean.Elab.Tactic

namespace Iris

open OFE

variable {A PROP : Type _} [OFE A] [OFE PROP]

/-- Typeclass wrapper for "F preserves NonExpansive" -/
class PreservesNonExpansive (F : (A → PROP) → (A → PROP)) : Prop where
  preserves : ∀ Φ, NonExpansive Φ → NonExpansive (F Φ)

end Iris
