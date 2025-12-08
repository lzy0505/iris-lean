/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Instances
import Iris.ProofMode.Patterns.CasesPattern
import Iris.ProofMode.Tactics.Clear
import Iris.ProofMode.Tactics.Move
import Iris.ProofMode.Tactics.Pure

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

/-- Elimination rule for `False` in a spatial hypothesis: any goal follows from `P ∗ False`. -/
theorem false_elim_spatial [BI PROP] {P Q : PROP} : P ∗ False ⊢ Q := wand_elim' false_elim

/-- Elimination rule for `□ False` in an intuitionistic hypothesis: any goal follows from `P ∗ □ False`. -/
theorem false_elim_intuitionistic [BI PROP] {P Q : PROP} : P ∗ □ False ⊢ Q :=
  wand_elim' <| intuitionistically_elim.trans false_elim

/-- Introduces `emp` on the right of a separating conjunction: `P ∗ emp ⊢ Q` reduces to `P ⊢ Q`. -/
theorem sep_emp_intro_spatial [BI PROP] {P Q : PROP} (h : P ⊢ Q) : P ∗ emp ⊢ Q := sep_emp.1.trans h

/-- Introduces `□ emp` on the right of a separating conjunction: `P ∗ □ emp ⊢ Q` reduces to `P ⊢ Q`. -/
theorem sep_emp_intro_intuitionistic [BI PROP] {P Q : PROP}
    (h : P ⊢ Q) : P ∗ □ emp ⊢ Q := (sep_mono_r intuitionistically_emp.1).trans <| sep_emp.1.trans h

/--
Handles case analysis on an empty conjunction pattern (i.e., `[]`).

This handles two cases:
- If `A'` is `False`, applies false elimination to close the goal.
- If `A'` is `emp`, removes the trivial hypothesis and continues with `k`.

**Parameters:**
- `bi`: The BI (bunched implications) instance for the proposition type
- `hyps`: The current hypothesis context
- `Q`: The goal proposition to prove
- `A'`: The hypothesis being destructed
- `p`: Whether the hypothesis is intuitionistic (`true`) or spatial (`false`)
- `k`: Continuation that produces a proof of the goal given updated hypotheses

**Returns:** A proof of `P ∗ □?p A' ⊢ Q`

**Example:** For a goal with hypothesis `H : emp`, the pattern `icases H with []`
removes `H` and continues with the remaining hypotheses.
-/
def iCasesEmptyConj {prop : Q(Type u)} (bi : Q(BI $prop))
    {P} (hyps : Hyps bi P) (Q A' : Q($prop)) (p : Q(Bool))
    (k : ∀ {P}, Hyps bi P → MetaM Q($P ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  try
    let ⟨_⟩ ← assertDefEqQ A' q(iprop(False))
    if p.constName! == ``true then
      have : $p =Q true := ⟨⟩; return q(false_elim_intuitionistic)
    else
      have : $p =Q false := ⟨⟩; return q(false_elim_spatial)
  catch _ =>
    let ⟨_⟩ ← assertDefEqQ A' q(iprop(emp))
    if p.constName! == ``true then
      have : $p =Q true := ⟨⟩; return q(sep_emp_intro_intuitionistic $(← k hyps))
    else
      have : $p =Q false := ⟨⟩; return q(sep_emp_intro_spatial $(← k hyps))


/-- Eliminates an existential in a spatial hypothesis using `IntoExists`. -/
theorem exists_elim_spatial [BI PROP] {P A Q : PROP} {Φ : α → PROP} [inst : IntoExists A Φ]
    (h : ∀ a, P ∗ Φ a ⊢ Q) : P ∗ A ⊢ Q :=
  (sep_mono_r inst.1).trans <| sep_exists_l.1.trans (exists_elim h)

/-- Eliminates an existential in an intuitionistic hypothesis using `IntoExists`. -/
theorem exists_elim_intuitionistic [BI PROP] {P A Q : PROP} {Φ : α → PROP} [IntoExists A Φ]
    (h : ∀ a, P ∗ □ Φ a ⊢ Q) : P ∗ □ A ⊢ Q := exists_elim_spatial h

/--
Handles case analysis on an existential hypothesis.

Given a hypothesis `A'` that can be decomposed via `IntoExists A' Φ`, this introduces a fresh
variable of type `α` and continues case analysis on `Φ x`.

**Parameters:**
- `_bi`: The BI instance (unused but kept for consistency)
- `P`: The remaining hypotheses proposition
- `Q`: The goal proposition to prove
- `A'`: The existential hypothesis being destructed
- `p`: Whether the hypothesis is intuitionistic (`true`) or spatial (`false`)
- `name`: The binder name for the introduced variable (from the pattern syntax)
- `α`: The type of the existentially quantified variable
- `Φ`: The predicate `α → prop` such that `A'` is `∃ x, Φ x`
- `_inst`: Proof that `A'` can be decomposed via `IntoExists`
- `k`: Continuation for processing the body `Φ x`

**Returns:** A proof of `P ∗ □?p A' ⊢ Q`

**Example:** For hypothesis `H : ∃ x, P x`, the pattern `icases H with [x H']`
introduces `x` and renames the body to `H'`.
-/
def iCasesExists {prop : Q(Type u)} (_bi : Q(BI $prop)) (P Q A' : Q($prop)) (p : Q(Bool))
    (name : TSyntax ``binderIdent) (α : Q(Sort v)) (Φ : Q(«$α» → «$prop»))
    (_inst : Q(IntoExists «$A'» «$Φ»))
    (k : (B B' : Q($prop)) → (_ : $B =Q iprop(□?$p $B')) → MetaM Q($P ∗ $B ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  let (name, ref) ← getFreshName name
  withLocalDeclDQ name α fun x => do
    addLocalVarInfo ref (← getLCtx) x α
    have B' : Q($prop) := Expr.headBeta q($Φ $x)
    have : $B' =Q $Φ $x := ⟨⟩
    if p.constName! == ``true then
      have : $p =Q true := ⟨⟩
      let pf : Q(∀ x, $P ∗ □ $Φ x ⊢ $Q) ← mkLambdaFVars #[x] <|← k q(iprop(□ $B')) B' ⟨⟩
      return q(exists_elim_intuitionistic (A := $A') $pf)
    else
      have : $p =Q false := ⟨⟩
      let pf : Q(∀ x, $P ∗ $Φ x ⊢ $Q) ← mkLambdaFVars #[x] <|← k B' B' ⟨⟩
      return q(exists_elim_spatial (A := $A') $pf)

/-- Eliminates a conjunction by projecting to the left component. -/
theorem sep_and_elim_l [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoAnd p A A1 A2]
    (h : P ∗ □?p A1 ⊢ Q) : P ∗ □?p A ⊢ Q :=
  (sep_mono_r <| inst.1.trans <| intuitionisticallyIf_mono and_elim_l).trans h

/-- Spatial version of left conjunction elimination. -/
theorem and_elim_l_spatial [BI PROP] {P A Q A1 A2 : PROP} [IntoAnd false A A1 A2]
    (h : P ∗ A1 ⊢ Q) : P ∗ A ⊢ Q := sep_and_elim_l (p := false) h

/-- Intuitionistic version of left conjunction elimination. -/
theorem and_elim_l_intuitionistic [BI PROP] {P A Q A1 A2 : PROP} [IntoAnd true A A1 A2]
    (h : P ∗ □ A1 ⊢ Q) : P ∗ □ A ⊢ Q := sep_and_elim_l (p := true) h

/-- Eliminates a conjunction by projecting to the right component. -/
theorem sep_and_elim_r [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoAnd p A A1 A2]
    (h : P ∗ □?p A2 ⊢ Q) : P ∗ □?p A ⊢ Q :=
  (sep_mono_r <| inst.1.trans <| intuitionisticallyIf_mono and_elim_r).trans h

/-- Spatial version of right conjunction elimination. -/
theorem and_elim_r_spatial [BI PROP] {P A Q A1 A2 : PROP} [IntoAnd false A A1 A2]
    (h : P ∗ A2 ⊢ Q) : P ∗ A ⊢ Q := sep_and_elim_r (p := false) h

/-- Intuitionistic version of right conjunction elimination. -/
theorem and_elim_r_intuitionistic [BI PROP] {P A Q A1 A2 : PROP} [IntoAnd true A A1 A2]
    (h : P ∗ □ A2 ⊢ Q) : P ∗ □ A ⊢ Q := sep_and_elim_r (p := true) h

/--
Handles case analysis on a conjunction when one side is being cleared (discarded).

This is used when the pattern is `[_ H]` or `[H _]`, where one component of the conjunction
is not needed.

**Parameters:**
- `_bi`: The BI instance (unused but kept for consistency)
- `P`: The remaining hypotheses proposition
- `Q`: The goal proposition to prove
- `A'`: The conjunction hypothesis being destructed
- `A1`, `A2`: The left and right components of the conjunction
- `p`: Whether the hypothesis is intuitionistic (`true`) or spatial (`false`)
- `_inst`: Proof that `A'` can be decomposed via `IntoAnd`
- `right`: Which component to keep:
  - `true`: keep `A2`, discard `A1`
  - `false`: keep `A1`, discard `A2`
- `k`: Continuation for processing the kept component

**Returns:** A proof of `P ∗ □?p A' ⊢ Q`

**Example:** For hypothesis `H : P ∧ Q`, the pattern `icases H with [_ H']`
discards `P` and keeps `Q` as `H'`.
-/
def iCasesAndLR {prop : Q(Type u)} (_bi : Q(BI $prop)) (P Q A' A1 A2 : Q($prop)) (p : Q(Bool))
    (_inst : Q(IntoAnd $p $A' $A1 $A2)) (right : Bool)
    (k : (B B' : Q($prop)) → (_ : $B =Q iprop(□?$p $B')) → MetaM Q($P ∗ $B ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  if p.constName! == ``true then
    have : $p =Q true := ⟨⟩
    if right then
      return q(and_elim_r_intuitionistic (A := $A') $(← k q(iprop(□ $A2)) A2 ⟨⟩))
    else
      return q(and_elim_l_intuitionistic (A := $A') $(← k q(iprop(□ $A1)) A1 ⟨⟩))
  else
    have : $p =Q false := ⟨⟩
    if right then
      return q(and_elim_r_spatial (A := $A') $(← k A2 A2 ⟨⟩))
    else
      return q(and_elim_l_spatial (A := $A') $(← k A1 A1 ⟨⟩))

/-- Eliminates a separating conjunction in a spatial hypothesis, splitting it into two parts. -/
theorem sep_elim_spatial [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoSep A A1 A2]
    (h : P ∗ A1 ⊢ A2 -∗ Q) : P ∗ A ⊢ Q :=
  (sep_mono_r inst.1).trans <| sep_assoc.2.trans <| wand_elim h

/-- Eliminates an intuitionistic conjunction, splitting it into two intuitionistic hypotheses. -/
theorem and_elim_intuitionistic [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoAnd true A A1 A2]
    (h : P ∗ □ A1 ⊢ □ A2 -∗ Q) : P ∗ □ A ⊢ Q :=
  (sep_mono_r <| inst.1.trans intuitionistically_and_sep.1).trans <|
  sep_assoc.2.trans <| wand_elim h

/--
Handles case analysis on a separating conjunction or intuitionistic conjunction.

For spatial hypotheses, uses `IntoSep` to split `A'` into `A1 ∗ A2`.
For intuitionistic hypotheses, uses `IntoAnd` to split `□ A'` into `□ A1` and `□ A2`.

**Parameters:**
- `bi`: The BI instance for the proposition type
- `hyps`: The current hypothesis context
- `Q`: The goal proposition to prove
- `A'`: The conjunction hypothesis being destructed
- `A1`, `A2`: The left and right components of the conjunction
- `p`: Whether the hypothesis is intuitionistic (`true`) or spatial (`false`)
- `inst`: Optional `IntoAnd` instance (used for intuitionistic case)
- `k`: Final continuation after all components are processed
- `k1`: Continuation for processing the first component `A1`
- `k2`: Continuation for processing the second component `A2`

**Returns:** A proof of `P ∗ □?p A' ⊢ Q`

**Example:** For hypothesis `H : P ∗ Q`, the pattern `icases H with [H1 H2]`
splits into `H1 : P` and `H2 : Q`.
-/
def iCasesSep {prop : Q(Type u)} (bi : Q(BI $prop))
    {P} (hyps : Hyps bi P) (Q A' A1 A2 : Q($prop)) (p : Q(Bool))
    (inst : Option Q(IntoAnd $p $A' $A1 $A2))
    (k : ∀ {P}, Hyps bi P → MetaM Q($P ⊢ $Q))
    (k1 k2 : ∀ {P}, Hyps bi P → (Q B B' : Q($prop)) → (_ : $B =Q iprop(□?$p $B')) →
      (∀ {P}, Hyps bi P → MetaM Q($P ⊢ $Q)) → MetaM Q($P ∗ $B ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  if p.constName! == ``true then
    let some _ := inst | _ ← synthInstanceQ q(IntoAnd $p $A' $A1 $A2); unreachable!
    have : $p =Q true := ⟨⟩
    let Q' := q(iprop(□ $A2 -∗ $Q))
    let pf ← k1 hyps Q' q(iprop(□ $A1)) A1 ⟨⟩ fun hyps => do
      let pf ← k2 hyps Q q(iprop(□ $A2)) A2 ⟨⟩ k
      return q(wand_intro $pf)
    return q(and_elim_intuitionistic (A := $A') $pf)
  else
    let _ ← synthInstanceQ q(IntoSep $A' $A1 $A2)
    have : $p =Q false := ⟨⟩
    let Q' := q(iprop($A2 -∗ $Q))
    let pf ← k1 hyps Q' A1 A1 ⟨⟩ fun hyps => do
      let pf ← k2 hyps Q A2 A2 ⟨⟩ k
      return q(wand_intro $pf)
    return q(sep_elim_spatial (A := $A') $pf)

/-- Eliminates a disjunction in a spatial hypothesis, creating two subgoals. -/
theorem or_elim_spatial [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoOr A A1 A2]
    (h1 : P ∗ A1 ⊢ Q) (h2 : P ∗ A2 ⊢ Q) : P ∗ A ⊢ Q :=
  (sep_mono_r inst.1).trans <| BI.sep_or_l.1.trans <| or_elim h1 h2

/-- Eliminates a disjunction in an intuitionistic hypothesis, creating two subgoals. -/
theorem or_elim_intuitionistic [BI PROP] {P A Q A1 A2 : PROP} [IntoOr A A1 A2]
    (h1 : P ∗ □ A1 ⊢ Q) (h2 : P ∗ □ A2 ⊢ Q) : P ∗ □ A ⊢ Q := or_elim_spatial h1 h2

/--
Handles case analysis on a disjunction hypothesis.

Uses `IntoOr` to decompose `A'` into `A1 ∨ A2`, then creates two subgoals:
one where `A1` holds and one where `A2` holds.

**Parameters:**
- `_bi`: The BI instance (unused but kept for consistency)
- `P`: The remaining hypotheses proposition
- `Q`: The goal proposition to prove
- `A'`: The disjunction hypothesis being destructed
- `p`: Whether the hypothesis is intuitionistic (`true`) or spatial (`false`)
- `k1`: Continuation for the left branch (when `A1` holds)
- `k2`: Continuation for the right branch (when `A2` holds)

**Returns:** A proof of `P ∗ □?p A' ⊢ Q`

**Example:** For hypothesis `H : P ∨ Q`, the pattern `icases H with [H1 | H2]`
creates two goals: one with `H1 : P` and one with `H2 : Q`.
-/
def iCasesOr {prop : Q(Type u)} (_bi : Q(BI $prop)) (P Q A' : Q($prop)) (p : Q(Bool))
    (k1 k2 : (B B' : Q($prop)) → (_ : $B =Q iprop(□?$p $B')) → MetaM Q($P ∗ $B ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)
  let _ ← synthInstanceQ q(IntoOr $A' $A1 $A2)
  if p.constName! == ``true then
    have : $p =Q true := ⟨⟩
    let pf1 ← k1 q(iprop(□ $A1)) A1 ⟨⟩
    let pf2 ← k2 q(iprop(□ $A2)) A2 ⟨⟩
    return q(or_elim_intuitionistic (A := $A') $pf1 $pf2)
  else
    have : $p =Q false := ⟨⟩
    let pf1 ← k1 A1 A1 ⟨⟩
    let pf2 ← k2 A2 A2 ⟨⟩
    return q(or_elim_spatial (A := $A') $pf1 $pf2)

/-- Converts a spatial hypothesis to intuitionistic form using `IntoPersistently`. -/
theorem intuitionistic_elim_spatial [BI PROP] {A A' Q : PROP}
    [IntoPersistently false A A'] [TCOr (Affine A) (Absorbing Q)]
    (h : P ∗ □ A' ⊢ Q) : P ∗ A ⊢ Q := (replaces_r to_persistent_spatial).apply h

/-- Converts an intuitionistic hypothesis to a different intuitionistic form using `IntoPersistently`. -/
theorem intuitionistic_elim_intuitionistic [BI PROP] {A A' Q : PROP} [IntoPersistently true A A']
    (h : P ∗ □ A' ⊢ Q) : P ∗ □ A ⊢ Q := intuitionistic_elim_spatial h

/--
Handles the `#` pattern modifier, which marks a hypothesis as intuitionistic.

Uses `IntoPersistently` to convert the hypothesis to intuitionistic form `□ B'`.
For spatial hypotheses, requires either `Affine A'` or `Absorbing Q`.

**Parameters:**
- `_bi`: The BI instance (unused but kept for consistency)
- `P`: The remaining hypotheses proposition
- `Q`: The goal proposition to prove
- `A'`: The hypothesis being made intuitionistic
- `p`: Whether the hypothesis is already intuitionistic (`true`) or spatial (`false`)
- `k`: Continuation for processing the resulting intuitionistic hypothesis

**Returns:** A proof of `P ∗ □?p A' ⊢ Q`

**Example:** For hypothesis `H : P` where `P` is persistent, the pattern `icases H with #H'`
moves `H` to the intuitionistic context as `H' : □ P`.
-/
def iCasesIntuitionistic {prop : Q(Type u)} (_bi : Q(BI $prop)) (P Q A' : Q($prop)) (p : Q(Bool))
    (k : (B' : Q($prop)) → MetaM Q($P ∗ □ $B' ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  let B' ← mkFreshExprMVarQ q($prop)
  let _ ← synthInstanceQ q(IntoPersistently $p $A' $B')
  if p.constName! == ``true then
    have : $p =Q true := ⟨⟩
    return q(intuitionistic_elim_intuitionistic $(← k B'))
  else
    have : $p =Q false := ⟨⟩
    let _ ← synthInstanceQ q(TCOr (Affine $A') (Absorbing $Q))
    return q(intuitionistic_elim_spatial (A := $A') $(← k B'))

/-- Converts a spatial hypothesis to a different spatial form using `FromAffinely`. -/
theorem spatial_elim_spatial [BI PROP] {A A' Q : PROP} [FromAffinely A' A false]
    (h : P ∗ A' ⊢ Q) : P ∗ A ⊢ Q := (replaces_r (from_affine (p := false))).apply h

/-- Converts an intuitionistic hypothesis to spatial form using `FromAffinely`. -/
theorem spatial_elim_intuitionistic [BI PROP] {A A' Q : PROP} [FromAffinely A' A true]
    (h : P ∗ A' ⊢ Q) : P ∗ □ A ⊢ Q := (replaces_r (from_affine (p := true))).apply h

/--
Handles the `-` pattern modifier, which marks a hypothesis as spatial.

Uses `FromAffinely` to convert the hypothesis from intuitionistic to spatial form.

**Parameters:**
- `_bi`: The BI instance (unused but kept for consistency)
- `P`: The remaining hypotheses proposition
- `Q`: The goal proposition to prove
- `A'`: The hypothesis being made spatial
- `p`: Whether the hypothesis is intuitionistic (`true`) or already spatial (`false`)
- `k`: Continuation for processing the resulting spatial hypothesis

**Returns:** A proof of `P ∗ □?p A' ⊢ Q`

**Example:** For intuitionistic hypothesis `H : □ P`, the pattern `icases H with -H'`
moves `H` to the spatial context as `H' : P`.
-/
def iCasesSpatial {prop : Q(Type u)} (_bi : Q(BI $prop)) (P Q A' : Q($prop)) (p : Q(Bool))
    (k : (B' : Q($prop)) → MetaM Q($P ∗ $B' ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  let B' ← mkFreshExprMVarQ q($prop)
  let _ ← synthInstanceQ q(FromAffinely $B' $A' $p)
  if p.constName! == ``true then
    have : $p =Q true := ⟨⟩
    return q(spatial_elim_intuitionistic $(← k B'))
  else
    have : $p =Q false := ⟨⟩
    return q(spatial_elim_spatial (A := $A') $(← k B'))

/-- Eliminates `emp` on the left of a separating conjunction: `emp ∗ A ⊢ Q` reduces to `A ⊢ Q`. -/
theorem of_emp_sep [BI PROP] {A Q : PROP} (h : A ⊢ Q) : emp ∗ A ⊢ Q := emp_sep.1.trans h

variable {u : Level} {prop : Q(Type u)} (bi : Q(BI $prop)) in
/--
Core recursive function for case analysis on Iris proof mode hypotheses.

This function processes an `iCasesPat` pattern and performs the corresponding
destructions on a hypothesis. It handles all pattern types including:
- Simple naming (`.one name`)
- Clearing (`.clear`)
- Conjunctions (`.conjunction`): splits `∗` or `∧`, handles `∃`
- Disjunctions (`.disjunction`): splits `∨` into multiple goals
- Pure patterns (`.pure`): moves hypothesis to Lean context
- Intuitionistic (`.intuitionistic`): applies `#` modifier
- Spatial (`.spatial`): applies `-` modifier

**Parameters:**
- `bi`: The BI instance for the proposition type
- `hyps`: The current hypothesis context (excluding the hypothesis being destructed)
- `Q`: The goal proposition to prove
- `p`: Whether the hypothesis is intuitionistic (`true`) or spatial (`false`)
- `A`: The full hypothesis type (including `□` wrapper if intuitionistic)
- `A'`: The unwrapped hypothesis type
- `pat`: The pattern to apply
- `k`: Continuation that produces a proof given the final hypothesis context

**Returns:** A proof of `P ∗ A ⊢ Q` where `P` represents `hyps`

**Example patterns:**
- `H` → names the hypothesis `H`
- `[H1 H2]` → splits a conjunction into `H1` and `H2`
- `[H1 | H2]` → case splits a disjunction
- `[x H]` → introduces existential witness `x` with body `H`
- `%H` → moves `H` to the Lean context as a pure fact
- `#H` → makes `H` intuitionistic
- `-H` → makes `H` spatial
- `_` → clears the hypothesis
-/
partial def iCasesCore
    {P} (hyps : Hyps bi P) (Q : Q($prop)) (p : Q(Bool))
    (A A' : Q($prop)) (_ : $A =Q iprop(□?$p $A'))
    (pat : iCasesPat) (k : ∀ {P}, Hyps bi P → MetaM Q($P ⊢ $Q)) : MetaM (Q($P ∗ $A ⊢ $Q)) :=
  match pat with
  | .one name => do
    let (name, ref) ← getFreshName name
    let uniq ← mkFreshId
    addHypInfo ref name uniq prop A' (isBinder := true)
    let hyp := .mkHyp bi name uniq p A' A
    if let .emp _ := hyps then
      let pf : Q($A ⊢ $Q) ← k hyp
      pure q(of_emp_sep $pf)
    else
      k (.mkSep hyps hyp)

  | .clear => do
    let pf ← clearCore bi (isTrue p) q(iprop($P ∗ $A)) P A Q q(.rfl)
    pure q($pf $(← k hyps))

  | .conjunction [arg] | .disjunction [arg] => iCasesCore hyps Q p A A' ⟨⟩ arg @k

  | .disjunction [] => throwUnsupportedSyntax

  | .conjunction [] => iCasesEmptyConj bi hyps Q A' p @k

  | .conjunction (arg :: args) => do
    let exres ← try? (α := _ × (v : Level) × (α : Q(Sort v)) × (Φ : Q($α → $prop)) ×
        Q(IntoExists $A' $Φ)) do
      let .one n := arg | failure
      let v ← mkFreshLevelMVar
      let α ← mkFreshExprMVarQ q(Sort v)
      let Φ ← mkFreshExprMVarQ q($α → $prop)
      Pure.pure ⟨n, v, α, Φ, ← synthInstanceQ q(IntoExists $A' $Φ)⟩
    if let some ⟨n, _, α, Φ, inst⟩ := exres then
      iCasesExists bi P Q A' p n α Φ inst
        (iCasesCore hyps Q p · · · (.conjunction args) k)
    else
      let A1 ← mkFreshExprMVarQ q($prop)
      let A2 ← mkFreshExprMVarQ q($prop)
      let A'reduced : Q($prop) ← whnfR A'
      let inst ← try? (α := Q(IntoAnd $p $A' $A1 $A2)) do
        unless arg matches .clear || args matches [.clear] || p.constName! == ``true do failure
        synthInstanceQ q(IntoAnd $p $A'reduced $A1 $A2)
      if let (.clear, some inst) := (arg, inst) then
        iCasesAndLR bi P Q A' A1 A2 p inst (right := true) fun B B' h =>
          iCasesCore hyps Q p B B' h (.conjunction args) @k
      else if let ([.clear], some inst) := (args, inst) then
        iCasesAndLR bi P Q A' A1 A2 p inst (right := false) fun B B' h =>
          iCasesCore hyps Q p B B' h arg @k
      else
        iCasesSep bi hyps Q A' A1 A2 p inst @k
          (iCasesCore · · p · · · arg)
          (iCasesCore · · p · · · (.conjunction args))

  | .disjunction (arg :: args) =>
    iCasesOr bi P Q A' p
      (iCasesCore hyps Q p · · · arg @k)
      (iCasesCore hyps Q p · · · (.disjunction args) @k)

  | .pure arg => do
    let .one n := arg
      | throwError "cannot further destruct a hypothesis after moving it to the Lean context"
    (·.2) <$> ipureCore bi q(iprop($P ∗ $A)) P A Q n q(.rfl) fun _ _ =>
      ((), ·) <$> k hyps

  | .intuitionistic arg =>
    iCasesIntuitionistic bi P Q A' p fun B' =>
      iCasesCore hyps Q q(true) q(iprop(□ $B')) B' ⟨⟩ arg @k

  | .spatial arg =>
    iCasesSpatial bi P Q A' p fun B' =>
      iCasesCore hyps Q q(false) B' B' ⟨⟩ arg @k

/--
Performs case analysis on an Iris proof mode hypothesis.

**Syntax:** `icases H with pat`

**Parameters:**
- `hyp`: The name of the hypothesis to destruct
- `pat`: The pattern describing how to destruct the hypothesis

**Pattern syntax:**
- `H` — rename the hypothesis to `H`
- `_` — clear/discard the hypothesis
- `[H1 H2]` — split a separating conjunction `P ∗ Q` into `H1 : P` and `H2 : Q`
- `[H1 | H2]` — case split a disjunction `P ∨ Q` into two goals
- `[x H]` — introduce existential `∃ x, P x` with witness `x` and body `H`
- `%H` — move a pure hypothesis to the Lean context
- `#H` — make the hypothesis intuitionistic (move to `□` context)
- `-H` — make the hypothesis spatial (remove from `□` context)
- `[]` — eliminate `False` or `emp`

Patterns can be nested: `[x [H1 H2]]` destructs `∃ x, P ∗ Q`.

**Examples:**
```
icases H with [H1 H2]       -- split H : P ∗ Q
icases H with [x Hx]        -- intro H : ∃ x, P x
icases H with [H1 | H2]     -- case split H : P ∨ Q
icases H with #H'           -- make H intuitionistic
icases H with [[a b] [c d]] -- nested destruction
```
-/
elab "icases" colGt hyp:ident "with" colGt pat:icasesPat : tactic => do
  -- parse syntax
  let pat ← liftMacroM <| iCasesPat.parse pat

  let (mvar, { u, prop, bi, e, hyps, goal }) ← istart (← getMainGoal)
  mvar.withContext do

  let uniq ← hyps.findWithInfo hyp
  let ⟨_, hyps', A, A', b, h, pf⟩ := hyps.remove true uniq

  -- process pattern
  let goals ← IO.mkRef #[]
  let pf2 ← iCasesCore bi hyps' goal b A A' h pat (λ hyps => goalTracker goals .anonymous hyps goal)

  mvar.assign q(($pf).1.trans $pf2)
  replaceMainGoal (← goals.get).toList
