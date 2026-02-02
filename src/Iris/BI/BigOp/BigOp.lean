/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.Algebra.BigOp
import Iris.BI.DerivedLaws
import Iris.BI.DerivedLawsLater
import Iris.Std.FiniteMap
import Iris.Std.FiniteSet
import Lean

namespace Iris.BI

open Iris.Algebra
open Iris.Std
open OFE
open BIBase
open Lean PrettyPrinter Delaborator SubExpr

/-! # BI-Instantiated Big Operators over Lists
- `bigSepL`: Big separating conjunction `[∗list]`
- `bigAndL`: Big conjunction `[∧list]`
- `bigOrL`: Big disjunction `[∨list]`
-/

section List
/-! ## Core Definitions -/

/-- Big separating conjunction over a list with index access.
    `bigSepL Φ l` computes `Φ 0 l[0] ∗ Φ 1 l[1] ∗ ... ∗ Φ (n-1) l[n-1]` -/
abbrev bigSepL [BI PROP] {A : Type _} (Φ : Nat → A → PROP) (l : List A) : PROP :=
  bigOpL sep emp Φ l

/-- Big conjunction over a list with index access.
    `bigAndL Φ l` computes `Φ 0 l[0] ∧ Φ 1 l[1] ∧ ... ∧ Φ (n-1) l[n-1]` -/
abbrev bigAndL [BI PROP] {A : Type _} (Φ : Nat → A → PROP) (l : List A) : PROP :=
  bigOpL and iprop(True) Φ l

/-- Big disjunction over a list with index access.
    `bigOrL Φ l` computes `Φ 0 l[0] ∨ Φ 1 l[1] ∨ ... ∨ Φ (n-1) l[n-1]` -/
abbrev bigOrL [BI PROP] {A : Type _} (Φ : Nat → A → PROP) (l : List A) : PROP :=
  bigOpL or iprop(False) Φ l

/-! ## Notation -/

-- Notation for bigSepL without index
syntax "[∗list] " ident " ∈ " term ", " term : term
-- Notation for bigSepL with index
syntax "[∗list] " ident " ↦ " ident " ∈ " term ", " term : term
-- Notation for bigSepL2 without index (two lists)
syntax "[∗list] " ident ";" ident " ∈ " term ";" term ", " term : term
-- Notation for bigSepL2 with index (two lists)
syntax "[∗list] " ident " ↦ " ident ";" ident " ∈ " term ";" term ", " term : term

-- Notation for bigAndL without index
syntax "[∧list] " ident " ∈ " term ", " term : term
-- Notation for bigAndL with index
syntax "[∧list] " ident " ↦ " ident " ∈ " term ", " term : term

-- Notation for bigOrL without index
syntax "[∨list] " ident " ∈ " term ", " term : term
-- Notation for bigOrL with index
syntax "[∨list] " ident " ↦ " ident " ∈ " term ", " term : term

macro_rules
  | `([∗list] $x:ident ∈ $l, $P) => `(bigSepL (fun _ $x => $P) $l)
  | `([∗list] $k:ident ↦ $x:ident ∈ $l, $P) => `(bigSepL (fun $k $x => $P) $l)
  | `([∧list] $x:ident ∈ $l, $P) => `(bigAndL (fun _ $x => $P) $l)
  | `([∧list] $k:ident ↦ $x:ident ∈ $l, $P) => `(bigAndL (fun $k $x => $P) $l)
  | `([∨list] $x:ident ∈ $l, $P) => `(bigOrL (fun _ $x => $P) $l)
  | `([∨list] $k:ident ↦ $x:ident ∈ $l, $P) => `(bigOrL (fun $k $x => $P) $l)

-- iprop macro rules
macro_rules
  | `(iprop([∗list] $x:ident ∈ $l, $P)) => `(bigSepL (fun _ $x => iprop($P)) $l)
  | `(iprop([∗list] $k:ident ↦ $x:ident ∈ $l, $P)) => `(bigSepL (fun $k $x => iprop($P)) $l)
  | `(iprop([∧list] $x:ident ∈ $l, $P)) => `(bigAndL (fun _ $x => iprop($P)) $l)
  | `(iprop([∧list] $k:ident ↦ $x:ident ∈ $l, $P)) => `(bigAndL (fun $k $x => iprop($P)) $l)
  | `(iprop([∨list] $x:ident ∈ $l, $P)) => `(bigOrL (fun _ $x => iprop($P)) $l)
  | `(iprop([∨list] $k:ident ↦ $x:ident ∈ $l, $P)) => `(bigOrL (fun $k $x => iprop($P)) $l)

/-! ## Delaborators -/

/-- Delaborator for `bigSepL` with index -/
@[delab app.Iris.BI.bigSepL]
def delabBigSepL : Delab := do
  let e ← getExpr
  -- Check if it's an application of bigSepL
  unless e.isApp do failure
  unless e.getAppFn.isConstOf ``bigSepL do failure

  -- Get arguments
  let args := e.getAppArgs
  unless args.size == 5 do failure

  -- Delab the list argument (arg 4)
  let l ← withNaryArg 4 delab

  -- Get the function argument (arg 3)
  let fn := args[3]!

  match fn with
  | .lam xn _ body _ =>
    match body with
    | .lam yn _ fnBody _ =>
      -- Two-parameter lambda: fun k x => P
      let xUsed := fnBody.hasLooseBVar 1  -- Check if index variable is used
      let y := mkIdent yn
      let P ← withNaryArg 3 <| withBindingBody yn <| withBindingBody xn <| delab

      if xUsed then
        let x := mkIdent xn
        `([∗list]  $x ↦ $y ∈ $l, $P)
      else
        `([∗list]  $y ∈ $l, $P)
    | _ =>
      -- Single-parameter lambda: fun n => Φ (n + 1) where Φ : Nat → A → PROP
      -- This is eta-reduced form of (fun n x => Φ (n + 1) x)
      -- Show it with both index and element variable
      let k := mkIdent xn
      let x := mkIdent `x
      let P ← withNaryArg 3 <| withBindingBody xn <| delab
      `([∗list]  $k ↦ $x ∈ $l, $P $x)
  | _ => failure

/-- Delaborator for `bigAndL` with index -/
@[delab app.Iris.BI.bigAndL]
def delabBigAndL : Delab := do
  let e ← getExpr
  unless e.isApp do failure
  unless e.getAppFn.isConstOf ``bigAndL do failure
  let args := e.getAppArgs
  unless args.size == 5 do failure
  let l ← withNaryArg 4 delab
  let fn := args[3]!
  match fn with
  | .lam xn _ body _ =>
    match body with
    | .lam yn _ fnBody _ =>
      let xUsed := fnBody.hasLooseBVar 1
      let y := mkIdent yn
      let P ← withNaryArg 3 <| withBindingBody yn <| withBindingBody xn <| delab
      if xUsed then
        let x := mkIdent xn
        `([∧list]  $x ↦ $y ∈ $l, $P)
      else
        `([∧list]  $y ∈ $l, $P)
    | _ =>
      let k := mkIdent xn
      let x := mkIdent `x
      let P ← withNaryArg 3 <| withBindingBody xn <| delab
      `([∧list]  $k ↦ $x ∈ $l, $P $x)
  | _ => failure

/-- Delaborator for `bigOrL` with index -/
@[delab app.Iris.BI.bigOrL]
def delabBigOrL : Delab := do
  let e ← getExpr
  unless e.isApp do failure
  unless e.getAppFn.isConstOf ``bigOrL do failure
  let args := e.getAppArgs
  unless args.size == 5 do failure
  let l ← withNaryArg 4 delab
  let fn := args[3]!
  match fn with
  | .lam xn _ body _ =>
    match body with
    | .lam yn _ fnBody _ =>
      let xUsed := fnBody.hasLooseBVar 1
      let y := mkIdent yn
      let P ← withNaryArg 3 <| withBindingBody yn <| withBindingBody xn <| delab
      if xUsed then
        let x := mkIdent xn
        `([∨list]  $x ↦ $y ∈ $l, $P)
      else
        `([∨list]  $y ∈ $l, $P)
    | _ =>
      let k := mkIdent xn
      let x := mkIdent `x
      let P ← withNaryArg 3 <| withBindingBody xn <| delab
      `([∨list]  $k ↦ $x ∈ $l, $P $x)
  | _ => failure

end List

/-! # BI-Instantiated Big Operators over Maps
- `bigSepM`: Big separating conjunction `[∗map]`
- `bigAndM`: Big conjunction `[∧map]`
-/

section Map
/-! ## Core Definitions -/

/-- Big separating conjunction over a map.
    `bigSepM Φ m` computes `∗_{k ↦ v ∈ m} Φ k v` -/
abbrev bigSepM [BI PROP] {M : Type _ → Type _} {K : Type _} {V : Type _} [FiniteMap K M]
    (Φ : K → V → PROP) (m : M V) : PROP :=
  bigOpL sep emp (fun _ kv => Φ kv.1 kv.2) (toList m)

/-- Big conjunction over a map.
    `bigAndM Φ m` computes `∧_{k ↦ v ∈ m} Φ k v` -/
abbrev bigAndM [BI PROP] {M : Type _ → Type _} {K : Type _} {V : Type _} [FiniteMap K M]
    (Φ : K → V → PROP) (m : M V) : PROP :=
  bigOpL and iprop(True) (fun _ kv => Φ kv.1 kv.2) (toList m)

/-! ## Notation -/

-- Notation for bigSepM without key binding
syntax "[∗map] " ident " ∈ " term ", " term : term
-- Notation for bigSepM with key binding
syntax "[∗map] " ident " ↦ " ident " ∈ " term ", " term : term

-- Notation for bigAndM without key binding
syntax "[∧map] " ident " ∈ " term ", " term : term
-- Notation for bigAndM with key binding
syntax "[∧map] " ident " ↦ " ident " ∈ " term ", " term : term

macro_rules
  | `([∗map] $x:ident ∈ $m, $P) => `(bigSepM (fun _ $x => $P) $m)
  | `([∗map] $k:ident ↦ $x:ident ∈ $m, $P) => `(bigSepM (fun $k $x => $P) $m)
  | `([∧map] $x:ident ∈ $m, $P) => `(bigAndM (fun _ $x => $P) $m)
  | `([∧map] $k:ident ↦ $x:ident ∈ $m, $P) => `(bigAndM (fun $k $x => $P) $m)

-- iprop macro rules
macro_rules
  | `(iprop([∗map] $x:ident ∈ $m, $P)) => `(bigSepM (fun _ $x => iprop($P)) $m)
  | `(iprop([∗map] $k:ident ↦ $x:ident ∈ $m, $P)) => `(bigSepM (fun $k $x => iprop($P)) $m)
  | `(iprop([∧map] $x:ident ∈ $m, $P)) => `(bigAndM (fun _ $x => iprop($P)) $m)
  | `(iprop([∧map] $k:ident ↦ $x:ident ∈ $m, $P)) => `(bigAndM (fun $k $x => iprop($P)) $m)

/-! ## Delaborators -/

/-- Delaborator for `bigSepM` with key -/
@[delab app.Iris.BI.bigSepM]
def delabBigSepM : Delab := do
  let e ← getExpr
  unless e.isApp do failure
  unless e.getAppFn.isConstOf ``bigSepM do failure
  let args := e.getAppArgs
  unless args.size == 8 do failure
  let m ← withNaryArg 7 delab
  let fn := args[6]!
  match fn with
  | .lam kn _ body _ =>
    match body with
    | .lam vn _ fnBody _ =>
      let kUsed := fnBody.hasLooseBVar 1
      let v := mkIdent vn
      let P ← withNaryArg 6 <| withBindingBody vn <| withBindingBody kn <| delab
      if kUsed then
        let k := mkIdent kn
        `([∗map]  $k ↦ $v ∈ $m, $P)
      else
        `([∗map]  $v ∈ $m, $P)
    | _ =>
      let k := mkIdent kn
      let v := mkIdent `v
      let P ← withNaryArg 6 <| withBindingBody kn <| delab
      `([∗map]  $k ↦ $v ∈ $m, $P $v)
  | _ => failure

/-- Delaborator for `bigAndM` with key -/
@[delab app.Iris.BI.bigAndM]
def delabBigAndM : Delab := do
  let e ← getExpr
  unless e.isApp do failure
  unless e.getAppFn.isConstOf ``bigAndM do failure
  let args := e.getAppArgs
  unless args.size == 8 do failure
  let m ← withNaryArg 7 delab
  let fn := args[6]!
  match fn with
  | .lam kn _ body _ =>
    match body with
    | .lam vn _ fnBody _ =>
      let kUsed := fnBody.hasLooseBVar 1
      let v := mkIdent vn
      let P ← withNaryArg 6 <| withBindingBody vn <| withBindingBody kn <| delab
      if kUsed then
        let k := mkIdent kn
        `([∧map]  $k ↦ $v ∈ $m, $P)
      else
        `([∧map]  $v ∈ $m, $P)
    | _ =>
      let k := mkIdent kn
      let v := mkIdent `v
      let P ← withNaryArg 6 <| withBindingBody kn <| delab
      `([∧map]  $k ↦ $v ∈ $m, $P $v)
  | _ => failure

end Map

/-! # BI-Instantiated Big Operators over Sets
- `bigSepS`: Big separating conjunction `[∗set]`
-/

section Set

/-! ## Core Definitions -/

/-- Big separating conjunction over a set.
    `bigSepS Φ S` computes `∗_{x ∈ S} Φ x`

    Corresponds to `big_opS` in Rocq Iris. -/
abbrev bigSepS [BI PROP] {S : Type _} {A : Type _} [FiniteSet A S]
    (Φ : A → PROP) (s : S) : PROP :=
  bigOpL sep emp (fun _ x => Φ x) (FiniteSet.toList s)

/-! ## Notation -/

-- Notation for bigSepS
syntax "[∗set] " ident " ∈ " term ", " term : term

macro_rules
  | `([∗set] $x:ident ∈ $s, $P) => `(bigSepS (fun $x => $P) $s)

-- iprop macro rules
macro_rules
  | `(iprop([∗set] $x:ident ∈ $s, $P)) => `(bigSepS (fun $x => iprop($P)) $s)

/-! ## Delaborators -/

/-- Delaborator for `bigSepS` -/
@[delab app.Iris.BI.bigSepS]
def delabBigSepS : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``bigSepS 7
  let s ← withNaryArg 6 delab
  let fn := e.getArg! 5
  match fn with
  | .lam xn _ _ _ =>
    let x := mkIdent xn
    let P ← withNaryArg 5 <| withBindingBody xn <| delab
    `([∗set]  $x ∈ $s, $P)
  | _ => failure

end Set

end Iris.BI
