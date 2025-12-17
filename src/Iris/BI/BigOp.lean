/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.Algebra.BigOp
import Iris.BI.DerivedLaws

namespace Iris.BI

open Iris.Algebra
open OFE
open BIBase

/-! # BI-Instantiated Big Operators over Lists

This file provides BI-instantiated big operators over lists with index access:
- `bigSepL`: Big separating conjunction `[∗ list]`
- `bigAndL`: Big conjunction `[∧ list]`
- `bigOrL`: Big disjunction `[∨ list]`

These wrap the abstract `bigOpL` from `Iris.Algebra.BigOp` with specific BI operations.
-/

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
syntax "[∗ " "list" "] " ident " ∈ " term ", " term : term
-- Notation for bigSepL with index
syntax "[∗ " "list" "] " ident " ↦ " ident " ∈ " term ", " term : term

-- Notation for bigAndL without index
syntax "[∧ " "list" "] " ident " ∈ " term ", " term : term
-- Notation for bigAndL with index
syntax "[∧ " "list" "] " ident " ↦ " ident " ∈ " term ", " term : term

-- Notation for bigOrL without index
syntax "[∨ " "list" "] " ident " ∈ " term ", " term : term
-- Notation for bigOrL with index
syntax "[∨ " "list" "] " ident " ↦ " ident " ∈ " term ", " term : term

macro_rules
  | `([∗ list] $x:ident ∈ $l, $P) => `(bigSepL (fun _ $x => $P) $l)
  | `([∗ list] $k:ident ↦ $x:ident ∈ $l, $P) => `(bigSepL (fun $k $x => $P) $l)
  | `([∧ list] $x:ident ∈ $l, $P) => `(bigAndL (fun _ $x => $P) $l)
  | `([∧ list] $k:ident ↦ $x:ident ∈ $l, $P) => `(bigAndL (fun $k $x => $P) $l)
  | `([∨ list] $x:ident ∈ $l, $P) => `(bigOrL (fun _ $x => $P) $l)
  | `([∨ list] $k:ident ↦ $x:ident ∈ $l, $P) => `(bigOrL (fun $k $x => $P) $l)

-- iprop macro rules
macro_rules
  | `(iprop([∗ list] $x:ident ∈ $l, $P)) => `(bigSepL (fun _ $x => iprop($P)) $l)
  | `(iprop([∗ list] $k:ident ↦ $x:ident ∈ $l, $P)) => `(bigSepL (fun $k $x => iprop($P)) $l)
  | `(iprop([∧ list] $x:ident ∈ $l, $P)) => `(bigAndL (fun _ $x => iprop($P)) $l)
  | `(iprop([∧ list] $k:ident ↦ $x:ident ∈ $l, $P)) => `(bigAndL (fun $k $x => iprop($P)) $l)
  | `(iprop([∨ list] $x:ident ∈ $l, $P)) => `(bigOrL (fun _ $x => iprop($P)) $l)
  | `(iprop([∨ list] $k:ident ↦ $x:ident ∈ $l, $P)) => `(bigOrL (fun $k $x => iprop($P)) $l)

end Iris.BI
