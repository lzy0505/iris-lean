/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Zongyuan Liu
-/
import Iris.Algebra.BigOp

namespace Iris.Std

open Iris.Algebra

/-! # Big Operators for BI

This file provides big operator definitions for use with separation logic.
The core implementation is in `Iris.Algebra.BigOp`; this file provides
convenience wrappers that take the operator and unit as explicit arguments.
-/

/-- Fold a binary operator `f` over a list. If the list is empty, `unit` is returned.
This is a wrapper around `Algebra.bigOp` that takes the operator explicitly. -/
def bigOp (f : PROP → PROP → PROP) (unit : PROP) (l : List PROP) : PROP :=
  match l with
  | []      => unit
  | [P]     => P
  | P :: Ps => f P (bigOp f unit Ps)

/-- Typeclass asserting that `f` with `unit` forms a lawful commutative monoid
with respect to equivalence relation `eq`. This is used for big operator lemmas.

This is essentially `Algebra.CommMonoid` but parameterized by explicit `f` and `unit`
rather than bundling them in an instance. -/
class LawfulBigOp (f : PROP → PROP → PROP) (unit : outParam PROP)
    (eq : outParam (PROP → PROP → Prop)) where
  refl {a : PROP} : eq a a
  symm {a b : PROP} : eq a b → eq b a
  trans {a b c : PROP} : eq a b → eq b c → eq a c
  comm {a b : PROP} : eq (f a b) (f b a)
  assoc {a b c : PROP} : eq (f (f a b) c) (f a (f b c))
  left_id {a : PROP} : eq (f unit a) a
  congr_l {a a' b : PROP} : eq a a' → eq (f a b) (f a' b)

theorem LawfulBigOp.right_id [LawfulBigOp (PROP := PROP) f unit eq] : eq (f a unit) a :=
  trans f comm left_id

theorem LawfulBigOp.congr_r [LawfulBigOp (PROP := PROP) f unit eq]
    (h : eq b b') : eq (f a b) (f a b') :=
  trans f comm <| trans f (congr_l h) comm

open LawfulBigOp

theorem bigOp_nil {f : PROP → PROP → PROP} {unit : PROP} : bigOp f unit [] = unit := rfl

theorem bigOp_cons {f : PROP → PROP → PROP} {unit : PROP} [LawfulBigOp f unit eq] :
    eq (bigOp f unit (P :: Ps)) (f P (bigOp f unit Ps)) :=
  match Ps with
  | [] => symm f right_id
  | _ :: _ => refl f

end Iris.Std
