/-
Copyright (c) 2020 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Control.Functor.Multivariate
import Data.Qpf.Multivariate.Basic

#align_import data.qpf.multivariate.constructions.const from "leanprover-community/mathlib"@"23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6"

/-!
# Constant functors are QPFs

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Constant functors map every type vectors to the same target type. This
is a useful device for constructing data types from more basic types
that are not actually functorial. For instance `const n nat` makes
`nat` into a functor that can be used in a functor-based data type
specification.
-/


universe u

namespace MvQPF

open scoped MvFunctor

variable (n : ℕ)

#print MvQPF.Const /-
/-- Constant multivariate functor -/
@[nolint unused_arguments]
def Const (A : Type _) (v : TypeVec.{u} n) : Type _ :=
  A
#align mvqpf.const MvQPF.Const
-/

#print MvQPF.Const.inhabited /-
instance Const.inhabited {A α} [Inhabited A] : Inhabited (Const n A α) :=
  ⟨(default : A)⟩
#align mvqpf.const.inhabited MvQPF.Const.inhabited
-/

namespace Const

open MvFunctor MvPFunctor

variable {n} {A : Type u} {α β : TypeVec.{u} n} (f : α ⟹ β)

#print MvQPF.Const.mk /-
/-- Constructor for constant functor -/
protected def mk (x : A) : (Const n A) α :=
  x
#align mvqpf.const.mk MvQPF.Const.mk
-/

#print MvQPF.Const.get /-
/-- Destructor for constant functor -/
protected def get (x : (Const n A) α) : A :=
  x
#align mvqpf.const.get MvQPF.Const.get
-/

#print MvQPF.Const.mk_get /-
@[simp]
protected theorem mk_get (x : (Const n A) α) : Const.mk (Const.get x) = x :=
  rfl
#align mvqpf.const.mk_get MvQPF.Const.mk_get
-/

#print MvQPF.Const.get_mk /-
@[simp]
protected theorem get_mk (x : A) : Const.get (Const.mk x : Const n A α) = x :=
  rfl
#align mvqpf.const.get_mk MvQPF.Const.get_mk
-/

#print MvQPF.Const.map /-
/-- `map` for constant functor -/
protected def map : (Const n A) α → (Const n A) β := fun x => x
#align mvqpf.const.map MvQPF.Const.map
-/

instance : MvFunctor (Const n A) where map α β f := Const.map

#print MvQPF.Const.map_mk /-
theorem map_mk (x : A) : f <$$> Const.mk x = Const.mk x :=
  rfl
#align mvqpf.const.map_mk MvQPF.Const.map_mk
-/

#print MvQPF.Const.get_map /-
theorem get_map (x : (Const n A) α) : Const.get (f <$$> x) = Const.get x :=
  rfl
#align mvqpf.const.get_map MvQPF.Const.get_map
-/

#print MvQPF.Const.mvqpf /-
instance mvqpf : @MvQPF _ (Const n A) MvQPF.Const.mvfunctor
    where
  p := MvPFunctor.const n A
  abs α x := MvPFunctor.const.get x
  repr α x := MvPFunctor.const.mk n x
  abs_repr := by intros <;> simp
  abs_map := by intros <;> simp <;> rfl
#align mvqpf.const.mvqpf MvQPF.Const.mvqpf
-/

end Const

end MvQPF

