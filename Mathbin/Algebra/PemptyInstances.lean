/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer

! This file was ported from Lean 3 source module algebra.pempty_instances
! leanprover-community/mathlib commit 940d371319c6658e526349d2c3e1daeeabfae0fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Tactic.ToAdditive

/-!
# Instances on pempty

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file collects facts about algebraic structures on the (universe-polymorphic) empty type, e.g.
that it is a semigroup.
-/


universe u

#print SemigroupPEmpty /-
@[to_additive]
instance SemigroupPEmpty : Semigroup PEmpty.{u + 1}
    where
  mul x y := by cases x
  mul_assoc x y z := by cases x
#align semigroup_pempty SemigroupPEmpty
-/

