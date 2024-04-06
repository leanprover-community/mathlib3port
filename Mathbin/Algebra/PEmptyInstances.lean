/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Algebra.Group.Defs
import Tactic.ToAdditive

#align_import algebra.pempty_instances from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

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
#align add_semigroup_pempty AddSemigroupPEmpty
-/

