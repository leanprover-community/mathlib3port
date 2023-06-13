/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.nat.cast.prod
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Cast.Basic
import Mathbin.Algebra.Group.Prod

/-!
# The product of two `add_monoid_with_one`s.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α β : Type _}

namespace Prod

variable [AddMonoidWithOne α] [AddMonoidWithOne β]

instance : AddMonoidWithOne (α × β) :=
  { Prod.addMonoid, Prod.hasOne with
    natCast := fun n => (n, n)
    natCast_zero := congr_arg₂ Prod.mk Nat.cast_zero Nat.cast_zero
    natCast_succ := fun n => congr_arg₂ Prod.mk (Nat.cast_succ _) (Nat.cast_succ _) }

#print Prod.fst_natCast /-
@[simp]
theorem fst_natCast (n : ℕ) : (n : α × β).fst = n := by induction n <;> simp [*]
#align prod.fst_nat_cast Prod.fst_natCast
-/

#print Prod.snd_natCast /-
@[simp]
theorem snd_natCast (n : ℕ) : (n : α × β).snd = n := by induction n <;> simp [*]
#align prod.snd_nat_cast Prod.snd_natCast
-/

end Prod

