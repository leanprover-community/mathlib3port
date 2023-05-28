/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.int.cast.prod
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Cast.Lemmas
import Mathbin.Data.Nat.Cast.Prod

/-!
# The product of two `add_group_with_one`s.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Prod

variable {α β : Type _} [AddGroupWithOne α] [AddGroupWithOne β]

instance : AddGroupWithOne (α × β) :=
  { Prod.addMonoidWithOne,
    Prod.addGroup with
    intCast := fun n => (n, n)
    intCast_ofNat := fun _ => by simp <;> rfl
    intCast_negSucc := fun _ => by simp <;> rfl }

@[simp]
theorem fst_intCast (n : ℤ) : (n : α × β).fst = n :=
  rfl
#align prod.fst_int_cast Prod.fst_intCast

@[simp]
theorem snd_intCast (n : ℤ) : (n : α × β).snd = n :=
  rfl
#align prod.snd_int_cast Prod.snd_intCast

end Prod

