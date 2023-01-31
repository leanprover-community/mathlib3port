/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.int.cast.prod
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
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

/- warning: prod.fst_int_cast -> Prod.fst_intCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddGroupWithOne.{u1} α] [_inst_2 : AddGroupWithOne.{u2} β] (n : Int), Eq.{succ u1} α (Prod.fst.{u1, u2} α β ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Int (Prod.{u1, u2} α β) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Int (Prod.{u1, u2} α β) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Int (Prod.{u1, u2} α β) (Int.castCoe.{max u1 u2} (Prod.{u1, u2} α β) (AddGroupWithOne.toHasIntCast.{max u1 u2} (Prod.{u1, u2} α β) (Prod.addGroupWithOne.{u1, u2} α β _inst_1 _inst_2))))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α _inst_1)))) n)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddGroupWithOne.{u2} α] [_inst_2 : AddGroupWithOne.{u1} β] (n : Int), Eq.{succ u2} α (Prod.fst.{u2, u1} α β (Int.cast.{max u2 u1} (Prod.{u2, u1} α β) (AddGroupWithOne.toIntCast.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instAddGroupWithOneProd.{u2, u1} α β _inst_1 _inst_2)) n)) (Int.cast.{u2} α (AddGroupWithOne.toIntCast.{u2} α _inst_1) n)
Case conversion may be inaccurate. Consider using '#align prod.fst_int_cast Prod.fst_intCastₓ'. -/
@[simp]
theorem fst_intCast (n : ℤ) : (n : α × β).fst = n :=
  rfl
#align prod.fst_int_cast Prod.fst_intCast

/- warning: prod.snd_int_cast -> Prod.snd_intCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddGroupWithOne.{u1} α] [_inst_2 : AddGroupWithOne.{u2} β] (n : Int), Eq.{succ u2} β (Prod.snd.{u1, u2} α β ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Int (Prod.{u1, u2} α β) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Int (Prod.{u1, u2} α β) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Int (Prod.{u1, u2} α β) (Int.castCoe.{max u1 u2} (Prod.{u1, u2} α β) (AddGroupWithOne.toHasIntCast.{max u1 u2} (Prod.{u1, u2} α β) (Prod.addGroupWithOne.{u1, u2} α β _inst_1 _inst_2))))) n)) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int β (HasLiftT.mk.{1, succ u2} Int β (CoeTCₓ.coe.{1, succ u2} Int β (Int.castCoe.{u2} β (AddGroupWithOne.toHasIntCast.{u2} β _inst_2)))) n)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddGroupWithOne.{u1} α] [_inst_2 : AddGroupWithOne.{u2} β] (n : Int), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (Int.cast.{max u1 u2} (Prod.{u1, u2} α β) (AddGroupWithOne.toIntCast.{max u1 u2} (Prod.{u1, u2} α β) (Prod.instAddGroupWithOneProd.{u1, u2} α β _inst_1 _inst_2)) n)) (Int.cast.{u2} β (AddGroupWithOne.toIntCast.{u2} β _inst_2) n)
Case conversion may be inaccurate. Consider using '#align prod.snd_int_cast Prod.snd_intCastₓ'. -/
@[simp]
theorem snd_intCast (n : ℤ) : (n : α × β).snd = n :=
  rfl
#align prod.snd_int_cast Prod.snd_intCast

end Prod

