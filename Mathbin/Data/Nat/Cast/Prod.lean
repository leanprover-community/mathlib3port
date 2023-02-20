/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.nat.cast.prod
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
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

/- warning: prod.fst_nat_cast -> Prod.fst_natCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : AddMonoidWithOne.{u2} β] (n : Nat), Eq.{succ u1} α (Prod.fst.{u1, u2} α β ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Nat (Prod.{u1, u2} α β) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Nat (Prod.{u1, u2} α β) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Nat (Prod.{u1, u2} α β) (Nat.castCoe.{max u1 u2} (Prod.{u1, u2} α β) (AddMonoidWithOne.toNatCast.{max u1 u2} (Prod.{u1, u2} α β) (Prod.addMonoidWithOne.{u1, u2} α β _inst_1 _inst_2))))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α _inst_1)))) n)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u2} α] [_inst_2 : AddMonoidWithOne.{u1} β] (n : Nat), Eq.{succ u2} α (Prod.fst.{u2, u1} α β (Nat.cast.{max u2 u1} (Prod.{u2, u1} α β) (AddMonoidWithOne.toNatCast.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instAddMonoidWithOneProd.{u2, u1} α β _inst_1 _inst_2)) n)) (Nat.cast.{u2} α (AddMonoidWithOne.toNatCast.{u2} α _inst_1) n)
Case conversion may be inaccurate. Consider using '#align prod.fst_nat_cast Prod.fst_natCastₓ'. -/
@[simp]
theorem fst_natCast (n : ℕ) : (n : α × β).fst = n := by induction n <;> simp [*]
#align prod.fst_nat_cast Prod.fst_natCast

/- warning: prod.snd_nat_cast -> Prod.snd_natCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : AddMonoidWithOne.{u2} β] (n : Nat), Eq.{succ u2} β (Prod.snd.{u1, u2} α β ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Nat (Prod.{u1, u2} α β) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Nat (Prod.{u1, u2} α β) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Nat (Prod.{u1, u2} α β) (Nat.castCoe.{max u1 u2} (Prod.{u1, u2} α β) (AddMonoidWithOne.toNatCast.{max u1 u2} (Prod.{u1, u2} α β) (Prod.addMonoidWithOne.{u1, u2} α β _inst_1 _inst_2))))) n)) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat β (HasLiftT.mk.{1, succ u2} Nat β (CoeTCₓ.coe.{1, succ u2} Nat β (Nat.castCoe.{u2} β (AddMonoidWithOne.toNatCast.{u2} β _inst_2)))) n)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddMonoidWithOne.{u1} α] [_inst_2 : AddMonoidWithOne.{u2} β] (n : Nat), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (Nat.cast.{max u1 u2} (Prod.{u1, u2} α β) (AddMonoidWithOne.toNatCast.{max u1 u2} (Prod.{u1, u2} α β) (Prod.instAddMonoidWithOneProd.{u1, u2} α β _inst_1 _inst_2)) n)) (Nat.cast.{u2} β (AddMonoidWithOne.toNatCast.{u2} β _inst_2) n)
Case conversion may be inaccurate. Consider using '#align prod.snd_nat_cast Prod.snd_natCastₓ'. -/
@[simp]
theorem snd_natCast (n : ℕ) : (n : α × β).snd = n := by induction n <;> simp [*]
#align prod.snd_nat_cast Prod.snd_natCast

end Prod

