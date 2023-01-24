/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin

! This file was ported from Lean 3 source module algebra.group.with_one.units
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.WithOne.Basic
import Mathbin.Algebra.GroupWithZero.Units.Basic

/-!
# Isomorphism between a group and the units of itself adjoined with `0`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Notes
This is here to keep `algebra.group_with_zero.units.basic` out of the import requirements of
`algebra.order.field.defs`.
-/


namespace WithZero

/- warning: with_zero.units_with_zero_equiv -> WithZero.unitsWithZeroEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α], MulEquiv.{u1, u1} (Units.{u1} (WithZero.{u1} α) (MonoidWithZero.toMonoid.{u1} (WithZero.{u1} α) (WithZero.monoidWithZero.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) α (MulOneClass.toHasMul.{u1} (Units.{u1} (WithZero.{u1} α) (MonoidWithZero.toMonoid.{u1} (WithZero.{u1} α) (WithZero.monoidWithZero.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Units.mulOneClass.{u1} (WithZero.{u1} α) (MonoidWithZero.toMonoid.{u1} (WithZero.{u1} α) (WithZero.monoidWithZero.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α], MulEquiv.{u1, u1} (Units.{u1} (WithZero.{u1} α) (MonoidWithZero.toMonoid.{u1} (WithZero.{u1} α) (WithZero.monoidWithZero.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) α (MulOneClass.toMul.{u1} (Units.{u1} (WithZero.{u1} α) (MonoidWithZero.toMonoid.{u1} (WithZero.{u1} α) (WithZero.monoidWithZero.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Units.instMulOneClassUnits.{u1} (WithZero.{u1} α) (MonoidWithZero.toMonoid.{u1} (WithZero.{u1} α) (WithZero.monoidWithZero.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align with_zero.units_with_zero_equiv WithZero.unitsWithZeroEquivₓ'. -/
/-- Any group is isomorphic to the units of itself adjoined with `0`. -/
def unitsWithZeroEquiv {α : Type _} [Group α] : (WithZero α)ˣ ≃* α
    where
  toFun a := unzero a.NeZero
  invFun a := Units.mk0 a coe_ne_zero
  left_inv _ := Units.ext <| by simpa only [coe_unzero]
  right_inv _ := rfl
  map_mul' _ _ := coe_inj.mp <| by simpa only [coe_unzero, coe_mul]
#align with_zero.units_with_zero_equiv WithZero.unitsWithZeroEquiv

end WithZero

