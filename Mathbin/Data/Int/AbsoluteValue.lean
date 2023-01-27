/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module data.int.absolute_value
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Order.AbsoluteValue
import Mathbin.Data.Int.Cast.Lemmas
import Mathbin.Data.Int.Units
import Mathbin.GroupTheory.GroupAction.Units

/-!
# Absolute values and the integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some results on absolute values applied to integers.

## Main results

 * `absolute_value.map_units_int`: an absolute value sends all units of `ℤ` to `1`
 * `int.nat_abs_hom`: `int.nat_abs` bundled as a `monoid_with_zero_hom`
-/


variable {R S : Type _} [Ring R] [LinearOrderedCommRing S]

/- warning: absolute_value.map_units_int -> AbsoluteValue.map_units_int is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u1}} [_inst_2 : LinearOrderedCommRing.{u1} S] (abv : AbsoluteValue.{0, u1} Int S Int.semiring (StrictOrderedSemiring.toOrderedSemiring.{u1} S (StrictOrderedRing.toStrictOrderedSemiring.{u1} S (LinearOrderedRing.toStrictOrderedRing.{u1} S (LinearOrderedCommRing.toLinearOrderedRing.{u1} S _inst_2))))) (x : Units.{0} Int Int.monoid), Eq.{succ u1} S (coeFn.{succ u1, succ u1} (AbsoluteValue.{0, u1} Int S Int.semiring (StrictOrderedSemiring.toOrderedSemiring.{u1} S (StrictOrderedRing.toStrictOrderedSemiring.{u1} S (LinearOrderedRing.toStrictOrderedRing.{u1} S (LinearOrderedCommRing.toLinearOrderedRing.{u1} S _inst_2))))) (fun (f : AbsoluteValue.{0, u1} Int S Int.semiring (StrictOrderedSemiring.toOrderedSemiring.{u1} S (StrictOrderedRing.toStrictOrderedSemiring.{u1} S (LinearOrderedRing.toStrictOrderedRing.{u1} S (LinearOrderedCommRing.toLinearOrderedRing.{u1} S _inst_2))))) => Int -> S) (AbsoluteValue.hasCoeToFun.{0, u1} Int S Int.semiring (StrictOrderedSemiring.toOrderedSemiring.{u1} S (StrictOrderedRing.toStrictOrderedSemiring.{u1} S (LinearOrderedRing.toStrictOrderedRing.{u1} S (LinearOrderedCommRing.toLinearOrderedRing.{u1} S _inst_2))))) abv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Units.{0} Int Int.monoid) Int (HasLiftT.mk.{1, 1} (Units.{0} Int Int.monoid) Int (CoeTCₓ.coe.{1, 1} (Units.{0} Int Int.monoid) Int (coeBase.{1, 1} (Units.{0} Int Int.monoid) Int (Units.hasCoe.{0} Int Int.monoid)))) x)) (OfNat.ofNat.{u1} S 1 (OfNat.mk.{u1} S 1 (One.one.{u1} S (AddMonoidWithOne.toOne.{u1} S (AddGroupWithOne.toAddMonoidWithOne.{u1} S (NonAssocRing.toAddGroupWithOne.{u1} S (Ring.toNonAssocRing.{u1} S (StrictOrderedRing.toRing.{u1} S (LinearOrderedRing.toStrictOrderedRing.{u1} S (LinearOrderedCommRing.toLinearOrderedRing.{u1} S _inst_2))))))))))
but is expected to have type
  forall {S : Type.{u1}} [_inst_2 : LinearOrderedCommRing.{u1} S] (abv : AbsoluteValue.{0, u1} Int S Int.instSemiringInt (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))) (x : Units.{0} Int Int.instMonoidInt), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : Int) => S) (Units.val.{0} Int Int.instMonoidInt x)) (FunLike.coe.{succ u1, 1, succ u1} (AbsoluteValue.{0, u1} Int S Int.instSemiringInt (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))) Int (fun (f : Int) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : Int) => S) f) (SubadditiveHomClass.toFunLike.{u1, 0, u1} (AbsoluteValue.{0, u1} Int S Int.instSemiringInt (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))) Int S (Distrib.toAdd.{0} Int (NonUnitalNonAssocSemiring.toDistrib.{0} Int (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Int (Semiring.toNonAssocSemiring.{0} Int Int.instSemiringInt)))) (Distrib.toAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (OrderedSemiring.toSemiring.{u1} S (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))))))) (Preorder.toLE.{u1} S (PartialOrder.toPreorder.{u1} S (OrderedSemiring.toPartialOrder.{u1} S (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))))) (AbsoluteValue.subadditiveHomClass.{0, u1} Int S Int.instSemiringInt (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2)))))) abv (Units.val.{0} Int Int.instMonoidInt x)) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : Int) => S) (Units.val.{0} Int Int.instMonoidInt x)) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : Int) => S) (Units.val.{0} Int Int.instMonoidInt x)) (NonAssocRing.toOne.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : Int) => S) (Units.val.{0} Int Int.instMonoidInt x)) (Ring.toNonAssocRing.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : Int) => S) (Units.val.{0} Int Int.instMonoidInt x)) (StrictOrderedRing.toRing.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : Int) => S) (Units.val.{0} Int Int.instMonoidInt x)) (LinearOrderedRing.toStrictOrderedRing.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : Int) => S) (Units.val.{0} Int Int.instMonoidInt x)) (LinearOrderedCommRing.toLinearOrderedRing.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : Int) => S) (Units.val.{0} Int Int.instMonoidInt x)) _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align absolute_value.map_units_int AbsoluteValue.map_units_intₓ'. -/
@[simp]
theorem AbsoluteValue.map_units_int (abv : AbsoluteValue ℤ S) (x : ℤˣ) : abv x = 1 := by
  rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp
#align absolute_value.map_units_int AbsoluteValue.map_units_int

/- warning: absolute_value.map_units_int_cast -> AbsoluteValue.map_units_int_cast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : LinearOrderedCommRing.{u2} S] [_inst_3 : Nontrivial.{u1} R] (abv : AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u2} S (StrictOrderedRing.toStrictOrderedSemiring.{u2} S (LinearOrderedRing.toStrictOrderedRing.{u2} S (LinearOrderedCommRing.toLinearOrderedRing.{u2} S _inst_2))))) (x : Units.{0} Int Int.monoid), Eq.{succ u2} S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u2} S (StrictOrderedRing.toStrictOrderedSemiring.{u2} S (LinearOrderedRing.toStrictOrderedRing.{u2} S (LinearOrderedCommRing.toLinearOrderedRing.{u2} S _inst_2))))) (fun (f : AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u2} S (StrictOrderedRing.toStrictOrderedSemiring.{u2} S (LinearOrderedRing.toStrictOrderedRing.{u2} S (LinearOrderedCommRing.toLinearOrderedRing.{u2} S _inst_2))))) => R -> S) (AbsoluteValue.hasCoeToFun.{u1, u2} R S (Ring.toSemiring.{u1} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u2} S (StrictOrderedRing.toStrictOrderedSemiring.{u2} S (LinearOrderedRing.toStrictOrderedRing.{u2} S (LinearOrderedCommRing.toLinearOrderedRing.{u2} S _inst_2))))) abv ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Units.{0} Int Int.monoid) Int (HasLiftT.mk.{1, 1} (Units.{0} Int Int.monoid) Int (CoeTCₓ.coe.{1, 1} (Units.{0} Int Int.monoid) Int (coeBase.{1, 1} (Units.{0} Int Int.monoid) Int (Units.hasCoe.{0} Int Int.monoid)))) x))) (OfNat.ofNat.{u2} S 1 (OfNat.mk.{u2} S 1 (One.one.{u2} S (AddMonoidWithOne.toOne.{u2} S (AddGroupWithOne.toAddMonoidWithOne.{u2} S (NonAssocRing.toAddGroupWithOne.{u2} S (Ring.toNonAssocRing.{u2} S (StrictOrderedRing.toRing.{u2} S (LinearOrderedRing.toStrictOrderedRing.{u2} S (LinearOrderedCommRing.toLinearOrderedRing.{u2} S _inst_2))))))))))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : LinearOrderedCommRing.{u1} S] [_inst_3 : Nontrivial.{u2} R] (abv : AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))) (x : Units.{0} Int Int.instMonoidInt), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) (Int.cast.{u2} R (Ring.toIntCast.{u2} R _inst_1) (Units.val.{0} Int Int.instMonoidInt x))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))) R (fun (f : R) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) f) (SubadditiveHomClass.toFunLike.{max u2 u1, u2, u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))) R S (Distrib.toAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))))) (Distrib.toAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (OrderedSemiring.toSemiring.{u1} S (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))))))) (Preorder.toLE.{u1} S (PartialOrder.toPreorder.{u1} S (OrderedSemiring.toPartialOrder.{u1} S (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))))) (AbsoluteValue.subadditiveHomClass.{u2, u1} R S (Ring.toSemiring.{u2} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2)))))) abv (Int.cast.{u2} R (Ring.toIntCast.{u2} R _inst_1) (Units.val.{0} Int Int.instMonoidInt x))) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) (Int.cast.{u2} R (Ring.toIntCast.{u2} R _inst_1) (Units.val.{0} Int Int.instMonoidInt x))) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) (Int.cast.{u2} R (Ring.toIntCast.{u2} R _inst_1) (Units.val.{0} Int Int.instMonoidInt x))) (NonAssocRing.toOne.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) (Int.cast.{u2} R (Ring.toIntCast.{u2} R _inst_1) (Units.val.{0} Int Int.instMonoidInt x))) (Ring.toNonAssocRing.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) (Int.cast.{u2} R (Ring.toIntCast.{u2} R _inst_1) (Units.val.{0} Int Int.instMonoidInt x))) (StrictOrderedRing.toRing.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) (Int.cast.{u2} R (Ring.toIntCast.{u2} R _inst_1) (Units.val.{0} Int Int.instMonoidInt x))) (LinearOrderedRing.toStrictOrderedRing.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) (Int.cast.{u2} R (Ring.toIntCast.{u2} R _inst_1) (Units.val.{0} Int Int.instMonoidInt x))) (LinearOrderedCommRing.toLinearOrderedRing.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) (Int.cast.{u2} R (Ring.toIntCast.{u2} R _inst_1) (Units.val.{0} Int Int.instMonoidInt x))) _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align absolute_value.map_units_int_cast AbsoluteValue.map_units_int_castₓ'. -/
@[simp]
theorem AbsoluteValue.map_units_int_cast [Nontrivial R] (abv : AbsoluteValue R S) (x : ℤˣ) :
    abv ((x : ℤ) : R) = 1 := by rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp
#align absolute_value.map_units_int_cast AbsoluteValue.map_units_int_cast

/- warning: absolute_value.map_units_int_smul -> AbsoluteValue.map_units_int_smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : LinearOrderedCommRing.{u2} S] (abv : AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u2} S (StrictOrderedRing.toStrictOrderedSemiring.{u2} S (LinearOrderedRing.toStrictOrderedRing.{u2} S (LinearOrderedCommRing.toLinearOrderedRing.{u2} S _inst_2))))) (x : Units.{0} Int Int.monoid) (y : R), Eq.{succ u2} S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u2} S (StrictOrderedRing.toStrictOrderedSemiring.{u2} S (LinearOrderedRing.toStrictOrderedRing.{u2} S (LinearOrderedCommRing.toLinearOrderedRing.{u2} S _inst_2))))) (fun (f : AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u2} S (StrictOrderedRing.toStrictOrderedSemiring.{u2} S (LinearOrderedRing.toStrictOrderedRing.{u2} S (LinearOrderedCommRing.toLinearOrderedRing.{u2} S _inst_2))))) => R -> S) (AbsoluteValue.hasCoeToFun.{u1, u2} R S (Ring.toSemiring.{u1} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u2} S (StrictOrderedRing.toStrictOrderedSemiring.{u2} S (LinearOrderedRing.toStrictOrderedRing.{u2} S (LinearOrderedCommRing.toLinearOrderedRing.{u2} S _inst_2))))) abv (SMul.smul.{0, u1} (Units.{0} Int Int.monoid) R (Units.hasSmul.{0, u1} Int R Int.monoid (SubNegMonoid.SMulInt.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) x y)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u2} S (StrictOrderedRing.toStrictOrderedSemiring.{u2} S (LinearOrderedRing.toStrictOrderedRing.{u2} S (LinearOrderedCommRing.toLinearOrderedRing.{u2} S _inst_2))))) (fun (f : AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u2} S (StrictOrderedRing.toStrictOrderedSemiring.{u2} S (LinearOrderedRing.toStrictOrderedRing.{u2} S (LinearOrderedCommRing.toLinearOrderedRing.{u2} S _inst_2))))) => R -> S) (AbsoluteValue.hasCoeToFun.{u1, u2} R S (Ring.toSemiring.{u1} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u2} S (StrictOrderedRing.toStrictOrderedSemiring.{u2} S (LinearOrderedRing.toStrictOrderedRing.{u2} S (LinearOrderedCommRing.toLinearOrderedRing.{u2} S _inst_2))))) abv y)
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : LinearOrderedCommRing.{u1} S] (abv : AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))) (x : Units.{0} Int Int.instMonoidInt) (y : R), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) (HSMul.hSMul.{0, u2, u2} (Units.{0} Int Int.instMonoidInt) R R (instHSMul.{0, u2} (Units.{0} Int Int.instMonoidInt) R (Units.instSMulUnits.{0, u2} Int R Int.instMonoidInt (SubNegMonoid.SMulInt.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_1)))))) x y)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))) R (fun (f : R) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) f) (SubadditiveHomClass.toFunLike.{max u2 u1, u2, u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))) R S (Distrib.toAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))))) (Distrib.toAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (OrderedSemiring.toSemiring.{u1} S (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))))))) (Preorder.toLE.{u1} S (PartialOrder.toPreorder.{u1} S (OrderedSemiring.toPartialOrder.{u1} S (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))))) (AbsoluteValue.subadditiveHomClass.{u2, u1} R S (Ring.toSemiring.{u2} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2)))))) abv (HSMul.hSMul.{0, u2, u2} (Units.{0} Int Int.instMonoidInt) R R (instHSMul.{0, u2} (Units.{0} Int Int.instMonoidInt) R (Units.instSMulUnits.{0, u2} Int R Int.instMonoidInt (SubNegMonoid.SMulInt.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_1)))))) x y)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))) R (fun (f : R) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) f) (SubadditiveHomClass.toFunLike.{max u2 u1, u2, u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))) R S (Distrib.toAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))))) (Distrib.toAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (OrderedSemiring.toSemiring.{u1} S (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))))))) (Preorder.toLE.{u1} S (PartialOrder.toPreorder.{u1} S (OrderedSemiring.toPartialOrder.{u1} S (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2))))))) (AbsoluteValue.subadditiveHomClass.{u2, u1} R S (Ring.toSemiring.{u2} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u1} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} S _inst_2)))))) abv y)
Case conversion may be inaccurate. Consider using '#align absolute_value.map_units_int_smul AbsoluteValue.map_units_int_smulₓ'. -/
@[simp]
theorem AbsoluteValue.map_units_int_smul (abv : AbsoluteValue R S) (x : ℤˣ) (y : R) :
    abv (x • y) = abv y := by rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp
#align absolute_value.map_units_int_smul AbsoluteValue.map_units_int_smul

/- warning: int.nat_abs_hom -> Int.natAbsHom is a dubious translation:
lean 3 declaration is
  MonoidWithZeroHom.{0, 0} Int Nat (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))
but is expected to have type
  MonoidWithZeroHom.{0, 0} Int Nat (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))
Case conversion may be inaccurate. Consider using '#align int.nat_abs_hom Int.natAbsHomₓ'. -/
/-- `int.nat_abs` as a bundled monoid with zero hom. -/
@[simps]
def Int.natAbsHom : ℤ →*₀ ℕ where
  toFun := Int.natAbs
  map_mul' := Int.natAbs_mul
  map_one' := Int.natAbs_one
  map_zero' := Int.natAbs_zero
#align int.nat_abs_hom Int.natAbsHom

