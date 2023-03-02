/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.order.algebra
! leanprover-community/mathlib commit f5a600f8102c8bfdbd22781968a20a539304c1b4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.Order.Smul

/-!
# Ordered algebras

An ordered algebra is an ordered semiring, which is an algebra over an ordered commutative semiring,
for which scalar multiplication is "compatible" with the two orders.

The prototypical example is 2x2 matrices over the reals or complexes (or indeed any C^* algebra)
where the ordering the one determined by the positive cone of positive operators,
i.e. `A ≤ B` iff `B - A = star R * R` for some `R`.
(We don't yet have this example in mathlib.)

## Implementation

Because the axioms for an ordered algebra are exactly the same as those for the underlying
module being ordered, we don't actually introduce a new class, but just use the `ordered_smul`
mixin.

## Tags

ordered algebra
-/


section OrderedAlgebra

variable {R A : Type _} {a b : A} {r : R}

variable [OrderedCommRing R] [OrderedRing A] [Algebra R A] [OrderedSMul R A]

/- warning: algebra_map_monotone -> algebraMap_monotone is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : OrderedCommRing.{u1} R] [_inst_2 : OrderedRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (OrderedCommSemiring.toCommSemiring.{u1} R (OrderedCommRing.toOrderedCommSemiring.{u1} R _inst_1)) (Ring.toSemiring.{u2} A (OrderedRing.toRing.{u2} A _inst_2))] [_inst_4 : OrderedSMul.{u1, u2} R A (OrderedRing.toOrderedSemiring.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)) (OrderedSemiring.toOrderedAddCommMonoid.{u2} A (OrderedRing.toOrderedSemiring.{u2} A _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (OrderedAddCommMonoid.toAddCommMonoid.{u2} A (OrderedSemiring.toOrderedAddCommMonoid.{u2} A (OrderedRing.toOrderedSemiring.{u2} A _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} R A (Ring.toSemiring.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} A (OrderedAddCommGroup.toAddCommGroup.{u2} A (OrderedRing.toOrderedAddCommGroup.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A (OrderedCommSemiring.toCommSemiring.{u1} R (OrderedCommRing.toOrderedCommSemiring.{u1} R _inst_1)) (Ring.toSemiring.{u2} A (OrderedRing.toRing.{u2} A _inst_2)) _inst_3)))], Monotone.{u1, u2} R A (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (OrderedRing.toOrderedAddCommGroup.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))) (PartialOrder.toPreorder.{u2} A (OrderedAddCommGroup.toPartialOrder.{u2} A (OrderedRing.toOrderedAddCommGroup.{u2} A _inst_2))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R (OrderedCommRing.toOrderedCommSemiring.{u1} R _inst_1)))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (OrderedRing.toRing.{u2} A _inst_2)))) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R (OrderedCommRing.toOrderedCommSemiring.{u1} R _inst_1)))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (OrderedRing.toRing.{u2} A _inst_2)))) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R (OrderedCommRing.toOrderedCommSemiring.{u1} R _inst_1)))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (OrderedRing.toRing.{u2} A _inst_2)))) (algebraMap.{u1, u2} R A (OrderedCommSemiring.toCommSemiring.{u1} R (OrderedCommRing.toOrderedCommSemiring.{u1} R _inst_1)) (Ring.toSemiring.{u2} A (OrderedRing.toRing.{u2} A _inst_2)) _inst_3))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : OrderedCommRing.{u2} R] [_inst_2 : OrderedRing.{u1} A] [_inst_3 : Algebra.{u2, u1} R A (OrderedCommSemiring.toCommSemiring.{u2} R (OrderedCommRing.toOrderedCommSemiring.{u2} R _inst_1)) (OrderedSemiring.toSemiring.{u1} A (OrderedRing.toOrderedSemiring.{u1} A _inst_2))] [_inst_4 : OrderedSMul.{u2, u1} R A (OrderedCommSemiring.toOrderedSemiring.{u2} R (OrderedCommRing.toOrderedCommSemiring.{u2} R _inst_1)) (OrderedSemiring.toOrderedAddCommMonoid.{u1} A (OrderedRing.toOrderedSemiring.{u1} A _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} R A (Semiring.toMonoidWithZero.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (OrderedCommRing.toOrderedCommSemiring.{u2} R _inst_1)))) (AddMonoid.toZero.{u1} A (AddCommMonoid.toAddMonoid.{u1} A (OrderedAddCommMonoid.toAddCommMonoid.{u1} A (OrderedSemiring.toOrderedAddCommMonoid.{u1} A (OrderedRing.toOrderedSemiring.{u1} A _inst_2))))) (Module.toMulActionWithZero.{u2, u1} R A (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (OrderedCommRing.toOrderedCommSemiring.{u2} R _inst_1))) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} A (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} A (OrderedRing.toOrderedAddCommGroup.{u1} A _inst_2))) (instModuleToSemiringToOrderedSemiringToOrderedCommSemiringToAddCommMonoidToOrderedCancelAddCommMonoidToOrderedAddCommGroup.{u2, u1} R A _inst_1 _inst_2 _inst_3)))], Monotone.{u2, u1} R A (PartialOrder.toPreorder.{u2} R (OrderedRing.toPartialOrder.{u2} R (OrderedCommRing.toOrderedRing.{u2} R _inst_1))) (PartialOrder.toPreorder.{u1} A (OrderedRing.toPartialOrder.{u1} A _inst_2)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R (OrderedCommRing.toOrderedCommSemiring.{u2} R _inst_1)))) (Semiring.toNonAssocSemiring.{u1} A (OrderedSemiring.toSemiring.{u1} A (OrderedRing.toOrderedSemiring.{u1} A _inst_2)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => A) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R (OrderedCommRing.toOrderedCommSemiring.{u2} R _inst_1)))) (Semiring.toNonAssocSemiring.{u1} A (OrderedSemiring.toSemiring.{u1} A (OrderedRing.toOrderedSemiring.{u1} A _inst_2)))) R A (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R (OrderedCommRing.toOrderedCommSemiring.{u2} R _inst_1)))))) (NonUnitalNonAssocSemiring.toMul.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A (OrderedSemiring.toSemiring.{u1} A (OrderedRing.toOrderedSemiring.{u1} A _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R (OrderedCommRing.toOrderedCommSemiring.{u2} R _inst_1)))) (Semiring.toNonAssocSemiring.{u1} A (OrderedSemiring.toSemiring.{u1} A (OrderedRing.toOrderedSemiring.{u1} A _inst_2)))) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R (OrderedCommRing.toOrderedCommSemiring.{u2} R _inst_1))))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A (OrderedSemiring.toSemiring.{u1} A (OrderedRing.toOrderedSemiring.{u1} A _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R (OrderedCommRing.toOrderedCommSemiring.{u2} R _inst_1)))) (Semiring.toNonAssocSemiring.{u1} A (OrderedSemiring.toSemiring.{u1} A (OrderedRing.toOrderedSemiring.{u1} A _inst_2)))) R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R (OrderedCommRing.toOrderedCommSemiring.{u2} R _inst_1)))) (Semiring.toNonAssocSemiring.{u1} A (OrderedSemiring.toSemiring.{u1} A (OrderedRing.toOrderedSemiring.{u1} A _inst_2))) (RingHom.instRingHomClassRingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R (OrderedCommRing.toOrderedCommSemiring.{u2} R _inst_1)))) (Semiring.toNonAssocSemiring.{u1} A (OrderedSemiring.toSemiring.{u1} A (OrderedRing.toOrderedSemiring.{u1} A _inst_2))))))) (algebraMap.{u2, u1} R A (OrderedCommSemiring.toCommSemiring.{u2} R (OrderedCommRing.toOrderedCommSemiring.{u2} R _inst_1)) (OrderedSemiring.toSemiring.{u1} A (OrderedRing.toOrderedSemiring.{u1} A _inst_2)) _inst_3))
Case conversion may be inaccurate. Consider using '#align algebra_map_monotone algebraMap_monotoneₓ'. -/
theorem algebraMap_monotone : Monotone (algebraMap R A) := fun a b h =>
  by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← sub_nonneg, ← sub_smul]
  trans (b - a) • (0 : A)
  · simp
  · exact smul_le_smul_of_nonneg zero_le_one (sub_nonneg.mpr h)
#align algebra_map_monotone algebraMap_monotone

end OrderedAlgebra

