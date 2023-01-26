/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module algebra.order.euclidean_absolute_value
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.AbsoluteValue
import Mathbin.Algebra.EuclideanDomain.Instances

/-!
# Euclidean absolute values

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a predicate `absolute_value.is_euclidean abv` stating the
absolute value is compatible with the Euclidean domain structure on its domain.

## Main definitions

 * `absolute_value.is_euclidean abv` is a predicate on absolute values on `R` mapping to `S`
    that preserve the order on `R` arising from the Euclidean domain structure.
 * `absolute_value.abs_is_euclidean` shows the "standard" absolute value on `ℤ`,
   mapping negative `x` to `-x`, is euclidean.
-/


-- mathport name: «expr ≺ »
local infixl:50 " ≺ " => EuclideanDomain.r

namespace AbsoluteValue

section OrderedSemiring

variable {R S : Type _} [EuclideanDomain R] [OrderedSemiring S]

variable (abv : AbsoluteValue R S)

#print AbsoluteValue.IsEuclidean /-
/-- An absolute value `abv : R → S` is Euclidean if it is compatible with the
`euclidean_domain` structure on `R`, namely `abv` is strictly monotone with respect to the well
founded relation `≺` on `R`. -/
structure IsEuclidean : Prop where
  map_lt_map_iff' : ∀ {x y}, abv x < abv y ↔ x ≺ y
#align absolute_value.is_euclidean AbsoluteValue.IsEuclidean
-/

namespace IsEuclidean

variable {abv}

/- warning: absolute_value.is_euclidean.map_lt_map_iff -> AbsoluteValue.IsEuclidean.map_lt_map_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : OrderedSemiring.{u2} S] {abv : AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2} {x : R} {y : R}, (AbsoluteValue.IsEuclidean.{u1, u2} R S _inst_1 _inst_2 abv) -> (Iff (LT.lt.{u2} S (Preorder.toLT.{u2} S (PartialOrder.toPreorder.{u2} S (OrderedAddCommMonoid.toPartialOrder.{u2} S (OrderedSemiring.toOrderedAddCommMonoid.{u2} S _inst_2)))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2) (fun (f : AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2) => R -> S) (AbsoluteValue.hasCoeToFun.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2) abv x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2) (fun (f : AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2) => R -> S) (AbsoluteValue.hasCoeToFun.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2) abv y)) (EuclideanDomain.r.{u1} R _inst_1 x y))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : EuclideanDomain.{u2} R] [_inst_2 : OrderedSemiring.{u1} S] {abv : AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2} {x : R} {y : R}, (AbsoluteValue.IsEuclidean.{u2, u1} R S _inst_1 _inst_2 abv) -> (Iff (LT.lt.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) x) (Preorder.toLT.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) x) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) x) (OrderedSemiring.toPartialOrder.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) x) _inst_2))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2) R (fun (f : R) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) f) (SubadditiveHomClass.toFunLike.{max u2 u1, u2, u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2) R S (Distrib.toAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))))))) (Distrib.toAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (OrderedSemiring.toSemiring.{u1} S _inst_2))))) (Preorder.toLE.{u1} S (PartialOrder.toPreorder.{u1} S (OrderedSemiring.toPartialOrder.{u1} S _inst_2))) (AbsoluteValue.subadditiveHomClass.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2)) abv x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2) R (fun (f : R) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) f) (SubadditiveHomClass.toFunLike.{max u2 u1, u2, u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2) R S (Distrib.toAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))))))) (Distrib.toAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (OrderedSemiring.toSemiring.{u1} S _inst_2))))) (Preorder.toLE.{u1} S (PartialOrder.toPreorder.{u1} S (OrderedSemiring.toPartialOrder.{u1} S _inst_2))) (AbsoluteValue.subadditiveHomClass.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2)) abv y)) (EuclideanDomain.r.{u2} R _inst_1 x y))
Case conversion may be inaccurate. Consider using '#align absolute_value.is_euclidean.map_lt_map_iff AbsoluteValue.IsEuclidean.map_lt_map_iffₓ'. -/
-- Rearrange the parameters to `map_lt_map_iff'` so it elaborates better.
theorem map_lt_map_iff {x y : R} (h : abv.IsEuclidean) : abv x < abv y ↔ x ≺ y :=
  map_lt_map_iff' h
#align absolute_value.is_euclidean.map_lt_map_iff AbsoluteValue.IsEuclidean.map_lt_map_iff

attribute [simp] map_lt_map_iff

/- warning: absolute_value.is_euclidean.sub_mod_lt -> AbsoluteValue.IsEuclidean.sub_mod_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : OrderedSemiring.{u2} S] {abv : AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2}, (AbsoluteValue.IsEuclidean.{u1, u2} R S _inst_1 _inst_2 abv) -> (forall (a : R) {b : R}, (Ne.{succ u1} R b (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (LT.lt.{u2} S (Preorder.toLT.{u2} S (PartialOrder.toPreorder.{u2} S (OrderedAddCommMonoid.toPartialOrder.{u2} S (OrderedSemiring.toOrderedAddCommMonoid.{u2} S _inst_2)))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2) (fun (f : AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2) => R -> S) (AbsoluteValue.hasCoeToFun.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2) abv (HMod.hMod.{u1, u1, u1} R R R (instHMod.{u1} R (EuclideanDomain.hasMod.{u1} R _inst_1)) a b)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2) (fun (f : AbsoluteValue.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2) => R -> S) (AbsoluteValue.hasCoeToFun.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))) _inst_2) abv b)))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : EuclideanDomain.{u2} R] [_inst_2 : OrderedSemiring.{u1} S] {abv : AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2}, (AbsoluteValue.IsEuclidean.{u2, u1} R S _inst_1 _inst_2 abv) -> (forall (a : R) {b : R}, (Ne.{succ u2} R b (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R (CommRing.toCommSemiring.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))))))) -> (LT.lt.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) (HMod.hMod.{u2, u2, u2} R R R (instHMod.{u2} R (EuclideanDomain.instMod.{u2} R _inst_1)) a b)) (Preorder.toLT.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) (HMod.hMod.{u2, u2, u2} R R R (instHMod.{u2} R (EuclideanDomain.instMod.{u2} R _inst_1)) a b)) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) (HMod.hMod.{u2, u2, u2} R R R (instHMod.{u2} R (EuclideanDomain.instMod.{u2} R _inst_1)) a b)) (OrderedSemiring.toPartialOrder.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) (HMod.hMod.{u2, u2, u2} R R R (instHMod.{u2} R (EuclideanDomain.instMod.{u2} R _inst_1)) a b)) _inst_2))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2) R (fun (f : R) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) f) (SubadditiveHomClass.toFunLike.{max u2 u1, u2, u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2) R S (Distrib.toAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))))))) (Distrib.toAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (OrderedSemiring.toSemiring.{u1} S _inst_2))))) (Preorder.toLE.{u1} S (PartialOrder.toPreorder.{u1} S (OrderedSemiring.toPartialOrder.{u1} S _inst_2))) (AbsoluteValue.subadditiveHomClass.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2)) abv (HMod.hMod.{u2, u2, u2} R R R (instHMod.{u2} R (EuclideanDomain.instMod.{u2} R _inst_1)) a b)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2) R (fun (f : R) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.96 : R) => S) f) (SubadditiveHomClass.toFunLike.{max u2 u1, u2, u1} (AbsoluteValue.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2) R S (Distrib.toAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))))))) (Distrib.toAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (OrderedSemiring.toSemiring.{u1} S _inst_2))))) (Preorder.toLE.{u1} S (PartialOrder.toPreorder.{u1} S (OrderedSemiring.toPartialOrder.{u1} S _inst_2))) (AbsoluteValue.subadditiveHomClass.{u2, u1} R S (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R (EuclideanDomain.toCommRing.{u2} R _inst_1))) _inst_2)) abv b)))
Case conversion may be inaccurate. Consider using '#align absolute_value.is_euclidean.sub_mod_lt AbsoluteValue.IsEuclidean.sub_mod_ltₓ'. -/
theorem sub_mod_lt (h : abv.IsEuclidean) (a : R) {b : R} (hb : b ≠ 0) : abv (a % b) < abv b :=
  h.map_lt_map_iff.mpr (EuclideanDomain.mod_lt a hb)
#align absolute_value.is_euclidean.sub_mod_lt AbsoluteValue.IsEuclidean.sub_mod_lt

end IsEuclidean

end OrderedSemiring

section Int

open Int

#print AbsoluteValue.abs_isEuclidean /-
-- TODO: generalize to `linear_ordered_euclidean_domain`s if we ever get a definition of those
/-- `abs : ℤ → ℤ` is a Euclidean absolute value -/
protected theorem abs_isEuclidean : IsEuclidean (AbsoluteValue.abs : AbsoluteValue ℤ ℤ) :=
  {
    map_lt_map_iff' := fun x y =>
      show abs x < abs y ↔ natAbs x < natAbs y by rw [abs_eq_nat_abs, abs_eq_nat_abs, coe_nat_lt] }
#align absolute_value.abs_is_euclidean AbsoluteValue.abs_isEuclidean
-/

end Int

end AbsoluteValue

