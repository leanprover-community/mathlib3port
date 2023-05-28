/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module analysis.complex.circle
! leanprover-community/mathlib commit 50251fd6309cca5ca2e747882ffecd2729f38c5d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Exp
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Analysis.Normed.Field.UnitBall

/-!
# The circle

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `circle` to be the metric sphere (`metric.sphere`) in `ℂ` centred at `0` of
radius `1`.  We equip it with the following structure:

* a submonoid of `ℂ`
* a group
* a topological group

We furthermore define `exp_map_circle` to be the natural map `λ t, exp (t * I)` from `ℝ` to
`circle`, and show that this map is a group homomorphism.

## Implementation notes

Because later (in `geometry.manifold.instances.sphere`) one wants to equip the circle with a smooth
manifold structure borrowed from `metric.sphere`, the underlying set is
`{z : ℂ | abs (z - 0) = 1}`.  This prevents certain algebraic facts from working definitionally --
for example, the circle is not defeq to `{z : ℂ | abs z = 1}`, which is the kernel of `complex.abs`
considered as a homomorphism from `ℂ` to `ℝ`, nor is it defeq to `{z : ℂ | norm_sq z = 1}`, which
is the kernel of the homomorphism `complex.norm_sq` from `ℂ` to `ℝ`.

-/


noncomputable section

open Complex Metric

open ComplexConjugate

#print circle /-
/-- The unit circle in `ℂ`, here given the structure of a submonoid of `ℂ`. -/
def circle : Submonoid ℂ :=
  Submonoid.unitSphere ℂ
#align circle circle
-/

/- warning: mem_circle_iff_abs -> mem_circle_iff_abs is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, Iff (Membership.Mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) (SetLike.hasMem.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) z circle) (Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {z : Complex}, Iff (Membership.mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (SetLike.instMembership.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))))) z circle) (Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs z) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align mem_circle_iff_abs mem_circle_iff_absₓ'. -/
@[simp]
theorem mem_circle_iff_abs {z : ℂ} : z ∈ circle ↔ abs z = 1 :=
  mem_sphere_zero_iff_norm
#align mem_circle_iff_abs mem_circle_iff_abs

/- warning: circle_def -> circle_def is a dubious translation:
lean 3 declaration is
  Eq.{1} (Set.{0} Complex) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) (Set.{0} Complex) (HasLiftT.mk.{1, 1} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) (Set.{0} Complex) (CoeTCₓ.coe.{1, 1} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) (Set.{0} Complex) (SetLike.Set.hasCoeT.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))))) circle) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  Eq.{1} (Set.{0} Complex) (SetLike.coe.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) circle) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs z) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align circle_def circle_defₓ'. -/
theorem circle_def : ↑circle = { z : ℂ | abs z = 1 } :=
  Set.ext fun z => mem_circle_iff_abs
#align circle_def circle_def

/- warning: abs_coe_circle -> abs_coe_circle is a dubious translation:
lean 3 declaration is
  forall (z : coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle), Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle) Complex (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle) Complex (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle) Complex (coeBase.{1, 1} (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle) Complex (coeSubtype.{1} Complex (fun (x : Complex) => Membership.Mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) (SetLike.hasMem.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) x circle))))) z)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (z : Subtype.{1} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (SetLike.instMembership.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))))) x circle)), Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (Subtype.val.{1} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Set.{0} Complex) (Set.instMembershipSet.{0} Complex) x (SetLike.coe.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) circle)) z)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs (Subtype.val.{1} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Set.{0} Complex) (Set.instMembershipSet.{0} Complex) x (SetLike.coe.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) circle)) z)) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (Subtype.val.{1} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Set.{0} Complex) (Set.instMembershipSet.{0} Complex) x (SetLike.coe.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) circle)) z)) 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (Subtype.val.{1} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Set.{0} Complex) (Set.instMembershipSet.{0} Complex) x (SetLike.coe.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) circle)) z)) Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align abs_coe_circle abs_coe_circleₓ'. -/
@[simp]
theorem abs_coe_circle (z : circle) : abs z = 1 :=
  mem_circle_iff_abs.mp z.2
#align abs_coe_circle abs_coe_circle

/- warning: mem_circle_iff_norm_sq -> mem_circle_iff_normSq is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, Iff (Membership.Mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) (SetLike.hasMem.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) z circle) (Eq.{1} Real (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Complex Real (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring)))) (fun (_x : MonoidWithZeroHom.{0, 0} Complex Real (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring)))) => Complex -> Real) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Complex Real (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring)))) Complex.normSq z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {z : Complex}, Iff (Membership.mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (SetLike.instMembership.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))))) z circle) (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Real) z) (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Complex Real (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)) (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Real) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Complex Real (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)) (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex Real (MulOneClass.toMul.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (MulOneClass.toMul.{0} Real (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Complex Real (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)) (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex Real (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))) (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Complex Real (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)) (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) Complex Real (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)) (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Complex Real (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)) (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))) Complex.normSq z) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Real) z) 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Real) z) Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align mem_circle_iff_norm_sq mem_circle_iff_normSqₓ'. -/
theorem mem_circle_iff_normSq {z : ℂ} : z ∈ circle ↔ normSq z = 1 := by simp [Complex.abs]
#align mem_circle_iff_norm_sq mem_circle_iff_normSq

/- warning: norm_sq_eq_of_mem_circle -> normSq_eq_of_mem_circle is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align norm_sq_eq_of_mem_circle normSq_eq_of_mem_circleₓ'. -/
@[simp]
theorem normSq_eq_of_mem_circle (z : circle) : normSq z = 1 := by simp [norm_sq_eq_abs]
#align norm_sq_eq_of_mem_circle normSq_eq_of_mem_circle

/- warning: ne_zero_of_mem_circle -> ne_zero_of_mem_circle is a dubious translation:
lean 3 declaration is
  forall (z : coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle), Ne.{1} Complex ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle) Complex (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle) Complex (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle) Complex (coeBase.{1, 1} (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle) Complex (coeSubtype.{1} Complex (fun (x : Complex) => Membership.Mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) (SetLike.hasMem.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) x circle))))) z) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))
but is expected to have type
  forall (z : Subtype.{1} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (SetLike.instMembership.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))))) x circle)), Ne.{1} Complex (Subtype.val.{1} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Set.{0} Complex) (Set.instMembershipSet.{0} Complex) x (SetLike.coe.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) circle)) z) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))
Case conversion may be inaccurate. Consider using '#align ne_zero_of_mem_circle ne_zero_of_mem_circleₓ'. -/
theorem ne_zero_of_mem_circle (z : circle) : (z : ℂ) ≠ 0 :=
  ne_zero_of_mem_unit_sphere z
#align ne_zero_of_mem_circle ne_zero_of_mem_circle

instance : CommGroup circle :=
  Metric.sphere.commGroup

/- warning: coe_inv_circle -> coe_inv_circle is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align coe_inv_circle coe_inv_circleₓ'. -/
@[simp]
theorem coe_inv_circle (z : circle) : ↑z⁻¹ = (z : ℂ)⁻¹ :=
  rfl
#align coe_inv_circle coe_inv_circle

/- warning: coe_inv_circle_eq_conj -> coe_inv_circle_eq_conj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align coe_inv_circle_eq_conj coe_inv_circle_eq_conjₓ'. -/
theorem coe_inv_circle_eq_conj (z : circle) : ↑z⁻¹ = conj (z : ℂ) := by
  rw [coe_inv_circle, inv_def, normSq_eq_of_mem_circle, inv_one, of_real_one, mul_one]
#align coe_inv_circle_eq_conj coe_inv_circle_eq_conj

/- warning: coe_div_circle -> coe_div_circle is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align coe_div_circle coe_div_circleₓ'. -/
@[simp]
theorem coe_div_circle (z w : circle) : ↑(z / w) = (z : ℂ) / w :=
  circle.Subtype.map_div z w
#align coe_div_circle coe_div_circle

/- warning: circle.to_units -> circle.toUnits is a dubious translation:
lean 3 declaration is
  MonoidHom.{0, 0} (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle) (Units.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring)) (Submonoid.toMulOneClass.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))) circle) (Units.mulOneClass.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))
but is expected to have type
  MonoidHom.{0, 0} (Subtype.{1} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (SetLike.instMembership.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))))) x circle)) (Units.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex Complex.instSemiringComplex))) (Submonoid.toMulOneClass.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))) circle) (Units.instMulOneClassUnits.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex Complex.instSemiringComplex)))
Case conversion may be inaccurate. Consider using '#align circle.to_units circle.toUnitsₓ'. -/
/-- The elements of the circle embed into the units. -/
def circle.toUnits : circle →* Units ℂ :=
  unitSphereToUnits ℂ
#align circle.to_units circle.toUnits

/- warning: circle.to_units_apply -> circle.toUnits_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align circle.to_units_apply circle.toUnits_applyₓ'. -/
-- written manually because `@[simps]` was slow and generated the wrong lemma
@[simp]
theorem circle.toUnits_apply (z : circle) :
    circle.toUnits z = Units.mk0 z (ne_zero_of_mem_circle z) :=
  rfl
#align circle.to_units_apply circle.toUnits_apply

instance : CompactSpace circle :=
  Metric.sphere.compactSpace _ _

instance : TopologicalGroup circle :=
  Metric.sphere.topologicalGroup

/- warning: circle.of_conj_div_self -> circle.ofConjDivSelf is a dubious translation:
lean 3 declaration is
  forall (z : Complex), (Ne.{1} Complex z (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle)
but is expected to have type
  forall (z : Complex), (Ne.{1} Complex z (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Subtype.{1} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (SetLike.instMembership.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))))) x circle))
Case conversion may be inaccurate. Consider using '#align circle.of_conj_div_self circle.ofConjDivSelfₓ'. -/
/-- If `z` is a nonzero complex number, then `conj z / z` belongs to the unit circle. -/
@[simps]
def circle.ofConjDivSelf (z : ℂ) (hz : z ≠ 0) : circle :=
  ⟨conj z / z,
    mem_circle_iff_abs.2 <| by rw [map_div₀, abs_conj, div_self (complex.abs.ne_zero hz)]⟩
#align circle.of_conj_div_self circle.ofConjDivSelf

/- warning: exp_map_circle -> expMapCircle is a dubious translation:
lean 3 declaration is
  ContinuousMap.{0, 0} Real (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Subtype.topologicalSpace.{0} Complex (fun (x : Complex) => Membership.Mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) (SetLike.hasMem.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) x circle) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))))
but is expected to have type
  ContinuousMap.{0, 0} Real (Subtype.{1} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (SetLike.instMembership.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))))) x circle)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (instTopologicalSpaceSubtype.{0} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (SetLike.instMembership.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))))) x circle) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))))
Case conversion may be inaccurate. Consider using '#align exp_map_circle expMapCircleₓ'. -/
/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ`. -/
def expMapCircle : C(ℝ, circle)
    where toFun t := ⟨exp (t * I), by simp [exp_mul_I, abs_cos_add_sin_mul_I]⟩
#align exp_map_circle expMapCircle

/- warning: exp_map_circle_apply -> expMapCircle_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align exp_map_circle_apply expMapCircle_applyₓ'. -/
@[simp]
theorem expMapCircle_apply (t : ℝ) : ↑(expMapCircle t) = Complex.exp (t * Complex.I) :=
  rfl
#align exp_map_circle_apply expMapCircle_apply

/- warning: exp_map_circle_zero -> expMapCircle_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align exp_map_circle_zero expMapCircle_zeroₓ'. -/
@[simp]
theorem expMapCircle_zero : expMapCircle 0 = 1 :=
  Subtype.ext <| by
    rw [expMapCircle_apply, of_real_zero, MulZeroClass.zero_mul, exp_zero, Submonoid.coe_one]
#align exp_map_circle_zero expMapCircle_zero

/- warning: exp_map_circle_add -> expMapCircle_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align exp_map_circle_add expMapCircle_addₓ'. -/
@[simp]
theorem expMapCircle_add (x y : ℝ) : expMapCircle (x + y) = expMapCircle x * expMapCircle y :=
  Subtype.ext <| by
    simp only [expMapCircle_apply, Submonoid.coe_mul, of_real_add, add_mul, Complex.exp_add]
#align exp_map_circle_add expMapCircle_add

/- warning: exp_map_circle_hom -> expMapCircleHom is a dubious translation:
lean 3 declaration is
  AddMonoidHom.{0, 0} Real (Additive.{0} (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle)) (AddMonoid.toAddZeroClass.{0} Real Real.addMonoid) (Additive.addZeroClass.{0} (coeSort.{1, 2} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Type (SetLike.hasCoeToSort.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring))))) Complex (Submonoid.setLike.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))))) circle) (Submonoid.toMulOneClass.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (NonAssocRing.toNonAssocSemiring.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.ring)))) circle))
but is expected to have type
  AddMonoidHom.{0, 0} Real (Additive.{0} (Subtype.{1} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (SetLike.instMembership.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))))) x circle))) (AddMonoid.toAddZeroClass.{0} Real Real.instAddMonoidReal) (Additive.addZeroClass.{0} (Subtype.{1} Complex (fun (x : Complex) => Membership.mem.{0, 0} Complex (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (SetLike.instMembership.{0, 0} (Submonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) Complex (Submonoid.instSetLikeSubmonoid.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))))) x circle)) (Submonoid.toMulOneClass.{0} Complex (MulZeroOneClass.toMulOneClass.{0} Complex (NonAssocSemiring.toMulZeroOneClass.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex))) circle))
Case conversion may be inaccurate. Consider using '#align exp_map_circle_hom expMapCircleHomₓ'. -/
/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ`, considered as a homomorphism of
groups. -/
@[simps]
def expMapCircleHom : ℝ →+ Additive circle
    where
  toFun := Additive.ofMul ∘ expMapCircle
  map_zero' := expMapCircle_zero
  map_add' := expMapCircle_add
#align exp_map_circle_hom expMapCircleHom

/- warning: exp_map_circle_sub -> expMapCircle_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align exp_map_circle_sub expMapCircle_subₓ'. -/
@[simp]
theorem expMapCircle_sub (x y : ℝ) : expMapCircle (x - y) = expMapCircle x / expMapCircle y :=
  expMapCircleHom.map_sub x y
#align exp_map_circle_sub expMapCircle_sub

/- warning: exp_map_circle_neg -> expMapCircle_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align exp_map_circle_neg expMapCircle_negₓ'. -/
@[simp]
theorem expMapCircle_neg (x : ℝ) : expMapCircle (-x) = (expMapCircle x)⁻¹ :=
  expMapCircleHom.map_neg x
#align exp_map_circle_neg expMapCircle_neg

