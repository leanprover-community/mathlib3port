/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.uniform_space.absolute_value
! leanprover-community/mathlib commit e1a7bdeb4fd826b7e71d130d34988f0a2d26a177
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.AbsoluteValue
import Mathbin.Topology.UniformSpace.Basic

/-!
# Uniform structure induced by an absolute value

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We build a uniform space structure on a commutative ring `R` equipped with an absolute value into
a linear ordered field `𝕜`. Of course in the case `R` is `ℚ`, `ℝ` or `ℂ` and
`𝕜 = ℝ`, we get the same thing as the metric space construction, and the general construction
follows exactly the same path.

## Implementation details

Note that we import `data.real.cau_seq` because this is where absolute values are defined, but
the current file does not depend on real numbers. TODO: extract absolute values from that
`data.real` folder.

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

absolute value, uniform spaces
-/


open Set Function Filter UniformSpace

open Filter Topology

namespace AbsoluteValue

variable {𝕜 : Type _} [LinearOrderedField 𝕜]

variable {R : Type _} [CommRing R] (abv : AbsoluteValue R 𝕜)

#print AbsoluteValue.uniformSpace /-
/-- The uniform space structure coming from an absolute value. -/
protected def uniformSpace : UniformSpace R :=
  UniformSpace.ofFun (fun x y => abv (y - x)) (by simp) (fun x y => abv.map_sub y x)
    (fun x y z => (abv.sub_le _ _ _).trans_eq (add_comm _ _)) fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, fun _ h₁ _ h₂ => (add_lt_add h₁ h₂).trans_eq (add_halves ε)⟩
#align absolute_value.uniform_space AbsoluteValue.uniformSpace
-/

/- warning: absolute_value.has_basis_uniformity -> AbsoluteValue.hasBasis_uniformity is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {R : Type.{u2}} [_inst_2 : CommRing.{u2} R] (abv : AbsoluteValue.{u2, u1} R 𝕜 (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))), Filter.HasBasis.{u2, succ u1} (Prod.{u2, u2} R R) 𝕜 (uniformity.{u2} R (AbsoluteValue.uniformSpace.{u1, u2} 𝕜 _inst_1 R _inst_2 abv)) (fun (ε : 𝕜) => LT.lt.{u1} 𝕜 (Preorder.toLT.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))))))))) ε) (fun (ε : 𝕜) => setOf.{u2} (Prod.{u2, u2} R R) (fun (p : Prod.{u2, u2} R R) => LT.lt.{u1} 𝕜 (Preorder.toLT.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (AbsoluteValue.{u2, u1} R 𝕜 (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (fun (f : AbsoluteValue.{u2, u1} R 𝕜 (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) => R -> 𝕜) (AbsoluteValue.hasCoeToFun.{u2, u1} R 𝕜 (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) abv (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (SubNegMonoid.toHasSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (AddCommGroupWithOne.toAddGroupWithOne.{u2} R (Ring.toAddCommGroupWithOne.{u2} R (CommRing.toRing.{u2} R _inst_2))))))) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) ε))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {R : Type.{u2}} [_inst_2 : CommRing.{u2} R] (abv : AbsoluteValue.{u2, u1} R 𝕜 (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (OrderedCommSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1)))))), Filter.HasBasis.{u2, succ u1} (Prod.{u2, u2} R R) 𝕜 (uniformity.{u2} R (AbsoluteValue.uniformSpace.{u1, u2} 𝕜 _inst_1 R _inst_2 abv)) (fun (ε : 𝕜) => LT.lt.{u1} 𝕜 (Preorder.toLT.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (LinearOrderedSemifield.toSemifield.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))) ε) (fun (ε : 𝕜) => setOf.{u2} (Prod.{u2, u2} R R) (fun (p : Prod.{u2, u2} R R) => LT.lt.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => 𝕜) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R (CommRing.toRing.{u2} R _inst_2))) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) (Preorder.toLT.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => 𝕜) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R (CommRing.toRing.{u2} R _inst_2))) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => 𝕜) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R (CommRing.toRing.{u2} R _inst_2))) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) (StrictOrderedRing.toPartialOrder.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => 𝕜) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R (CommRing.toRing.{u2} R _inst_2))) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) (LinearOrderedRing.toStrictOrderedRing.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => 𝕜) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R (CommRing.toRing.{u2} R _inst_2))) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) (LinearOrderedCommRing.toLinearOrderedRing.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => 𝕜) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R (CommRing.toRing.{u2} R _inst_2))) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) (LinearOrderedField.toLinearOrderedCommRing.{u1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => 𝕜) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R (CommRing.toRing.{u2} R _inst_2))) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) _inst_1)))))) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (AbsoluteValue.{u2, u1} R 𝕜 (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (OrderedCommSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1)))))) R (fun (f : R) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => 𝕜) f) (SubadditiveHomClass.toFunLike.{max u1 u2, u2, u1} (AbsoluteValue.{u2, u1} R 𝕜 (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (OrderedCommSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1)))))) R 𝕜 (Distrib.toAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)))))) (Distrib.toAdd.{u1} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u1} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 (OrderedCommSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1)))))))))) (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedSemiring.toPartialOrder.{u1} 𝕜 (OrderedCommSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1)))))))) (AbsoluteValue.subadditiveHomClass.{u2, u1} R 𝕜 (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) (OrderedCommSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))) abv (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R (CommRing.toRing.{u2} R _inst_2))) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) ε))
Case conversion may be inaccurate. Consider using '#align absolute_value.has_basis_uniformity AbsoluteValue.hasBasis_uniformityₓ'. -/
theorem hasBasis_uniformity :
    𝓤[abv.UniformSpace].HasBasis (fun ε : 𝕜 => 0 < ε) fun ε =>
      { p : R × R | abv (p.2 - p.1) < ε } :=
  UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _
#align absolute_value.has_basis_uniformity AbsoluteValue.hasBasis_uniformity

end AbsoluteValue

