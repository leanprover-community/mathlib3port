/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module topology.algebra.order.archimedean
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Order.Basic
import Mathbin.Algebra.Order.Archimedean

/-!
# Rational numbers are dense in a linear ordered archimedean field

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that coercion from `ℚ` to a linear ordered archimedean field has dense range.
This lemma is in a separate file because `topology.order.basic` does not import
`algebra.order.archimedean`.
-/


variable {𝕜 : Type _} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜]

/- warning: rat.dense_range_cast -> Rat.denseRange_cast is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : TopologicalSpace.{u1} 𝕜] [_inst_3 : OrderTopology.{u1} 𝕜 _inst_2 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))] [_inst_4 : Archimedean.{u1} 𝕜 (OrderedSemiring.toOrderedAddCommMonoid.{u1} 𝕜 (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))], DenseRange.{u1, 0} 𝕜 _inst_2 Rat ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat 𝕜 (HasLiftT.mk.{1, succ u1} Rat 𝕜 (CoeTCₓ.coe.{1, succ u1} Rat 𝕜 (Rat.castCoe.{u1} 𝕜 (DivisionRing.toHasRatCast.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : TopologicalSpace.{u1} 𝕜] [_inst_3 : OrderTopology.{u1} 𝕜 _inst_2 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))] [_inst_4 : Archimedean.{u1} 𝕜 (OrderedSemiring.toOrderedAddCommMonoid.{u1} 𝕜 (OrderedCommSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))], DenseRange.{u1, 0} 𝕜 _inst_2 Rat (RatCast.ratCast.{u1} 𝕜 (LinearOrderedField.toRatCast.{u1} 𝕜 _inst_1))
Case conversion may be inaccurate. Consider using '#align rat.dense_range_cast Rat.denseRange_castₓ'. -/
/-- Rational numbers are dense in a linear ordered archimedean field. -/
theorem Rat.denseRange_cast : DenseRange (coe : ℚ → 𝕜) :=
  dense_of_exists_between fun a b h => Set.exists_range_iff.2 <| exists_rat_btwn h
#align rat.dense_range_cast Rat.denseRange_cast

