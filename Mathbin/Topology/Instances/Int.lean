/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module topology.instances.int
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Interval
import Mathbin.Topology.MetricSpace.Basic
import Mathbin.Order.Filter.Archimedean

/-!
# Topology on the integers

The structure of a metric space on `ℤ` is introduced in this file, induced from `ℝ`.
-/


noncomputable section

open Metric Set Filter

namespace Int

instance : Dist ℤ :=
  ⟨fun x y => dist (x : ℝ) y⟩

/- warning: int.dist_eq -> Int.dist_eq is a dubious translation:
lean 3 declaration is
  forall (x : Int) (y : Int), Eq.{1} Real (Dist.dist.{0} Int Int.hasDist x y) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) y)))
but is expected to have type
  forall (x : Int) (y : Int), Eq.{1} Real (Dist.dist.{0} Int Int.instDistInt x y) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Int.cast.{0} Real Real.intCast x) (Int.cast.{0} Real Real.intCast y)))
Case conversion may be inaccurate. Consider using '#align int.dist_eq Int.dist_eqₓ'. -/
theorem dist_eq (x y : ℤ) : dist x y = |x - y| :=
  rfl
#align int.dist_eq Int.dist_eq

/- warning: int.dist_cast_real -> Int.dist_cast_real is a dubious translation:
lean 3 declaration is
  forall (x : Int) (y : Int), Eq.{1} Real (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) y)) (Dist.dist.{0} Int Int.hasDist x y)
but is expected to have type
  forall (x : Int) (y : Int), Eq.{1} Real (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) (Int.cast.{0} Real Real.intCast x) (Int.cast.{0} Real Real.intCast y)) (Dist.dist.{0} Int Int.instDistInt x y)
Case conversion may be inaccurate. Consider using '#align int.dist_cast_real Int.dist_cast_realₓ'. -/
@[norm_cast, simp]
theorem dist_cast_real (x y : ℤ) : dist (x : ℝ) y = dist x y :=
  rfl
#align int.dist_cast_real Int.dist_cast_real

/- warning: int.pairwise_one_le_dist -> Int.pairwise_one_le_dist is a dubious translation:
lean 3 declaration is
  Pairwise.{0} Int (fun (m : Int) (n : Int) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Dist.dist.{0} Int Int.hasDist m n))
but is expected to have type
  Pairwise.{0} Int (fun (m : Int) (n : Int) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Dist.dist.{0} Int Int.instDistInt m n))
Case conversion may be inaccurate. Consider using '#align int.pairwise_one_le_dist Int.pairwise_one_le_distₓ'. -/
theorem pairwise_one_le_dist : Pairwise fun m n : ℤ => 1 ≤ dist m n :=
  by
  intro m n hne
  rw [dist_eq]; norm_cast; rwa [← zero_add (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]
#align int.pairwise_one_le_dist Int.pairwise_one_le_dist

/- warning: int.uniform_embedding_coe_real -> Int.uniformEmbedding_coe_real is a dubious translation:
lean 3 declaration is
  UniformEmbedding.{0, 0} Int Real Int.uniformSpace (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))))
but is expected to have type
  UniformEmbedding.{0, 0} Int Real instUniformSpaceInt (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) (Int.cast.{0} Real Real.intCast)
Case conversion may be inaccurate. Consider using '#align int.uniform_embedding_coe_real Int.uniformEmbedding_coe_realₓ'. -/
theorem uniformEmbedding_coe_real : UniformEmbedding (coe : ℤ → ℝ) :=
  uniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align int.uniform_embedding_coe_real Int.uniformEmbedding_coe_real

/- warning: int.closed_embedding_coe_real -> Int.closedEmbedding_coe_real is a dubious translation:
lean 3 declaration is
  ClosedEmbedding.{0, 0} Int Real Int.topologicalSpace (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))))
but is expected to have type
  ClosedEmbedding.{0, 0} Int Real instTopologicalSpaceInt (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Int.cast.{0} Real Real.intCast)
Case conversion may be inaccurate. Consider using '#align int.closed_embedding_coe_real Int.closedEmbedding_coe_realₓ'. -/
theorem closedEmbedding_coe_real : ClosedEmbedding (coe : ℤ → ℝ) :=
  closedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align int.closed_embedding_coe_real Int.closedEmbedding_coe_real

instance : MetricSpace ℤ :=
  Int.uniformEmbedding_coe_real.comapMetricSpace _

/- warning: int.preimage_ball -> Int.preimage_ball is a dubious translation:
lean 3 declaration is
  forall (x : Int) (r : Real), Eq.{1} (Set.{0} Int) (Set.preimage.{0, 0} Int Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast)))) (Metric.ball.{0} Real Real.pseudoMetricSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) x) r)) (Metric.ball.{0} Int (MetricSpace.toPseudoMetricSpace.{0} Int Int.metricSpace) x r)
but is expected to have type
  forall (x : Int) (r : Real), Eq.{1} (Set.{0} Int) (Set.preimage.{0, 0} Int Real (Int.cast.{0} Real Real.intCast) (Metric.ball.{0} Real Real.pseudoMetricSpace (Int.cast.{0} Real Real.intCast x) r)) (Metric.ball.{0} Int (MetricSpace.toPseudoMetricSpace.{0} Int Int.instMetricSpaceInt) x r)
Case conversion may be inaccurate. Consider using '#align int.preimage_ball Int.preimage_ballₓ'. -/
theorem preimage_ball (x : ℤ) (r : ℝ) : coe ⁻¹' ball (x : ℝ) r = ball x r :=
  rfl
#align int.preimage_ball Int.preimage_ball

/- warning: int.preimage_closed_ball -> Int.preimage_closedBall is a dubious translation:
lean 3 declaration is
  forall (x : Int) (r : Real), Eq.{1} (Set.{0} Int) (Set.preimage.{0, 0} Int Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast)))) (Metric.closedBall.{0} Real Real.pseudoMetricSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) x) r)) (Metric.closedBall.{0} Int (MetricSpace.toPseudoMetricSpace.{0} Int Int.metricSpace) x r)
but is expected to have type
  forall (x : Int) (r : Real), Eq.{1} (Set.{0} Int) (Set.preimage.{0, 0} Int Real (Int.cast.{0} Real Real.intCast) (Metric.closedBall.{0} Real Real.pseudoMetricSpace (Int.cast.{0} Real Real.intCast x) r)) (Metric.closedBall.{0} Int (MetricSpace.toPseudoMetricSpace.{0} Int Int.instMetricSpaceInt) x r)
Case conversion may be inaccurate. Consider using '#align int.preimage_closed_ball Int.preimage_closedBallₓ'. -/
theorem preimage_closedBall (x : ℤ) (r : ℝ) : coe ⁻¹' closedBall (x : ℝ) r = closedBall x r :=
  rfl
#align int.preimage_closed_ball Int.preimage_closedBall

/- warning: int.ball_eq_Ioo -> Int.ball_eq_Ioo is a dubious translation:
lean 3 declaration is
  forall (x : Int) (r : Real), Eq.{1} (Set.{0} Int) (Metric.ball.{0} Int (MetricSpace.toPseudoMetricSpace.{0} Int Int.metricSpace) x r) (Set.Ioo.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (Int.floor.{0} Real Real.linearOrderedRing Real.floorRing (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) x) r)) (Int.ceil.{0} Real Real.linearOrderedRing Real.floorRing (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) x) r)))
but is expected to have type
  forall (x : Int) (r : Real), Eq.{1} (Set.{0} Int) (Metric.ball.{0} Int (MetricSpace.toPseudoMetricSpace.{0} Int Int.instMetricSpaceInt) x r) (Set.Ioo.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (Int.floor.{0} Real Real.instLinearOrderedRingReal Real.instFloorRingRealInstLinearOrderedRingReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Int.cast.{0} Real Real.intCast x) r)) (Int.ceil.{0} Real Real.instLinearOrderedRingReal Real.instFloorRingRealInstLinearOrderedRingReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Int.cast.{0} Real Real.intCast x) r)))
Case conversion may be inaccurate. Consider using '#align int.ball_eq_Ioo Int.ball_eq_Iooₓ'. -/
theorem ball_eq_Ioo (x : ℤ) (r : ℝ) : ball x r = Ioo ⌊↑x - r⌋ ⌈↑x + r⌉ := by
  rw [← preimage_ball, Real.ball_eq_Ioo, preimage_Ioo]
#align int.ball_eq_Ioo Int.ball_eq_Ioo

/- warning: int.closed_ball_eq_Icc -> Int.closedBall_eq_Icc is a dubious translation:
lean 3 declaration is
  forall (x : Int) (r : Real), Eq.{1} (Set.{0} Int) (Metric.closedBall.{0} Int (MetricSpace.toPseudoMetricSpace.{0} Int Int.metricSpace) x r) (Set.Icc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (Int.ceil.{0} Real Real.linearOrderedRing Real.floorRing (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) x) r)) (Int.floor.{0} Real Real.linearOrderedRing Real.floorRing (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) x) r)))
but is expected to have type
  forall (x : Int) (r : Real), Eq.{1} (Set.{0} Int) (Metric.closedBall.{0} Int (MetricSpace.toPseudoMetricSpace.{0} Int Int.instMetricSpaceInt) x r) (Set.Icc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (Int.ceil.{0} Real Real.instLinearOrderedRingReal Real.instFloorRingRealInstLinearOrderedRingReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Int.cast.{0} Real Real.intCast x) r)) (Int.floor.{0} Real Real.instLinearOrderedRingReal Real.instFloorRingRealInstLinearOrderedRingReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Int.cast.{0} Real Real.intCast x) r)))
Case conversion may be inaccurate. Consider using '#align int.closed_ball_eq_Icc Int.closedBall_eq_Iccₓ'. -/
theorem closedBall_eq_Icc (x : ℤ) (r : ℝ) : closedBall x r = Icc ⌈↑x - r⌉ ⌊↑x + r⌋ := by
  rw [← preimage_closed_ball, Real.closedBall_eq_Icc, preimage_Icc]
#align int.closed_ball_eq_Icc Int.closedBall_eq_Icc

instance : ProperSpace ℤ :=
  ⟨by
    intro x r
    rw [closed_ball_eq_Icc]
    exact (Set.finite_Icc _ _).IsCompact⟩

#print Int.cocompact_eq /-
@[simp]
theorem cocompact_eq : cocompact ℤ = atBot ⊔ atTop := by
  simp only [← comap_dist_right_atTop_eq_cocompact (0 : ℤ), dist_eq, sub_zero, cast_zero, ←
    cast_abs, ← @comap_comap _ _ _ _ abs, Int.comap_cast_atTop, comap_abs_at_top]
#align int.cocompact_eq Int.cocompact_eq
-/

/- warning: int.cofinite_eq -> Int.cofinite_eq is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} Int) (Filter.cofinite.{0} Int) (Sup.sup.{0} (Filter.{0} Int) (SemilatticeSup.toHasSup.{0} (Filter.{0} Int) (Lattice.toSemilatticeSup.{0} (Filter.{0} Int) (ConditionallyCompleteLattice.toLattice.{0} (Filter.{0} Int) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} Int) (Filter.completeLattice.{0} Int))))) (Filter.atBot.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (Filter.atTop.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))
but is expected to have type
  Eq.{1} (Filter.{0} Int) (Filter.cofinite.{0} Int) (Sup.sup.{0} (Filter.{0} Int) (SemilatticeSup.toSup.{0} (Filter.{0} Int) (Lattice.toSemilatticeSup.{0} (Filter.{0} Int) (ConditionallyCompleteLattice.toLattice.{0} (Filter.{0} Int) (CompleteLattice.toConditionallyCompleteLattice.{0} (Filter.{0} Int) (Filter.instCompleteLatticeFilter.{0} Int))))) (Filter.atBot.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (Filter.atTop.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))
Case conversion may be inaccurate. Consider using '#align int.cofinite_eq Int.cofinite_eqₓ'. -/
@[simp]
theorem cofinite_eq : (cofinite : Filter ℤ) = atBot ⊔ atTop := by
  rw [← cocompact_eq_cofinite, cocompact_eq]
#align int.cofinite_eq Int.cofinite_eq

end Int

