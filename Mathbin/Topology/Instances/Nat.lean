/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module topology.instances.nat
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Instances.Int

/-!
# Topology on the natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The structure of a metric space on `ℕ` is introduced in this file, induced from `ℝ`.
-/


noncomputable section

open Metric Set Filter

namespace Nat

noncomputable instance : Dist ℕ :=
  ⟨fun x y => dist (x : ℝ) y⟩

/- warning: nat.dist_eq -> Nat.dist_eq is a dubious translation:
lean 3 declaration is
  forall (x : Nat) (y : Nat), Eq.{1} Real (Dist.dist.{0} Nat Nat.hasDist x y) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) y)))
but is expected to have type
  forall (x : Nat) (y : Nat), Eq.{1} Real (Dist.dist.{0} Nat Nat.instDistNat x y) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Nat.cast.{0} Real Real.natCast x) (Nat.cast.{0} Real Real.natCast y)))
Case conversion may be inaccurate. Consider using '#align nat.dist_eq Nat.dist_eqₓ'. -/
theorem dist_eq (x y : ℕ) : dist x y = |x - y| :=
  rfl
#align nat.dist_eq Nat.dist_eq

/- warning: nat.dist_coe_int -> Nat.dist_coe_int is a dubious translation:
lean 3 declaration is
  forall (x : Nat) (y : Nat), Eq.{1} Real (Dist.dist.{0} Int Int.hasDist ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) y)) (Dist.dist.{0} Nat Nat.hasDist x y)
but is expected to have type
  forall (x : Nat) (y : Nat), Eq.{1} Real (Dist.dist.{0} Int Int.instDistInt (Nat.cast.{0} Int Int.instNatCastInt x) (Nat.cast.{0} Int Int.instNatCastInt y)) (Dist.dist.{0} Nat Nat.instDistNat x y)
Case conversion may be inaccurate. Consider using '#align nat.dist_coe_int Nat.dist_coe_intₓ'. -/
theorem dist_coe_int (x y : ℕ) : dist (x : ℤ) (y : ℤ) = dist x y :=
  rfl
#align nat.dist_coe_int Nat.dist_coe_int

/- warning: nat.dist_cast_real -> Nat.dist_cast_real is a dubious translation:
lean 3 declaration is
  forall (x : Nat) (y : Nat), Eq.{1} Real (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) y)) (Dist.dist.{0} Nat Nat.hasDist x y)
but is expected to have type
  forall (x : Nat) (y : Nat), Eq.{1} Real (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) (Nat.cast.{0} Real Real.natCast x) (Nat.cast.{0} Real Real.natCast y)) (Dist.dist.{0} Nat Nat.instDistNat x y)
Case conversion may be inaccurate. Consider using '#align nat.dist_cast_real Nat.dist_cast_realₓ'. -/
@[norm_cast, simp]
theorem dist_cast_real (x y : ℕ) : dist (x : ℝ) y = dist x y :=
  rfl
#align nat.dist_cast_real Nat.dist_cast_real

/- warning: nat.pairwise_one_le_dist -> Nat.pairwise_one_le_dist is a dubious translation:
lean 3 declaration is
  Pairwise.{0} Nat (fun (m : Nat) (n : Nat) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Dist.dist.{0} Nat Nat.hasDist m n))
but is expected to have type
  Pairwise.{0} Nat (fun (m : Nat) (n : Nat) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Dist.dist.{0} Nat Nat.instDistNat m n))
Case conversion may be inaccurate. Consider using '#align nat.pairwise_one_le_dist Nat.pairwise_one_le_distₓ'. -/
theorem pairwise_one_le_dist : Pairwise fun m n : ℕ => 1 ≤ dist m n :=
  by
  intro m n hne
  rw [← dist_coe_int]
  apply Int.pairwise_one_le_dist
  exact_mod_cast hne
#align nat.pairwise_one_le_dist Nat.pairwise_one_le_dist

/- warning: nat.uniform_embedding_coe_real -> Nat.uniformEmbedding_coe_real is a dubious translation:
lean 3 declaration is
  UniformEmbedding.{0, 0} Nat Real Nat.uniformSpace (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))))
but is expected to have type
  UniformEmbedding.{0, 0} Nat Real instUniformSpaceNat (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) (Nat.cast.{0} Real Real.natCast)
Case conversion may be inaccurate. Consider using '#align nat.uniform_embedding_coe_real Nat.uniformEmbedding_coe_realₓ'. -/
theorem uniformEmbedding_coe_real : UniformEmbedding (coe : ℕ → ℝ) :=
  uniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align nat.uniform_embedding_coe_real Nat.uniformEmbedding_coe_real

/- warning: nat.closed_embedding_coe_real -> Nat.closedEmbedding_coe_real is a dubious translation:
lean 3 declaration is
  ClosedEmbedding.{0, 0} Nat Real Nat.topologicalSpace (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))))
but is expected to have type
  ClosedEmbedding.{0, 0} Nat Real instTopologicalSpaceNat (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Nat.cast.{0} Real Real.natCast)
Case conversion may be inaccurate. Consider using '#align nat.closed_embedding_coe_real Nat.closedEmbedding_coe_realₓ'. -/
theorem closedEmbedding_coe_real : ClosedEmbedding (coe : ℕ → ℝ) :=
  closedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align nat.closed_embedding_coe_real Nat.closedEmbedding_coe_real

instance : MetricSpace ℕ :=
  Nat.uniformEmbedding_coe_real.comapMetricSpace _

/- warning: nat.preimage_ball -> Nat.preimage_ball is a dubious translation:
lean 3 declaration is
  forall (x : Nat) (r : Real), Eq.{1} (Set.{0} Nat) (Set.preimage.{0, 0} Nat Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast)))) (Metric.ball.{0} Real Real.pseudoMetricSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) x) r)) (Metric.ball.{0} Nat (MetricSpace.toPseudoMetricSpace.{0} Nat Nat.metricSpace) x r)
but is expected to have type
  forall (x : Nat) (r : Real), Eq.{1} (Set.{0} Nat) (Set.preimage.{0, 0} Nat Real (Nat.cast.{0} Real Real.natCast) (Metric.ball.{0} Real Real.pseudoMetricSpace (Nat.cast.{0} Real Real.natCast x) r)) (Metric.ball.{0} Nat (MetricSpace.toPseudoMetricSpace.{0} Nat Nat.instMetricSpaceNat) x r)
Case conversion may be inaccurate. Consider using '#align nat.preimage_ball Nat.preimage_ballₓ'. -/
theorem preimage_ball (x : ℕ) (r : ℝ) : coe ⁻¹' ball (x : ℝ) r = ball x r :=
  rfl
#align nat.preimage_ball Nat.preimage_ball

/- warning: nat.preimage_closed_ball -> Nat.preimage_closedBall is a dubious translation:
lean 3 declaration is
  forall (x : Nat) (r : Real), Eq.{1} (Set.{0} Nat) (Set.preimage.{0, 0} Nat Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast)))) (Metric.closedBall.{0} Real Real.pseudoMetricSpace ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) x) r)) (Metric.closedBall.{0} Nat (MetricSpace.toPseudoMetricSpace.{0} Nat Nat.metricSpace) x r)
but is expected to have type
  forall (x : Nat) (r : Real), Eq.{1} (Set.{0} Nat) (Set.preimage.{0, 0} Nat Real (Nat.cast.{0} Real Real.natCast) (Metric.closedBall.{0} Real Real.pseudoMetricSpace (Nat.cast.{0} Real Real.natCast x) r)) (Metric.closedBall.{0} Nat (MetricSpace.toPseudoMetricSpace.{0} Nat Nat.instMetricSpaceNat) x r)
Case conversion may be inaccurate. Consider using '#align nat.preimage_closed_ball Nat.preimage_closedBallₓ'. -/
theorem preimage_closedBall (x : ℕ) (r : ℝ) : coe ⁻¹' closedBall (x : ℝ) r = closedBall x r :=
  rfl
#align nat.preimage_closed_ball Nat.preimage_closedBall

/- warning: nat.closed_ball_eq_Icc -> Nat.closedBall_eq_Icc is a dubious translation:
lean 3 declaration is
  forall (x : Nat) (r : Real), Eq.{1} (Set.{0} Nat) (Metric.closedBall.{0} Nat (MetricSpace.toPseudoMetricSpace.{0} Nat Nat.metricSpace) x r) (Set.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (Nat.ceil.{0} Real Real.orderedSemiring (FloorRing.toFloorSemiring.{0} Real Real.linearOrderedRing Real.floorRing) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) x) r)) (Nat.floor.{0} Real Real.orderedSemiring (FloorRing.toFloorSemiring.{0} Real Real.linearOrderedRing Real.floorRing) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) x) r)))
but is expected to have type
  forall (x : Nat) (r : Real), Eq.{1} (Set.{0} Nat) (Metric.closedBall.{0} Nat (MetricSpace.toPseudoMetricSpace.{0} Nat Nat.instMetricSpaceNat) x r) (Set.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (Nat.ceil.{0} Real Real.orderedSemiring (FloorRing.toFloorSemiring.{0} Real Real.instLinearOrderedRingReal Real.instFloorRingRealInstLinearOrderedRingReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Nat.cast.{0} Real Real.natCast x) r)) (Nat.floor.{0} Real Real.orderedSemiring (FloorRing.toFloorSemiring.{0} Real Real.instLinearOrderedRingReal Real.instFloorRingRealInstLinearOrderedRingReal) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast x) r)))
Case conversion may be inaccurate. Consider using '#align nat.closed_ball_eq_Icc Nat.closedBall_eq_Iccₓ'. -/
theorem closedBall_eq_Icc (x : ℕ) (r : ℝ) : closedBall x r = Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊ :=
  by
  rcases le_or_lt 0 r with (hr | hr)
  · rw [← preimage_closed_ball, Real.closedBall_eq_Icc, preimage_Icc]
    exact add_nonneg (cast_nonneg x) hr
  · rw [closed_ball_eq_empty.2 hr]
    apply (Icc_eq_empty _).symm
    rw [not_le]
    calc
      ⌊(x : ℝ) + r⌋₊ ≤ ⌊(x : ℝ)⌋₊ := by
        apply floor_mono
        linarith
      _ < ⌈↑x - r⌉₊ := by
        rw [floor_coe, Nat.lt_ceil]
        linarith
      
#align nat.closed_ball_eq_Icc Nat.closedBall_eq_Icc

instance : ProperSpace ℕ :=
  ⟨by
    intro x r
    rw [closed_ball_eq_Icc]
    exact (Set.finite_Icc _ _).IsCompact⟩

instance : NoncompactSpace ℕ :=
  noncompactSpace_of_neBot <| by simp [Filter.atTop_neBot]

end Nat

