/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module measure_theory.measure.doubling
! leanprover-community/mathlib commit 5f6e827d81dfbeb6151d7016586ceeb0099b9655
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Log.Base
import Mathbin.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Uniformly locally doubling measures

A uniformly locally doubling measure `μ` on a metric space is a measure for which there exists a
constant `C` such that for all sufficiently small radii `ε`, and for any centre, the measure of a
ball of radius `2 * ε` is bounded by `C` times the measure of the concentric ball of radius `ε`.

This file records basic facts about uniformly locally doubling measures.

## Main definitions

  * `is_unif_loc_doubling_measure`: the definition of a uniformly locally doubling measure (as a
  typeclass).
  * `is_unif_loc_doubling_measure.doubling_constant`: a function yielding the doubling constant `C`
  appearing in the definition of a uniformly locally doubling measure.
-/


noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace

open ENNReal NNReal Topology

#print IsUnifLocDoublingMeasure /-
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`exists_measure_closedBall_le_mul] [] -/
/-- A measure `μ` is said to be a uniformly locally doubling measure if there exists a constant `C`
such that for all sufficiently small radii `ε`, and for any centre, the measure of a ball of radius
`2 * ε` is bounded by `C` times the measure of the concentric ball of radius `ε`.

Note: it is important that this definition makes a demand only for sufficiently small `ε`. For
example we want hyperbolic space to carry the instance `is_unif_loc_doubling_measure volume` but
volumes grow exponentially in hyperbolic space. To be really explicit, consider the hyperbolic plane
of curvature -1, the area of a disc of radius `ε` is `A(ε) = 2π(cosh(ε) - 1)` so
`A(2ε)/A(ε) ~ exp(ε)`. -/
class IsUnifLocDoublingMeasure {α : Type _} [MetricSpace α] [MeasurableSpace α]
  (μ : Measure α) where
  exists_measure_closedBall_le_mul :
    ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ C * μ (closedBall x ε)
#align is_unif_loc_doubling_measure IsUnifLocDoublingMeasure
-/

namespace IsUnifLocDoublingMeasure

variable {α : Type _} [MetricSpace α] [MeasurableSpace α] (μ : Measure α)
  [IsUnifLocDoublingMeasure μ]

#print IsUnifLocDoublingMeasure.doublingConstant /-
/-- A doubling constant for a uniformly locally doubling measure.

See also `is_unif_loc_doubling_measure.scaling_constant_of`. -/
def doublingConstant : ℝ≥0 :=
  Classical.choose <| exists_measure_closedBall_le_mul μ
#align is_unif_loc_doubling_measure.doubling_constant IsUnifLocDoublingMeasure.doublingConstant
-/

/- warning: is_unif_loc_doubling_measure.exists_measure_closed_ball_le_mul' -> IsUnifLocDoublingMeasure.exists_measure_closedBall_le_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ], Filter.Eventually.{0} Real (fun (ε : Real) => forall (x : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) ε))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (IsUnifLocDoublingMeasure.doublingConstant.{u1} α _inst_1 _inst_2 μ _inst_3)) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε)))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ], Filter.Eventually.{0} Real (fun (ε : Real) => forall (x : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) ε))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some (IsUnifLocDoublingMeasure.doublingConstant.{u1} α _inst_1 _inst_2 μ _inst_3)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε)))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align is_unif_loc_doubling_measure.exists_measure_closed_ball_le_mul' IsUnifLocDoublingMeasure.exists_measure_closedBall_le_mul'ₓ'. -/
theorem exists_measure_closedBall_le_mul' :
    ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ doublingConstant μ * μ (closedBall x ε) :=
  Classical.choose_spec <| exists_measure_closedBall_le_mul μ
#align is_unif_loc_doubling_measure.exists_measure_closed_ball_le_mul' IsUnifLocDoublingMeasure.exists_measure_closedBall_le_mul'

/- warning: is_unif_loc_doubling_measure.exists_eventually_forall_measure_closed_ball_le_mul -> IsUnifLocDoublingMeasure.exists_eventually_forall_measure_closedBall_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] (K : Real), Exists.{1} NNReal (fun (C : NNReal) => Filter.Eventually.{0} Real (fun (ε : Real) => forall (x : α) (t : Real), (LE.le.{0} Real Real.hasLe t K) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) t ε))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε))))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] (K : Real), Exists.{1} NNReal (fun (C : NNReal) => Filter.Eventually.{0} Real (fun (ε : Real) => forall (x : α) (t : Real), (LE.le.{0} Real Real.instLEReal t K) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) t ε))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε))))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))))
Case conversion may be inaccurate. Consider using '#align is_unif_loc_doubling_measure.exists_eventually_forall_measure_closed_ball_le_mul IsUnifLocDoublingMeasure.exists_eventually_forall_measure_closedBall_le_mulₓ'. -/
theorem exists_eventually_forall_measure_closedBall_le_mul (K : ℝ) :
    ∃ C : ℝ≥0,
      ∀ᶠ ε in 𝓝[>] 0, ∀ (x t) (ht : t ≤ K), μ (closedBall x (t * ε)) ≤ C * μ (closedBall x ε) :=
  by
  let C := doubling_constant μ
  have hμ :
    ∀ n : ℕ, ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closed_ball x (2 ^ n * ε)) ≤ ↑(C ^ n) * μ (closed_ball x ε) :=
    by
    intro n
    induction' n with n ih
    · simp
    replace ih := eventually_nhdsWithin_pos_mul_left (two_pos : 0 < (2 : ℝ)) ih
    refine' (ih.and (exists_measure_closed_ball_le_mul' μ)).mono fun ε hε x => _
    calc
      μ (closed_ball x (2 ^ (n + 1) * ε)) = μ (closed_ball x (2 ^ n * (2 * ε))) := by
        rw [pow_succ', mul_assoc]
      _ ≤ ↑(C ^ n) * μ (closed_ball x (2 * ε)) := (hε.1 x)
      _ ≤ ↑(C ^ n) * (C * μ (closed_ball x ε)) := (ENNReal.mul_left_mono (hε.2 x))
      _ = ↑(C ^ (n + 1)) * μ (closed_ball x ε) := by rw [← mul_assoc, pow_succ', ENNReal.coe_mul]
      
  rcases lt_or_le K 1 with (hK | hK)
  · refine' ⟨1, _⟩
    simp only [ENNReal.coe_one, one_mul]
    exact
      eventually_mem_nhds_within.mono fun ε hε x t ht =>
        measure_mono <| closed_ball_subset_closed_ball (by nlinarith [mem_Ioi.mp hε])
  · refine'
      ⟨C ^ ⌈Real.logb 2 K⌉₊,
        ((hμ ⌈Real.logb 2 K⌉₊).And eventually_mem_nhdsWithin).mono fun ε hε x t ht =>
          le_trans (measure_mono <| closed_ball_subset_closed_ball _) (hε.1 x)⟩
    refine' mul_le_mul_of_nonneg_right (ht.trans _) (mem_Ioi.mp hε.2).le
    conv_lhs => rw [← Real.rpow_logb two_pos (by norm_num) (by linarith : 0 < K)]
    rw [← Real.rpow_nat_cast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil (Real.logb 2 K))
#align is_unif_loc_doubling_measure.exists_eventually_forall_measure_closed_ball_le_mul IsUnifLocDoublingMeasure.exists_eventually_forall_measure_closedBall_le_mul

#print IsUnifLocDoublingMeasure.scalingConstantOf /-
/-- A variant of `is_unif_loc_doubling_measure.doubling_constant` which allows for scaling the
radius by values other than `2`. -/
def scalingConstantOf (K : ℝ) : ℝ≥0 :=
  max (Classical.choose <| exists_eventually_forall_measure_closedBall_le_mul μ K) 1
#align is_unif_loc_doubling_measure.scaling_constant_of IsUnifLocDoublingMeasure.scalingConstantOf
-/

/- warning: is_unif_loc_doubling_measure.one_le_scaling_constant_of -> IsUnifLocDoublingMeasure.one_le_scalingConstantOf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] (K : Real), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (IsUnifLocDoublingMeasure.scalingConstantOf.{u1} α _inst_1 _inst_2 μ _inst_3 K)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] (K : Real), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (IsUnifLocDoublingMeasure.scalingConstantOf.{u1} α _inst_1 _inst_2 μ _inst_3 K)
Case conversion may be inaccurate. Consider using '#align is_unif_loc_doubling_measure.one_le_scaling_constant_of IsUnifLocDoublingMeasure.one_le_scalingConstantOfₓ'. -/
@[simp]
theorem one_le_scalingConstantOf (K : ℝ) : 1 ≤ scalingConstantOf μ K :=
  le_max_of_le_right <| le_refl 1
#align is_unif_loc_doubling_measure.one_le_scaling_constant_of IsUnifLocDoublingMeasure.one_le_scalingConstantOf

/- warning: is_unif_loc_doubling_measure.eventually_measure_mul_le_scaling_constant_of_mul -> IsUnifLocDoublingMeasure.eventually_measure_mul_le_scalingConstantOf_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] (K : Real), Exists.{1} Real (fun (R : Real) => And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) R) (forall (x : α) (t : Real) (r : Real), (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) t (Set.Ioc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) K)) -> (LE.le.{0} Real Real.hasLe r R) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) t r))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (IsUnifLocDoublingMeasure.scalingConstantOf.{u1} α _inst_1 _inst_2 μ _inst_3 K)) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x r))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] (K : Real), Exists.{1} Real (fun (R : Real) => And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) R) (forall (x : α) (t : Real) (r : Real), (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) t (Set.Ioc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) K)) -> (LE.le.{0} Real Real.instLEReal r R) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) t r))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some (IsUnifLocDoublingMeasure.scalingConstantOf.{u1} α _inst_1 _inst_2 μ _inst_3 K)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x r))))))
Case conversion may be inaccurate. Consider using '#align is_unif_loc_doubling_measure.eventually_measure_mul_le_scaling_constant_of_mul IsUnifLocDoublingMeasure.eventually_measure_mul_le_scalingConstantOf_mulₓ'. -/
theorem eventually_measure_mul_le_scalingConstantOf_mul (K : ℝ) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ (x t r) (ht : t ∈ Ioc 0 K) (hr : r ≤ R),
          μ (closedBall x (t * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) :=
  by
  have h := Classical.choose_spec (exists_eventually_forall_measure_closed_ball_le_mul μ K)
  rcases mem_nhdsWithin_Ioi_iff_exists_Ioc_subset.1 h with ⟨R, Rpos, hR⟩
  refine' ⟨R, Rpos, fun x t r ht hr => _⟩
  rcases lt_trichotomy r 0 with (rneg | rfl | rpos)
  · have : t * r < 0 := mul_neg_of_pos_of_neg ht.1 rneg
    simp only [closed_ball_eq_empty.2 this, measure_empty, zero_le']
  · simp only [MulZeroClass.mul_zero, closed_ball_zero]
    refine' le_mul_of_one_le_of_le _ le_rfl
    apply ENNReal.one_le_coe_iff.2 (le_max_right _ _)
  · apply (hR ⟨rpos, hr⟩ x t ht.2).trans _
    exact mul_le_mul_right' (ENNReal.coe_le_coe.2 (le_max_left _ _)) _
#align is_unif_loc_doubling_measure.eventually_measure_mul_le_scaling_constant_of_mul IsUnifLocDoublingMeasure.eventually_measure_mul_le_scalingConstantOf_mul

/- warning: is_unif_loc_doubling_measure.eventually_measure_le_scaling_constant_mul -> IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] (K : Real), Filter.Eventually.{0} Real (fun (r : Real) => forall (x : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) K r))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (IsUnifLocDoublingMeasure.scalingConstantOf.{u1} α _inst_1 _inst_2 μ _inst_3 K)) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x r)))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] (K : Real), Filter.Eventually.{0} Real (fun (r : Real) => forall (x : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) K r))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some (IsUnifLocDoublingMeasure.scalingConstantOf.{u1} α _inst_1 _inst_2 μ _inst_3 K)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x r)))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align is_unif_loc_doubling_measure.eventually_measure_le_scaling_constant_mul IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mulₓ'. -/
theorem eventually_measure_le_scaling_constant_mul (K : ℝ) :
    ∀ᶠ r in 𝓝[>] 0, ∀ x, μ (closedBall x (K * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) :=
  by
  filter_upwards [Classical.choose_spec
      (exists_eventually_forall_measure_closed_ball_le_mul μ K)]with r hr x
  exact (hr x K le_rfl).trans (mul_le_mul_right' (ENNReal.coe_le_coe.2 (le_max_left _ _)) _)
#align is_unif_loc_doubling_measure.eventually_measure_le_scaling_constant_mul IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul

/- warning: is_unif_loc_doubling_measure.eventually_measure_le_scaling_constant_mul' -> IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] (K : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) K) -> (Filter.Eventually.{0} Real (fun (r : Real) => forall (x : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x r)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (IsUnifLocDoublingMeasure.scalingConstantOf.{u1} α _inst_1 _inst_2 μ _inst_3 (Inv.inv.{0} Real Real.hasInv K))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) K r))))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] (K : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) K) -> (Filter.Eventually.{0} Real (fun (r : Real) => forall (x : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x r)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some (IsUnifLocDoublingMeasure.scalingConstantOf.{u1} α _inst_1 _inst_2 μ _inst_3 (Inv.inv.{0} Real Real.instInvReal K))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) K r))))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))))
Case conversion may be inaccurate. Consider using '#align is_unif_loc_doubling_measure.eventually_measure_le_scaling_constant_mul' IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul'ₓ'. -/
theorem eventually_measure_le_scaling_constant_mul' (K : ℝ) (hK : 0 < K) :
    ∀ᶠ r in 𝓝[>] 0, ∀ x, μ (closedBall x r) ≤ scalingConstantOf μ K⁻¹ * μ (closedBall x (K * r)) :=
  by
  convert eventually_nhdsWithin_pos_mul_left hK (eventually_measure_le_scaling_constant_mul μ K⁻¹)
  ext
  simp [inv_mul_cancel_left₀ hK.ne']
#align is_unif_loc_doubling_measure.eventually_measure_le_scaling_constant_mul' IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul'

#print IsUnifLocDoublingMeasure.scalingScaleOf /-
/-- A scale below which the doubling measure `μ` satisfies good rescaling properties when one
multiplies the radius of balls by at most `K`, as stated
in `measure_mul_le_scaling_constant_of_mul`. -/
def scalingScaleOf (K : ℝ) : ℝ :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).some
#align is_unif_loc_doubling_measure.scaling_scale_of IsUnifLocDoublingMeasure.scalingScaleOf
-/

/- warning: is_unif_loc_doubling_measure.scaling_scale_of_pos -> IsUnifLocDoublingMeasure.scalingScaleOf_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] (K : Real), LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (IsUnifLocDoublingMeasure.scalingScaleOf.{u1} α _inst_1 _inst_2 μ _inst_3 K)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] (K : Real), LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (IsUnifLocDoublingMeasure.scalingScaleOf.{u1} α _inst_1 _inst_2 μ _inst_3 K)
Case conversion may be inaccurate. Consider using '#align is_unif_loc_doubling_measure.scaling_scale_of_pos IsUnifLocDoublingMeasure.scalingScaleOf_posₓ'. -/
theorem scalingScaleOf_pos (K : ℝ) : 0 < scalingScaleOf μ K :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.1
#align is_unif_loc_doubling_measure.scaling_scale_of_pos IsUnifLocDoublingMeasure.scalingScaleOf_pos

/- warning: is_unif_loc_doubling_measure.measure_mul_le_scaling_constant_of_mul -> IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] {K : Real} {x : α} {t : Real} {r : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) t (Set.Ioc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) K)) -> (LE.le.{0} Real Real.hasLe r (IsUnifLocDoublingMeasure.scalingScaleOf.{u1} α _inst_1 _inst_2 μ _inst_3 K)) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) t r))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (IsUnifLocDoublingMeasure.scalingConstantOf.{u1} α _inst_1 _inst_2 μ _inst_3 K)) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x r))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_3 : IsUnifLocDoublingMeasure.{u1} α _inst_1 _inst_2 μ] {K : Real} {x : α} {t : Real} {r : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) t (Set.Ioc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) K)) -> (LE.le.{0} Real Real.instLEReal r (IsUnifLocDoublingMeasure.scalingScaleOf.{u1} α _inst_1 _inst_2 μ _inst_3 K)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) t r))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some (IsUnifLocDoublingMeasure.scalingConstantOf.{u1} α _inst_1 _inst_2 μ _inst_3 K)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x r))))
Case conversion may be inaccurate. Consider using '#align is_unif_loc_doubling_measure.measure_mul_le_scaling_constant_of_mul IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mulₓ'. -/
theorem measure_mul_le_scalingConstantOf_mul {K : ℝ} {x : α} {t r : ℝ} (ht : t ∈ Ioc 0 K)
    (hr : r ≤ scalingScaleOf μ K) :
    μ (closedBall x (t * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.2 x t r ht hr
#align is_unif_loc_doubling_measure.measure_mul_le_scaling_constant_of_mul IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul

end IsUnifLocDoublingMeasure

