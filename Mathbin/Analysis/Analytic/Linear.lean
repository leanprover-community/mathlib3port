/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module analysis.analytic.linear
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Analytic.Basic

/-!
# Linear functions are analytic

In this file we prove that a `continuous_linear_map` defines an analytic function with
the formal power series `f x = f a + f (x - a)`.
-/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open Topology Classical BigOperators NNReal ENNReal

open Set Filter Asymptotics

noncomputable section

namespace ContinuousLinearMap

/- warning: continuous_linear_map.fpower_series -> ContinuousLinearMap.fpowerSeries is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)], (ContinuousLinearMap.{u1, u1, u2, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)) -> E -> (FormalMultilinearSeries.{u1, u2, u3} 𝕜 E F (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (ContinuousLinearMap.FpowerSeries._proof_1.{u2} E _inst_2) (ContinuousLinearMap.FpowerSeries._proof_2.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (ContinuousLinearMap.FpowerSeries._proof_3.{u3} F _inst_4) (ContinuousLinearMap.FpowerSeries._proof_4.{u1, u3} 𝕜 _inst_1 F _inst_4 _inst_5))
but is expected to have type
  PUnit.{max (max (succ (succ u1)) (succ (succ u2))) (succ (succ u3))}
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.fpower_series ContinuousLinearMap.fpowerSeriesₓ'. -/
/-- Formal power series of a continuous linear map `f : E →L[𝕜] F` at `x : E`:
`f y = f x + f (y - x)`. -/
@[simp]
def fpowerSeries (f : E →L[𝕜] F) (x : E) : FormalMultilinearSeries 𝕜 E F
  | 0 => ContinuousMultilinearMap.curry0 𝕜 _ (f x)
  | 1 => (continuousMultilinearCurryFin1 𝕜 E F).symm f
  | _ => 0
#align continuous_linear_map.fpower_series ContinuousLinearMap.fpowerSeries

@[simp]
theorem fpowerSeries_apply_add_two (f : E →L[𝕜] F) (x : E) (n : ℕ) : f.fpowerSeries x (n + 2) = 0 :=
  rfl
#align continuous_linear_map.fpower_series_apply_add_two ContinuousLinearMap.fpowerSeries_apply_add_two

@[simp]
theorem fpowerSeries_radius (f : E →L[𝕜] F) (x : E) : (f.fpowerSeries x).radius = ∞ :=
  (f.fpowerSeries x).radius_eq_top_of_forall_image_add_eq_zero 2 fun n => rfl
#align continuous_linear_map.fpower_series_radius ContinuousLinearMap.fpowerSeries_radius

protected theorem hasFpowerSeriesOnBall (f : E →L[𝕜] F) (x : E) :
    HasFpowerSeriesOnBall f (f.fpowerSeries x) x ∞ :=
  { r_le := by simp
    r_pos := ENNReal.coe_lt_top
    HasSum := fun y _ =>
      (hasSum_nat_add_iff' 2).1 <| by simp [Finset.sum_range_succ, ← sub_sub, hasSum_zero] }
#align continuous_linear_map.has_fpower_series_on_ball ContinuousLinearMap.hasFpowerSeriesOnBall

protected theorem hasFpowerSeriesAt (f : E →L[𝕜] F) (x : E) :
    HasFpowerSeriesAt f (f.fpowerSeries x) x :=
  ⟨∞, f.HasFpowerSeriesOnBall x⟩
#align continuous_linear_map.has_fpower_series_at ContinuousLinearMap.hasFpowerSeriesAt

protected theorem analyticAt (f : E →L[𝕜] F) (x : E) : AnalyticAt 𝕜 f x :=
  (f.HasFpowerSeriesAt x).AnalyticAt
#align continuous_linear_map.analytic_at ContinuousLinearMap.analyticAt

/-- Reinterpret a bilinear map `f : E →L[𝕜] F →L[𝕜] G` as a multilinear map
`(E × F) [×2]→L[𝕜] G`. This multilinear map is the second term in the formal
multilinear series expansion of `uncurry f`. It is given by
`f.uncurry_bilinear ![(x, y), (x', y')] = f x y'`. -/
def uncurryBilinear (f : E →L[𝕜] F →L[𝕜] G) : E × F[×2]→L[𝕜] G :=
  @ContinuousLinearMap.uncurryLeft 𝕜 1 (fun _ => E × F) G _ _ _ _ _ <|
    (↑(continuousMultilinearCurryFin1 𝕜 (E × F) G).symm : (E × F →L[𝕜] G) →L[𝕜] _).comp <|
      f.bilinearComp (fst _ _ _) (snd _ _ _)
#align continuous_linear_map.uncurry_bilinear ContinuousLinearMap.uncurryBilinear

@[simp]
theorem uncurryBilinear_apply (f : E →L[𝕜] F →L[𝕜] G) (m : Fin 2 → E × F) :
    f.uncurryBilinear m = f (m 0).1 (m 1).2 :=
  rfl
#align continuous_linear_map.uncurry_bilinear_apply ContinuousLinearMap.uncurryBilinear_apply

/- warning: continuous_linear_map.fpower_series_bilinear -> ContinuousLinearMap.fpowerSeriesBilinear is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)], (ContinuousLinearMap.{u1, u1, u2, max u3 u4} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (ContinuousLinearMap.{u1, u1, u3, u4} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) G (UniformSpace.toTopologicalSpace.{u4} G (PseudoMetricSpace.toUniformSpace.{u4} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)))) (AddCommGroup.toAddCommMonoid.{u4} G (NormedAddCommGroup.toAddCommGroup.{u4} G _inst_6)) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) (NormedSpace.toModule.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7)) (ContinuousLinearMap.topologicalSpace.{u1, u1, u3, u4} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) F G (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) (NormedAddCommGroup.toAddCommGroup.{u4} G _inst_6) (NormedSpace.toModule.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (UniformSpace.toTopologicalSpace.{u4} G (PseudoMetricSpace.toUniformSpace.{u4} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)))) (ContinuousLinearMap.FpowerSeriesBilinear._proof_1.{u4} G _inst_6)) (ContinuousLinearMap.addCommMonoid.{u1, u1, u3, u4} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) G (UniformSpace.toTopologicalSpace.{u4} G (PseudoMetricSpace.toUniformSpace.{u4} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)))) (AddCommGroup.toAddCommMonoid.{u4} G (NormedAddCommGroup.toAddCommGroup.{u4} G _inst_6)) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) (NormedSpace.toModule.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) (ContinuousLinearMap.FpowerSeriesBilinear._proof_2.{u4} G _inst_6)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (ContinuousLinearMap.module.{u1, u1, u1, u3, u4} 𝕜 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) G (UniformSpace.toTopologicalSpace.{u4} G (PseudoMetricSpace.toUniformSpace.{u4} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)))) (AddCommGroup.toAddCommMonoid.{u4} G (NormedAddCommGroup.toAddCommGroup.{u4} G _inst_6)) (NormedSpace.toModule.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) (NormedSpace.toModule.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) (ContinuousLinearMap.FpowerSeriesBilinear._proof_3.{u1, u4} 𝕜 _inst_1 G _inst_6 _inst_7) (ContinuousLinearMap.FpowerSeriesBilinear._proof_4.{u1, u4} 𝕜 _inst_1 G _inst_6 _inst_7) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (ContinuousLinearMap.FpowerSeriesBilinear._proof_5.{u4} G _inst_6))) -> (Prod.{u2, u3} E F) -> (FormalMultilinearSeries.{u1, max u2 u3, u4} 𝕜 (Prod.{u2, u3} E F) G (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))) (Prod.addCommGroup.{u2, u3} E F (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (Prod.module.{u1, u2, u3} 𝕜 E F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)) (Prod.topologicalSpace.{u2, u3} E F (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4))))) (ContinuousLinearMap.FpowerSeriesBilinear._proof_6.{u2, u3} E _inst_2 F _inst_4) (ContinuousLinearMap.FpowerSeriesBilinear._proof_7.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5) (NormedAddCommGroup.toAddCommGroup.{u4} G _inst_6) (NormedSpace.toModule.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) (UniformSpace.toTopologicalSpace.{u4} G (PseudoMetricSpace.toUniformSpace.{u4} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)))) (ContinuousLinearMap.FpowerSeriesBilinear._proof_8.{u4} G _inst_6) (ContinuousLinearMap.FpowerSeriesBilinear._proof_9.{u1, u4} 𝕜 _inst_1 G _inst_6 _inst_7))
but is expected to have type
  PUnit.{max (max (max (succ (succ u1)) (succ (succ u2))) (succ (succ u3))) (succ (succ u4))}
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.fpower_series_bilinear ContinuousLinearMap.fpowerSeriesBilinearₓ'. -/
/-- Formal multilinear series expansion of a bilinear function `f : E →L[𝕜] F →L[𝕜] G`. -/
@[simp]
def fpowerSeriesBilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) : FormalMultilinearSeries 𝕜 (E × F) G
  | 0 => ContinuousMultilinearMap.curry0 𝕜 _ (f x.1 x.2)
  | 1 => (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x)
  | 2 => f.uncurryBilinear
  | _ => 0
#align continuous_linear_map.fpower_series_bilinear ContinuousLinearMap.fpowerSeriesBilinear

@[simp]
theorem fpowerSeriesBilinear_radius (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    (f.fpowerSeriesBilinear x).radius = ∞ :=
  (f.fpowerSeriesBilinear x).radius_eq_top_of_forall_image_add_eq_zero 3 fun n => rfl
#align continuous_linear_map.fpower_series_bilinear_radius ContinuousLinearMap.fpowerSeriesBilinear_radius

protected theorem hasFpowerSeriesOnBallBilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    HasFpowerSeriesOnBall (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x ∞ :=
  { r_le := by simp
    r_pos := ENNReal.coe_lt_top
    HasSum := fun y _ =>
      (hasSum_nat_add_iff' 3).1 <|
        by
        simp only [Finset.sum_range_succ, Finset.sum_range_one, Prod.fst_add, Prod.snd_add,
          f.map_add_add]
        dsimp; simp only [add_comm, sub_self, hasSum_zero] }
#align continuous_linear_map.has_fpower_series_on_ball_bilinear ContinuousLinearMap.hasFpowerSeriesOnBallBilinear

protected theorem hasFpowerSeriesAtBilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    HasFpowerSeriesAt (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x :=
  ⟨∞, f.hasFpowerSeriesOnBallBilinear x⟩
#align continuous_linear_map.has_fpower_series_at_bilinear ContinuousLinearMap.hasFpowerSeriesAtBilinear

protected theorem analyticAt_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    AnalyticAt 𝕜 (fun x : E × F => f x.1 x.2) x :=
  (f.hasFpowerSeriesAtBilinear x).AnalyticAt
#align continuous_linear_map.analytic_at_bilinear ContinuousLinearMap.analyticAt_bilinear

end ContinuousLinearMap

