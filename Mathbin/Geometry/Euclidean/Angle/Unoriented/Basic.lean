/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales

! This file was ported from Lean 3 source module geometry.euclidean.angle.unoriented.basic
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Angles between vectors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines unoriented angles in real inner product spaces.

## Main definitions

* `inner_product_geometry.angle` is the undirected angle between two vectors.

-/


assert_not_exists HasFDerivAt

assert_not_exists ConformalAt

noncomputable section

open Real Set

open BigOperators

open Real

open RealInnerProductSpace

namespace InnerProductGeometry

variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {x y : V}

#print InnerProductGeometry.angle /-
/-- The undirected angle between two vectors. If either vector is 0,
this is π/2. See `orientation.oangle` for the corresponding oriented angle
definition. -/
def angle (x y : V) : ℝ :=
  Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))
#align inner_product_geometry.angle InnerProductGeometry.angle
-/

/- warning: inner_product_geometry.continuous_at_angle -> InnerProductGeometry.continuousAt_angle is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : Prod.{u1, u1} V V}, (Ne.{succ u1} V (Prod.fst.{u1, u1} V V x) (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Ne.{succ u1} V (Prod.snd.{u1, u1} V V x) (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (ContinuousAt.{u1, 0} (Prod.{u1, u1} V V) Real (Prod.topologicalSpace.{u1, u1} V V (UniformSpace.toTopologicalSpace.{u1} V (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} V (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (y : Prod.{u1, u1} V V) => InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (Prod.fst.{u1, u1} V V y) (Prod.snd.{u1, u1} V V y)) x)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : Prod.{u1, u1} V V}, (Ne.{succ u1} V (Prod.fst.{u1, u1} V V x) (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Ne.{succ u1} V (Prod.snd.{u1, u1} V V x) (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (ContinuousAt.{u1, 0} (Prod.{u1, u1} V V) Real (instTopologicalSpaceProd.{u1, u1} V V (UniformSpace.toTopologicalSpace.{u1} V (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} V (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (y : Prod.{u1, u1} V V) => InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (Prod.fst.{u1, u1} V V y) (Prod.snd.{u1, u1} V V y)) x)
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.continuous_at_angle InnerProductGeometry.continuousAt_angleₓ'. -/
theorem continuousAt_angle {x : V × V} (hx1 : x.1 ≠ 0) (hx2 : x.2 ≠ 0) :
    ContinuousAt (fun y : V × V => angle y.1 y.2) x :=
  Real.continuous_arccos.ContinuousAt.comp <|
    continuous_inner.ContinuousAt.div
      ((continuous_norm.comp continuous_fst).mul (continuous_norm.comp continuous_snd)).ContinuousAt
      (by simp [hx1, hx2])
#align inner_product_geometry.continuous_at_angle InnerProductGeometry.continuousAt_angle

/- warning: inner_product_geometry.angle_smul_smul -> InnerProductGeometry.angle_smul_smul is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {c : Real}, (Ne.{1} Real c (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (x : V) (y : V), Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (SMul.smul.{0, u1} Real V (SMulZeroClass.toHasSmul.{0, u1} Real V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real V (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedSpace.toModule.{0, u1} Real V (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)))))) c x) (SMul.smul.{0, u1} Real V (SMulZeroClass.toHasSmul.{0, u1} Real V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real V (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedSpace.toModule.{0, u1} Real V (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)))))) c y)) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {c : Real}, (Ne.{1} Real c (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (x : V) (y : V), Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (HSMul.hSMul.{0, u1, u1} Real V V (instHSMul.{0, u1} Real V (SMulZeroClass.toSMul.{0, u1} Real V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real V Real.instZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V Real.semiring (AddCommGroup.toAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2))))))) c x) (HSMul.hSMul.{0, u1, u1} Real V V (instHSMul.{0, u1} Real V (SMulZeroClass.toSMul.{0, u1} Real V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real V Real.instZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V Real.semiring (AddCommGroup.toAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2))))))) c y)) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_smul_smul InnerProductGeometry.angle_smul_smulₓ'. -/
theorem angle_smul_smul {c : ℝ} (hc : c ≠ 0) (x y : V) : angle (c • x) (c • y) = angle x y :=
  by
  have : c * c ≠ 0 := mul_ne_zero hc hc
  rw [angle, angle, real_inner_smul_left, inner_smul_right, norm_smul, norm_smul, Real.norm_eq_abs,
    mul_mul_mul_comm _ ‖x‖, abs_mul_abs_self, ← mul_assoc c c, mul_div_mul_left _ _ this]
#align inner_product_geometry.angle_smul_smul InnerProductGeometry.angle_smul_smul

/- warning: linear_isometry.angle_map -> LinearIsometry.angle_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry.angle_map LinearIsometry.angle_mapₓ'. -/
@[simp]
theorem LinearIsometry.angle_map {E F : Type _} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] (f : E →ₗᵢ[ℝ] F) (u v : E) :
    angle (f u) (f v) = angle u v := by rw [angle, angle, f.inner_map_map, f.norm_map, f.norm_map]
#align linear_isometry.angle_map LinearIsometry.angle_map

#print Submodule.angle_coe /-
@[simp, norm_cast]
theorem Submodule.angle_coe {s : Submodule ℝ V} (x y : s) : angle (x : V) (y : V) = angle x y :=
  s.subtypeₗᵢ.angle_map x y
#align submodule.angle_coe Submodule.angle_coe
-/

/- warning: inner_product_geometry.cos_angle -> InnerProductGeometry.cos_angle is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Eq.{1} Real (Real.cos (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) y)))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Eq.{1} Real (Real.cos (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) y)))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.cos_angle InnerProductGeometry.cos_angleₓ'. -/
/-- The cosine of the angle between two vectors. -/
theorem cos_angle (x y : V) : Real.cos (angle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖) :=
  Real.cos_arccos (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2
#align inner_product_geometry.cos_angle InnerProductGeometry.cos_angle

#print InnerProductGeometry.angle_comm /-
/-- The angle between two vectors does not depend on their order. -/
theorem angle_comm (x y : V) : angle x y = angle y x :=
  by
  unfold angle
  rw [real_inner_comm, mul_comm]
#align inner_product_geometry.angle_comm InnerProductGeometry.angle_comm
-/

/- warning: inner_product_geometry.angle_neg_neg -> InnerProductGeometry.angle_neg_neg is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (Neg.neg.{u1} V (SubNegMonoid.toHasNeg.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) x) (Neg.neg.{u1} V (SubNegMonoid.toHasNeg.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) y)) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (Neg.neg.{u1} V (NegZeroClass.toNeg.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) x) (Neg.neg.{u1} V (NegZeroClass.toNeg.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) y)) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_neg_neg InnerProductGeometry.angle_neg_negₓ'. -/
/-- The angle between the negation of two vectors. -/
@[simp]
theorem angle_neg_neg (x y : V) : angle (-x) (-y) = angle x y :=
  by
  unfold angle
  rw [inner_neg_neg, norm_neg, norm_neg]
#align inner_product_geometry.angle_neg_neg InnerProductGeometry.angle_neg_neg

/- warning: inner_product_geometry.angle_nonneg -> InnerProductGeometry.angle_nonneg is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_nonneg InnerProductGeometry.angle_nonnegₓ'. -/
/-- The angle between two vectors is nonnegative. -/
theorem angle_nonneg (x y : V) : 0 ≤ angle x y :=
  Real.arccos_nonneg _
#align inner_product_geometry.angle_nonneg InnerProductGeometry.angle_nonneg

/- warning: inner_product_geometry.angle_le_pi -> InnerProductGeometry.angle_le_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), LE.le.{0} Real Real.hasLe (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), LE.le.{0} Real Real.instLEReal (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_le_pi InnerProductGeometry.angle_le_piₓ'. -/
/-- The angle between two vectors is at most π. -/
theorem angle_le_pi (x y : V) : angle x y ≤ π :=
  Real.arccos_le_pi _
#align inner_product_geometry.angle_le_pi InnerProductGeometry.angle_le_pi

/- warning: inner_product_geometry.angle_neg_right -> InnerProductGeometry.angle_neg_right is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x (Neg.neg.{u1} V (SubNegMonoid.toHasNeg.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) y)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) Real.pi (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x (Neg.neg.{u1} V (NegZeroClass.toNeg.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) y)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) Real.pi (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_neg_right InnerProductGeometry.angle_neg_rightₓ'. -/
/-- The angle between a vector and the negation of another vector. -/
theorem angle_neg_right (x y : V) : angle x (-y) = π - angle x y :=
  by
  unfold angle
  rw [← Real.arccos_neg, norm_neg, inner_neg_right, neg_div]
#align inner_product_geometry.angle_neg_right InnerProductGeometry.angle_neg_right

/- warning: inner_product_geometry.angle_neg_left -> InnerProductGeometry.angle_neg_left is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (Neg.neg.{u1} V (SubNegMonoid.toHasNeg.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) x) y) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) Real.pi (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (Neg.neg.{u1} V (NegZeroClass.toNeg.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) x) y) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) Real.pi (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_neg_left InnerProductGeometry.angle_neg_leftₓ'. -/
/-- The angle between the negation of a vector and another vector. -/
theorem angle_neg_left (x y : V) : angle (-x) y = π - angle x y := by
  rw [← angle_neg_neg, neg_neg, angle_neg_right]
#align inner_product_geometry.angle_neg_left InnerProductGeometry.angle_neg_left

/- warning: inner_product_geometry.angle_zero_left -> InnerProductGeometry.angle_zero_left is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V), Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))))) x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V), Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))))) x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_zero_left InnerProductGeometry.angle_zero_leftₓ'. -/
/-- The angle between the zero vector and a vector. -/
@[simp]
theorem angle_zero_left (x : V) : angle 0 x = π / 2 :=
  by
  unfold angle
  rw [inner_zero_left, zero_div, Real.arccos_zero]
#align inner_product_geometry.angle_zero_left InnerProductGeometry.angle_zero_left

/- warning: inner_product_geometry.angle_zero_right -> InnerProductGeometry.angle_zero_right is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V), Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V), Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_zero_right InnerProductGeometry.angle_zero_rightₓ'. -/
/-- The angle between a vector and the zero vector. -/
@[simp]
theorem angle_zero_right (x : V) : angle x 0 = π / 2 :=
  by
  unfold angle
  rw [inner_zero_right, zero_div, Real.arccos_zero]
#align inner_product_geometry.angle_zero_right InnerProductGeometry.angle_zero_right

/- warning: inner_product_geometry.angle_self -> InnerProductGeometry.angle_self is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_self InnerProductGeometry.angle_selfₓ'. -/
/-- The angle between a nonzero vector and itself. -/
@[simp]
theorem angle_self {x : V} (hx : x ≠ 0) : angle x x = 0 :=
  by
  unfold angle
  rw [← real_inner_self_eq_norm_mul_norm, div_self (inner_self_ne_zero.2 hx : ⟪x, x⟫ ≠ 0),
    Real.arccos_one]
#align inner_product_geometry.angle_self InnerProductGeometry.angle_self

/- warning: inner_product_geometry.angle_self_neg_of_nonzero -> InnerProductGeometry.angle_self_neg_of_nonzero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x (Neg.neg.{u1} V (SubNegMonoid.toHasNeg.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) x)) Real.pi)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x (Neg.neg.{u1} V (NegZeroClass.toNeg.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) x)) Real.pi)
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_self_neg_of_nonzero InnerProductGeometry.angle_self_neg_of_nonzeroₓ'. -/
/-- The angle between a nonzero vector and its negation. -/
@[simp]
theorem angle_self_neg_of_nonzero {x : V} (hx : x ≠ 0) : angle x (-x) = π := by
  rw [angle_neg_right, angle_self hx, sub_zero]
#align inner_product_geometry.angle_self_neg_of_nonzero InnerProductGeometry.angle_self_neg_of_nonzero

/- warning: inner_product_geometry.angle_neg_self_of_nonzero -> InnerProductGeometry.angle_neg_self_of_nonzero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (Neg.neg.{u1} V (SubNegMonoid.toHasNeg.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) x) x) Real.pi)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (Neg.neg.{u1} V (NegZeroClass.toNeg.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) x) x) Real.pi)
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_neg_self_of_nonzero InnerProductGeometry.angle_neg_self_of_nonzeroₓ'. -/
/-- The angle between the negation of a nonzero vector and that
vector. -/
@[simp]
theorem angle_neg_self_of_nonzero {x : V} (hx : x ≠ 0) : angle (-x) x = π := by
  rw [angle_comm, angle_self_neg_of_nonzero hx]
#align inner_product_geometry.angle_neg_self_of_nonzero InnerProductGeometry.angle_neg_self_of_nonzero

/- warning: inner_product_geometry.angle_smul_right_of_pos -> InnerProductGeometry.angle_smul_right_of_pos is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V) {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x (SMul.smul.{0, u1} Real V (SMulZeroClass.toHasSmul.{0, u1} Real V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real V (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedSpace.toModule.{0, u1} Real V (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)))))) r y)) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V) {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x (HSMul.hSMul.{0, u1, u1} Real V V (instHSMul.{0, u1} Real V (SMulZeroClass.toSMul.{0, u1} Real V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real V Real.instZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V Real.semiring (AddCommGroup.toAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2))))))) r y)) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_smul_right_of_pos InnerProductGeometry.angle_smul_right_of_posₓ'. -/
/-- The angle between a vector and a positive multiple of a vector. -/
@[simp]
theorem angle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) : angle x (r • y) = angle x y :=
  by
  unfold angle
  rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr), ← mul_assoc,
    mul_comm _ r, mul_assoc, mul_div_mul_left _ _ (ne_of_gt hr)]
#align inner_product_geometry.angle_smul_right_of_pos InnerProductGeometry.angle_smul_right_of_pos

/- warning: inner_product_geometry.angle_smul_left_of_pos -> InnerProductGeometry.angle_smul_left_of_pos is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V) {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (SMul.smul.{0, u1} Real V (SMulZeroClass.toHasSmul.{0, u1} Real V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real V (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedSpace.toModule.{0, u1} Real V (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)))))) r x) y) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V) {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (HSMul.hSMul.{0, u1, u1} Real V V (instHSMul.{0, u1} Real V (SMulZeroClass.toSMul.{0, u1} Real V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real V Real.instZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V Real.semiring (AddCommGroup.toAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2))))))) r x) y) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_smul_left_of_pos InnerProductGeometry.angle_smul_left_of_posₓ'. -/
/-- The angle between a positive multiple of a vector and a vector. -/
@[simp]
theorem angle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) : angle (r • x) y = angle x y := by
  rw [angle_comm, angle_smul_right_of_pos y x hr, angle_comm]
#align inner_product_geometry.angle_smul_left_of_pos InnerProductGeometry.angle_smul_left_of_pos

/- warning: inner_product_geometry.angle_smul_right_of_neg -> InnerProductGeometry.angle_smul_right_of_neg is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V) {r : Real}, (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x (SMul.smul.{0, u1} Real V (SMulZeroClass.toHasSmul.{0, u1} Real V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real V (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedSpace.toModule.{0, u1} Real V (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)))))) r y)) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x (Neg.neg.{u1} V (SubNegMonoid.toHasNeg.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) y)))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V) {r : Real}, (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x (HSMul.hSMul.{0, u1, u1} Real V V (instHSMul.{0, u1} Real V (SMulZeroClass.toSMul.{0, u1} Real V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real V Real.instZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V Real.semiring (AddCommGroup.toAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2))))))) r y)) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x (Neg.neg.{u1} V (NegZeroClass.toNeg.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) y)))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_smul_right_of_neg InnerProductGeometry.angle_smul_right_of_negₓ'. -/
/-- The angle between a vector and a negative multiple of a vector. -/
@[simp]
theorem angle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) : angle x (r • y) = angle x (-y) :=
  by
  rw [← neg_neg r, neg_smul, angle_neg_right, angle_smul_right_of_pos x y (neg_pos_of_neg hr),
    angle_neg_right]
#align inner_product_geometry.angle_smul_right_of_neg InnerProductGeometry.angle_smul_right_of_neg

/- warning: inner_product_geometry.angle_smul_left_of_neg -> InnerProductGeometry.angle_smul_left_of_neg is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V) {r : Real}, (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (SMul.smul.{0, u1} Real V (SMulZeroClass.toHasSmul.{0, u1} Real V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real V (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedSpace.toModule.{0, u1} Real V (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)))))) r x) y) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (Neg.neg.{u1} V (SubNegMonoid.toHasNeg.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) x) y))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V) {r : Real}, (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (HSMul.hSMul.{0, u1, u1} Real V V (instHSMul.{0, u1} Real V (SMulZeroClass.toSMul.{0, u1} Real V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real V Real.instZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V Real.semiring (AddCommGroup.toAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2))))))) r x) y) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 (Neg.neg.{u1} V (NegZeroClass.toNeg.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) x) y))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_smul_left_of_neg InnerProductGeometry.angle_smul_left_of_negₓ'. -/
/-- The angle between a negative multiple of a vector and a vector. -/
@[simp]
theorem angle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) : angle (r • x) y = angle (-x) y := by
  rw [angle_comm, angle_smul_right_of_neg y x hr, angle_comm]
#align inner_product_geometry.angle_smul_left_of_neg InnerProductGeometry.angle_smul_left_of_neg

/- warning: inner_product_geometry.cos_angle_mul_norm_mul_norm -> InnerProductGeometry.cos_angle_mul_norm_mul_norm is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.cos (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) y))) (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.cos (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) y))) (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y)
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.cos_angle_mul_norm_mul_norm InnerProductGeometry.cos_angle_mul_norm_mul_normₓ'. -/
/-- The cosine of the angle between two vectors, multiplied by the
product of their norms. -/
theorem cos_angle_mul_norm_mul_norm (x y : V) : Real.cos (angle x y) * (‖x‖ * ‖y‖) = ⟪x, y⟫ :=
  by
  rw [cos_angle, div_mul_cancel_of_imp]
  simp (config := { contextual := true }) [or_imp]
#align inner_product_geometry.cos_angle_mul_norm_mul_norm InnerProductGeometry.cos_angle_mul_norm_mul_norm

/- warning: inner_product_geometry.sin_angle_mul_norm_mul_norm -> InnerProductGeometry.sin_angle_mul_norm_mul_norm is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.sin (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) y))) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x x) (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) y y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.sin (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) y))) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x x) (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) y y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.sin_angle_mul_norm_mul_norm InnerProductGeometry.sin_angle_mul_norm_mul_normₓ'. -/
/-- The sine of the angle between two vectors, multiplied by the
product of their norms. -/
theorem sin_angle_mul_norm_mul_norm (x y : V) :
    Real.sin (angle x y) * (‖x‖ * ‖y‖) = Real.sqrt (⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) :=
  by
  unfold angle
  rw [Real.sin_arccos, ← Real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)), ←
    Real.sqrt_mul' _ (mul_self_nonneg _), sq,
    Real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)),
    real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm]
  by_cases h : ‖x‖ * ‖y‖ = 0
  · rw [show ‖x‖ * ‖x‖ * (‖y‖ * ‖y‖) = ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) by ring, h, MulZeroClass.mul_zero,
      MulZeroClass.mul_zero, zero_sub]
    cases' eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy
    · rw [norm_eq_zero] at hx
      rw [hx, inner_zero_left, MulZeroClass.zero_mul, neg_zero]
    · rw [norm_eq_zero] at hy
      rw [hy, inner_zero_right, MulZeroClass.zero_mul, neg_zero]
  · field_simp [h]
    ring_nf
#align inner_product_geometry.sin_angle_mul_norm_mul_norm InnerProductGeometry.sin_angle_mul_norm_mul_norm

/- warning: inner_product_geometry.angle_eq_zero_iff -> InnerProductGeometry.angle_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (And (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) (Exists.{1} Real (fun (r : Real) => And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) (Eq.{succ u1} V y (SMul.smul.{0, u1} Real V (SMulZeroClass.toHasSmul.{0, u1} Real V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real V (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedSpace.toModule.{0, u1} Real V (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)))))) r x)))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (And (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) (Exists.{1} Real (fun (r : Real) => And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) (Eq.{succ u1} V y (HSMul.hSMul.{0, u1, u1} Real V V (instHSMul.{0, u1} Real V (SMulZeroClass.toSMul.{0, u1} Real V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real V Real.instZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V Real.semiring (AddCommGroup.toAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2))))))) r x)))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_eq_zero_iff InnerProductGeometry.angle_eq_zero_iffₓ'. -/
/-- The angle between two vectors is zero if and only if they are
nonzero and one is a positive multiple of the other. -/
theorem angle_eq_zero_iff {x y : V} : angle x y = 0 ↔ x ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • x :=
  by
  rw [angle, ← real_inner_div_norm_mul_norm_eq_one_iff, Real.arccos_eq_zero, LE.le.le_iff_eq,
    eq_comm]
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2
#align inner_product_geometry.angle_eq_zero_iff InnerProductGeometry.angle_eq_zero_iff

/- warning: inner_product_geometry.angle_eq_pi_iff -> InnerProductGeometry.angle_eq_pi_iff is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi) (And (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) (Exists.{1} Real (fun (r : Real) => And (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{succ u1} V y (SMul.smul.{0, u1} Real V (SMulZeroClass.toHasSmul.{0, u1} Real V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real V (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedSpace.toModule.{0, u1} Real V (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)))))) r x)))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi) (And (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) (Exists.{1} Real (fun (r : Real) => And (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{succ u1} V y (HSMul.hSMul.{0, u1, u1} Real V V (instHSMul.{0, u1} Real V (SMulZeroClass.toSMul.{0, u1} Real V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real V Real.instZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V Real.semiring (AddCommGroup.toAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2))))))) r x)))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_eq_pi_iff InnerProductGeometry.angle_eq_pi_iffₓ'. -/
/-- The angle between two vectors is π if and only if they are nonzero
and one is a negative multiple of the other. -/
theorem angle_eq_pi_iff {x y : V} : angle x y = π ↔ x ≠ 0 ∧ ∃ r : ℝ, r < 0 ∧ y = r • x :=
  by
  rw [angle, ← real_inner_div_norm_mul_norm_eq_neg_one_iff, Real.arccos_eq_pi, LE.le.le_iff_eq]
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
#align inner_product_geometry.angle_eq_pi_iff InnerProductGeometry.angle_eq_pi_iff

/- warning: inner_product_geometry.angle_add_angle_eq_pi_of_angle_eq_pi -> InnerProductGeometry.angle_add_angle_eq_pi_of_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V} (z : V), (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi) -> (Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x z) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 y z)) Real.pi)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V} (z : V), (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi) -> (Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x z) (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 y z)) Real.pi)
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.angle_add_angle_eq_pi_of_angle_eq_pi InnerProductGeometry.angle_add_angle_eq_pi_of_angle_eq_piₓ'. -/
/-- If the angle between two vectors is π, the angles between those
vectors and a third vector add to π. -/
theorem angle_add_angle_eq_pi_of_angle_eq_pi {x y : V} (z : V) (h : angle x y = π) :
    angle x z + angle y z = π :=
  by
  rcases angle_eq_pi_iff.1 h with ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
  rw [angle_smul_left_of_neg x z hr, angle_neg_left, add_sub_cancel'_right]
#align inner_product_geometry.angle_add_angle_eq_pi_of_angle_eq_pi InnerProductGeometry.angle_add_angle_eq_pi_of_angle_eq_pi

/- warning: inner_product_geometry.inner_eq_zero_iff_angle_eq_pi_div_two -> InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Iff (Eq.{1} Real (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Iff (Eq.{1} Real (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.inner_eq_zero_iff_angle_eq_pi_div_two InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_twoₓ'. -/
/-- Two vectors have inner product 0 if and only if the angle between
them is π/2. -/
theorem inner_eq_zero_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2 :=
  Iff.symm <| by simp (config := { contextual := true }) [angle, or_imp]
#align inner_product_geometry.inner_eq_zero_iff_angle_eq_pi_div_two InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two

/- warning: inner_product_geometry.inner_eq_neg_mul_norm_of_angle_eq_pi -> InnerProductGeometry.inner_eq_neg_mul_norm_of_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi) -> (Eq.{1} Real (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (Neg.neg.{0} Real Real.hasNeg (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) y))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi) -> (Eq.{1} Real (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (Neg.neg.{0} Real Real.instNegReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) y))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.inner_eq_neg_mul_norm_of_angle_eq_pi InnerProductGeometry.inner_eq_neg_mul_norm_of_angle_eq_piₓ'. -/
/-- If the angle between two vectors is π, the inner product equals the negative product
of the norms. -/
theorem inner_eq_neg_mul_norm_of_angle_eq_pi {x y : V} (h : angle x y = π) :
    ⟪x, y⟫ = -(‖x‖ * ‖y‖) := by simp [← cos_angle_mul_norm_mul_norm, h]
#align inner_product_geometry.inner_eq_neg_mul_norm_of_angle_eq_pi InnerProductGeometry.inner_eq_neg_mul_norm_of_angle_eq_pi

/- warning: inner_product_geometry.inner_eq_mul_norm_of_angle_eq_zero -> InnerProductGeometry.inner_eq_mul_norm_of_angle_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) y)))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) y)))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.inner_eq_mul_norm_of_angle_eq_zero InnerProductGeometry.inner_eq_mul_norm_of_angle_eq_zeroₓ'. -/
/-- If the angle between two vectors is 0, the inner product equals the product of the norms. -/
theorem inner_eq_mul_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) : ⟪x, y⟫ = ‖x‖ * ‖y‖ := by
  simp [← cos_angle_mul_norm_mul_norm, h]
#align inner_product_geometry.inner_eq_mul_norm_of_angle_eq_zero InnerProductGeometry.inner_eq_mul_norm_of_angle_eq_zero

/- warning: inner_product_geometry.inner_eq_neg_mul_norm_iff_angle_eq_pi -> InnerProductGeometry.inner_eq_neg_mul_norm_iff_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Ne.{succ u1} V y (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Iff (Eq.{1} Real (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (Neg.neg.{0} Real Real.hasNeg (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) y)))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Ne.{succ u1} V y (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Iff (Eq.{1} Real (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (Neg.neg.{0} Real Real.instNegReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) y)))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.inner_eq_neg_mul_norm_iff_angle_eq_pi InnerProductGeometry.inner_eq_neg_mul_norm_iff_angle_eq_piₓ'. -/
/-- The inner product of two non-zero vectors equals the negative product of their norms
if and only if the angle between the two vectors is π. -/
theorem inner_eq_neg_mul_norm_iff_angle_eq_pi {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ⟪x, y⟫ = -(‖x‖ * ‖y‖) ↔ angle x y = π :=
  by
  refine' ⟨fun h => _, inner_eq_neg_mul_norm_of_angle_eq_pi⟩
  have h₁ : ‖x‖ * ‖y‖ ≠ 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  rw [angle, h, neg_div, div_self h₁, Real.arccos_neg_one]
#align inner_product_geometry.inner_eq_neg_mul_norm_iff_angle_eq_pi InnerProductGeometry.inner_eq_neg_mul_norm_iff_angle_eq_pi

/- warning: inner_product_geometry.inner_eq_mul_norm_iff_angle_eq_zero -> InnerProductGeometry.inner_eq_mul_norm_iff_angle_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Ne.{succ u1} V y (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Iff (Eq.{1} Real (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) y))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Ne.{succ u1} V y (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Iff (Eq.{1} Real (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) y))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.inner_eq_mul_norm_iff_angle_eq_zero InnerProductGeometry.inner_eq_mul_norm_iff_angle_eq_zeroₓ'. -/
/-- The inner product of two non-zero vectors equals the product of their norms
if and only if the angle between the two vectors is 0. -/
theorem inner_eq_mul_norm_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ⟪x, y⟫ = ‖x‖ * ‖y‖ ↔ angle x y = 0 :=
  by
  refine' ⟨fun h => _, inner_eq_mul_norm_of_angle_eq_zero⟩
  have h₁ : ‖x‖ * ‖y‖ ≠ 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  rw [angle, h, div_self h₁, Real.arccos_one]
#align inner_product_geometry.inner_eq_mul_norm_iff_angle_eq_zero InnerProductGeometry.inner_eq_mul_norm_iff_angle_eq_zero

/- warning: inner_product_geometry.norm_sub_eq_add_norm_of_angle_eq_pi -> InnerProductGeometry.norm_sub_eq_add_norm_of_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi) -> (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toHasSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) y)))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi) -> (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) y)))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.norm_sub_eq_add_norm_of_angle_eq_pi InnerProductGeometry.norm_sub_eq_add_norm_of_angle_eq_piₓ'. -/
/-- If the angle between two vectors is π, the norm of their difference equals
the sum of their norms. -/
theorem norm_sub_eq_add_norm_of_angle_eq_pi {x y : V} (h : angle x y = π) : ‖x - y‖ = ‖x‖ + ‖y‖ :=
  by
  rw [← sq_eq_sq (norm_nonneg (x - y)) (add_nonneg (norm_nonneg x) (norm_nonneg y))]
  rw [norm_sub_pow_two_real, inner_eq_neg_mul_norm_of_angle_eq_pi h]
  ring
#align inner_product_geometry.norm_sub_eq_add_norm_of_angle_eq_pi InnerProductGeometry.norm_sub_eq_add_norm_of_angle_eq_pi

/- warning: inner_product_geometry.norm_add_eq_add_norm_of_angle_eq_zero -> InnerProductGeometry.norm_add_eq_add_norm_of_angle_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toHasAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) y)))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) y)))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.norm_add_eq_add_norm_of_angle_eq_zero InnerProductGeometry.norm_add_eq_add_norm_of_angle_eq_zeroₓ'. -/
/-- If the angle between two vectors is 0, the norm of their sum equals
the sum of their norms. -/
theorem norm_add_eq_add_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) : ‖x + y‖ = ‖x‖ + ‖y‖ :=
  by
  rw [← sq_eq_sq (norm_nonneg (x + y)) (add_nonneg (norm_nonneg x) (norm_nonneg y))]
  rw [norm_add_pow_two_real, inner_eq_mul_norm_of_angle_eq_zero h]
  ring
#align inner_product_geometry.norm_add_eq_add_norm_of_angle_eq_zero InnerProductGeometry.norm_add_eq_add_norm_of_angle_eq_zero

/- warning: inner_product_geometry.norm_sub_eq_abs_sub_norm_of_angle_eq_zero -> InnerProductGeometry.norm_sub_eq_abs_sub_norm_of_angle_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toHasSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) x y)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) y))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) x y)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) y))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.norm_sub_eq_abs_sub_norm_of_angle_eq_zero InnerProductGeometry.norm_sub_eq_abs_sub_norm_of_angle_eq_zeroₓ'. -/
/-- If the angle between two vectors is 0, the norm of their difference equals
the absolute value of the difference of their norms. -/
theorem norm_sub_eq_abs_sub_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) :
    ‖x - y‖ = |‖x‖ - ‖y‖| :=
  by
  rw [← sq_eq_sq (norm_nonneg (x - y)) (abs_nonneg (‖x‖ - ‖y‖)), norm_sub_pow_two_real,
    inner_eq_mul_norm_of_angle_eq_zero h, sq_abs (‖x‖ - ‖y‖)]
  ring
#align inner_product_geometry.norm_sub_eq_abs_sub_norm_of_angle_eq_zero InnerProductGeometry.norm_sub_eq_abs_sub_norm_of_angle_eq_zero

/- warning: inner_product_geometry.norm_sub_eq_add_norm_iff_angle_eq_pi -> InnerProductGeometry.norm_sub_eq_add_norm_iff_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Ne.{succ u1} V y (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Iff (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toHasSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) y))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Ne.{succ u1} V y (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Iff (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) y))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.norm_sub_eq_add_norm_iff_angle_eq_pi InnerProductGeometry.norm_sub_eq_add_norm_iff_angle_eq_piₓ'. -/
/-- The norm of the difference of two non-zero vectors equals the sum of their norms
if and only the angle between the two vectors is π. -/
theorem norm_sub_eq_add_norm_iff_angle_eq_pi {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x - y‖ = ‖x‖ + ‖y‖ ↔ angle x y = π :=
  by
  refine' ⟨fun h => _, norm_sub_eq_add_norm_of_angle_eq_pi⟩
  rw [← inner_eq_neg_mul_norm_iff_angle_eq_pi hx hy]
  obtain ⟨hxy₁, hxy₂⟩ := norm_nonneg (x - y), add_nonneg (norm_nonneg x) (norm_nonneg y)
  rw [← sq_eq_sq hxy₁ hxy₂, norm_sub_pow_two_real] at h
  calc
    ⟪x, y⟫ = (‖x‖ ^ 2 + ‖y‖ ^ 2 - (‖x‖ + ‖y‖) ^ 2) / 2 := by linarith
    _ = -(‖x‖ * ‖y‖) := by ring
    
#align inner_product_geometry.norm_sub_eq_add_norm_iff_angle_eq_pi InnerProductGeometry.norm_sub_eq_add_norm_iff_angle_eq_pi

/- warning: inner_product_geometry.norm_add_eq_add_norm_iff_angle_eq_zero -> InnerProductGeometry.norm_add_eq_add_norm_iff_angle_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Ne.{succ u1} V y (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Iff (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toHasAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) y))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Ne.{succ u1} V y (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Iff (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) y))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.norm_add_eq_add_norm_iff_angle_eq_zero InnerProductGeometry.norm_add_eq_add_norm_iff_angle_eq_zeroₓ'. -/
/-- The norm of the sum of two non-zero vectors equals the sum of their norms
if and only the angle between the two vectors is 0. -/
theorem norm_add_eq_add_norm_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x + y‖ = ‖x‖ + ‖y‖ ↔ angle x y = 0 :=
  by
  refine' ⟨fun h => _, norm_add_eq_add_norm_of_angle_eq_zero⟩
  rw [← inner_eq_mul_norm_iff_angle_eq_zero hx hy]
  obtain ⟨hxy₁, hxy₂⟩ := norm_nonneg (x + y), add_nonneg (norm_nonneg x) (norm_nonneg y)
  rw [← sq_eq_sq hxy₁ hxy₂, norm_add_pow_two_real] at h
  calc
    ⟪x, y⟫ = ((‖x‖ + ‖y‖) ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2) / 2 := by linarith
    _ = ‖x‖ * ‖y‖ := by ring
    
#align inner_product_geometry.norm_add_eq_add_norm_iff_angle_eq_zero InnerProductGeometry.norm_add_eq_add_norm_iff_angle_eq_zero

/- warning: inner_product_geometry.norm_sub_eq_abs_sub_norm_iff_angle_eq_zero -> InnerProductGeometry.norm_sub_eq_abs_sub_norm_iff_angle_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Ne.{succ u1} V y (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) -> (Iff (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toHasSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) x y)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) y)))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, (Ne.{succ u1} V x (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Ne.{succ u1} V y (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) -> (Iff (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) x y)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) x) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) y)))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.norm_sub_eq_abs_sub_norm_iff_angle_eq_zero InnerProductGeometry.norm_sub_eq_abs_sub_norm_iff_angle_eq_zeroₓ'. -/
/-- The norm of the difference of two non-zero vectors equals the absolute value
of the difference of their norms if and only the angle between the two vectors is 0. -/
theorem norm_sub_eq_abs_sub_norm_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x - y‖ = |‖x‖ - ‖y‖| ↔ angle x y = 0 :=
  by
  refine' ⟨fun h => _, norm_sub_eq_abs_sub_norm_of_angle_eq_zero⟩
  rw [← inner_eq_mul_norm_iff_angle_eq_zero hx hy]
  have h1 : ‖x - y‖ ^ 2 = (‖x‖ - ‖y‖) ^ 2 := by
    rw [h]
    exact sq_abs (‖x‖ - ‖y‖)
  rw [norm_sub_pow_two_real] at h1
  calc
    ⟪x, y⟫ = ((‖x‖ + ‖y‖) ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2) / 2 := by linarith
    _ = ‖x‖ * ‖y‖ := by ring
    
#align inner_product_geometry.norm_sub_eq_abs_sub_norm_iff_angle_eq_zero InnerProductGeometry.norm_sub_eq_abs_sub_norm_iff_angle_eq_zero

/- warning: inner_product_geometry.norm_add_eq_norm_sub_iff_angle_eq_pi_div_two -> InnerProductGeometry.norm_add_eq_norm_sub_iff_angle_eq_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Iff (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toHasAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) x y)) (Norm.norm.{u1} V (NormedAddCommGroup.toHasNorm.{u1} V _inst_1) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toHasSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) x y))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (x : V) (y : V), Iff (Eq.{1} Real (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) x y)) (Norm.norm.{u1} V (NormedAddCommGroup.toNorm.{u1} V _inst_1) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) x y))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.norm_add_eq_norm_sub_iff_angle_eq_pi_div_two InnerProductGeometry.norm_add_eq_norm_sub_iff_angle_eq_pi_div_twoₓ'. -/
/-- The norm of the sum of two vectors equals the norm of their difference if and only if
the angle between them is π/2. -/
theorem norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (x y : V) :
    ‖x + y‖ = ‖x - y‖ ↔ angle x y = π / 2 :=
  by
  rw [← sq_eq_sq (norm_nonneg (x + y)) (norm_nonneg (x - y)), ←
    inner_eq_zero_iff_angle_eq_pi_div_two x y, norm_add_pow_two_real, norm_sub_pow_two_real]
  constructor <;> intro h <;> linarith
#align inner_product_geometry.norm_add_eq_norm_sub_iff_angle_eq_pi_div_two InnerProductGeometry.norm_add_eq_norm_sub_iff_angle_eq_pi_div_two

/- warning: inner_product_geometry.cos_eq_one_iff_angle_eq_zero -> InnerProductGeometry.cos_eq_one_iff_angle_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (Real.cos (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (Real.cos (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.cos_eq_one_iff_angle_eq_zero InnerProductGeometry.cos_eq_one_iff_angle_eq_zeroₓ'. -/
/-- The cosine of the angle between two vectors is 1 if and only if the angle is 0. -/
theorem cos_eq_one_iff_angle_eq_zero : cos (angle x y) = 1 ↔ angle x y = 0 :=
  by
  rw [← cos_zero]
  exact inj_on_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (left_mem_Icc.2 pi_pos.le)
#align inner_product_geometry.cos_eq_one_iff_angle_eq_zero InnerProductGeometry.cos_eq_one_iff_angle_eq_zero

/- warning: inner_product_geometry.cos_eq_zero_iff_angle_eq_pi_div_two -> InnerProductGeometry.cos_eq_zero_iff_angle_eq_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (Real.cos (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (Real.cos (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.cos_eq_zero_iff_angle_eq_pi_div_two InnerProductGeometry.cos_eq_zero_iff_angle_eq_pi_div_twoₓ'. -/
/-- The cosine of the angle between two vectors is 0 if and only if the angle is π / 2. -/
theorem cos_eq_zero_iff_angle_eq_pi_div_two : cos (angle x y) = 0 ↔ angle x y = π / 2 :=
  by
  rw [← cos_pi_div_two]
  apply inj_on_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩
  constructor <;> linarith [pi_pos]
#align inner_product_geometry.cos_eq_zero_iff_angle_eq_pi_div_two InnerProductGeometry.cos_eq_zero_iff_angle_eq_pi_div_two

/- warning: inner_product_geometry.cos_eq_neg_one_iff_angle_eq_pi -> InnerProductGeometry.cos_eq_neg_one_iff_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (Real.cos (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (Real.cos (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi)
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.cos_eq_neg_one_iff_angle_eq_pi InnerProductGeometry.cos_eq_neg_one_iff_angle_eq_piₓ'. -/
/-- The cosine of the angle between two vectors is -1 if and only if the angle is π. -/
theorem cos_eq_neg_one_iff_angle_eq_pi : cos (angle x y) = -1 ↔ angle x y = π :=
  by
  rw [← cos_pi]
  exact inj_on_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (right_mem_Icc.2 pi_pos.le)
#align inner_product_geometry.cos_eq_neg_one_iff_angle_eq_pi InnerProductGeometry.cos_eq_neg_one_iff_angle_eq_pi

/- warning: inner_product_geometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi -> InnerProductGeometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (Real.sin (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Or (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (Real.sin (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Or (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) Real.pi))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi InnerProductGeometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_piₓ'. -/
/-- The sine of the angle between two vectors is 0 if and only if the angle is 0 or π. -/
theorem sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi :
    sin (angle x y) = 0 ↔ angle x y = 0 ∨ angle x y = π := by
  rw [sin_eq_zero_iff_cos_eq, cos_eq_one_iff_angle_eq_zero, cos_eq_neg_one_iff_angle_eq_pi]
#align inner_product_geometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi InnerProductGeometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi

/- warning: inner_product_geometry.sin_eq_one_iff_angle_eq_pi_div_two -> InnerProductGeometry.sin_eq_one_iff_angle_eq_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (Real.sin (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] {x : V} {y : V}, Iff (Eq.{1} Real (Real.sin (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Eq.{1} Real (InnerProductGeometry.angle.{u1} V _inst_1 _inst_2 x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align inner_product_geometry.sin_eq_one_iff_angle_eq_pi_div_two InnerProductGeometry.sin_eq_one_iff_angle_eq_pi_div_twoₓ'. -/
/-- The sine of the angle between two vectors is 1 if and only if the angle is π / 2. -/
theorem sin_eq_one_iff_angle_eq_pi_div_two : sin (angle x y) = 1 ↔ angle x y = π / 2 :=
  by
  refine' ⟨fun h => _, fun h => by rw [h, sin_pi_div_two]⟩
  rw [← cos_eq_zero_iff_angle_eq_pi_div_two, ← abs_eq_zero, abs_cos_eq_sqrt_one_sub_sin_sq, h]
  simp
#align inner_product_geometry.sin_eq_one_iff_angle_eq_pi_div_two InnerProductGeometry.sin_eq_one_iff_angle_eq_pi_div_two

end InnerProductGeometry

