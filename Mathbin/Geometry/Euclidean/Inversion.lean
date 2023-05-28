/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module geometry.euclidean.inversion
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Basic

/-!
# Inversion in an affine space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define inversion in a sphere in an affine space. This map sends each point `x` to
the point `y` such that `y -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c)`, where `c` and `R` are the center
and the radius the sphere.

In many applications, it is convenient to assume that the inversions swaps the center and the point
at infinity. In order to stay in the original affine space, we define the map so that it sends
center to itself.

Currently, we prove only a few basic lemmas needed to prove Ptolemy's inequality, see
`euclidean_geometry.mul_dist_le_mul_dist_add_mul_dist`.
-/


noncomputable section

open Metric Real Function

namespace EuclideanGeometry

variable {V P : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {a b c d x y z : P} {R : ℝ}

include V

#print EuclideanGeometry.inversion /-
/-- Inversion in a sphere in an affine space. This map sends each point `x` to the point `y` such
that `y -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c)`, where `c` and `R` are the center and the radius the
sphere. -/
def inversion (c : P) (R : ℝ) (x : P) : P :=
  (R / dist x c) ^ 2 • (x -ᵥ c) +ᵥ c
#align euclidean_geometry.inversion EuclideanGeometry.inversion
-/

/- warning: euclidean_geometry.inversion_vsub_center -> EuclideanGeometry.inversion_vsub_center is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) (R : Real) (x : P), Eq.{succ u1} V (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R x) c) (SMul.smul.{0, u1} Real V (SMulZeroClass.toHasSmul.{0, u1} Real V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real V (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real V (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (AddCommMonoid.toAddMonoid.{u1} V (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real V (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedSpace.toModule.{0, u1} Real V (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) R (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) x c)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) x c))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] (c : P) (R : Real) (x : P), Eq.{succ u2} V (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)) (EuclideanGeometry.inversion.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 c R x) c) (HSMul.hSMul.{0, u2, u2} Real V V (instHSMul.{0, u2} Real V (SMulZeroClass.toSMul.{0, u2} Real V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u2} Real V Real.instZeroReal (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u2} Real V Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1)))))) (Module.toMulActionWithZero.{0, u2} Real V Real.semiring (AddCommGroup.toAddCommMonoid.{u2} V (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1)) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2))))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) R (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) x c)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)) x c))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.inversion_vsub_center EuclideanGeometry.inversion_vsub_centerₓ'. -/
theorem inversion_vsub_center (c : P) (R : ℝ) (x : P) :
    inversion c R x -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c) :=
  vadd_vsub _ _
#align euclidean_geometry.inversion_vsub_center EuclideanGeometry.inversion_vsub_center

#print EuclideanGeometry.inversion_self /-
@[simp]
theorem inversion_self (c : P) (R : ℝ) : inversion c R c = c := by simp [inversion]
#align euclidean_geometry.inversion_self EuclideanGeometry.inversion_self
-/

#print EuclideanGeometry.inversion_dist_center /-
@[simp]
theorem inversion_dist_center (c x : P) : inversion c (dist x c) x = x :=
  by
  rcases eq_or_ne x c with (rfl | hne)
  · apply inversion_self
  · rw [inversion, div_self, one_pow, one_smul, vsub_vadd]
    rwa [dist_ne_zero]
#align euclidean_geometry.inversion_dist_center EuclideanGeometry.inversion_dist_center
-/

#print EuclideanGeometry.inversion_of_mem_sphere /-
theorem inversion_of_mem_sphere (h : x ∈ Metric.sphere c R) : inversion c R x = x :=
  h.out ▸ inversion_dist_center c x
#align euclidean_geometry.inversion_of_mem_sphere EuclideanGeometry.inversion_of_mem_sphere
-/

/- warning: euclidean_geometry.dist_inversion_center -> EuclideanGeometry.dist_inversion_center is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) (x : P) (R : Real), Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R x) c) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) R (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) x c))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) (x : P) (R : Real), Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R x) c) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) R (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) x c))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.dist_inversion_center EuclideanGeometry.dist_inversion_centerₓ'. -/
/-- Distance from the image of a point under inversion to the center. This formula accidentally
works for `x = c`. -/
theorem dist_inversion_center (c x : P) (R : ℝ) : dist (inversion c R x) c = R ^ 2 / dist x c :=
  by
  rcases eq_or_ne x c with (rfl | hx)
  · simp
  have : dist x c ≠ 0 := dist_ne_zero.2 hx
  field_simp [inversion, norm_smul, abs_div, ← dist_eq_norm_vsub, sq, mul_assoc]
#align euclidean_geometry.dist_inversion_center EuclideanGeometry.dist_inversion_center

/- warning: euclidean_geometry.dist_center_inversion -> EuclideanGeometry.dist_center_inversion is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) (x : P) (R : Real), Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) c (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) R (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) c x))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) (x : P) (R : Real), Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) c (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) R (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) c x))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.dist_center_inversion EuclideanGeometry.dist_center_inversionₓ'. -/
/-- Distance from the center of an inversion to the image of a point under the inversion. This
formula accidentally works for `x = c`. -/
theorem dist_center_inversion (c x : P) (R : ℝ) : dist c (inversion c R x) = R ^ 2 / dist c x := by
  rw [dist_comm c, dist_comm c, dist_inversion_center]
#align euclidean_geometry.dist_center_inversion EuclideanGeometry.dist_center_inversion

/- warning: euclidean_geometry.inversion_inversion -> EuclideanGeometry.inversion_inversion is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) {R : Real}, (Ne.{1} Real R (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (x : P), Eq.{succ u2} P (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R x)) x)
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) {R : Real}, (Ne.{1} Real R (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (x : P), Eq.{succ u2} P (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R x)) x)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.inversion_inversion EuclideanGeometry.inversion_inversionₓ'. -/
@[simp]
theorem inversion_inversion (c : P) {R : ℝ} (hR : R ≠ 0) (x : P) :
    inversion c R (inversion c R x) = x :=
  by
  rcases eq_or_ne x c with (rfl | hne)
  · rw [inversion_self, inversion_self]
  · rw [inversion, dist_inversion_center, inversion_vsub_center, smul_smul, ← mul_pow,
      div_mul_div_comm, div_mul_cancel _ (dist_ne_zero.2 hne), ← sq, div_self, one_pow, one_smul,
      vsub_vadd]
    exact pow_ne_zero _ hR
#align euclidean_geometry.inversion_inversion EuclideanGeometry.inversion_inversion

/- warning: euclidean_geometry.inversion_involutive -> EuclideanGeometry.inversion_involutive is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) {R : Real}, (Ne.{1} Real R (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Function.Involutive.{succ u2} P (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) {R : Real}, (Ne.{1} Real R (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Function.Involutive.{succ u2} P (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.inversion_involutive EuclideanGeometry.inversion_involutiveₓ'. -/
theorem inversion_involutive (c : P) {R : ℝ} (hR : R ≠ 0) : Involutive (inversion c R) :=
  inversion_inversion c hR
#align euclidean_geometry.inversion_involutive EuclideanGeometry.inversion_involutive

/- warning: euclidean_geometry.inversion_surjective -> EuclideanGeometry.inversion_surjective is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) {R : Real}, (Ne.{1} Real R (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Function.Surjective.{succ u2, succ u2} P P (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) {R : Real}, (Ne.{1} Real R (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Function.Surjective.{succ u2, succ u2} P P (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.inversion_surjective EuclideanGeometry.inversion_surjectiveₓ'. -/
theorem inversion_surjective (c : P) {R : ℝ} (hR : R ≠ 0) : Surjective (inversion c R) :=
  (inversion_involutive c hR).Surjective
#align euclidean_geometry.inversion_surjective EuclideanGeometry.inversion_surjective

/- warning: euclidean_geometry.inversion_injective -> EuclideanGeometry.inversion_injective is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) {R : Real}, (Ne.{1} Real R (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Function.Injective.{succ u2, succ u2} P P (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) {R : Real}, (Ne.{1} Real R (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Function.Injective.{succ u2, succ u2} P P (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.inversion_injective EuclideanGeometry.inversion_injectiveₓ'. -/
theorem inversion_injective (c : P) {R : ℝ} (hR : R ≠ 0) : Injective (inversion c R) :=
  (inversion_involutive c hR).Injective
#align euclidean_geometry.inversion_injective EuclideanGeometry.inversion_injective

/- warning: euclidean_geometry.inversion_bijective -> EuclideanGeometry.inversion_bijective is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) {R : Real}, (Ne.{1} Real R (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Function.Bijective.{succ u2, succ u2} P P (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (c : P) {R : Real}, (Ne.{1} Real R (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Function.Bijective.{succ u2, succ u2} P P (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.inversion_bijective EuclideanGeometry.inversion_bijectiveₓ'. -/
theorem inversion_bijective (c : P) {R : ℝ} (hR : R ≠ 0) : Bijective (inversion c R) :=
  (inversion_involutive c hR).Bijective
#align euclidean_geometry.inversion_bijective EuclideanGeometry.inversion_bijective

/- warning: euclidean_geometry.dist_inversion_inversion -> EuclideanGeometry.dist_inversion_inversion is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {c : P} {x : P} {y : P}, (Ne.{succ u2} P x c) -> (Ne.{succ u2} P y c) -> (forall (R : Real), Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R x) (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) R (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) x c) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) y c))) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) x y)))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {c : P} {x : P} {y : P}, (Ne.{succ u2} P x c) -> (Ne.{succ u2} P y c) -> (forall (R : Real), Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R x) (EuclideanGeometry.inversion.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 c R y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) R (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) x c) (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) y c))) (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) x y)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.dist_inversion_inversion EuclideanGeometry.dist_inversion_inversionₓ'. -/
/-- Distance between the images of two points under an inversion. -/
theorem dist_inversion_inversion (hx : x ≠ c) (hy : y ≠ c) (R : ℝ) :
    dist (inversion c R x) (inversion c R y) = R ^ 2 / (dist x c * dist y c) * dist x y :=
  by
  dsimp only [inversion]
  simp_rw [dist_vadd_cancel_right, dist_eq_norm_vsub V _ c]
  simpa only [dist_vsub_cancel_right] using
    dist_div_norm_sq_smul (vsub_ne_zero.2 hx) (vsub_ne_zero.2 hy) R
#align euclidean_geometry.dist_inversion_inversion EuclideanGeometry.dist_inversion_inversion

/- warning: euclidean_geometry.mul_dist_le_mul_dist_add_mul_dist -> EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (a : P) (b : P) (c : P) (d : P), LE.le.{0} Real Real.hasLe (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) a c) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) b d)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) a b) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) c d)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) b c) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) a d)))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] (a : P) (b : P) (c : P) (d : P), LE.le.{0} Real Real.instLEReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) a c) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) b d)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) a b) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) c d)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) b c) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) a d)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.mul_dist_le_mul_dist_add_mul_dist EuclideanGeometry.mul_dist_le_mul_dist_add_mul_distₓ'. -/
/-- **Ptolemy's inequality**: in a quadrangle `ABCD`, `|AC| * |BD| ≤ |AB| * |CD| + |BC| * |AD|`. If
`ABCD` is a convex cyclic polygon, then this inequality becomes an equality, see
`euclidean_geometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`.  -/
theorem mul_dist_le_mul_dist_add_mul_dist (a b c d : P) :
    dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d :=
  by
  -- If one of the points `b`, `c`, `d` is equal to `a`, then the inequality is trivial.
  rcases eq_or_ne b a with (rfl | hb)
  · rw [dist_self, MulZeroClass.zero_mul, zero_add]
  rcases eq_or_ne c a with (rfl | hc)
  · rw [dist_self, MulZeroClass.zero_mul]
    apply_rules [add_nonneg, mul_nonneg, dist_nonneg]
  rcases eq_or_ne d a with (rfl | hd)
  · rw [dist_self, MulZeroClass.mul_zero, add_zero, dist_comm d, dist_comm d, mul_comm]
  /- Otherwise, we apply the triangle inequality to `euclidean_geometry.inversion a 1 b`,
    `euclidean_geometry.inversion a 1 c`, and `euclidean_geometry.inversion a 1 d`. -/
  have H := dist_triangle (inversion a 1 b) (inversion a 1 c) (inversion a 1 d)
  rw [dist_inversion_inversion hb hd, dist_inversion_inversion hb hc,
    dist_inversion_inversion hc hd, one_pow] at H
  rw [← dist_pos] at hb hc hd
  rw [← div_le_div_right (mul_pos hb (mul_pos hc hd))]
  convert H <;>
    · field_simp [hb.ne', hc.ne', hd.ne', dist_comm a]
      ring
#align euclidean_geometry.mul_dist_le_mul_dist_add_mul_dist EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist

end EuclideanGeometry

