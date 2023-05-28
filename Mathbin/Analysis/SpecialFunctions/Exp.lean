/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne

! This file was ported from Lean 3 source module analysis.special_functions.exp
! leanprover-community/mathlib commit ba5ff5ad5d120fb0ef094ad2994967e9bfaf5112
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Asymptotics.Theta
import Mathbin.Analysis.Complex.Basic
import Mathbin.Analysis.SpecificLimits.Normed

/-!
# Complex and real exponential

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove continuity of `complex.exp` and `real.exp`. We also prove a few facts about
limits of `real.exp` at infinity.

## Tags

exp
-/


noncomputable section

open Finset Filter Metric Asymptotics Set Function

open Classical Topology

namespace Complex

variable {z y x : ℝ}

/- warning: complex.exp_bound_sq -> Complex.exp_bound_sq is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (z : Complex), (LE.le.{0} Real Real.hasLe (Norm.norm.{0} Complex Complex.hasNorm z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{0} Complex Complex.hasNorm (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.exp (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) x z)) (Complex.exp x)) (SMul.smul.{0, 0} Complex Complex (Mul.toSMul.{0} Complex Complex.hasMul) z (Complex.exp x)))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{0} Complex Complex.hasNorm (Complex.exp x)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{0} Complex Complex.hasNorm z) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall (x : Complex) (z : Complex), (LE.le.{0} Real Real.instLEReal (Norm.norm.{0} Complex Complex.instNormComplex z) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{0} Complex Complex.instNormComplex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) x z)) (Complex.exp x)) (HSMul.hSMul.{0, 0, 0} Complex Complex Complex (instHSMul.{0, 0} Complex Complex (Algebra.toSMul.{0, 0} Complex Complex Complex.instCommSemiringComplex Complex.instSemiringComplex (NormedAlgebra.toAlgebra.{0, 0} Complex Complex Complex.instNormedFieldComplex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex))) (NormedAlgebra.id.{0} Complex Complex.instNormedFieldComplex)))) z (Complex.exp x)))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{0} Complex Complex.instNormComplex (Complex.exp x)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{0} Complex Complex.instNormComplex z) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align complex.exp_bound_sq Complex.exp_bound_sqₓ'. -/
theorem exp_bound_sq (x z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖exp (x + z) - exp x - z • exp x‖ ≤ ‖exp x‖ * ‖z‖ ^ 2 :=
  calc
    ‖exp (x + z) - exp x - z * exp x‖ = ‖exp x * (exp z - 1 - z)‖ := by congr ; rw [exp_add]; ring
    _ = ‖exp x‖ * ‖exp z - 1 - z‖ := (norm_mul _ _)
    _ ≤ ‖exp x‖ * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (abs_exp_sub_one_sub_id_le hz) (norm_nonneg _)
    
#align complex.exp_bound_sq Complex.exp_bound_sq

/- warning: complex.locally_lipschitz_exp -> Complex.locally_lipschitz_exp is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LE.le.{0} Real Real.hasLe r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (forall (x : Complex) (y : Complex), (LT.lt.{0} Real Real.hasLt (Norm.norm.{0} Complex Complex.hasNorm (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) y x)) r) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{0} Complex Complex.hasNorm (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) (Complex.exp y) (Complex.exp x))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) r) (Norm.norm.{0} Complex Complex.hasNorm (Complex.exp x))) (Norm.norm.{0} Complex Complex.hasNorm (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) y x)))))
but is expected to have type
  forall {r : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LE.le.{0} Real Real.instLEReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (forall (x : Complex) (y : Complex), (LT.lt.{0} Real Real.instLTReal (Norm.norm.{0} Complex Complex.instNormComplex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) y x)) r) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{0} Complex Complex.instNormComplex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.exp y) (Complex.exp x))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) r) (Norm.norm.{0} Complex Complex.instNormComplex (Complex.exp x))) (Norm.norm.{0} Complex Complex.instNormComplex (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) y x)))))
Case conversion may be inaccurate. Consider using '#align complex.locally_lipschitz_exp Complex.locally_lipschitz_expₓ'. -/
theorem locally_lipschitz_exp {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_le : r ≤ 1) (x y : ℂ)
    (hyx : ‖y - x‖ < r) : ‖exp y - exp x‖ ≤ (1 + r) * ‖exp x‖ * ‖y - x‖ :=
  by
  have hy_eq : y = x + (y - x) := by abel
  have hyx_sq_le : ‖y - x‖ ^ 2 ≤ r * ‖y - x‖ :=
    by
    rw [pow_two]
    exact mul_le_mul hyx.le le_rfl (norm_nonneg _) hr_nonneg
  have h_sq : ∀ z, ‖z‖ ≤ 1 → ‖exp (x + z) - exp x‖ ≤ ‖z‖ * ‖exp x‖ + ‖exp x‖ * ‖z‖ ^ 2 :=
    by
    intro z hz
    have : ‖exp (x + z) - exp x - z • exp x‖ ≤ ‖exp x‖ * ‖z‖ ^ 2 := exp_bound_sq x z hz
    rw [← sub_le_iff_le_add', ← norm_smul z (_ : ℂ)]
    exact (norm_sub_norm_le _ _).trans this
  calc
    ‖exp y - exp x‖ = ‖exp (x + (y - x)) - exp x‖ := by nth_rw 1 [hy_eq]
    _ ≤ ‖y - x‖ * ‖exp x‖ + ‖exp x‖ * ‖y - x‖ ^ 2 := (h_sq (y - x) (hyx.le.trans hr_le))
    _ ≤ ‖y - x‖ * ‖exp x‖ + ‖exp x‖ * (r * ‖y - x‖) :=
      (add_le_add_left (mul_le_mul le_rfl hyx_sq_le (sq_nonneg _) (norm_nonneg _)) _)
    _ = (1 + r) * ‖exp x‖ * ‖y - x‖ := by ring
    
#align complex.locally_lipschitz_exp Complex.locally_lipschitz_exp

/- warning: complex.continuous_exp -> Complex.continuous_exp is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) Complex.exp
but is expected to have type
  Continuous.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) Complex.exp
Case conversion may be inaccurate. Consider using '#align complex.continuous_exp Complex.continuous_expₓ'. -/
@[continuity]
theorem continuous_exp : Continuous exp :=
  continuous_iff_continuousAt.mpr fun x =>
    continuousAt_of_locally_lipschitz zero_lt_one (2 * ‖exp x‖)
      (locally_lipschitz_exp zero_le_one le_rfl x)
#align complex.continuous_exp Complex.continuous_exp

/- warning: complex.continuous_on_exp -> Complex.continuousOn_exp is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Complex}, ContinuousOn.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) Complex.exp s
but is expected to have type
  forall {s : Set.{0} Complex}, ContinuousOn.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) Complex.exp s
Case conversion may be inaccurate. Consider using '#align complex.continuous_on_exp Complex.continuousOn_expₓ'. -/
theorem continuousOn_exp {s : Set ℂ} : ContinuousOn exp s :=
  continuous_exp.ContinuousOn
#align complex.continuous_on_exp Complex.continuousOn_exp

end Complex

section ComplexContinuousExpComp

variable {α : Type _}

open Complex

/- warning: filter.tendsto.cexp -> Filter.Tendsto.cexp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {z : Complex}, (Filter.Tendsto.{u1, 0} α Complex f l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) z)) -> (Filter.Tendsto.{u1, 0} α Complex (fun (x : α) => Complex.exp (f x)) l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (Complex.exp z)))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {z : Complex}, (Filter.Tendsto.{u1, 0} α Complex f l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) z)) -> (Filter.Tendsto.{u1, 0} α Complex (fun (x : α) => Complex.exp (f x)) l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (Complex.exp z)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.cexp Filter.Tendsto.cexpₓ'. -/
theorem Filter.Tendsto.cexp {l : Filter α} {f : α → ℂ} {z : ℂ} (hf : Tendsto f l (𝓝 z)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp z)) :=
  (continuous_exp.Tendsto _).comp hf
#align filter.tendsto.cexp Filter.Tendsto.cexp

variable [TopologicalSpace α] {f : α → ℂ} {s : Set α} {x : α}

/- warning: continuous_within_at.cexp -> ContinuousWithinAt.cexp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f s x) -> (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (y : α) => Complex.exp (f y)) s x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f s x) -> (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (y : α) => Complex.exp (f y)) s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.cexp ContinuousWithinAt.cexpₓ'. -/
theorem ContinuousWithinAt.cexp (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun y => exp (f y)) s x :=
  h.cexp
#align continuous_within_at.cexp ContinuousWithinAt.cexp

/- warning: continuous_at.cexp -> ContinuousAt.cexp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {x : α}, (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f x) -> (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (y : α) => Complex.exp (f y)) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {x : α}, (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f x) -> (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (y : α) => Complex.exp (f y)) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.cexp ContinuousAt.cexpₓ'. -/
theorem ContinuousAt.cexp (h : ContinuousAt f x) : ContinuousAt (fun y => exp (f y)) x :=
  h.cexp
#align continuous_at.cexp ContinuousAt.cexp

/- warning: continuous_on.cexp -> ContinuousOn.cexp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α}, (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f s) -> (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (y : α) => Complex.exp (f y)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α}, (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f s) -> (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (y : α) => Complex.exp (f y)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.cexp ContinuousOn.cexpₓ'. -/
theorem ContinuousOn.cexp (h : ContinuousOn f s) : ContinuousOn (fun y => exp (f y)) s :=
  fun x hx => (h x hx).cexp
#align continuous_on.cexp ContinuousOn.cexp

/- warning: continuous.cexp -> Continuous.cexp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex}, (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f) -> (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (y : α) => Complex.exp (f y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex}, (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f) -> (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (y : α) => Complex.exp (f y)))
Case conversion may be inaccurate. Consider using '#align continuous.cexp Continuous.cexpₓ'. -/
theorem Continuous.cexp (h : Continuous f) : Continuous fun y => exp (f y) :=
  continuous_iff_continuousAt.2 fun x => h.ContinuousAt.cexp
#align continuous.cexp Continuous.cexp

end ComplexContinuousExpComp

namespace Real

#print Real.continuous_exp /-
@[continuity]
theorem continuous_exp : Continuous exp :=
  Complex.continuous_re.comp Complex.continuous_ofReal.cexp
#align real.continuous_exp Real.continuous_exp
-/

#print Real.continuousOn_exp /-
theorem continuousOn_exp {s : Set ℝ} : ContinuousOn exp s :=
  continuous_exp.ContinuousOn
#align real.continuous_on_exp Real.continuousOn_exp
-/

end Real

section RealContinuousExpComp

variable {α : Type _}

open Real

#print Filter.Tendsto.exp /-
theorem Filter.Tendsto.exp {l : Filter α} {f : α → ℝ} {z : ℝ} (hf : Tendsto f l (𝓝 z)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp z)) :=
  (continuous_exp.Tendsto _).comp hf
#align filter.tendsto.exp Filter.Tendsto.exp
-/

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {x : α}

#print ContinuousWithinAt.exp /-
theorem ContinuousWithinAt.exp (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun y => exp (f y)) s x :=
  h.exp
#align continuous_within_at.exp ContinuousWithinAt.exp
-/

#print ContinuousAt.exp /-
theorem ContinuousAt.exp (h : ContinuousAt f x) : ContinuousAt (fun y => exp (f y)) x :=
  h.exp
#align continuous_at.exp ContinuousAt.exp
-/

#print ContinuousOn.exp /-
theorem ContinuousOn.exp (h : ContinuousOn f s) : ContinuousOn (fun y => exp (f y)) s := fun x hx =>
  (h x hx).exp
#align continuous_on.exp ContinuousOn.exp
-/

#print Continuous.exp /-
theorem Continuous.exp (h : Continuous f) : Continuous fun y => exp (f y) :=
  continuous_iff_continuousAt.2 fun x => h.ContinuousAt.exp
#align continuous.exp Continuous.exp
-/

end RealContinuousExpComp

namespace Real

variable {α : Type _} {x y z : ℝ} {l : Filter α}

/- warning: real.exp_half -> Real.exp_half is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.exp (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Real.sqrt (Real.exp x))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.exp (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Real.sqrt (Real.exp x))
Case conversion may be inaccurate. Consider using '#align real.exp_half Real.exp_halfₓ'. -/
theorem exp_half (x : ℝ) : exp (x / 2) = sqrt (exp x) := by
  rw [eq_comm, sqrt_eq_iff_sq_eq, sq, ← exp_add, add_halves] <;> exact (exp_pos _).le
#align real.exp_half Real.exp_half

#print Real.tendsto_exp_atTop /-
/-- The real exponential function tends to `+∞` at `+∞`. -/
theorem tendsto_exp_atTop : Tendsto exp atTop atTop :=
  by
  have A : tendsto (fun x : ℝ => x + 1) at_top at_top :=
    tendsto_at_top_add_const_right at_top 1 tendsto_id
  have B : ∀ᶠ x in at_top, x + 1 ≤ exp x := eventually_at_top.2 ⟨0, fun x hx => add_one_le_exp x⟩
  exact tendsto_at_top_mono' at_top B A
#align real.tendsto_exp_at_top Real.tendsto_exp_atTop
-/

/- warning: real.tendsto_exp_neg_at_top_nhds_0 -> Real.tendsto_exp_neg_atTop_nhds_0 is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => Real.exp (Neg.neg.{0} Real Real.hasNeg x)) (Filter.atTop.{0} Real Real.preorder) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => Real.exp (Neg.neg.{0} Real Real.instNegReal x)) (Filter.atTop.{0} Real Real.instPreorderReal) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.tendsto_exp_neg_at_top_nhds_0 Real.tendsto_exp_neg_atTop_nhds_0ₓ'. -/
/-- The real exponential function tends to `0` at `-∞` or, equivalently, `exp(-x)` tends to `0`
at `+∞` -/
theorem tendsto_exp_neg_atTop_nhds_0 : Tendsto (fun x => exp (-x)) atTop (𝓝 0) :=
  (tendsto_inv_atTop_zero.comp tendsto_exp_atTop).congr fun x => (exp_neg x).symm
#align real.tendsto_exp_neg_at_top_nhds_0 Real.tendsto_exp_neg_atTop_nhds_0

/- warning: real.tendsto_exp_nhds_0_nhds_1 -> Real.tendsto_exp_nhds_0_nhds_1 is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real Real.exp (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real Real.exp (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.tendsto_exp_nhds_0_nhds_1 Real.tendsto_exp_nhds_0_nhds_1ₓ'. -/
/-- The real exponential function tends to `1` at `0`. -/
theorem tendsto_exp_nhds_0_nhds_1 : Tendsto exp (𝓝 0) (𝓝 1) := by convert continuous_exp.tendsto 0;
  simp
#align real.tendsto_exp_nhds_0_nhds_1 Real.tendsto_exp_nhds_0_nhds_1

/- warning: real.tendsto_exp_at_bot -> Real.tendsto_exp_atBot is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real Real.exp (Filter.atBot.{0} Real Real.preorder) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real Real.exp (Filter.atBot.{0} Real Real.instPreorderReal) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.tendsto_exp_at_bot Real.tendsto_exp_atBotₓ'. -/
theorem tendsto_exp_atBot : Tendsto exp atBot (𝓝 0) :=
  (tendsto_exp_neg_atTop_nhds_0.comp tendsto_neg_atBot_atTop).congr fun x =>
    congr_arg exp <| neg_neg x
#align real.tendsto_exp_at_bot Real.tendsto_exp_atBot

/- warning: real.tendsto_exp_at_bot_nhds_within -> Real.tendsto_exp_atBot_nhdsWithin is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real Real.exp (Filter.atBot.{0} Real Real.preorder) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real Real.exp (Filter.atBot.{0} Real Real.instPreorderReal) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.tendsto_exp_at_bot_nhds_within Real.tendsto_exp_atBot_nhdsWithinₓ'. -/
theorem tendsto_exp_atBot_nhdsWithin : Tendsto exp atBot (𝓝[>] 0) :=
  tendsto_inf.2 ⟨tendsto_exp_atBot, tendsto_principal.2 <| eventually_of_forall exp_pos⟩
#align real.tendsto_exp_at_bot_nhds_within Real.tendsto_exp_atBot_nhdsWithin

/- warning: real.is_bounded_under_ge_exp_comp -> Real.isBoundedUnder_ge_exp_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (l : Filter.{u1} α) (f : α -> Real), Filter.IsBoundedUnder.{0, u1} Real α (GE.ge.{0} Real Real.hasLe) l (fun (x : α) => Real.exp (f x))
but is expected to have type
  forall {α : Type.{u1}} (l : Filter.{u1} α) (f : α -> Real), Filter.IsBoundedUnder.{0, u1} Real α (fun (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.1807 : Real) (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.1809 : Real) => GE.ge.{0} Real Real.instLEReal x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.1807 x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.1809) l (fun (x : α) => Real.exp (f x))
Case conversion may be inaccurate. Consider using '#align real.is_bounded_under_ge_exp_comp Real.isBoundedUnder_ge_exp_compₓ'. -/
@[simp]
theorem isBoundedUnder_ge_exp_comp (l : Filter α) (f : α → ℝ) :
    IsBoundedUnder (· ≥ ·) l fun x => exp (f x) :=
  isBoundedUnder_of ⟨0, fun x => (exp_pos _).le⟩
#align real.is_bounded_under_ge_exp_comp Real.isBoundedUnder_ge_exp_comp

/- warning: real.is_bounded_under_le_exp_comp -> Real.isBoundedUnder_le_exp_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real}, Iff (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (fun (x : α) => Real.exp (f x))) (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l f)
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real}, Iff (Filter.IsBoundedUnder.{0, u1} Real α (fun (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.1869 : Real) (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.1871 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.1869 x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.1871) l (fun (x : α) => Real.exp (f x))) (Filter.IsBoundedUnder.{0, u1} Real α (fun (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.1894 : Real) (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.1896 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.1894 x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.1896) l f)
Case conversion may be inaccurate. Consider using '#align real.is_bounded_under_le_exp_comp Real.isBoundedUnder_le_exp_compₓ'. -/
@[simp]
theorem isBoundedUnder_le_exp_comp {f : α → ℝ} :
    (IsBoundedUnder (· ≤ ·) l fun x => exp (f x)) ↔ IsBoundedUnder (· ≤ ·) l f :=
  exp_monotone.isBoundedUnder_le_comp tendsto_exp_atTop
#align real.is_bounded_under_le_exp_comp Real.isBoundedUnder_le_exp_comp

/- warning: real.tendsto_exp_div_pow_at_top -> Real.tendsto_exp_div_pow_atTop is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.exp x) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n)) (Filter.atTop.{0} Real Real.preorder) (Filter.atTop.{0} Real Real.preorder)
but is expected to have type
  forall (n : Nat), Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.exp x) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n)) (Filter.atTop.{0} Real Real.instPreorderReal) (Filter.atTop.{0} Real Real.instPreorderReal)
Case conversion may be inaccurate. Consider using '#align real.tendsto_exp_div_pow_at_top Real.tendsto_exp_div_pow_atTopₓ'. -/
/-- The function `exp(x)/x^n` tends to `+∞` at `+∞`, for any natural number `n` -/
theorem tendsto_exp_div_pow_atTop (n : ℕ) : Tendsto (fun x => exp x / x ^ n) atTop atTop :=
  by
  refine' (at_top_basis_Ioi.tendsto_iff (at_top_basis' 1)).2 fun C hC₁ => _
  have hC₀ : 0 < C := zero_lt_one.trans_le hC₁
  have : 0 < (exp 1 * C)⁻¹ := inv_pos.2 (mul_pos (exp_pos _) hC₀)
  obtain ⟨N, hN⟩ : ∃ N, ∀ k ≥ N, (↑k ^ n : ℝ) / exp 1 ^ k < (exp 1 * C)⁻¹ :=
    eventually_at_top.1
      ((tendsto_pow_const_div_const_pow_of_one_lt n (one_lt_exp_iff.2 zero_lt_one)).Eventually
        (gt_mem_nhds this))
  simp only [← exp_nat_mul, mul_one, div_lt_iff, exp_pos, ← div_eq_inv_mul] at hN
  refine' ⟨N, trivial, fun x hx => _⟩; rw [Set.mem_Ioi] at hx
  have hx₀ : 0 < x := N.cast_nonneg.trans_lt hx
  rw [Set.mem_Ici, le_div_iff (pow_pos hx₀ _), ← le_div_iff' hC₀]
  calc
    x ^ n ≤ ⌈x⌉₊ ^ n := pow_le_pow_of_le_left hx₀.le (Nat.le_ceil _) _
    _ ≤ exp ⌈x⌉₊ / (exp 1 * C) := (hN _ (Nat.lt_ceil.2 hx).le).le
    _ ≤ exp (x + 1) / (exp 1 * C) :=
      (div_le_div_of_le (mul_pos (exp_pos _) hC₀).le
        (exp_le_exp.2 <| (Nat.ceil_lt_add_one hx₀.le).le))
    _ = exp x / C := by rw [add_comm, exp_add, mul_div_mul_left _ _ (exp_pos _).ne']
    
#align real.tendsto_exp_div_pow_at_top Real.tendsto_exp_div_pow_atTop

/- warning: real.tendsto_pow_mul_exp_neg_at_top_nhds_0 -> Real.tendsto_pow_mul_exp_neg_atTop_nhds_0 is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n) (Real.exp (Neg.neg.{0} Real Real.hasNeg x))) (Filter.atTop.{0} Real Real.preorder) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall (n : Nat), Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n) (Real.exp (Neg.neg.{0} Real Real.instNegReal x))) (Filter.atTop.{0} Real Real.instPreorderReal) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.tendsto_pow_mul_exp_neg_at_top_nhds_0 Real.tendsto_pow_mul_exp_neg_atTop_nhds_0ₓ'. -/
/-- The function `x^n * exp(-x)` tends to `0` at `+∞`, for any natural number `n`. -/
theorem tendsto_pow_mul_exp_neg_atTop_nhds_0 (n : ℕ) :
    Tendsto (fun x => x ^ n * exp (-x)) atTop (𝓝 0) :=
  (tendsto_inv_atTop_zero.comp (tendsto_exp_div_pow_atTop n)).congr fun x => by
    rw [comp_app, inv_eq_one_div, div_div_eq_mul_div, one_mul, div_eq_mul_inv, exp_neg]
#align real.tendsto_pow_mul_exp_neg_at_top_nhds_0 Real.tendsto_pow_mul_exp_neg_atTop_nhds_0

/- warning: real.tendsto_mul_exp_add_div_pow_at_top -> Real.tendsto_mul_exp_add_div_pow_atTop is a dubious translation:
lean 3 declaration is
  forall (b : Real) (c : Real) (n : Nat), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) b (Real.exp x)) c) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n)) (Filter.atTop.{0} Real Real.preorder) (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  forall (b : Real) (c : Real) (n : Nat), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) b (Real.exp x)) c) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n)) (Filter.atTop.{0} Real Real.instPreorderReal) (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align real.tendsto_mul_exp_add_div_pow_at_top Real.tendsto_mul_exp_add_div_pow_atTopₓ'. -/
/-- The function `(b * exp x + c) / (x ^ n)` tends to `+∞` at `+∞`, for any natural number
`n` and any real numbers `b` and `c` such that `b` is positive. -/
theorem tendsto_mul_exp_add_div_pow_atTop (b c : ℝ) (n : ℕ) (hb : 0 < b) :
    Tendsto (fun x => (b * exp x + c) / x ^ n) atTop atTop :=
  by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp only [pow_zero, div_one]
    exact (tendsto_exp_at_top.const_mul_at_top hb).atTop_add tendsto_const_nhds
  simp only [add_div, mul_div_assoc]
  exact
    ((tendsto_exp_div_pow_at_top n).const_mul_atTop hb).atTop_add
      (tendsto_const_nhds.div_at_top (tendsto_pow_at_top hn))
#align real.tendsto_mul_exp_add_div_pow_at_top Real.tendsto_mul_exp_add_div_pow_atTop

/- warning: real.tendsto_div_pow_mul_exp_add_at_top -> Real.tendsto_div_pow_mul_exp_add_atTop is a dubious translation:
lean 3 declaration is
  forall (b : Real) (c : Real) (n : Nat), (Ne.{1} Real (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) b (Real.exp x)) c)) (Filter.atTop.{0} Real Real.preorder) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall (b : Real) (c : Real) (n : Nat), (Ne.{1} Real (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) b (Real.exp x)) c)) (Filter.atTop.{0} Real Real.instPreorderReal) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.tendsto_div_pow_mul_exp_add_at_top Real.tendsto_div_pow_mul_exp_add_atTopₓ'. -/
/-- The function `(x ^ n) / (b * exp x + c)` tends to `0` at `+∞`, for any natural number
`n` and any real numbers `b` and `c` such that `b` is nonzero. -/
theorem tendsto_div_pow_mul_exp_add_atTop (b c : ℝ) (n : ℕ) (hb : 0 ≠ b) :
    Tendsto (fun x => x ^ n / (b * exp x + c)) atTop (𝓝 0) :=
  by
  have H : ∀ d e, 0 < d → tendsto (fun x : ℝ => x ^ n / (d * exp x + e)) at_top (𝓝 0) :=
    by
    intro b' c' h
    convert(tendsto_mul_exp_add_div_pow_at_top b' c' n h).inv_tendsto_atTop
    ext x
    simpa only [Pi.inv_apply] using (inv_div _ _).symm
  cases lt_or_gt_of_ne hb
  · exact H b c h
  · convert(H (-b) (-c) (neg_pos.mpr h)).neg
    · ext x
      field_simp
      rw [← neg_add (b * exp x) c, neg_div_neg_eq]
    · exact neg_zero.symm
#align real.tendsto_div_pow_mul_exp_add_at_top Real.tendsto_div_pow_mul_exp_add_atTop

/- warning: real.exp_order_iso -> Real.expOrderIso is a dubious translation:
lean 3 declaration is
  OrderIso.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real.hasLe (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))
but is expected to have type
  OrderIso.{0, 0} Real (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real.instLEReal (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))))
Case conversion may be inaccurate. Consider using '#align real.exp_order_iso Real.expOrderIsoₓ'. -/
/-- `real.exp` as an order isomorphism between `ℝ` and `(0, +∞)`. -/
def expOrderIso : ℝ ≃o Ioi (0 : ℝ) :=
  StrictMono.orderIsoOfSurjective _ (exp_strictMono.codRestrict exp_pos) <|
    (continuous_exp.subtype_mk _).Surjective
      (by simp only [tendsto_Ioi_at_top, Subtype.coe_mk, tendsto_exp_at_top])
      (by simp [tendsto_exp_at_bot_nhds_within])
#align real.exp_order_iso Real.expOrderIso

/- warning: real.coe_exp_order_iso_apply -> Real.coe_expOrderIso_apply is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))))) (coeFn.{1, 1} (OrderIso.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real.hasLe (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))) (fun (_x : RelIso.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (LE.le.{0} Real Real.hasLe) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))))) => Real -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) (RelIso.hasCoeToFun.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (LE.le.{0} Real Real.hasLe) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))))) Real.expOrderIso x)) (Real.exp x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (FunLike.coe.{1, 1, 1} (RelIso.{0, 0} Real (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) Real (fun (_x : Real) => Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (RelHomClass.toFunLike.{0, 0, 0} (RelIso.{0, 0} Real (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) Real (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{0, 0} Real (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) Real.expOrderIso x)) (Real.exp x)
Case conversion may be inaccurate. Consider using '#align real.coe_exp_order_iso_apply Real.coe_expOrderIso_applyₓ'. -/
@[simp]
theorem coe_expOrderIso_apply (x : ℝ) : (expOrderIso x : ℝ) = exp x :=
  rfl
#align real.coe_exp_order_iso_apply Real.coe_expOrderIso_apply

/- warning: real.coe_comp_exp_order_iso -> Real.coe_comp_expOrderIso is a dubious translation:
lean 3 declaration is
  Eq.{1} (Real -> Real) (Function.comp.{1, 1, 1} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))))))) (coeFn.{1, 1} (OrderIso.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real.hasLe (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))) (fun (_x : RelIso.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (LE.le.{0} Real Real.hasLe) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))))) => Real -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) (RelIso.hasCoeToFun.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (LE.le.{0} Real Real.hasLe) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))))) Real.expOrderIso)) Real.exp
but is expected to have type
  Eq.{1} (Real -> Real) (Function.comp.{1, 1, 1} Real (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) (FunLike.coe.{1, 1, 1} (RelIso.{0, 0} Real (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) Real (fun (_x : Real) => Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (RelHomClass.toFunLike.{0, 0, 0} (RelIso.{0, 0} Real (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) Real (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{0, 0} Real (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) Real.expOrderIso)) Real.exp
Case conversion may be inaccurate. Consider using '#align real.coe_comp_exp_order_iso Real.coe_comp_expOrderIsoₓ'. -/
@[simp]
theorem coe_comp_expOrderIso : coe ∘ expOrderIso = exp :=
  rfl
#align real.coe_comp_exp_order_iso Real.coe_comp_expOrderIso

/- warning: real.range_exp -> Real.range_exp is a dubious translation:
lean 3 declaration is
  Eq.{1} (Set.{0} Real) (Set.range.{0, 1} Real Real Real.exp) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  Eq.{1} (Set.{0} Real) (Set.range.{0, 1} Real Real Real.exp) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.range_exp Real.range_expₓ'. -/
@[simp]
theorem range_exp : range exp = Ioi 0 := by
  rw [← coe_comp_exp_order_iso, range_comp, exp_order_iso.range_eq, image_univ, Subtype.range_coe]
#align real.range_exp Real.range_exp

#print Real.map_exp_atTop /-
@[simp]
theorem map_exp_atTop : map exp atTop = atTop := by
  rw [← coe_comp_exp_order_iso, ← Filter.map_map, OrderIso.map_atTop, map_coe_Ioi_at_top]
#align real.map_exp_at_top Real.map_exp_atTop
-/

#print Real.comap_exp_atTop /-
@[simp]
theorem comap_exp_atTop : comap exp atTop = atTop := by
  rw [← map_exp_at_top, comap_map exp_injective, map_exp_at_top]
#align real.comap_exp_at_top Real.comap_exp_atTop
-/

#print Real.tendsto_exp_comp_atTop /-
@[simp]
theorem tendsto_exp_comp_atTop {f : α → ℝ} :
    Tendsto (fun x => exp (f x)) l atTop ↔ Tendsto f l atTop := by
  rw [← tendsto_comap_iff, comap_exp_at_top]
#align real.tendsto_exp_comp_at_top Real.tendsto_exp_comp_atTop
-/

#print Real.tendsto_comp_exp_atTop /-
theorem tendsto_comp_exp_atTop {f : ℝ → α} :
    Tendsto (fun x => f (exp x)) atTop l ↔ Tendsto f atTop l := by
  rw [← tendsto_map'_iff, map_exp_at_top]
#align real.tendsto_comp_exp_at_top Real.tendsto_comp_exp_atTop
-/

/- warning: real.map_exp_at_bot -> Real.map_exp_atBot is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} Real) (Filter.map.{0, 0} Real Real Real.exp (Filter.atBot.{0} Real Real.preorder)) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  Eq.{1} (Filter.{0} Real) (Filter.map.{0, 0} Real Real Real.exp (Filter.atBot.{0} Real Real.instPreorderReal)) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.map_exp_at_bot Real.map_exp_atBotₓ'. -/
@[simp]
theorem map_exp_atBot : map exp atBot = 𝓝[>] 0 := by
  rw [← coe_comp_exp_order_iso, ← Filter.map_map, exp_order_iso.map_at_bot, ← map_coe_Ioi_atBot]
#align real.map_exp_at_bot Real.map_exp_atBot

/- warning: real.comap_exp_nhds_within_Ioi_zero -> Real.comap_exp_nhdsWithin_Ioi_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} Real) (Filter.comap.{0, 0} Real Real Real.exp (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) (Filter.atBot.{0} Real Real.preorder)
but is expected to have type
  Eq.{1} (Filter.{0} Real) (Filter.comap.{0, 0} Real Real Real.exp (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) (Filter.atBot.{0} Real Real.instPreorderReal)
Case conversion may be inaccurate. Consider using '#align real.comap_exp_nhds_within_Ioi_zero Real.comap_exp_nhdsWithin_Ioi_zeroₓ'. -/
@[simp]
theorem comap_exp_nhdsWithin_Ioi_zero : comap exp (𝓝[>] 0) = atBot := by
  rw [← map_exp_at_bot, comap_map exp_injective]
#align real.comap_exp_nhds_within_Ioi_zero Real.comap_exp_nhdsWithin_Ioi_zero

/- warning: real.tendsto_comp_exp_at_bot -> Real.tendsto_comp_exp_atBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : Real -> α}, Iff (Filter.Tendsto.{0, u1} Real α (fun (x : Real) => f (Real.exp x)) (Filter.atBot.{0} Real Real.preorder) l) (Filter.Tendsto.{0, u1} Real α f (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) l)
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : Real -> α}, Iff (Filter.Tendsto.{0, u1} Real α (fun (x : Real) => f (Real.exp x)) (Filter.atBot.{0} Real Real.instPreorderReal) l) (Filter.Tendsto.{0, u1} Real α f (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) l)
Case conversion may be inaccurate. Consider using '#align real.tendsto_comp_exp_at_bot Real.tendsto_comp_exp_atBotₓ'. -/
theorem tendsto_comp_exp_atBot {f : ℝ → α} :
    Tendsto (fun x => f (exp x)) atBot l ↔ Tendsto f (𝓝[>] 0) l := by
  rw [← map_exp_at_bot, tendsto_map'_iff]
#align real.tendsto_comp_exp_at_bot Real.tendsto_comp_exp_atBot

/- warning: real.comap_exp_nhds_zero -> Real.comap_exp_nhds_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} Real) (Filter.comap.{0, 0} Real Real Real.exp (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Filter.atBot.{0} Real Real.preorder)
but is expected to have type
  Eq.{1} (Filter.{0} Real) (Filter.comap.{0, 0} Real Real Real.exp (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Filter.atBot.{0} Real Real.instPreorderReal)
Case conversion may be inaccurate. Consider using '#align real.comap_exp_nhds_zero Real.comap_exp_nhds_zeroₓ'. -/
@[simp]
theorem comap_exp_nhds_zero : comap exp (𝓝 0) = atBot :=
  (comap_nhdsWithin_range exp 0).symm.trans <| by simp
#align real.comap_exp_nhds_zero Real.comap_exp_nhds_zero

/- warning: real.tendsto_exp_comp_nhds_zero -> Real.tendsto_exp_comp_nhds_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real}, Iff (Filter.Tendsto.{u1, 0} α Real (fun (x : α) => Real.exp (f x)) l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Filter.Tendsto.{u1, 0} α Real f l (Filter.atBot.{0} Real Real.preorder))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real}, Iff (Filter.Tendsto.{u1, 0} α Real (fun (x : α) => Real.exp (f x)) l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Filter.Tendsto.{u1, 0} α Real f l (Filter.atBot.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align real.tendsto_exp_comp_nhds_zero Real.tendsto_exp_comp_nhds_zeroₓ'. -/
@[simp]
theorem tendsto_exp_comp_nhds_zero {f : α → ℝ} :
    Tendsto (fun x => exp (f x)) l (𝓝 0) ↔ Tendsto f l atBot := by
  rw [← tendsto_comap_iff, comap_exp_nhds_zero]
#align real.tendsto_exp_comp_nhds_zero Real.tendsto_exp_comp_nhds_zero

/- warning: real.is_o_pow_exp_at_top -> Real.isLittleO_pow_exp_atTop is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Real Real.preorder) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n) Real.exp
but is expected to have type
  forall {n : Nat}, Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm (Filter.atTop.{0} Real Real.instPreorderReal) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n) Real.exp
Case conversion may be inaccurate. Consider using '#align real.is_o_pow_exp_at_top Real.isLittleO_pow_exp_atTopₓ'. -/
theorem isLittleO_pow_exp_atTop {n : ℕ} : (fun x => x ^ n) =o[atTop] Real.exp := by
  simpa [is_o_iff_tendsto fun x hx => ((exp_pos x).ne' hx).elim] using
    tendsto_div_pow_mul_exp_add_at_top 1 0 n zero_ne_one
#align real.is_o_pow_exp_at_top Real.isLittleO_pow_exp_atTop

/- warning: real.is_O_exp_comp_exp_comp -> Real.isBigO_exp_comp_exp_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real}, Iff (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Real.exp (f x)) (fun (x : α) => Real.exp (g x))) (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (HSub.hSub.{u1, u1, u1} (α -> Real) (α -> Real) (α -> Real) (instHSub.{u1} (α -> Real) (Pi.instSub.{u1, 0} α (fun (ᾰ : α) => Real) (fun (i : α) => Real.hasSub))) f g))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real}, Iff (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Real.exp (f x)) (fun (x : α) => Real.exp (g x))) (Filter.IsBoundedUnder.{0, u1} Real α (fun (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.3755 : Real) (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.3757 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.3755 x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.3757) l (HSub.hSub.{u1, u1, u1} (α -> Real) (α -> Real) (α -> Real) (instHSub.{u1} (α -> Real) (Pi.instSub.{u1, 0} α (fun (ᾰ : α) => Real) (fun (i : α) => Real.instSubReal))) f g))
Case conversion may be inaccurate. Consider using '#align real.is_O_exp_comp_exp_comp Real.isBigO_exp_comp_exp_compₓ'. -/
@[simp]
theorem isBigO_exp_comp_exp_comp {f g : α → ℝ} :
    ((fun x => exp (f x)) =O[l] fun x => exp (g x)) ↔ IsBoundedUnder (· ≤ ·) l (f - g) :=
  Iff.trans (isBigO_iff_isBoundedUnder_le_div <| eventually_of_forall fun x => exp_ne_zero _) <| by
    simp only [norm_eq_abs, abs_exp, ← exp_sub, is_bounded_under_le_exp_comp, Pi.sub_def]
#align real.is_O_exp_comp_exp_comp Real.isBigO_exp_comp_exp_comp

/- warning: real.is_Theta_exp_comp_exp_comp -> Real.isTheta_exp_comp_exp_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real}, Iff (Asymptotics.IsTheta.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Real.exp (f x)) (fun (x : α) => Real.exp (g x))) (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (f x) (g x))))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real}, Iff (Asymptotics.IsTheta.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Real.exp (f x)) (fun (x : α) => Real.exp (g x))) (Filter.IsBoundedUnder.{0, u1} Real α (fun (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.3854 : Real) (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.3856 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.3854 x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.3856) l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (f x) (g x))))
Case conversion may be inaccurate. Consider using '#align real.is_Theta_exp_comp_exp_comp Real.isTheta_exp_comp_exp_compₓ'. -/
@[simp]
theorem isTheta_exp_comp_exp_comp {f g : α → ℝ} :
    ((fun x => exp (f x)) =Θ[l] fun x => exp (g x)) ↔
      IsBoundedUnder (· ≤ ·) l fun x => |f x - g x| :=
  by
  simp only [is_bounded_under_le_abs, ← is_bounded_under_le_neg, neg_sub, is_Theta,
    is_O_exp_comp_exp_comp, Pi.sub_def]
#align real.is_Theta_exp_comp_exp_comp Real.isTheta_exp_comp_exp_comp

/- warning: real.is_o_exp_comp_exp_comp -> Real.isLittleO_exp_comp_exp_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real}, Iff (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Real.exp (f x)) (fun (x : α) => Real.exp (g x))) (Filter.Tendsto.{u1, 0} α Real (fun (x : α) => HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (g x) (f x)) l (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real}, Iff (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Real.exp (f x)) (fun (x : α) => Real.exp (g x))) (Filter.Tendsto.{u1, 0} α Real (fun (x : α) => HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (g x) (f x)) l (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align real.is_o_exp_comp_exp_comp Real.isLittleO_exp_comp_exp_compₓ'. -/
@[simp]
theorem isLittleO_exp_comp_exp_comp {f g : α → ℝ} :
    ((fun x => exp (f x)) =o[l] fun x => exp (g x)) ↔ Tendsto (fun x => g x - f x) l atTop := by
  simp only [is_o_iff_tendsto, exp_ne_zero, ← exp_sub, ← tendsto_neg_at_top_iff, false_imp_iff,
    imp_true_iff, tendsto_exp_comp_nhds_zero, neg_sub]
#align real.is_o_exp_comp_exp_comp Real.isLittleO_exp_comp_exp_comp

/- warning: real.is_o_one_exp_comp -> Real.isLittleO_one_exp_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real}, Iff (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (fun (x : α) => Real.exp (f x))) (Filter.Tendsto.{u1, 0} α Real f l (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real}, Iff (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (fun (x : α) => Real.exp (f x))) (Filter.Tendsto.{u1, 0} α Real f l (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align real.is_o_one_exp_comp Real.isLittleO_one_exp_compₓ'. -/
@[simp]
theorem isLittleO_one_exp_comp {f : α → ℝ} :
    ((fun x => 1 : α → ℝ) =o[l] fun x => exp (f x)) ↔ Tendsto f l atTop := by
  simp only [← exp_zero, is_o_exp_comp_exp_comp, sub_zero]
#align real.is_o_one_exp_comp Real.isLittleO_one_exp_comp

/- warning: real.is_O_one_exp_comp -> Real.isBigO_one_exp_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real}, Iff (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (fun (x : α) => Real.exp (f x))) (Filter.IsBoundedUnder.{0, u1} Real α (GE.ge.{0} Real Real.hasLe) l f)
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real}, Iff (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (fun (x : α) => Real.exp (f x))) (Filter.IsBoundedUnder.{0, u1} Real α (fun (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.4068 : Real) (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.4070 : Real) => GE.ge.{0} Real Real.instLEReal x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.4068 x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.4070) l f)
Case conversion may be inaccurate. Consider using '#align real.is_O_one_exp_comp Real.isBigO_one_exp_compₓ'. -/
/-- `real.exp (f x)` is bounded away from zero along a filter if and only if this filter is bounded
from below under `f`. -/
@[simp]
theorem isBigO_one_exp_comp {f : α → ℝ} :
    ((fun x => 1 : α → ℝ) =O[l] fun x => exp (f x)) ↔ IsBoundedUnder (· ≥ ·) l f := by
  simp only [← exp_zero, is_O_exp_comp_exp_comp, Pi.sub_def, zero_sub, is_bounded_under_le_neg]
#align real.is_O_one_exp_comp Real.isBigO_one_exp_comp

/- warning: real.is_O_exp_comp_one -> Real.isBigO_exp_comp_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real}, Iff (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Real.exp (f x)) (fun (x : α) => OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l f)
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real}, Iff (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Real.exp (f x)) (fun (x : α) => OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Filter.IsBoundedUnder.{0, u1} Real α (fun (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.4144 : Real) (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.4146 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.4144 x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.4146) l f)
Case conversion may be inaccurate. Consider using '#align real.is_O_exp_comp_one Real.isBigO_exp_comp_oneₓ'. -/
/-- `real.exp (f x)` is bounded away from zero along a filter if and only if this filter is bounded
from below under `f`. -/
theorem isBigO_exp_comp_one {f : α → ℝ} :
    (fun x => exp (f x)) =O[l] (fun x => 1 : α → ℝ) ↔ IsBoundedUnder (· ≤ ·) l f := by
  simp only [is_O_one_iff, norm_eq_abs, abs_exp, is_bounded_under_le_exp_comp]
#align real.is_O_exp_comp_one Real.isBigO_exp_comp_one

/- warning: real.is_Theta_exp_comp_one -> Real.isTheta_exp_comp_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real}, Iff (Asymptotics.IsTheta.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Real.exp (f x)) (fun (x : α) => OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (f x)))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real}, Iff (Asymptotics.IsTheta.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Real.exp (f x)) (fun (x : α) => OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Filter.IsBoundedUnder.{0, u1} Real α (fun (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.4220 : Real) (x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.4222 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.4220 x._@.Mathlib.Analysis.SpecialFunctions.Exp._hyg.4222) l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (f x)))
Case conversion may be inaccurate. Consider using '#align real.is_Theta_exp_comp_one Real.isTheta_exp_comp_oneₓ'. -/
/-- `real.exp (f x)` is bounded away from zero and infinity along a filter `l` if and only if
`|f x|` is bounded from above along this filter. -/
@[simp]
theorem isTheta_exp_comp_one {f : α → ℝ} :
    (fun x => exp (f x)) =Θ[l] (fun x => 1 : α → ℝ) ↔ IsBoundedUnder (· ≤ ·) l fun x => |f x| := by
  simp only [← exp_zero, is_Theta_exp_comp_exp_comp, sub_zero]
#align real.is_Theta_exp_comp_one Real.isTheta_exp_comp_one

end Real

namespace Complex

/- warning: complex.comap_exp_comap_abs_at_top -> Complex.comap_exp_comap_abs_atTop is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} Complex) (Filter.comap.{0, 0} Complex Complex Complex.exp (Filter.comap.{0, 0} Complex Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs) (Filter.atTop.{0} Real Real.preorder))) (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  Eq.{1} (Filter.{0} Complex) (Filter.comap.{0, 0} Complex Complex Complex.exp (Filter.comap.{0, 0} Complex Real (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs) (Filter.atTop.{0} Real Real.instPreorderReal))) (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align complex.comap_exp_comap_abs_at_top Complex.comap_exp_comap_abs_atTopₓ'. -/
theorem comap_exp_comap_abs_atTop : comap exp (comap abs atTop) = comap re atTop :=
  calc
    comap exp (comap abs atTop) = comap re (comap Real.exp atTop) := by
      simp only [comap_comap, (· ∘ ·), abs_exp]
    _ = comap re atTop := by rw [Real.comap_exp_atTop]
    
#align complex.comap_exp_comap_abs_at_top Complex.comap_exp_comap_abs_atTop

/- warning: complex.comap_exp_nhds_zero -> Complex.comap_exp_nhds_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} Complex) (Filter.comap.{0, 0} Complex Complex Complex.exp (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))))) (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atBot.{0} Real Real.preorder))
but is expected to have type
  Eq.{1} (Filter.{0} Complex) (Filter.comap.{0, 0} Complex Complex Complex.exp (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)))) (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atBot.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align complex.comap_exp_nhds_zero Complex.comap_exp_nhds_zeroₓ'. -/
theorem comap_exp_nhds_zero : comap exp (𝓝 0) = comap re atBot :=
  calc
    comap exp (𝓝 0) = comap re (comap Real.exp (𝓝 0)) := by
      simp only [comap_comap, ← comap_abs_nhds_zero, (· ∘ ·), abs_exp]
    _ = comap re atBot := by rw [Real.comap_exp_nhds_zero]
    
#align complex.comap_exp_nhds_zero Complex.comap_exp_nhds_zero

/- warning: complex.comap_exp_nhds_within_zero -> Complex.comap_exp_nhdsWithin_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} Complex) (Filter.comap.{0, 0} Complex Complex Complex.exp (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))) (HasCompl.compl.{0} (Set.{0} Complex) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Complex) (Set.booleanAlgebra.{0} Complex)) (Singleton.singleton.{0, 0} Complex (Set.{0} Complex) (Set.hasSingleton.{0} Complex) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))))))) (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atBot.{0} Real Real.preorder))
but is expected to have type
  Eq.{1} (Filter.{0} Complex) (Filter.comap.{0, 0} Complex Complex Complex.exp (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)) (HasCompl.compl.{0} (Set.{0} Complex) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Complex) (Set.instBooleanAlgebraSet.{0} Complex)) (Singleton.singleton.{0, 0} Complex (Set.{0} Complex) (Set.instSingletonSet.{0} Complex) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)))))) (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atBot.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align complex.comap_exp_nhds_within_zero Complex.comap_exp_nhdsWithin_zeroₓ'. -/
theorem comap_exp_nhdsWithin_zero : comap exp (𝓝[≠] 0) = comap re atBot :=
  by
  have : exp ⁻¹' {0}ᶜ = univ := eq_univ_of_forall exp_ne_zero
  simp [nhdsWithin, comap_exp_nhds_zero, this]
#align complex.comap_exp_nhds_within_zero Complex.comap_exp_nhdsWithin_zero

/- warning: complex.tendsto_exp_nhds_zero_iff -> Complex.tendsto_exp_nhds_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex}, Iff (Filter.Tendsto.{u1, 0} α Complex (fun (x : α) => Complex.exp (f x)) l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))))) (Filter.Tendsto.{u1, 0} α Real (fun (x : α) => Complex.re (f x)) l (Filter.atBot.{0} Real Real.preorder))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex}, Iff (Filter.Tendsto.{u1, 0} α Complex (fun (x : α) => Complex.exp (f x)) l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)))) (Filter.Tendsto.{u1, 0} α Real (fun (x : α) => Complex.re (f x)) l (Filter.atBot.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align complex.tendsto_exp_nhds_zero_iff Complex.tendsto_exp_nhds_zero_iffₓ'. -/
theorem tendsto_exp_nhds_zero_iff {α : Type _} {l : Filter α} {f : α → ℂ} :
    Tendsto (fun x => exp (f x)) l (𝓝 0) ↔ Tendsto (fun x => re (f x)) l atBot := by
  rw [← tendsto_comap_iff, comap_exp_nhds_zero, tendsto_comap_iff]
#align complex.tendsto_exp_nhds_zero_iff Complex.tendsto_exp_nhds_zero_iff

/- warning: complex.tendsto_exp_comap_re_at_top -> Complex.tendsto_exp_comap_re_atTop is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Complex Complex Complex.exp (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atTop.{0} Real Real.preorder)) (Filter.comap.{0, 0} Complex Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs) (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  Filter.Tendsto.{0, 0} Complex Complex Complex.exp (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atTop.{0} Real Real.instPreorderReal)) (Filter.comap.{0, 0} Complex Real (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs) (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align complex.tendsto_exp_comap_re_at_top Complex.tendsto_exp_comap_re_atTopₓ'. -/
/-- `complex.abs (complex.exp z) → ∞` as `complex.re z → ∞`. TODO: use `bornology.cobounded`. -/
theorem tendsto_exp_comap_re_atTop : Tendsto exp (comap re atTop) (comap abs atTop) :=
  comap_exp_comap_abs_atTop ▸ tendsto_comap
#align complex.tendsto_exp_comap_re_at_top Complex.tendsto_exp_comap_re_atTop

/- warning: complex.tendsto_exp_comap_re_at_bot -> Complex.tendsto_exp_comap_re_atBot is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Complex Complex Complex.exp (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atBot.{0} Real Real.preorder)) (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))))
but is expected to have type
  Filter.Tendsto.{0, 0} Complex Complex Complex.exp (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atBot.{0} Real Real.instPreorderReal)) (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)))
Case conversion may be inaccurate. Consider using '#align complex.tendsto_exp_comap_re_at_bot Complex.tendsto_exp_comap_re_atBotₓ'. -/
/-- `complex.exp z → 0` as `complex.re z → -∞`.-/
theorem tendsto_exp_comap_re_atBot : Tendsto exp (comap re atBot) (𝓝 0) :=
  comap_exp_nhds_zero ▸ tendsto_comap
#align complex.tendsto_exp_comap_re_at_bot Complex.tendsto_exp_comap_re_atBot

/- warning: complex.tendsto_exp_comap_re_at_bot_nhds_within -> Complex.tendsto_exp_comap_re_atBot_nhdsWithin is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Complex Complex Complex.exp (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atBot.{0} Real Real.preorder)) (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))) (HasCompl.compl.{0} (Set.{0} Complex) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Complex) (Set.booleanAlgebra.{0} Complex)) (Singleton.singleton.{0, 0} Complex (Set.{0} Complex) (Set.hasSingleton.{0} Complex) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))))))
but is expected to have type
  Filter.Tendsto.{0, 0} Complex Complex Complex.exp (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atBot.{0} Real Real.instPreorderReal)) (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)) (HasCompl.compl.{0} (Set.{0} Complex) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Complex) (Set.instBooleanAlgebraSet.{0} Complex)) (Singleton.singleton.{0, 0} Complex (Set.{0} Complex) (Set.instSingletonSet.{0} Complex) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)))))
Case conversion may be inaccurate. Consider using '#align complex.tendsto_exp_comap_re_at_bot_nhds_within Complex.tendsto_exp_comap_re_atBot_nhdsWithinₓ'. -/
theorem tendsto_exp_comap_re_atBot_nhdsWithin : Tendsto exp (comap re atBot) (𝓝[≠] 0) :=
  comap_exp_nhdsWithin_zero ▸ tendsto_comap
#align complex.tendsto_exp_comap_re_at_bot_nhds_within Complex.tendsto_exp_comap_re_atBot_nhdsWithin

end Complex

