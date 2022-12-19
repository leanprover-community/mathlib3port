/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne

! This file was ported from Lean 3 source module analysis.special_functions.pow_deriv
! leanprover-community/mathlib commit bbeb185db4ccee8ed07dc48449414ebfa39cb821
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Pow
import Mathbin.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathbin.Analysis.Calculus.ExtendDeriv
import Mathbin.Analysis.SpecialFunctions.Log.Deriv
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Derivatives of power function on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`

We also prove differentiability and provide derivatives for the power functions `x ^ y`.
-/


noncomputable section

open Classical Real TopologicalSpace Nnreal Ennreal Filter

open Filter

namespace Complex

theorem hasStrictFderivAtCpow {p : ℂ × ℂ} (hp : 0 < p.1.re ∨ p.1.im ≠ 0) :
    HasStrictFderivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℂ ℂ ℂ)
      p :=
  by
  have A : p.1 ≠ 0 := by 
    intro h
    simpa [h, lt_irrefl] using hp
  have : (fun x : ℂ × ℂ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    ((is_open_ne.preimage continuous_fst).eventually_mem A).mono fun p hp =>
      cpow_def_of_ne_zero hp _
  rw [cpow_sub _ _ A, cpow_one, mul_div_left_comm, mul_smul, mul_smul, ← smul_add]
  refine' HasStrictFderivAt.congrOfEventuallyEq _ this.symm
  simpa only [cpow_def_of_ne_zero A, div_eq_mul_inv, mul_smul, add_comm] using
    ((has_strict_fderiv_at_fst.clog hp).mul hasStrictFderivAtSnd).cexp
#align complex.has_strict_fderiv_at_cpow Complex.hasStrictFderivAtCpow

theorem hasStrictFderivAtCpow' {x y : ℂ} (hp : 0 < x.re ∨ x.im ≠ 0) :
    HasStrictFderivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((y * x ^ (y - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (x ^ y * log x) • ContinuousLinearMap.snd ℂ ℂ ℂ)
      (x, y) :=
  @hasStrictFderivAtCpow (x, y) hp
#align complex.has_strict_fderiv_at_cpow' Complex.hasStrictFderivAtCpow'

theorem hasStrictDerivAtConstCpow {x y : ℂ} (h : x ≠ 0 ∨ y ≠ 0) :
    HasStrictDerivAt (fun y => x ^ y) (x ^ y * log x) y := by
  rcases em (x = 0) with (rfl | hx)
  · replace h := h.neg_resolve_left rfl
    rw [log_zero, mul_zero]
    refine' (hasStrictDerivAtConst _ 0).congr_of_eventually_eq _
    exact (is_open_ne.eventually_mem h).mono fun y hy => (zero_cpow hy).symm
  ·
    simpa only [cpow_def_of_ne_zero hx, mul_one] using
      ((hasStrictDerivAtId y).const_mul (log x)).cexp
#align complex.has_strict_deriv_at_const_cpow Complex.hasStrictDerivAtConstCpow

theorem hasFderivAtCpow {p : ℂ × ℂ} (hp : 0 < p.1.re ∨ p.1.im ≠ 0) :
    HasFderivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℂ ℂ ℂ)
      p :=
  (hasStrictFderivAtCpow hp).HasFderivAt
#align complex.has_fderiv_at_cpow Complex.hasFderivAtCpow

end Complex

section fderiv

open Complex

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {f' g' : E →L[ℂ] ℂ}
  {x : E} {s : Set E} {c : ℂ}

theorem HasStrictFderivAt.cpow (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasStrictFderivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g') x :=
  by convert (@has_strict_fderiv_at_cpow ((fun x => (f x, g x)) x) h0).comp x (hf.prod hg)
#align has_strict_fderiv_at.cpow HasStrictFderivAt.cpow

theorem HasStrictFderivAt.constCpow (hf : HasStrictFderivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasStrictFderivAt (fun x => c ^ f x) ((c ^ f x * log c) • f') x :=
  (hasStrictDerivAtConstCpow h0).compHasStrictFderivAt x hf
#align has_strict_fderiv_at.const_cpow HasStrictFderivAt.constCpow

theorem HasFderivAt.cpow (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasFderivAt (fun x => f x ^ g x) ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g')
      x :=
  by convert (@Complex.hasFderivAtCpow ((fun x => (f x, g x)) x) h0).comp x (hf.prod hg)
#align has_fderiv_at.cpow HasFderivAt.cpow

theorem HasFderivAt.constCpow (hf : HasFderivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasFderivAt (fun x => c ^ f x) ((c ^ f x * log c) • f') x :=
  (hasStrictDerivAtConstCpow h0).HasDerivAt.compHasFderivAt x hf
#align has_fderiv_at.const_cpow HasFderivAt.constCpow

theorem HasFderivWithinAt.cpow (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt g g' s x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasFderivWithinAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g') s x :=
  by
  convert
    (@Complex.hasFderivAtCpow ((fun x => (f x, g x)) x) h0).compHasFderivWithinAt x (hf.prod hg)
#align has_fderiv_within_at.cpow HasFderivWithinAt.cpow

theorem HasFderivWithinAt.constCpow (hf : HasFderivWithinAt f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasFderivWithinAt (fun x => c ^ f x) ((c ^ f x * log c) • f') s x :=
  (hasStrictDerivAtConstCpow h0).HasDerivAt.compHasFderivWithinAt x hf
#align has_fderiv_within_at.const_cpow HasFderivWithinAt.constCpow

theorem DifferentiableAt.cpow (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) : DifferentiableAt ℂ (fun x => f x ^ g x) x :=
  (hf.HasFderivAt.cpow hg.HasFderivAt h0).DifferentiableAt
#align differentiable_at.cpow DifferentiableAt.cpow

theorem DifferentiableAt.constCpow (hf : DifferentiableAt ℂ f x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    DifferentiableAt ℂ (fun x => c ^ f x) x :=
  (hf.HasFderivAt.const_cpow h0).DifferentiableAt
#align differentiable_at.const_cpow DifferentiableAt.constCpow

theorem DifferentiableWithinAt.cpow (hf : DifferentiableWithinAt ℂ f s x)
    (hg : DifferentiableWithinAt ℂ g s x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    DifferentiableWithinAt ℂ (fun x => f x ^ g x) s x :=
  (hf.HasFderivWithinAt.cpow hg.HasFderivWithinAt h0).DifferentiableWithinAt
#align differentiable_within_at.cpow DifferentiableWithinAt.cpow

theorem DifferentiableWithinAt.constCpow (hf : DifferentiableWithinAt ℂ f s x)
    (h0 : c ≠ 0 ∨ f x ≠ 0) : DifferentiableWithinAt ℂ (fun x => c ^ f x) s x :=
  (hf.HasFderivWithinAt.const_cpow h0).DifferentiableWithinAt
#align differentiable_within_at.const_cpow DifferentiableWithinAt.constCpow

end fderiv

section deriv

open Complex

variable {f g : ℂ → ℂ} {s : Set ℂ} {f' g' x c : ℂ}

/-- A private lemma that rewrites the output of lemmas like `has_fderiv_at.cpow` to the form
expected by lemmas like `has_deriv_at.cpow`. -/
private theorem aux :
    ((g x * f x ^ (g x - 1)) • (1 : ℂ →L[ℂ] ℂ).smul_right f' +
          (f x ^ g x * log (f x)) • (1 : ℂ →L[ℂ] ℂ).smul_right g')
        1 =
      g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g' :=
  by
  simp only [Algebra.id.smul_eq_mul, one_mul, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_right_apply, ContinuousLinearMap.add_apply, Pi.smul_apply,
    ContinuousLinearMap.coe_smul']
#align aux aux

theorem HasStrictDerivAt.cpow (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasStrictDerivAt (fun x => f x ^ g x) (g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g')
      x :=
  by simpa only [aux] using (hf.cpow hg h0).HasStrictDerivAt
#align has_strict_deriv_at.cpow HasStrictDerivAt.cpow

theorem HasStrictDerivAt.constCpow (hf : HasStrictDerivAt f f' x) (h : c ≠ 0 ∨ f x ≠ 0) :
    HasStrictDerivAt (fun x => c ^ f x) (c ^ f x * log c * f') x :=
  (hasStrictDerivAtConstCpow h).comp x hf
#align has_strict_deriv_at.const_cpow HasStrictDerivAt.constCpow

theorem Complex.hasStrictDerivAtCpowConst (h : 0 < x.re ∨ x.im ≠ 0) :
    HasStrictDerivAt (fun z : ℂ => z ^ c) (c * x ^ (c - 1)) x := by
  simpa only [mul_zero, add_zero, mul_one] using
    (hasStrictDerivAtId x).cpow (hasStrictDerivAtConst x c) h
#align complex.has_strict_deriv_at_cpow_const Complex.hasStrictDerivAtCpowConst

theorem HasStrictDerivAt.cpowConst (hf : HasStrictDerivAt f f' x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasStrictDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAtCpowConst h0).comp x hf
#align has_strict_deriv_at.cpow_const HasStrictDerivAt.cpowConst

theorem HasDerivAt.cpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasDerivAt (fun x => f x ^ g x) (g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g') x :=
  by simpa only [aux] using (hf.has_fderiv_at.cpow hg h0).HasDerivAt
#align has_deriv_at.cpow HasDerivAt.cpow

theorem HasDerivAt.constCpow (hf : HasDerivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasDerivAt (fun x => c ^ f x) (c ^ f x * log c * f') x :=
  (hasStrictDerivAtConstCpow h0).HasDerivAt.comp x hf
#align has_deriv_at.const_cpow HasDerivAt.constCpow

theorem HasDerivAt.cpowConst (hf : HasDerivAt f f' x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAtCpowConst h0).HasDerivAt.comp x hf
#align has_deriv_at.cpow_const HasDerivAt.cpowConst

theorem HasDerivWithinAt.cpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasDerivWithinAt (fun x => f x ^ g x) (g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g')
      s x :=
  by simpa only [aux] using (hf.has_fderiv_within_at.cpow hg h0).HasDerivWithinAt
#align has_deriv_within_at.cpow HasDerivWithinAt.cpow

theorem HasDerivWithinAt.constCpow (hf : HasDerivWithinAt f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasDerivWithinAt (fun x => c ^ f x) (c ^ f x * log c * f') s x :=
  (hasStrictDerivAtConstCpow h0).HasDerivAt.compHasDerivWithinAt x hf
#align has_deriv_within_at.const_cpow HasDerivWithinAt.constCpow

theorem HasDerivWithinAt.cpowConst (hf : HasDerivWithinAt f f' s x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasDerivWithinAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') s x :=
  (Complex.hasStrictDerivAtCpowConst h0).HasDerivAt.compHasDerivWithinAt x hf
#align has_deriv_within_at.cpow_const HasDerivWithinAt.cpowConst

end deriv

namespace Real

variable {x y z : ℝ}

/-- `(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `0 < p.fst`. -/
theorem hasStrictFderivAtRpowOfPos (p : ℝ × ℝ) (hp : 0 < p.1) :
    HasStrictFderivAt (fun x : ℝ × ℝ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      p :=
  by
  have : (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    (continuous_at_fst.eventually (lt_mem_nhds hp)).mono fun p hp => rpow_def_of_pos hp _
  refine' HasStrictFderivAt.congrOfEventuallyEq _ this.symm
  convert ((has_strict_fderiv_at_fst.log hp.ne').mul hasStrictFderivAtSnd).exp
  rw [rpow_sub_one hp.ne', ← rpow_def_of_pos hp, smul_add, smul_smul, mul_div_left_comm,
    div_eq_mul_inv, smul_smul, smul_smul, mul_assoc, add_comm]
#align real.has_strict_fderiv_at_rpow_of_pos Real.hasStrictFderivAtRpowOfPos

/-- `(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `p.fst < 0`. -/
theorem hasStrictFderivAtRpowOfNeg (p : ℝ × ℝ) (hp : p.1 < 0) :
    HasStrictFderivAt (fun x : ℝ × ℝ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (p.1 ^ p.2 * log p.1 - exp (log p.1 * p.2) * sin (p.2 * π) * π) •
          ContinuousLinearMap.snd ℝ ℝ ℝ)
      p :=
  by
  have : (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) :=
    (continuous_at_fst.eventually (gt_mem_nhds hp)).mono fun p hp => rpow_def_of_neg hp _
  refine' HasStrictFderivAt.congrOfEventuallyEq _ this.symm
  convert
    ((has_strict_fderiv_at_fst.log hp.ne).mul hasStrictFderivAtSnd).exp.mul
      (has_strict_fderiv_at_snd.mul_const _).cos using
    1
  simp_rw [rpow_sub_one hp.ne, smul_add, ← add_assoc, smul_smul, ← add_smul, ← mul_assoc,
    mul_comm (cos _), ← rpow_def_of_neg hp]
  rw [div_eq_mul_inv, add_comm]
  congr 2 <;> ring
#align real.has_strict_fderiv_at_rpow_of_neg Real.hasStrictFderivAtRpowOfNeg

/-- The function `λ (x, y), x ^ y` is infinitely smooth at `(x, y)` unless `x = 0`. -/
theorem contDiffAtRpowOfNe (p : ℝ × ℝ) (hp : p.1 ≠ 0) {n : ℕ∞} :
    ContDiffAt ℝ n (fun p : ℝ × ℝ => p.1 ^ p.2) p := by
  cases' hp.lt_or_lt with hneg hpos
  exacts[(((cont_diff_at_fst.log hneg.ne).mul contDiffAtSnd).exp.mul
          (cont_diff_at_snd.mul contDiffAtConst).cos).congr_of_eventually_eq
      ((continuous_at_fst.eventually (gt_mem_nhds hneg)).mono fun p hp => rpow_def_of_neg hp _),
    ((cont_diff_at_fst.log hpos.ne').mul contDiffAtSnd).exp.congr_of_eventually_eq
      ((continuous_at_fst.eventually (lt_mem_nhds hpos)).mono fun p hp => rpow_def_of_pos hp _)]
#align real.cont_diff_at_rpow_of_ne Real.contDiffAtRpowOfNe

theorem differentiableAtRpowOfNe (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ p.2) p :=
  (contDiffAtRpowOfNe p hp).DifferentiableAt le_rfl
#align real.differentiable_at_rpow_of_ne Real.differentiableAtRpowOfNe

theorem HasStrictDerivAt.rpow {f g : ℝ → ℝ} {f' g' : ℝ} (hf : HasStrictDerivAt f f' x)
    (hg : HasStrictDerivAt g g' x) (h : 0 < f x) :
    HasStrictDerivAt (fun x => f x ^ g x) (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * log (f x))
      x :=
  by
  convert
    (has_strict_fderiv_at_rpow_of_pos ((fun x => (f x, g x)) x) h).compHasStrictDerivAt _
      (hf.prod hg) using
    1
  simp [mul_assoc, mul_comm, mul_left_comm]
#align has_strict_deriv_at.rpow HasStrictDerivAt.rpow

theorem hasStrictDerivAtRpowConstOfNe {x : ℝ} (hx : x ≠ 0) (p : ℝ) :
    HasStrictDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x := by
  cases' hx.lt_or_lt with hx hx
  · have :=
      (has_strict_fderiv_at_rpow_of_neg (x, p) hx).compHasStrictDerivAt x
        ((hasStrictDerivAtId x).Prod (hasStrictDerivAtConst _ _))
    convert this
    simp
  · simpa using (hasStrictDerivAtId x).rpow (hasStrictDerivAtConst x p) hx
#align real.has_strict_deriv_at_rpow_const_of_ne Real.hasStrictDerivAtRpowConstOfNe

theorem hasStrictDerivAtConstRpow {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a) x := by
  simpa using (hasStrictDerivAtConst _ _).rpow (hasStrictDerivAtId x) ha
#align real.has_strict_deriv_at_const_rpow Real.hasStrictDerivAtConstRpow

/-- This lemma says that `λ x, a ^ x` is strictly differentiable for `a < 0`. Note that these
values of `a` are outside of the "official" domain of `a ^ x`, and we may redefine `a ^ x`
for negative `a` if some other definition will be more convenient. -/
theorem hasStrictDerivAtConstRpowOfNeg {a x : ℝ} (ha : a < 0) :
    HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a - exp (log a * x) * sin (x * π) * π) x := by
  simpa using
    (has_strict_fderiv_at_rpow_of_neg (a, x) ha).compHasStrictDerivAt x
      ((hasStrictDerivAtConst _ _).Prod (hasStrictDerivAtId _))
#align real.has_strict_deriv_at_const_rpow_of_neg Real.hasStrictDerivAtConstRpowOfNeg

end Real

namespace Real

variable {z x y : ℝ}

theorem hasDerivAtRpowConst {x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p) :
    HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x := by
  rcases ne_or_eq x 0 with (hx | rfl)
  · exact (has_strict_deriv_at_rpow_const_of_ne hx _).HasDerivAt
  replace h : 1 ≤ p := h.neg_resolve_left rfl
  apply
    hasDerivAtOfHasDerivAtOfNe fun x hx => (has_strict_deriv_at_rpow_const_of_ne hx p).HasDerivAt
  exacts[continuous_at_id.rpow_const (Or.inr (zero_le_one.trans h)),
    continuous_at_const.mul (continuous_at_id.rpow_const (Or.inr (sub_nonneg.2 h)))]
#align real.has_deriv_at_rpow_const Real.hasDerivAtRpowConst

theorem differentiableRpowConst {p : ℝ} (hp : 1 ≤ p) : Differentiable ℝ fun x : ℝ => x ^ p :=
  fun x => (hasDerivAtRpowConst (Or.inr hp)).DifferentiableAt
#align real.differentiable_rpow_const Real.differentiableRpowConst

theorem deriv_rpow_const {x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p) :
    deriv (fun x : ℝ => x ^ p) x = p * x ^ (p - 1) :=
  (hasDerivAtRpowConst h).deriv
#align real.deriv_rpow_const Real.deriv_rpow_const

theorem deriv_rpow_const' {p : ℝ} (h : 1 ≤ p) :
    (deriv fun x : ℝ => x ^ p) = fun x => p * x ^ (p - 1) :=
  funext fun x => deriv_rpow_const (Or.inr h)
#align real.deriv_rpow_const' Real.deriv_rpow_const'

theorem contDiffAtRpowConstOfNe {x p : ℝ} {n : ℕ∞} (h : x ≠ 0) :
    ContDiffAt ℝ n (fun x => x ^ p) x :=
  (contDiffAtRpowOfNe (x, p) h).comp x (contDiffAtId.Prod contDiffAtConst)
#align real.cont_diff_at_rpow_const_of_ne Real.contDiffAtRpowConstOfNe

theorem contDiffRpowConstOfLe {p : ℝ} {n : ℕ} (h : ↑n ≤ p) : ContDiff ℝ n fun x : ℝ => x ^ p := by
  induction' n with n ihn generalizing p
  · exact cont_diff_zero.2 (continuous_id.rpow_const fun x => by exact_mod_cast Or.inr h)
  · have h1 : 1 ≤ p := le_trans (by simp) h
    rw [Nat.cast_succ, ← le_sub_iff_add_le] at h
    rw [cont_diff_succ_iff_deriv, deriv_rpow_const' h1]
    refine' ⟨differentiable_rpow_const h1, cont_diff_const.mul (ihn h)⟩
#align real.cont_diff_rpow_const_of_le Real.contDiffRpowConstOfLe

theorem contDiffAtRpowConstOfLe {x p : ℝ} {n : ℕ} (h : ↑n ≤ p) :
    ContDiffAt ℝ n (fun x : ℝ => x ^ p) x :=
  (contDiffRpowConstOfLe h).ContDiffAt
#align real.cont_diff_at_rpow_const_of_le Real.contDiffAtRpowConstOfLe

theorem contDiffAtRpowConst {x p : ℝ} {n : ℕ} (h : x ≠ 0 ∨ ↑n ≤ p) :
    ContDiffAt ℝ n (fun x : ℝ => x ^ p) x :=
  h.elim contDiffAtRpowConstOfNe contDiffAtRpowConstOfLe
#align real.cont_diff_at_rpow_const Real.contDiffAtRpowConst

theorem hasStrictDerivAtRpowConst {x p : ℝ} (hx : x ≠ 0 ∨ 1 ≤ p) :
    HasStrictDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x :=
  ContDiffAt.hasStrictDerivAt' (contDiffAtRpowConst (by rwa [Nat.cast_one]))
    (hasDerivAtRpowConst hx) le_rfl
#align real.has_strict_deriv_at_rpow_const Real.hasStrictDerivAtRpowConst

end Real

section Differentiability

open Real

section fderiv

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ}
  {x : E} {s : Set E} {c p : ℝ} {n : ℕ∞}

theorem HasFderivWithinAt.rpow (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt g g' s x)
    (h : 0 < f x) :
    HasFderivWithinAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g') s x :=
  (hasStrictFderivAtRpowOfPos (f x, g x) h).HasFderivAt.compHasFderivWithinAt x (hf.Prod hg)
#align has_fderiv_within_at.rpow HasFderivWithinAt.rpow

theorem HasFderivAt.rpow (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x) (h : 0 < f x) :
    HasFderivAt (fun x => f x ^ g x) ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g')
      x :=
  (hasStrictFderivAtRpowOfPos (f x, g x) h).HasFderivAt.comp x (hf.Prod hg)
#align has_fderiv_at.rpow HasFderivAt.rpow

theorem HasStrictFderivAt.rpow (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x)
    (h : 0 < f x) :
    HasStrictFderivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g') x :=
  (hasStrictFderivAtRpowOfPos (f x, g x) h).comp x (hf.Prod hg)
#align has_strict_fderiv_at.rpow HasStrictFderivAt.rpow

theorem DifferentiableWithinAt.rpow (hf : DifferentiableWithinAt ℝ f s x)
    (hg : DifferentiableWithinAt ℝ g s x) (h : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun x => f x ^ g x) s x :=
  (differentiableAtRpowOfNe (f x, g x) h).compDifferentiableWithinAt x (hf.Prod hg)
#align differentiable_within_at.rpow DifferentiableWithinAt.rpow

theorem DifferentiableAt.rpow (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (h : f x ≠ 0) : DifferentiableAt ℝ (fun x => f x ^ g x) x :=
  (differentiableAtRpowOfNe (f x, g x) h).comp x (hf.Prod hg)
#align differentiable_at.rpow DifferentiableAt.rpow

theorem DifferentiableOn.rpow (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s)
    (h : ∀ x ∈ s, f x ≠ 0) : DifferentiableOn ℝ (fun x => f x ^ g x) s := fun x hx =>
  (hf x hx).rpow (hg x hx) (h x hx)
#align differentiable_on.rpow DifferentiableOn.rpow

theorem Differentiable.rpow (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (h : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun x => f x ^ g x := fun x => (hf x).rpow (hg x) (h x)
#align differentiable.rpow Differentiable.rpow

theorem HasFderivWithinAt.rpowConst (hf : HasFderivWithinAt f f' s x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    HasFderivWithinAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') s x :=
  (hasDerivAtRpowConst h).compHasFderivWithinAt x hf
#align has_fderiv_within_at.rpow_const HasFderivWithinAt.rpowConst

theorem HasFderivAt.rpowConst (hf : HasFderivAt f f' x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    HasFderivAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') x :=
  (hasDerivAtRpowConst h).compHasFderivAt x hf
#align has_fderiv_at.rpow_const HasFderivAt.rpowConst

theorem HasStrictFderivAt.rpowConst (hf : HasStrictFderivAt f f' x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    HasStrictFderivAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') x :=
  (hasStrictDerivAtRpowConst h).compHasStrictFderivAt x hf
#align has_strict_fderiv_at.rpow_const HasStrictFderivAt.rpowConst

theorem DifferentiableWithinAt.rpowConst (hf : DifferentiableWithinAt ℝ f s x)
    (h : f x ≠ 0 ∨ 1 ≤ p) : DifferentiableWithinAt ℝ (fun x => f x ^ p) s x :=
  (hf.HasFderivWithinAt.rpow_const h).DifferentiableWithinAt
#align differentiable_within_at.rpow_const DifferentiableWithinAt.rpowConst

@[simp]
theorem DifferentiableAt.rpowConst (hf : DifferentiableAt ℝ f x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    DifferentiableAt ℝ (fun x => f x ^ p) x :=
  (hf.HasFderivAt.rpow_const h).DifferentiableAt
#align differentiable_at.rpow_const DifferentiableAt.rpowConst

theorem DifferentiableOn.rpowConst (hf : DifferentiableOn ℝ f s) (h : ∀ x ∈ s, f x ≠ 0 ∨ 1 ≤ p) :
    DifferentiableOn ℝ (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const (h x hx)
#align differentiable_on.rpow_const DifferentiableOn.rpowConst

theorem Differentiable.rpowConst (hf : Differentiable ℝ f) (h : ∀ x, f x ≠ 0 ∨ 1 ≤ p) :
    Differentiable ℝ fun x => f x ^ p := fun x => (hf x).rpow_const (h x)
#align differentiable.rpow_const Differentiable.rpowConst

theorem HasFderivWithinAt.constRpow (hf : HasFderivWithinAt f f' s x) (hc : 0 < c) :
    HasFderivWithinAt (fun x => c ^ f x) ((c ^ f x * log c) • f') s x :=
  (hasStrictDerivAtConstRpow hc (f x)).HasDerivAt.compHasFderivWithinAt x hf
#align has_fderiv_within_at.const_rpow HasFderivWithinAt.constRpow

theorem HasFderivAt.constRpow (hf : HasFderivAt f f' x) (hc : 0 < c) :
    HasFderivAt (fun x => c ^ f x) ((c ^ f x * log c) • f') x :=
  (hasStrictDerivAtConstRpow hc (f x)).HasDerivAt.compHasFderivAt x hf
#align has_fderiv_at.const_rpow HasFderivAt.constRpow

theorem HasStrictFderivAt.constRpow (hf : HasStrictFderivAt f f' x) (hc : 0 < c) :
    HasStrictFderivAt (fun x => c ^ f x) ((c ^ f x * log c) • f') x :=
  (hasStrictDerivAtConstRpow hc (f x)).compHasStrictFderivAt x hf
#align has_strict_fderiv_at.const_rpow HasStrictFderivAt.constRpow

theorem ContDiffWithinAt.rpow (hf : ContDiffWithinAt ℝ n f s x) (hg : ContDiffWithinAt ℝ n g s x)
    (h : f x ≠ 0) : ContDiffWithinAt ℝ n (fun x => f x ^ g x) s x :=
  (contDiffAtRpowOfNe (f x, g x) h).compContDiffWithinAt x (hf.Prod hg)
#align cont_diff_within_at.rpow ContDiffWithinAt.rpow

theorem ContDiffAt.rpow (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) (h : f x ≠ 0) :
    ContDiffAt ℝ n (fun x => f x ^ g x) x :=
  (contDiffAtRpowOfNe (f x, g x) h).comp x (hf.Prod hg)
#align cont_diff_at.rpow ContDiffAt.rpow

theorem ContDiffOn.rpow (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s) (h : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun x => f x ^ g x) s := fun x hx => (hf x hx).rpow (hg x hx) (h x hx)
#align cont_diff_on.rpow ContDiffOn.rpow

theorem ContDiff.rpow (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (h : ∀ x, f x ≠ 0) :
    ContDiff ℝ n fun x => f x ^ g x :=
  cont_diff_iff_cont_diff_at.mpr fun x => hf.ContDiffAt.rpow hg.ContDiffAt (h x)
#align cont_diff.rpow ContDiff.rpow

theorem ContDiffWithinAt.rpowConstOfNe (hf : ContDiffWithinAt ℝ n f s x) (h : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun x => f x ^ p) s x :=
  hf.rpow contDiffWithinAtConst h
#align cont_diff_within_at.rpow_const_of_ne ContDiffWithinAt.rpowConstOfNe

theorem ContDiffAt.rpowConstOfNe (hf : ContDiffAt ℝ n f x) (h : f x ≠ 0) :
    ContDiffAt ℝ n (fun x => f x ^ p) x :=
  hf.rpow contDiffAtConst h
#align cont_diff_at.rpow_const_of_ne ContDiffAt.rpowConstOfNe

theorem ContDiffOn.rpowConstOfNe (hf : ContDiffOn ℝ n f s) (h : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun x => f x ^ p) s := fun x hx => (hf x hx).rpowConstOfNe (h x hx)
#align cont_diff_on.rpow_const_of_ne ContDiffOn.rpowConstOfNe

theorem ContDiff.rpowConstOfNe (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) :
    ContDiff ℝ n fun x => f x ^ p :=
  hf.rpow contDiffConst h
#align cont_diff.rpow_const_of_ne ContDiff.rpowConstOfNe

variable {m : ℕ}

theorem ContDiffWithinAt.rpowConstOfLe (hf : ContDiffWithinAt ℝ m f s x) (h : ↑m ≤ p) :
    ContDiffWithinAt ℝ m (fun x => f x ^ p) s x :=
  (contDiffAtRpowConstOfLe h).compContDiffWithinAt x hf
#align cont_diff_within_at.rpow_const_of_le ContDiffWithinAt.rpowConstOfLe

theorem ContDiffAt.rpowConstOfLe (hf : ContDiffAt ℝ m f x) (h : ↑m ≤ p) :
    ContDiffAt ℝ m (fun x => f x ^ p) x := by
  rw [← cont_diff_within_at_univ] at *
  exact hf.rpow_const_of_le h
#align cont_diff_at.rpow_const_of_le ContDiffAt.rpowConstOfLe

theorem ContDiffOn.rpowConstOfLe (hf : ContDiffOn ℝ m f s) (h : ↑m ≤ p) :
    ContDiffOn ℝ m (fun x => f x ^ p) s := fun x hx => (hf x hx).rpowConstOfLe h
#align cont_diff_on.rpow_const_of_le ContDiffOn.rpowConstOfLe

theorem ContDiff.rpowConstOfLe (hf : ContDiff ℝ m f) (h : ↑m ≤ p) : ContDiff ℝ m fun x => f x ^ p :=
  cont_diff_iff_cont_diff_at.mpr fun x => hf.ContDiffAt.rpowConstOfLe h
#align cont_diff.rpow_const_of_le ContDiff.rpowConstOfLe

end fderiv

section deriv

variable {f g : ℝ → ℝ} {f' g' x y p : ℝ} {s : Set ℝ}

theorem HasDerivWithinAt.rpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
    (h : 0 < f x) :
    HasDerivWithinAt (fun x => f x ^ g x) (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * log (f x))
      s x :=
  by 
  convert (hf.has_fderiv_within_at.rpow hg.has_fderiv_within_at h).HasDerivWithinAt using 1
  dsimp; ring
#align has_deriv_within_at.rpow HasDerivWithinAt.rpow

theorem HasDerivAt.rpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (h : 0 < f x) :
    HasDerivAt (fun x => f x ^ g x) (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * log (f x)) x :=
  by 
  rw [← has_deriv_within_at_univ] at *
  exact hf.rpow hg h
#align has_deriv_at.rpow HasDerivAt.rpow

theorem HasDerivWithinAt.rpowConst (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
    HasDerivWithinAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) s x := by
  convert (has_deriv_at_rpow_const hx).compHasDerivWithinAt x hf using 1
  ring
#align has_deriv_within_at.rpow_const HasDerivWithinAt.rpowConst

theorem HasDerivAt.rpowConst (hf : HasDerivAt f f' x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
    HasDerivAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) x := by
  rw [← has_deriv_within_at_univ] at *
  exact hf.rpow_const hx
#align has_deriv_at.rpow_const HasDerivAt.rpowConst

theorem deriv_within_rpow_const (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0 ∨ 1 ≤ p)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => f x ^ p) s x = derivWithin f s x * p * f x ^ (p - 1) :=
  (hf.HasDerivWithinAt.rpow_const hx).derivWithin hxs
#align deriv_within_rpow_const deriv_within_rpow_const

@[simp]
theorem deriv_rpow_const (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
    deriv (fun x => f x ^ p) x = deriv f x * p * f x ^ (p - 1) :=
  (hf.HasDerivAt.rpow_const hx).deriv
#align deriv_rpow_const deriv_rpow_const

end deriv

end Differentiability

section Limits

open Real Filter

/-- The function `(1 + t/x) ^ x` tends to `exp t` at `+∞`. -/
theorem tendsto_one_plus_div_rpow_exp (t : ℝ) :
    Tendsto (fun x : ℝ => (1 + t / x) ^ x) atTop (𝓝 (exp t)) := by
  apply ((real.continuous_exp.tendsto _).comp (tendsto_mul_log_one_plus_div_at_top t)).congr' _
  have h₁ : (1 : ℝ) / 2 < 1 := by linarith
  have h₂ : tendsto (fun x : ℝ => 1 + t / x) at_top (𝓝 1) := by
    simpa using (tendsto_inv_at_top_zero.const_mul t).const_add 1
  refine' (eventually_ge_of_tendsto_gt h₁ h₂).mono fun x hx => _
  have hx' : 0 < 1 + t / x := by linarith
  simp [mul_comm x, exp_mul, exp_log hx']
#align tendsto_one_plus_div_rpow_exp tendsto_one_plus_div_rpow_exp

/-- The function `(1 + t/x) ^ x` tends to `exp t` at `+∞` for naturals `x`. -/
theorem tendsto_one_plus_div_pow_exp (t : ℝ) :
    Tendsto (fun x : ℕ => (1 + t / (x : ℝ)) ^ x) atTop (𝓝 (Real.exp t)) :=
  ((tendsto_one_plus_div_rpow_exp t).comp tendsto_coe_nat_at_top_at_top).congr (by simp)
#align tendsto_one_plus_div_pow_exp tendsto_one_plus_div_pow_exp

end Limits

