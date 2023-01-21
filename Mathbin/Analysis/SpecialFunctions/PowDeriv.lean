/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne

! This file was ported from Lean 3 source module analysis.special_functions.pow_deriv
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
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

theorem hasStrictFderivAt_cpow {p : ℂ × ℂ} (hp : 0 < p.1.re ∨ p.1.im ≠ 0) :
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
  refine' HasStrictFderivAt.congr_of_eventuallyEq _ this.symm
  simpa only [cpow_def_of_ne_zero A, div_eq_mul_inv, mul_smul, add_comm] using
    ((has_strict_fderiv_at_fst.clog hp).mul hasStrictFderivAt_snd).cexp
#align complex.has_strict_fderiv_at_cpow Complex.hasStrictFderivAt_cpow

theorem hasStrictFderivAt_cpow' {x y : ℂ} (hp : 0 < x.re ∨ x.im ≠ 0) :
    HasStrictFderivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((y * x ^ (y - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (x ^ y * log x) • ContinuousLinearMap.snd ℂ ℂ ℂ)
      (x, y) :=
  @hasStrictFderivAt_cpow (x, y) hp
#align complex.has_strict_fderiv_at_cpow' Complex.hasStrictFderivAt_cpow'

theorem hasStrictDerivAt_const_cpow {x y : ℂ} (h : x ≠ 0 ∨ y ≠ 0) :
    HasStrictDerivAt (fun y => x ^ y) (x ^ y * log x) y :=
  by
  rcases em (x = 0) with (rfl | hx)
  · replace h := h.neg_resolve_left rfl
    rw [log_zero, mul_zero]
    refine' (hasStrictDerivAt_const _ 0).congr_of_eventually_eq _
    exact (is_open_ne.eventually_mem h).mono fun y hy => (zero_cpow hy).symm
  ·
    simpa only [cpow_def_of_ne_zero hx, mul_one] using
      ((hasStrictDerivAt_id y).const_mul (log x)).cexp
#align complex.has_strict_deriv_at_const_cpow Complex.hasStrictDerivAt_const_cpow

theorem hasFderivAt_cpow {p : ℂ × ℂ} (hp : 0 < p.1.re ∨ p.1.im ≠ 0) :
    HasFderivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℂ ℂ ℂ)
      p :=
  (hasStrictFderivAt_cpow hp).HasFderivAt
#align complex.has_fderiv_at_cpow Complex.hasFderivAt_cpow

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

theorem HasStrictFderivAt.const_cpow (hf : HasStrictFderivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasStrictFderivAt (fun x => c ^ f x) ((c ^ f x * log c) • f') x :=
  (hasStrictDerivAt_const_cpow h0).comp_has_strict_fderiv_at x hf
#align has_strict_fderiv_at.const_cpow HasStrictFderivAt.const_cpow

theorem HasFderivAt.cpow (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasFderivAt (fun x => f x ^ g x) ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g')
      x :=
  by convert (@Complex.hasFderivAt_cpow ((fun x => (f x, g x)) x) h0).comp x (hf.prod hg)
#align has_fderiv_at.cpow HasFderivAt.cpow

theorem HasFderivAt.const_cpow (hf : HasFderivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasFderivAt (fun x => c ^ f x) ((c ^ f x * log c) • f') x :=
  (hasStrictDerivAt_const_cpow h0).HasDerivAt.comp_has_fderiv_at x hf
#align has_fderiv_at.const_cpow HasFderivAt.const_cpow

theorem HasFderivWithinAt.cpow (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt g g' s x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasFderivWithinAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g') s x :=
  by
  convert
    (@Complex.hasFderivAt_cpow ((fun x => (f x, g x)) x) h0).comp_has_fderiv_within_at x
      (hf.prod hg)
#align has_fderiv_within_at.cpow HasFderivWithinAt.cpow

theorem HasFderivWithinAt.const_cpow (hf : HasFderivWithinAt f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasFderivWithinAt (fun x => c ^ f x) ((c ^ f x * log c) • f') s x :=
  (hasStrictDerivAt_const_cpow h0).HasDerivAt.comp_has_fderiv_within_at x hf
#align has_fderiv_within_at.const_cpow HasFderivWithinAt.const_cpow

theorem DifferentiableAt.cpow (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) : DifferentiableAt ℂ (fun x => f x ^ g x) x :=
  (hf.HasFderivAt.cpow hg.HasFderivAt h0).DifferentiableAt
#align differentiable_at.cpow DifferentiableAt.cpow

theorem DifferentiableAt.const_cpow (hf : DifferentiableAt ℂ f x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    DifferentiableAt ℂ (fun x => c ^ f x) x :=
  (hf.HasFderivAt.const_cpow h0).DifferentiableAt
#align differentiable_at.const_cpow DifferentiableAt.const_cpow

theorem DifferentiableWithinAt.cpow (hf : DifferentiableWithinAt ℂ f s x)
    (hg : DifferentiableWithinAt ℂ g s x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    DifferentiableWithinAt ℂ (fun x => f x ^ g x) s x :=
  (hf.HasFderivWithinAt.cpow hg.HasFderivWithinAt h0).DifferentiableWithinAt
#align differentiable_within_at.cpow DifferentiableWithinAt.cpow

theorem DifferentiableWithinAt.const_cpow (hf : DifferentiableWithinAt ℂ f s x)
    (h0 : c ≠ 0 ∨ f x ≠ 0) : DifferentiableWithinAt ℂ (fun x => c ^ f x) s x :=
  (hf.HasFderivWithinAt.const_cpow h0).DifferentiableWithinAt
#align differentiable_within_at.const_cpow DifferentiableWithinAt.const_cpow

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
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply, Pi.smul_apply,
    ContinuousLinearMap.coe_smul']
#align aux aux

theorem HasStrictDerivAt.cpow (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasStrictDerivAt (fun x => f x ^ g x) (g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g')
      x :=
  by simpa only [aux] using (hf.cpow hg h0).HasStrictDerivAt
#align has_strict_deriv_at.cpow HasStrictDerivAt.cpow

theorem HasStrictDerivAt.const_cpow (hf : HasStrictDerivAt f f' x) (h : c ≠ 0 ∨ f x ≠ 0) :
    HasStrictDerivAt (fun x => c ^ f x) (c ^ f x * log c * f') x :=
  (hasStrictDerivAt_const_cpow h).comp x hf
#align has_strict_deriv_at.const_cpow HasStrictDerivAt.const_cpow

theorem Complex.hasStrictDerivAt_cpow_const (h : 0 < x.re ∨ x.im ≠ 0) :
    HasStrictDerivAt (fun z : ℂ => z ^ c) (c * x ^ (c - 1)) x := by
  simpa only [mul_zero, add_zero, mul_one] using
    (hasStrictDerivAt_id x).cpow (hasStrictDerivAt_const x c) h
#align complex.has_strict_deriv_at_cpow_const Complex.hasStrictDerivAt_cpow_const

theorem HasStrictDerivAt.cpow_const (hf : HasStrictDerivAt f f' x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasStrictDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAt_cpow_const h0).comp x hf
#align has_strict_deriv_at.cpow_const HasStrictDerivAt.cpow_const

theorem HasDerivAt.cpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasDerivAt (fun x => f x ^ g x) (g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g') x :=
  by simpa only [aux] using (hf.has_fderiv_at.cpow hg h0).HasDerivAt
#align has_deriv_at.cpow HasDerivAt.cpow

theorem HasDerivAt.const_cpow (hf : HasDerivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasDerivAt (fun x => c ^ f x) (c ^ f x * log c * f') x :=
  (hasStrictDerivAt_const_cpow h0).HasDerivAt.comp x hf
#align has_deriv_at.const_cpow HasDerivAt.const_cpow

theorem HasDerivAt.cpow_const (hf : HasDerivAt f f' x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAt_cpow_const h0).HasDerivAt.comp x hf
#align has_deriv_at.cpow_const HasDerivAt.cpow_const

theorem HasDerivWithinAt.cpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasDerivWithinAt (fun x => f x ^ g x) (g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g')
      s x :=
  by simpa only [aux] using (hf.has_fderiv_within_at.cpow hg h0).HasDerivWithinAt
#align has_deriv_within_at.cpow HasDerivWithinAt.cpow

theorem HasDerivWithinAt.const_cpow (hf : HasDerivWithinAt f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasDerivWithinAt (fun x => c ^ f x) (c ^ f x * log c * f') s x :=
  (hasStrictDerivAt_const_cpow h0).HasDerivAt.comp_has_deriv_within_at x hf
#align has_deriv_within_at.const_cpow HasDerivWithinAt.const_cpow

theorem HasDerivWithinAt.cpow_const (hf : HasDerivWithinAt f f' s x)
    (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasDerivWithinAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') s x :=
  (Complex.hasStrictDerivAt_cpow_const h0).HasDerivAt.comp_has_deriv_within_at x hf
#align has_deriv_within_at.cpow_const HasDerivWithinAt.cpow_const

end deriv

namespace Real

variable {x y z : ℝ}

/-- `(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `0 < p.fst`. -/
theorem hasStrictFderivAt_rpow_of_pos (p : ℝ × ℝ) (hp : 0 < p.1) :
    HasStrictFderivAt (fun x : ℝ × ℝ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      p :=
  by
  have : (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    (continuous_at_fst.eventually (lt_mem_nhds hp)).mono fun p hp => rpow_def_of_pos hp _
  refine' HasStrictFderivAt.congr_of_eventuallyEq _ this.symm
  convert ((has_strict_fderiv_at_fst.log hp.ne').mul hasStrictFderivAt_snd).exp
  rw [rpow_sub_one hp.ne', ← rpow_def_of_pos hp, smul_add, smul_smul, mul_div_left_comm,
    div_eq_mul_inv, smul_smul, smul_smul, mul_assoc, add_comm]
#align real.has_strict_fderiv_at_rpow_of_pos Real.hasStrictFderivAt_rpow_of_pos

/-- `(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `p.fst < 0`. -/
theorem hasStrictFderivAt_rpow_of_neg (p : ℝ × ℝ) (hp : p.1 < 0) :
    HasStrictFderivAt (fun x : ℝ × ℝ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (p.1 ^ p.2 * log p.1 - exp (log p.1 * p.2) * sin (p.2 * π) * π) •
          ContinuousLinearMap.snd ℝ ℝ ℝ)
      p :=
  by
  have : (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) :=
    (continuous_at_fst.eventually (gt_mem_nhds hp)).mono fun p hp => rpow_def_of_neg hp _
  refine' HasStrictFderivAt.congr_of_eventuallyEq _ this.symm
  convert
    ((has_strict_fderiv_at_fst.log hp.ne).mul hasStrictFderivAt_snd).exp.mul
      (has_strict_fderiv_at_snd.mul_const _).cos using
    1
  simp_rw [rpow_sub_one hp.ne, smul_add, ← add_assoc, smul_smul, ← add_smul, ← mul_assoc,
    mul_comm (cos _), ← rpow_def_of_neg hp]
  rw [div_eq_mul_inv, add_comm]
  congr 2 <;> ring
#align real.has_strict_fderiv_at_rpow_of_neg Real.hasStrictFderivAt_rpow_of_neg

/-- The function `λ (x, y), x ^ y` is infinitely smooth at `(x, y)` unless `x = 0`. -/
theorem contDiffAt_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) {n : ℕ∞} :
    ContDiffAt ℝ n (fun p : ℝ × ℝ => p.1 ^ p.2) p :=
  by
  cases' hp.lt_or_lt with hneg hpos
  exacts[(((cont_diff_at_fst.log hneg.ne).mul contDiffAt_snd).exp.mul
          (cont_diff_at_snd.mul contDiffAt_const).cos).congr_of_eventually_eq
      ((continuous_at_fst.eventually (gt_mem_nhds hneg)).mono fun p hp => rpow_def_of_neg hp _),
    ((cont_diff_at_fst.log hpos.ne').mul contDiffAt_snd).exp.congr_of_eventually_eq
      ((continuous_at_fst.eventually (lt_mem_nhds hpos)).mono fun p hp => rpow_def_of_pos hp _)]
#align real.cont_diff_at_rpow_of_ne Real.contDiffAt_rpow_of_ne

theorem differentiableAt_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ p.2) p :=
  (contDiffAt_rpow_of_ne p hp).DifferentiableAt le_rfl
#align real.differentiable_at_rpow_of_ne Real.differentiableAt_rpow_of_ne

theorem HasStrictDerivAt.rpow {f g : ℝ → ℝ} {f' g' : ℝ} (hf : HasStrictDerivAt f f' x)
    (hg : HasStrictDerivAt g g' x) (h : 0 < f x) :
    HasStrictDerivAt (fun x => f x ^ g x) (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * log (f x))
      x :=
  by
  convert
    (has_strict_fderiv_at_rpow_of_pos ((fun x => (f x, g x)) x) h).comp_has_strict_deriv_at _
      (hf.prod hg) using
    1
  simp [mul_assoc, mul_comm, mul_left_comm]
#align has_strict_deriv_at.rpow HasStrictDerivAt.rpow

theorem hasStrictDerivAt_rpow_const_of_ne {x : ℝ} (hx : x ≠ 0) (p : ℝ) :
    HasStrictDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x :=
  by
  cases' hx.lt_or_lt with hx hx
  · have :=
      (has_strict_fderiv_at_rpow_of_neg (x, p) hx).comp_has_strict_deriv_at x
        ((hasStrictDerivAt_id x).Prod (hasStrictDerivAt_const _ _))
    convert this
    simp
  · simpa using (hasStrictDerivAt_id x).rpow (hasStrictDerivAt_const x p) hx
#align real.has_strict_deriv_at_rpow_const_of_ne Real.hasStrictDerivAt_rpow_const_of_ne

theorem hasStrictDerivAt_const_rpow {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a) x := by
  simpa using (hasStrictDerivAt_const _ _).rpow (hasStrictDerivAt_id x) ha
#align real.has_strict_deriv_at_const_rpow Real.hasStrictDerivAt_const_rpow

/-- This lemma says that `λ x, a ^ x` is strictly differentiable for `a < 0`. Note that these
values of `a` are outside of the "official" domain of `a ^ x`, and we may redefine `a ^ x`
for negative `a` if some other definition will be more convenient. -/
theorem hasStrictDerivAt_const_rpow_of_neg {a x : ℝ} (ha : a < 0) :
    HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a - exp (log a * x) * sin (x * π) * π) x := by
  simpa using
    (has_strict_fderiv_at_rpow_of_neg (a, x) ha).comp_has_strict_deriv_at x
      ((hasStrictDerivAt_const _ _).Prod (hasStrictDerivAt_id _))
#align real.has_strict_deriv_at_const_rpow_of_neg Real.hasStrictDerivAt_const_rpow_of_neg

end Real

namespace Real

variable {z x y : ℝ}

theorem hasDerivAt_rpow_const {x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p) :
    HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x :=
  by
  rcases ne_or_eq x 0 with (hx | rfl)
  · exact (has_strict_deriv_at_rpow_const_of_ne hx _).HasDerivAt
  replace h : 1 ≤ p := h.neg_resolve_left rfl
  apply
    hasDerivAt_of_hasDerivAt_of_ne fun x hx =>
      (has_strict_deriv_at_rpow_const_of_ne hx p).HasDerivAt
  exacts[continuous_at_id.rpow_const (Or.inr (zero_le_one.trans h)),
    continuous_at_const.mul (continuous_at_id.rpow_const (Or.inr (sub_nonneg.2 h)))]
#align real.has_deriv_at_rpow_const Real.hasDerivAt_rpow_const

theorem differentiable_rpow_const {p : ℝ} (hp : 1 ≤ p) : Differentiable ℝ fun x : ℝ => x ^ p :=
  fun x => (hasDerivAt_rpow_const (Or.inr hp)).DifferentiableAt
#align real.differentiable_rpow_const Real.differentiable_rpow_const

theorem deriv_rpow_const {x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p) :
    deriv (fun x : ℝ => x ^ p) x = p * x ^ (p - 1) :=
  (hasDerivAt_rpow_const h).deriv
#align real.deriv_rpow_const Real.deriv_rpow_const

theorem deriv_rpow_const' {p : ℝ} (h : 1 ≤ p) :
    (deriv fun x : ℝ => x ^ p) = fun x => p * x ^ (p - 1) :=
  funext fun x => deriv_rpow_const (Or.inr h)
#align real.deriv_rpow_const' Real.deriv_rpow_const'

theorem contDiffAt_rpow_const_of_ne {x p : ℝ} {n : ℕ∞} (h : x ≠ 0) :
    ContDiffAt ℝ n (fun x => x ^ p) x :=
  (contDiffAt_rpow_of_ne (x, p) h).comp x (contDiffAt_id.Prod contDiffAt_const)
#align real.cont_diff_at_rpow_const_of_ne Real.contDiffAt_rpow_const_of_ne

theorem contDiff_rpow_const_of_le {p : ℝ} {n : ℕ} (h : ↑n ≤ p) : ContDiff ℝ n fun x : ℝ => x ^ p :=
  by
  induction' n with n ihn generalizing p
  · exact contDiff_zero.2 (continuous_id.rpow_const fun x => by exact_mod_cast Or.inr h)
  · have h1 : 1 ≤ p := le_trans (by simp) h
    rw [Nat.cast_succ, ← le_sub_iff_add_le] at h
    rw [contDiff_succ_iff_deriv, deriv_rpow_const' h1]
    refine' ⟨differentiable_rpow_const h1, cont_diff_const.mul (ihn h)⟩
#align real.cont_diff_rpow_const_of_le Real.contDiff_rpow_const_of_le

theorem contDiffAt_rpow_const_of_le {x p : ℝ} {n : ℕ} (h : ↑n ≤ p) :
    ContDiffAt ℝ n (fun x : ℝ => x ^ p) x :=
  (contDiff_rpow_const_of_le h).ContDiffAt
#align real.cont_diff_at_rpow_const_of_le Real.contDiffAt_rpow_const_of_le

theorem contDiffAt_rpow_const {x p : ℝ} {n : ℕ} (h : x ≠ 0 ∨ ↑n ≤ p) :
    ContDiffAt ℝ n (fun x : ℝ => x ^ p) x :=
  h.elim contDiffAt_rpow_const_of_ne contDiffAt_rpow_const_of_le
#align real.cont_diff_at_rpow_const Real.contDiffAt_rpow_const

theorem hasStrictDerivAt_rpow_const {x p : ℝ} (hx : x ≠ 0 ∨ 1 ≤ p) :
    HasStrictDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x :=
  ContDiffAt.has_strict_deriv_at' (contDiffAt_rpow_const (by rwa [Nat.cast_one]))
    (hasDerivAt_rpow_const hx) le_rfl
#align real.has_strict_deriv_at_rpow_const Real.hasStrictDerivAt_rpow_const

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
  (hasStrictFderivAt_rpow_of_pos (f x, g x) h).HasFderivAt.comp_has_fderiv_within_at x (hf.Prod hg)
#align has_fderiv_within_at.rpow HasFderivWithinAt.rpow

theorem HasFderivAt.rpow (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x) (h : 0 < f x) :
    HasFderivAt (fun x => f x ^ g x) ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g')
      x :=
  (hasStrictFderivAt_rpow_of_pos (f x, g x) h).HasFderivAt.comp x (hf.Prod hg)
#align has_fderiv_at.rpow HasFderivAt.rpow

theorem HasStrictFderivAt.rpow (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x)
    (h : 0 < f x) :
    HasStrictFderivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * log (f x)) • g') x :=
  (hasStrictFderivAt_rpow_of_pos (f x, g x) h).comp x (hf.Prod hg)
#align has_strict_fderiv_at.rpow HasStrictFderivAt.rpow

theorem DifferentiableWithinAt.rpow (hf : DifferentiableWithinAt ℝ f s x)
    (hg : DifferentiableWithinAt ℝ g s x) (h : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun x => f x ^ g x) s x :=
  (differentiableAt_rpow_of_ne (f x, g x) h).comp_differentiable_within_at x (hf.Prod hg)
#align differentiable_within_at.rpow DifferentiableWithinAt.rpow

theorem DifferentiableAt.rpow (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (h : f x ≠ 0) : DifferentiableAt ℝ (fun x => f x ^ g x) x :=
  (differentiableAt_rpow_of_ne (f x, g x) h).comp x (hf.Prod hg)
#align differentiable_at.rpow DifferentiableAt.rpow

theorem DifferentiableOn.rpow (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s)
    (h : ∀ x ∈ s, f x ≠ 0) : DifferentiableOn ℝ (fun x => f x ^ g x) s := fun x hx =>
  (hf x hx).rpow (hg x hx) (h x hx)
#align differentiable_on.rpow DifferentiableOn.rpow

theorem Differentiable.rpow (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (h : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun x => f x ^ g x := fun x => (hf x).rpow (hg x) (h x)
#align differentiable.rpow Differentiable.rpow

theorem HasFderivWithinAt.rpow_const (hf : HasFderivWithinAt f f' s x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    HasFderivWithinAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') s x :=
  (hasDerivAt_rpow_const h).comp_has_fderiv_within_at x hf
#align has_fderiv_within_at.rpow_const HasFderivWithinAt.rpow_const

theorem HasFderivAt.rpow_const (hf : HasFderivAt f f' x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    HasFderivAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') x :=
  (hasDerivAt_rpow_const h).comp_has_fderiv_at x hf
#align has_fderiv_at.rpow_const HasFderivAt.rpow_const

theorem HasStrictFderivAt.rpow_const (hf : HasStrictFderivAt f f' x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    HasStrictFderivAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') x :=
  (hasStrictDerivAt_rpow_const h).comp_has_strict_fderiv_at x hf
#align has_strict_fderiv_at.rpow_const HasStrictFderivAt.rpow_const

theorem DifferentiableWithinAt.rpow_const (hf : DifferentiableWithinAt ℝ f s x)
    (h : f x ≠ 0 ∨ 1 ≤ p) : DifferentiableWithinAt ℝ (fun x => f x ^ p) s x :=
  (hf.HasFderivWithinAt.rpow_const h).DifferentiableWithinAt
#align differentiable_within_at.rpow_const DifferentiableWithinAt.rpow_const

@[simp]
theorem DifferentiableAt.rpow_const (hf : DifferentiableAt ℝ f x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    DifferentiableAt ℝ (fun x => f x ^ p) x :=
  (hf.HasFderivAt.rpow_const h).DifferentiableAt
#align differentiable_at.rpow_const DifferentiableAt.rpow_const

theorem DifferentiableOn.rpow_const (hf : DifferentiableOn ℝ f s) (h : ∀ x ∈ s, f x ≠ 0 ∨ 1 ≤ p) :
    DifferentiableOn ℝ (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const (h x hx)
#align differentiable_on.rpow_const DifferentiableOn.rpow_const

theorem Differentiable.rpow_const (hf : Differentiable ℝ f) (h : ∀ x, f x ≠ 0 ∨ 1 ≤ p) :
    Differentiable ℝ fun x => f x ^ p := fun x => (hf x).rpow_const (h x)
#align differentiable.rpow_const Differentiable.rpow_const

theorem HasFderivWithinAt.const_rpow (hf : HasFderivWithinAt f f' s x) (hc : 0 < c) :
    HasFderivWithinAt (fun x => c ^ f x) ((c ^ f x * log c) • f') s x :=
  (hasStrictDerivAt_const_rpow hc (f x)).HasDerivAt.comp_has_fderiv_within_at x hf
#align has_fderiv_within_at.const_rpow HasFderivWithinAt.const_rpow

theorem HasFderivAt.const_rpow (hf : HasFderivAt f f' x) (hc : 0 < c) :
    HasFderivAt (fun x => c ^ f x) ((c ^ f x * log c) • f') x :=
  (hasStrictDerivAt_const_rpow hc (f x)).HasDerivAt.comp_has_fderiv_at x hf
#align has_fderiv_at.const_rpow HasFderivAt.const_rpow

theorem HasStrictFderivAt.const_rpow (hf : HasStrictFderivAt f f' x) (hc : 0 < c) :
    HasStrictFderivAt (fun x => c ^ f x) ((c ^ f x * log c) • f') x :=
  (hasStrictDerivAt_const_rpow hc (f x)).comp_has_strict_fderiv_at x hf
#align has_strict_fderiv_at.const_rpow HasStrictFderivAt.const_rpow

theorem ContDiffWithinAt.rpow (hf : ContDiffWithinAt ℝ n f s x) (hg : ContDiffWithinAt ℝ n g s x)
    (h : f x ≠ 0) : ContDiffWithinAt ℝ n (fun x => f x ^ g x) s x :=
  (contDiffAt_rpow_of_ne (f x, g x) h).comp_cont_diff_within_at x (hf.Prod hg)
#align cont_diff_within_at.rpow ContDiffWithinAt.rpow

theorem ContDiffAt.rpow (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) (h : f x ≠ 0) :
    ContDiffAt ℝ n (fun x => f x ^ g x) x :=
  (contDiffAt_rpow_of_ne (f x, g x) h).comp x (hf.Prod hg)
#align cont_diff_at.rpow ContDiffAt.rpow

theorem ContDiffOn.rpow (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s) (h : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun x => f x ^ g x) s := fun x hx => (hf x hx).rpow (hg x hx) (h x hx)
#align cont_diff_on.rpow ContDiffOn.rpow

theorem ContDiff.rpow (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (h : ∀ x, f x ≠ 0) :
    ContDiff ℝ n fun x => f x ^ g x :=
  contDiff_iff_contDiffAt.mpr fun x => hf.ContDiffAt.rpow hg.ContDiffAt (h x)
#align cont_diff.rpow ContDiff.rpow

theorem ContDiffWithinAt.rpow_const_of_ne (hf : ContDiffWithinAt ℝ n f s x) (h : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun x => f x ^ p) s x :=
  hf.rpow contDiffWithinAt_const h
#align cont_diff_within_at.rpow_const_of_ne ContDiffWithinAt.rpow_const_of_ne

theorem ContDiffAt.rpow_const_of_ne (hf : ContDiffAt ℝ n f x) (h : f x ≠ 0) :
    ContDiffAt ℝ n (fun x => f x ^ p) x :=
  hf.rpow contDiffAt_const h
#align cont_diff_at.rpow_const_of_ne ContDiffAt.rpow_const_of_ne

theorem ContDiffOn.rpow_const_of_ne (hf : ContDiffOn ℝ n f s) (h : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const_of_ne (h x hx)
#align cont_diff_on.rpow_const_of_ne ContDiffOn.rpow_const_of_ne

theorem ContDiff.rpow_const_of_ne (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) :
    ContDiff ℝ n fun x => f x ^ p :=
  hf.rpow contDiff_const h
#align cont_diff.rpow_const_of_ne ContDiff.rpow_const_of_ne

variable {m : ℕ}

theorem ContDiffWithinAt.rpow_const_of_le (hf : ContDiffWithinAt ℝ m f s x) (h : ↑m ≤ p) :
    ContDiffWithinAt ℝ m (fun x => f x ^ p) s x :=
  (contDiffAt_rpow_const_of_le h).comp_cont_diff_within_at x hf
#align cont_diff_within_at.rpow_const_of_le ContDiffWithinAt.rpow_const_of_le

theorem ContDiffAt.rpow_const_of_le (hf : ContDiffAt ℝ m f x) (h : ↑m ≤ p) :
    ContDiffAt ℝ m (fun x => f x ^ p) x :=
  by
  rw [← contDiffWithinAt_univ] at *
  exact hf.rpow_const_of_le h
#align cont_diff_at.rpow_const_of_le ContDiffAt.rpow_const_of_le

theorem ContDiffOn.rpow_const_of_le (hf : ContDiffOn ℝ m f s) (h : ↑m ≤ p) :
    ContDiffOn ℝ m (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const_of_le h
#align cont_diff_on.rpow_const_of_le ContDiffOn.rpow_const_of_le

theorem ContDiff.rpow_const_of_le (hf : ContDiff ℝ m f) (h : ↑m ≤ p) :
    ContDiff ℝ m fun x => f x ^ p :=
  contDiff_iff_contDiffAt.mpr fun x => hf.ContDiffAt.rpow_const_of_le h
#align cont_diff.rpow_const_of_le ContDiff.rpow_const_of_le

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
  rw [← hasDerivWithinAt_univ] at *
  exact hf.rpow hg h
#align has_deriv_at.rpow HasDerivAt.rpow

theorem HasDerivWithinAt.rpow_const (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
    HasDerivWithinAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) s x :=
  by
  convert (has_deriv_at_rpow_const hx).comp_has_deriv_within_at x hf using 1
  ring
#align has_deriv_within_at.rpow_const HasDerivWithinAt.rpow_const

theorem HasDerivAt.rpow_const (hf : HasDerivAt f f' x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
    HasDerivAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) x :=
  by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.rpow_const hx
#align has_deriv_at.rpow_const HasDerivAt.rpow_const

theorem derivWithin_rpow_const (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0 ∨ 1 ≤ p)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => f x ^ p) s x = derivWithin f s x * p * f x ^ (p - 1) :=
  (hf.HasDerivWithinAt.rpow_const hx).derivWithin hxs
#align deriv_within_rpow_const derivWithin_rpow_const

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
    Tendsto (fun x : ℝ => (1 + t / x) ^ x) atTop (𝓝 (exp t)) :=
  by
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
  ((tendsto_one_plus_div_rpow_exp t).comp tendsto_coe_nat_atTop_atTop).congr (by simp)
#align tendsto_one_plus_div_pow_exp tendsto_one_plus_div_pow_exp

end Limits

