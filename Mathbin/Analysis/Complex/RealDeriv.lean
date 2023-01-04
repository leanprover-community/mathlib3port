/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yourong Zang

! This file was ported from Lean 3 source module analysis.complex.real_deriv
! leanprover-community/mathlib commit d3e8e0a0237c10c2627bf52c246b15ff8e7df4c0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.ContDiff
import Mathbin.Analysis.Complex.Conformal
import Mathbin.Analysis.Calculus.Conformal.NormedSpace

/-! # Real differentiability of complex-differentiable functions

`has_deriv_at.real_of_complex` expresses that, if a function on `ℂ` is differentiable (over `ℂ`),
then its restriction to `ℝ` is differentiable over `ℝ`, with derivative the real part of the
complex derivative.

`differentiable_at.conformal_at` states that a real-differentiable function with a nonvanishing
differential from the complex plane into an arbitrary complex-normed space is conformal at a point
if it's holomorphic at that point. This is a version of Cauchy-Riemann equations.

`conformal_at_iff_differentiable_at_or_differentiable_at_comp_conj` proves that a real-differential
function with a nonvanishing differential between the complex plane is conformal at a point if and
only if it's holomorphic or antiholomorphic at that point.

## TODO

* The classical form of Cauchy-Riemann equations
* On a connected open set `u`, a function which is `conformal_at` each point is either holomorphic
throughout or antiholomorphic throughout.

## Warning

We do NOT require conformal functions to be orientation-preserving in this file.
-/


section RealDerivOfComplex

/-! ### Differentiability of the restriction to `ℝ` of complex functions -/


open Complex

variable {e : ℂ → ℂ} {e' : ℂ} {z : ℝ}

/-- If a complex function is differentiable at a real point, then the induced real function is also
differentiable at this point, with a derivative equal to the real part of the complex derivative. -/
theorem HasStrictDerivAt.real_of_complex (h : HasStrictDerivAt e e' z) :
    HasStrictDerivAt (fun x : ℝ => (e x).re) e'.re z :=
  by
  have A : HasStrictFderivAt (coe : ℝ → ℂ) of_real_clm z := of_real_clm.has_strict_fderiv_at
  have B :
    HasStrictFderivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (of_real_clm z) :=
    h.has_strict_fderiv_at.restrict_scalars ℝ
  have C : HasStrictFderivAt re re_clm (e (of_real_clm z)) := re_clm.has_strict_fderiv_at
  simpa using (C.comp z (B.comp z A)).HasStrictDerivAt
#align has_strict_deriv_at.real_of_complex HasStrictDerivAt.real_of_complex

/-- If a complex function `e` is differentiable at a real point, then the function `ℝ → ℝ` given by
the real part of `e` is also differentiable at this point, with a derivative equal to the real part
of the complex derivative. -/
theorem HasDerivAt.real_of_complex (h : HasDerivAt e e' z) :
    HasDerivAt (fun x : ℝ => (e x).re) e'.re z :=
  by
  have A : HasFderivAt (coe : ℝ → ℂ) of_real_clm z := of_real_clm.has_fderiv_at
  have B :
    HasFderivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (of_real_clm z) :=
    h.has_fderiv_at.restrict_scalars ℝ
  have C : HasFderivAt re re_clm (e (of_real_clm z)) := re_clm.has_fderiv_at
  simpa using (C.comp z (B.comp z A)).HasDerivAt
#align has_deriv_at.real_of_complex HasDerivAt.real_of_complex

theorem ContDiffAt.real_of_complex {n : ℕ∞} (h : ContDiffAt ℂ n e z) :
    ContDiffAt ℝ n (fun x : ℝ => (e x).re) z :=
  by
  have A : ContDiffAt ℝ n (coe : ℝ → ℂ) z := of_real_clm.cont_diff.cont_diff_at
  have B : ContDiffAt ℝ n e z := h.restrict_scalars ℝ
  have C : ContDiffAt ℝ n re (e z) := re_clm.cont_diff.cont_diff_at
  exact C.comp z (B.comp z A)
#align cont_diff_at.real_of_complex ContDiffAt.real_of_complex

theorem ContDiff.real_of_complex {n : ℕ∞} (h : ContDiff ℂ n e) :
    ContDiff ℝ n fun x : ℝ => (e x).re :=
  cont_diff_iff_cont_diff_at.2 fun x => h.ContDiffAt.real_of_complex
#align cont_diff.real_of_complex ContDiff.real_of_complex

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem HasStrictDerivAt.complexToRealFderiv' {f : ℂ → E} {x : ℂ} {f' : E}
    (h : HasStrictDerivAt f f' x) :
    HasStrictFderivAt f (reClm.smul_right f' + I • imClm.smul_right f') x := by
  simpa only [Complex.restrict_scalars_one_smul_right'] using
    h.has_strict_fderiv_at.restrict_scalars ℝ
#align has_strict_deriv_at.complex_to_real_fderiv' HasStrictDerivAt.complexToRealFderiv'

theorem HasDerivAt.complexToRealFderiv' {f : ℂ → E} {x : ℂ} {f' : E} (h : HasDerivAt f f' x) :
    HasFderivAt f (reClm.smul_right f' + I • imClm.smul_right f') x := by
  simpa only [Complex.restrict_scalars_one_smul_right'] using h.has_fderiv_at.restrict_scalars ℝ
#align has_deriv_at.complex_to_real_fderiv' HasDerivAt.complexToRealFderiv'

theorem HasDerivWithinAt.complexToRealFderiv' {f : ℂ → E} {s : Set ℂ} {x : ℂ} {f' : E}
    (h : HasDerivWithinAt f f' s x) :
    HasFderivWithinAt f (reClm.smul_right f' + I • imClm.smul_right f') s x := by
  simpa only [Complex.restrict_scalars_one_smul_right'] using
    h.has_fderiv_within_at.restrict_scalars ℝ
#align has_deriv_within_at.complex_to_real_fderiv' HasDerivWithinAt.complexToRealFderiv'

theorem HasStrictDerivAt.complexToRealFderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasStrictDerivAt f f' x) :
    HasStrictFderivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x := by
  simpa only [Complex.restrict_scalars_one_smul_right] using
    h.has_strict_fderiv_at.restrict_scalars ℝ
#align has_strict_deriv_at.complex_to_real_fderiv HasStrictDerivAt.complexToRealFderiv

theorem HasDerivAt.complexToRealFderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasDerivAt f f' x) :
    HasFderivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x := by
  simpa only [Complex.restrict_scalars_one_smul_right] using h.has_fderiv_at.restrict_scalars ℝ
#align has_deriv_at.complex_to_real_fderiv HasDerivAt.complexToRealFderiv

theorem HasDerivWithinAt.complexToRealFderiv {f : ℂ → ℂ} {s : Set ℂ} {f' x : ℂ}
    (h : HasDerivWithinAt f f' s x) : HasFderivWithinAt f (f' • (1 : ℂ →L[ℝ] ℂ)) s x := by
  simpa only [Complex.restrict_scalars_one_smul_right] using
    h.has_fderiv_within_at.restrict_scalars ℝ
#align has_deriv_within_at.complex_to_real_fderiv HasDerivWithinAt.complexToRealFderiv

/-- If a complex function `e` is differentiable at a real point, then its restriction to `ℝ` is
differentiable there as a function `ℝ → ℂ`, with the same derivative. -/
theorem HasDerivAt.comp_of_real (hf : HasDerivAt e e' ↑z) : HasDerivAt (fun y : ℝ => e ↑y) e' z :=
  by simpa only [of_real_clm_apply, of_real_one, mul_one] using hf.comp z of_real_clm.has_deriv_at
#align has_deriv_at.comp_of_real HasDerivAt.comp_of_real

/-- If a function `f : ℝ → ℝ` is differentiable at a (real) point `x`, then it is also
differentiable as a function `ℝ → ℂ`. -/
theorem HasDerivAt.of_real_comp {f : ℝ → ℝ} {u : ℝ} (hf : HasDerivAt f u z) :
    HasDerivAt (fun y : ℝ => ↑(f y) : ℝ → ℂ) u z := by
  simpa only [of_real_clm_apply, of_real_one, real_smul, mul_one] using
    of_real_clm.has_deriv_at.scomp z hf
#align has_deriv_at.of_real_comp HasDerivAt.of_real_comp

end RealDerivOfComplex

section Conformality

/-! ### Conformality of real-differentiable complex maps -/


open Complex ContinuousLinearMap

open ComplexConjugate

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : ℂ} {f : ℂ → E}

/-- A real differentiable function of the complex plane into some complex normed space `E` is
    conformal at a point `z` if it is holomorphic at that point with a nonvanishing differential.
    This is a version of the Cauchy-Riemann equations. -/
theorem DifferentiableAt.conformal_at (h : DifferentiableAt ℂ f z) (hf' : deriv f z ≠ 0) :
    ConformalAt f z :=
  by
  rw [conformal_at_iff_is_conformal_map_fderiv, (h.has_fderiv_at.restrict_scalars ℝ).fderiv]
  apply isConformalMapComplexLinear
  simpa only [Ne.def, ext_ring_iff]
#align differentiable_at.conformal_at DifferentiableAt.conformal_at

/-- A complex function is conformal if and only if the function is holomorphic or antiholomorphic
    with a nonvanishing differential. -/
theorem conformal_at_iff_differentiable_at_or_differentiable_at_comp_conj {f : ℂ → ℂ} {z : ℂ} :
    ConformalAt f z ↔
      (DifferentiableAt ℂ f z ∨ DifferentiableAt ℂ (f ∘ conj) (conj z)) ∧ fderiv ℝ f z ≠ 0 :=
  by
  rw [conformal_at_iff_is_conformal_map_fderiv]
  rw [is_conformal_map_iff_is_complex_or_conj_linear]
  apply and_congr_left
  intro h
  have h_diff := h.imp_symm fderiv_zero_of_not_differentiable_at
  apply or_congr
  · rw [differentiable_at_iff_restrict_scalars ℝ h_diff]
  rw [← conj_conj z] at h_diff
  rw [differentiable_at_iff_restrict_scalars ℝ (h_diff.comp _ conj_cle.differentiable_at)]
  refine' exists_congr fun g => rfl.congr _
  have : fderiv ℝ conj (conj z) = _ := conj_cle.fderiv
  simp [fderiv.comp _ h_diff conj_cle.differentiable_at, this, conj_conj]
#align
  conformal_at_iff_differentiable_at_or_differentiable_at_comp_conj conformal_at_iff_differentiable_at_or_differentiable_at_comp_conj

end Conformality

