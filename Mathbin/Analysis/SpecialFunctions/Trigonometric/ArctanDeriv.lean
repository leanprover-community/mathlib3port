/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson

! This file was ported from Lean 3 source module analysis.special_functions.trigonometric.arctan_deriv
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathbin.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv

/-!
# Derivatives of the `tan` and `arctan` functions.

Continuity and derivatives of the tangent and arctangent functions.
-/


noncomputable section

namespace Real

open Set Filter

open Topology Real

theorem hasStrictDerivAt_tan {x : ℝ} (h : cos x ≠ 0) : HasStrictDerivAt tan (1 / cos x ^ 2) x := by
  exact_mod_cast (Complex.hasStrictDerivAt_tan (by exact_mod_cast h)).real_of_complex
#align real.has_strict_deriv_at_tan Real.hasStrictDerivAt_tan

theorem hasDerivAt_tan {x : ℝ} (h : cos x ≠ 0) : HasDerivAt tan (1 / cos x ^ 2) x := by
  exact_mod_cast (Complex.hasDerivAt_tan (by exact_mod_cast h)).real_of_complex
#align real.has_deriv_at_tan Real.hasDerivAt_tan

theorem tendsto_abs_tan_of_cos_eq_zero {x : ℝ} (hx : cos x = 0) :
    Tendsto (fun x => abs (tan x)) (𝓝[≠] x) atTop :=
  by
  have hx : Complex.cos x = 0 := by exact_mod_cast hx
  simp only [← Complex.abs_of_real, Complex.of_real_tan]
  refine' (Complex.tendsto_abs_tan_of_cos_eq_zero hx).comp _
  refine' tendsto.inf complex.continuous_of_real.continuous_at _
  exact tendsto_principal_principal.2 fun y => mt Complex.of_real_inj.1
#align real.tendsto_abs_tan_of_cos_eq_zero Real.tendsto_abs_tan_of_cos_eq_zero

theorem tendsto_abs_tan_atTop (k : ℤ) :
    Tendsto (fun x => abs (tan x)) (𝓝[≠] ((2 * k + 1) * π / 2)) atTop :=
  tendsto_abs_tan_of_cos_eq_zero <| cos_eq_zero_iff.2 ⟨k, rfl⟩
#align real.tendsto_abs_tan_at_top Real.tendsto_abs_tan_atTop

theorem continuousAt_tan {x : ℝ} : ContinuousAt tan x ↔ cos x ≠ 0 :=
  by
  refine' ⟨fun hc h₀ => _, fun h => (has_deriv_at_tan h).ContinuousAt⟩
  exact
    not_tendsto_nhds_of_tendsto_atTop (tendsto_abs_tan_of_cos_eq_zero h₀) _
      (hc.norm.tendsto.mono_left inf_le_left)
#align real.continuous_at_tan Real.continuousAt_tan

theorem differentiableAt_tan {x : ℝ} : DifferentiableAt ℝ tan x ↔ cos x ≠ 0 :=
  ⟨fun h => continuousAt_tan.1 h.ContinuousAt, fun h => (hasDerivAt_tan h).DifferentiableAt⟩
#align real.differentiable_at_tan Real.differentiableAt_tan

@[simp]
theorem deriv_tan (x : ℝ) : deriv tan x = 1 / cos x ^ 2 :=
  if h : cos x = 0 then
    by
    have : ¬DifferentiableAt ℝ tan x := mt differentiableAt_tan.1 (Classical.not_not.2 h)
    simp [deriv_zero_of_not_differentiableAt this, h, sq]
  else (hasDerivAt_tan h).deriv
#align real.deriv_tan Real.deriv_tan

@[simp]
theorem contDiffAt_tan {n x} : ContDiffAt ℝ n tan x ↔ cos x ≠ 0 :=
  ⟨fun h => continuousAt_tan.1 h.ContinuousAt, fun h =>
    (Complex.contDiffAt_tan.2 <| by exact_mod_cast h).real_of_complex⟩
#align real.cont_diff_at_tan Real.contDiffAt_tan

theorem hasDerivAt_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π / 2) : ℝ) (π / 2)) :
    HasDerivAt tan (1 / cos x ^ 2) x :=
  hasDerivAt_tan (cos_pos_of_mem_Ioo h).ne'
#align real.has_deriv_at_tan_of_mem_Ioo Real.hasDerivAt_tan_of_mem_Ioo

theorem differentiableAt_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π / 2) : ℝ) (π / 2)) :
    DifferentiableAt ℝ tan x :=
  (hasDerivAt_tan_of_mem_Ioo h).DifferentiableAt
#align real.differentiable_at_tan_of_mem_Ioo Real.differentiableAt_tan_of_mem_Ioo

theorem hasStrictDerivAt_arctan (x : ℝ) : HasStrictDerivAt arctan (1 / (1 + x ^ 2)) x :=
  by
  have A : cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne'
  simpa [cos_sq_arctan] using
    tan_local_homeomorph.has_strict_deriv_at_symm trivial (by simpa) (has_strict_deriv_at_tan A)
#align real.has_strict_deriv_at_arctan Real.hasStrictDerivAt_arctan

theorem hasDerivAt_arctan (x : ℝ) : HasDerivAt arctan (1 / (1 + x ^ 2)) x :=
  (hasStrictDerivAt_arctan x).HasDerivAt
#align real.has_deriv_at_arctan Real.hasDerivAt_arctan

theorem differentiableAt_arctan (x : ℝ) : DifferentiableAt ℝ arctan x :=
  (hasDerivAt_arctan x).DifferentiableAt
#align real.differentiable_at_arctan Real.differentiableAt_arctan

theorem differentiable_arctan : Differentiable ℝ arctan :=
  differentiableAt_arctan
#align real.differentiable_arctan Real.differentiable_arctan

@[simp]
theorem deriv_arctan : deriv arctan = fun x => 1 / (1 + x ^ 2) :=
  funext fun x => (hasDerivAt_arctan x).deriv
#align real.deriv_arctan Real.deriv_arctan

theorem contDiff_arctan {n : ℕ∞} : ContDiff ℝ n arctan :=
  contDiff_iff_contDiffAt.2 fun x =>
    have : cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne'
    tanLocalHomeomorph.contDiffAt_symm_deriv (by simpa) trivial (hasDerivAt_tan this)
      (contDiffAt_tan.2 this)
#align real.cont_diff_arctan Real.contDiff_arctan

end Real

section

/-!
### Lemmas for derivatives of the composition of `real.arctan` with a differentiable function

In this section we register lemmas for the derivatives of the composition of `real.arctan` with a
differentiable function, for standalone use and use with `simp`. -/


open Real

section deriv

variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

theorem HasStrictDerivAt.arctan (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => arctan (f x)) (1 / (1 + f x ^ 2) * f') x :=
  (Real.hasStrictDerivAt_arctan (f x)).comp x hf
#align has_strict_deriv_at.arctan HasStrictDerivAt.arctan

theorem HasDerivAt.arctan (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => arctan (f x)) (1 / (1 + f x ^ 2) * f') x :=
  (Real.hasDerivAt_arctan (f x)).comp x hf
#align has_deriv_at.arctan HasDerivAt.arctan

theorem HasDerivWithinAt.arctan (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => arctan (f x)) (1 / (1 + f x ^ 2) * f') s x :=
  (Real.hasDerivAt_arctan (f x)).comp_hasDerivWithinAt x hf
#align has_deriv_within_at.arctan HasDerivWithinAt.arctan

theorem derivWithin_arctan (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => arctan (f x)) s x = 1 / (1 + f x ^ 2) * derivWithin f s x :=
  hf.HasDerivWithinAt.arctan.derivWithin hxs
#align deriv_within_arctan derivWithin_arctan

@[simp]
theorem deriv_arctan (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => arctan (f x)) x = 1 / (1 + f x ^ 2) * deriv f x :=
  hc.HasDerivAt.arctan.deriv
#align deriv_arctan deriv_arctan

end deriv

section fderiv

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
  {s : Set E} {n : ℕ∞}

theorem HasStrictFderivAt.arctan (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => arctan (f x)) ((1 / (1 + f x ^ 2)) • f') x :=
  (hasStrictDerivAt_arctan (f x)).comp_hasStrictFderivAt x hf
#align has_strict_fderiv_at.arctan HasStrictFderivAt.arctan

theorem HasFderivAt.arctan (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => arctan (f x)) ((1 / (1 + f x ^ 2)) • f') x :=
  (hasDerivAt_arctan (f x)).comp_hasFderivAt x hf
#align has_fderiv_at.arctan HasFderivAt.arctan

theorem HasFderivWithinAt.arctan (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => arctan (f x)) ((1 / (1 + f x ^ 2)) • f') s x :=
  (hasDerivAt_arctan (f x)).comp_hasFderivWithinAt x hf
#align has_fderiv_within_at.arctan HasFderivWithinAt.arctan

theorem fderivWithin_arctan (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => arctan (f x)) s x = (1 / (1 + f x ^ 2)) • fderivWithin ℝ f s x :=
  hf.HasFderivWithinAt.arctan.fderivWithin hxs
#align fderiv_within_arctan fderivWithin_arctan

@[simp]
theorem fderiv_arctan (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => arctan (f x)) x = (1 / (1 + f x ^ 2)) • fderiv ℝ f x :=
  hc.HasFderivAt.arctan.fderiv
#align fderiv_arctan fderiv_arctan

theorem DifferentiableWithinAt.arctan (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.arctan (f x)) s x :=
  hf.HasFderivWithinAt.arctan.DifferentiableWithinAt
#align differentiable_within_at.arctan DifferentiableWithinAt.arctan

@[simp]
theorem DifferentiableAt.arctan (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => arctan (f x)) x :=
  hc.HasFderivAt.arctan.DifferentiableAt
#align differentiable_at.arctan DifferentiableAt.arctan

theorem DifferentiableOn.arctan (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => arctan (f x)) s := fun x h => (hc x h).arctan
#align differentiable_on.arctan DifferentiableOn.arctan

@[simp]
theorem Differentiable.arctan (hc : Differentiable ℝ f) : Differentiable ℝ fun x => arctan (f x) :=
  fun x => (hc x).arctan
#align differentiable.arctan Differentiable.arctan

theorem ContDiffAt.arctan (h : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => arctan (f x)) x :=
  contDiff_arctan.ContDiffAt.comp x h
#align cont_diff_at.arctan ContDiffAt.arctan

theorem ContDiff.arctan (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => arctan (f x) :=
  contDiff_arctan.comp h
#align cont_diff.arctan ContDiff.arctan

theorem ContDiffWithinAt.arctan (h : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => arctan (f x)) s x :=
  contDiff_arctan.comp_contDiffWithinAt h
#align cont_diff_within_at.arctan ContDiffWithinAt.arctan

theorem ContDiffOn.arctan (h : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => arctan (f x)) s :=
  contDiff_arctan.comp_contDiffOn h
#align cont_diff_on.arctan ContDiffOn.arctan

end fderiv

end

