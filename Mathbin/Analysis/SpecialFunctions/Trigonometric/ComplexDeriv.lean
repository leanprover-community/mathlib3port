import Mathbin.Analysis.SpecialFunctions.Trigonometric.Complex 
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.
-/


noncomputable section 

namespace Complex

open Set Filter

open_locale Real

theorem has_strict_deriv_at_tan {x : ℂ} (h : cos x ≠ 0) : HasStrictDerivAt tan (1 / (cos x^2)) x :=
  by 
    convert (has_strict_deriv_at_sin x).div (has_strict_deriv_at_cos x) h 
    rw [←sin_sq_add_cos_sq x]
    ring

theorem has_deriv_at_tan {x : ℂ} (h : cos x ≠ 0) : HasDerivAt tan (1 / (cos x^2)) x :=
  (has_strict_deriv_at_tan h).HasDerivAt

open_locale TopologicalSpace

theorem tendsto_abs_tan_of_cos_eq_zero {x : ℂ} (hx : cos x = 0) : tendsto (fun x => abs (tan x)) (𝓝[{x}ᶜ] x) at_top :=
  by 
    simp only [tan_eq_sin_div_cos, ←norm_eq_abs, NormedField.norm_div]
    have A : sin x ≠ 0 :=
      fun h =>
        by 
          simpa [*, sq] using sin_sq_add_cos_sq x 
    have B : tendsto cos (𝓝[{x}ᶜ] x) (𝓝[{0}ᶜ] 0)
    ·
      refine' tendsto_inf.2 ⟨tendsto.mono_left _ inf_le_left, tendsto_principal.2 _⟩
      exacts[continuous_cos.tendsto' x 0 hx, hx ▸ (has_deriv_at_cos _).eventually_ne (neg_ne_zero.2 A)]
    exact
      continuous_sin.continuous_within_at.norm.mul_at_top (norm_pos_iff.2 A)
        (tendsto_norm_nhds_within_zero.comp B).inv_tendsto_zero

theorem tendsto_abs_tan_at_top (k : ℤ) :
  tendsto (fun x => abs (tan x)) (𝓝[{(((2*k)+1)*π) / 2}ᶜ] ((((2*k)+1)*π) / 2)) at_top :=
  tendsto_abs_tan_of_cos_eq_zero$ cos_eq_zero_iff.2 ⟨k, rfl⟩

@[simp]
theorem continuous_at_tan {x : ℂ} : ContinuousAt tan x ↔ cos x ≠ 0 :=
  by 
    refine' ⟨fun hc h₀ => _, fun h => (has_deriv_at_tan h).ContinuousAt⟩
    exact
      not_tendsto_nhds_of_tendsto_at_top (tendsto_abs_tan_of_cos_eq_zero h₀) _ (hc.norm.tendsto.mono_left inf_le_left)

@[simp]
theorem differentiable_at_tan {x : ℂ} : DifferentiableAt ℂ tan x ↔ cos x ≠ 0 :=
  ⟨fun h => continuous_at_tan.1 h.continuous_at, fun h => (has_deriv_at_tan h).DifferentiableAt⟩

@[simp]
theorem deriv_tan (x : ℂ) : deriv tan x = 1 / (cos x^2) :=
  if h : cos x = 0 then
    have  : ¬DifferentiableAt ℂ tan x := mt differentiable_at_tan.1 (not_not.2 h)
    by 
      simp [deriv_zero_of_not_differentiable_at this, h, sq]
  else (has_deriv_at_tan h).deriv

@[simp]
theorem times_cont_diff_at_tan {x : ℂ} {n : WithTop ℕ} : TimesContDiffAt ℂ n tan x ↔ cos x ≠ 0 :=
  ⟨fun h => continuous_at_tan.1 h.continuous_at,
    times_cont_diff_sin.TimesContDiffAt.div times_cont_diff_cos.TimesContDiffAt⟩

end Complex

