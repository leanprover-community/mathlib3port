import Mathbin.Analysis.SpecialFunctions.Trigonometric.Complex 
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.
-/


noncomputable theory

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

-- error in Analysis.SpecialFunctions.Trigonometric.ComplexDeriv: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem tendsto_abs_tan_of_cos_eq_zero
{x : exprℂ()}
(hx : «expr = »(cos x, 0)) : tendsto (λ x, abs (tan x)) «expr𝓝[ ] »(«expr ᶜ»({x}), x) at_top :=
begin
  simp [] [] ["only"] ["[", expr tan_eq_sin_div_cos, ",", "<-", expr norm_eq_abs, ",", expr normed_field.norm_div, "]"] [] [],
  have [ident A] [":", expr «expr ≠ »(sin x, 0)] [":=", expr λ
   h, by simpa [] [] [] ["[", "*", ",", expr sq, "]"] [] ["using", expr sin_sq_add_cos_sq x]],
  have [ident B] [":", expr tendsto cos «expr𝓝[ ] »(«expr ᶜ»({x}), x) «expr𝓝[ ] »(«expr ᶜ»({0}), 0)] [],
  { refine [expr tendsto_inf.2 ⟨tendsto.mono_left _ inf_le_left, tendsto_principal.2 _⟩],
    exacts ["[", expr continuous_cos.tendsto' x 0 hx, ",", expr «expr ▸ »(hx, (has_deriv_at_cos _).eventually_ne (neg_ne_zero.2 A)), "]"] },
  exact [expr continuous_sin.continuous_within_at.norm.mul_at_top (norm_pos_iff.2 A) (tendsto_norm_nhds_within_zero.comp B).inv_tendsto_zero]
end

theorem tendsto_abs_tan_at_top (k : ℤ) :
  tendsto (fun x => abs (tan x)) (𝓝[«expr ᶜ» {(((2*k)+1)*π) / 2}] ((((2*k)+1)*π) / 2)) at_top :=
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

