import Mathbin.Analysis.SpecialFunctions.Trigonometric.Arctan 
import Mathbin.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv

/-!
# The `arctan` function.

Inequalities, derivatives,
and `real.tan` as a `local_homeomorph` between `(-(π / 2), π / 2)` and the whole line.
-/


noncomputable theory

namespace Real

open Set Filter

open_locale TopologicalSpace Real

theorem has_strict_deriv_at_tan {x : ℝ} (h : cos x ≠ 0) : HasStrictDerivAt tan (1 / (cos x^2)) x :=
  by 
    exactModCast
      (Complex.has_strict_deriv_at_tan
          (by 
            exactModCast h)).real_of_complex

theorem has_deriv_at_tan {x : ℝ} (h : cos x ≠ 0) : HasDerivAt tan (1 / (cos x^2)) x :=
  by 
    exactModCast
      (Complex.has_deriv_at_tan
          (by 
            exactModCast h)).real_of_complex

-- error in Analysis.SpecialFunctions.Trigonometric.ArctanDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_abs_tan_of_cos_eq_zero
{x : exprℝ()}
(hx : «expr = »(cos x, 0)) : tendsto (λ x, abs (tan x)) «expr𝓝[ ] »(«expr ᶜ»({x}), x) at_top :=
begin
  have [ident hx] [":", expr «expr = »(complex.cos x, 0)] [],
  by exact_mod_cast [expr hx],
  simp [] [] ["only"] ["[", "<-", expr complex.abs_of_real, ",", expr complex.of_real_tan, "]"] [] [],
  refine [expr (complex.tendsto_abs_tan_of_cos_eq_zero hx).comp _],
  refine [expr tendsto.inf complex.continuous_of_real.continuous_at _],
  exact [expr tendsto_principal_principal.2 (λ y, mt complex.of_real_inj.1)]
end

theorem tendsto_abs_tan_at_top (k : ℤ) :
  tendsto (fun x => abs (tan x)) (𝓝[«expr ᶜ» {(((2*k)+1)*π) / 2}] ((((2*k)+1)*π) / 2)) at_top :=
  tendsto_abs_tan_of_cos_eq_zero$ cos_eq_zero_iff.2 ⟨k, rfl⟩

theorem continuous_at_tan {x : ℝ} : ContinuousAt tan x ↔ cos x ≠ 0 :=
  by 
    refine' ⟨fun hc h₀ => _, fun h => (has_deriv_at_tan h).ContinuousAt⟩
    exact
      not_tendsto_nhds_of_tendsto_at_top (tendsto_abs_tan_of_cos_eq_zero h₀) _ (hc.norm.tendsto.mono_left inf_le_left)

theorem differentiable_at_tan {x : ℝ} : DifferentiableAt ℝ tan x ↔ cos x ≠ 0 :=
  ⟨fun h => continuous_at_tan.1 h.continuous_at, fun h => (has_deriv_at_tan h).DifferentiableAt⟩

@[simp]
theorem deriv_tan (x : ℝ) : deriv tan x = 1 / (cos x^2) :=
  if h : cos x = 0 then
    have  : ¬DifferentiableAt ℝ tan x := mt differentiable_at_tan.1 (not_not.2 h)
    by 
      simp [deriv_zero_of_not_differentiable_at this, h, sq]
  else (has_deriv_at_tan h).deriv

@[simp]
theorem times_cont_diff_at_tan {n x} : TimesContDiffAt ℝ n tan x ↔ cos x ≠ 0 :=
  ⟨fun h => continuous_at_tan.1 h.continuous_at,
    fun h =>
      (Complex.times_cont_diff_at_tan.2$
          by 
            exactModCast h).real_of_complex⟩

theorem has_deriv_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π / 2) : ℝ) (π / 2)) : HasDerivAt tan (1 / (cos x^2)) x :=
  has_deriv_at_tan (cos_pos_of_mem_Ioo h).ne'

theorem differentiable_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π / 2) : ℝ) (π / 2)) : DifferentiableAt ℝ tan x :=
  (has_deriv_at_tan_of_mem_Ioo h).DifferentiableAt

theorem has_strict_deriv_at_arctan (x : ℝ) : HasStrictDerivAt arctan (1 / 1+x^2) x :=
  have A : cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne' 
  by 
    simpa [cos_sq_arctan] using
      tan_local_homeomorph.has_strict_deriv_at_symm trivialₓ
        (by 
          simpa)
        (has_strict_deriv_at_tan A)

theorem has_deriv_at_arctan (x : ℝ) : HasDerivAt arctan (1 / 1+x^2) x :=
  (has_strict_deriv_at_arctan x).HasDerivAt

theorem differentiable_at_arctan (x : ℝ) : DifferentiableAt ℝ arctan x :=
  (has_deriv_at_arctan x).DifferentiableAt

theorem differentiable_arctan : Differentiable ℝ arctan :=
  differentiable_at_arctan

@[simp]
theorem deriv_arctan : deriv arctan = fun x => 1 / 1+x^2 :=
  funext$ fun x => (has_deriv_at_arctan x).deriv

theorem times_cont_diff_arctan {n : WithTop ℕ} : TimesContDiff ℝ n arctan :=
  times_cont_diff_iff_times_cont_diff_at.2$
    fun x =>
      have  : cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne' 
      tan_local_homeomorph.times_cont_diff_at_symm_deriv
        (by 
          simpa)
        trivialₓ (has_deriv_at_tan this) (times_cont_diff_at_tan.2 this)

end Real

section 

/-!
### Lemmas for derivatives of the composition of `real.arctan` with a differentiable function

In this section we register lemmas for the derivatives of the composition of `real.arctan` with a
differentiable function, for standalone use and use with `simp`. -/


open Real

section deriv

variable{f : ℝ → ℝ}{f' x : ℝ}{s : Set ℝ}

theorem HasStrictDerivAt.arctan (hf : HasStrictDerivAt f f' x) :
  HasStrictDerivAt (fun x => arctan (f x)) ((1 / 1+f x^2)*f') x :=
  (Real.has_strict_deriv_at_arctan (f x)).comp x hf

theorem HasDerivAt.arctan (hf : HasDerivAt f f' x) : HasDerivAt (fun x => arctan (f x)) ((1 / 1+f x^2)*f') x :=
  (Real.has_deriv_at_arctan (f x)).comp x hf

theorem HasDerivWithinAt.arctan (hf : HasDerivWithinAt f f' s x) :
  HasDerivWithinAt (fun x => arctan (f x)) ((1 / 1+f x^2)*f') s x :=
  (Real.has_deriv_at_arctan (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_arctan (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
  derivWithin (fun x => arctan (f x)) s x = (1 / 1+f x^2)*derivWithin f s x :=
  hf.has_deriv_within_at.arctan.deriv_within hxs

@[simp]
theorem deriv_arctan (hc : DifferentiableAt ℝ f x) : deriv (fun x => arctan (f x)) x = (1 / 1+f x^2)*deriv f x :=
  hc.has_deriv_at.arctan.deriv

end deriv

section fderiv

variable{E : Type _}[NormedGroup E][NormedSpace ℝ E]{f : E → ℝ}{f' : E →L[ℝ] ℝ}{x : E}{s : Set E}{n : WithTop ℕ}

theorem HasStrictFderivAt.arctan (hf : HasStrictFderivAt f f' x) :
  HasStrictFderivAt (fun x => arctan (f x)) ((1 / 1+f x^2) • f') x :=
  (has_strict_deriv_at_arctan (f x)).comp_has_strict_fderiv_at x hf

theorem HasFderivAt.arctan (hf : HasFderivAt f f' x) : HasFderivAt (fun x => arctan (f x)) ((1 / 1+f x^2) • f') x :=
  (has_deriv_at_arctan (f x)).comp_has_fderiv_at x hf

theorem HasFderivWithinAt.arctan (hf : HasFderivWithinAt f f' s x) :
  HasFderivWithinAt (fun x => arctan (f x)) ((1 / 1+f x^2) • f') s x :=
  (has_deriv_at_arctan (f x)).comp_has_fderiv_within_at x hf

theorem fderiv_within_arctan (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
  fderivWithin ℝ (fun x => arctan (f x)) s x = (1 / 1+f x^2) • fderivWithin ℝ f s x :=
  hf.has_fderiv_within_at.arctan.fderiv_within hxs

@[simp]
theorem fderiv_arctan (hc : DifferentiableAt ℝ f x) :
  fderiv ℝ (fun x => arctan (f x)) x = (1 / 1+f x^2) • fderiv ℝ f x :=
  hc.has_fderiv_at.arctan.fderiv

theorem DifferentiableWithinAt.arctan (hf : DifferentiableWithinAt ℝ f s x) :
  DifferentiableWithinAt ℝ (fun x => Real.arctan (f x)) s x :=
  hf.has_fderiv_within_at.arctan.differentiable_within_at

@[simp]
theorem DifferentiableAt.arctan (hc : DifferentiableAt ℝ f x) : DifferentiableAt ℝ (fun x => arctan (f x)) x :=
  hc.has_fderiv_at.arctan.differentiable_at

theorem DifferentiableOn.arctan (hc : DifferentiableOn ℝ f s) : DifferentiableOn ℝ (fun x => arctan (f x)) s :=
  fun x h => (hc x h).arctan

@[simp]
theorem Differentiable.arctan (hc : Differentiable ℝ f) : Differentiable ℝ fun x => arctan (f x) :=
  fun x => (hc x).arctan

theorem TimesContDiffAt.arctan (h : TimesContDiffAt ℝ n f x) : TimesContDiffAt ℝ n (fun x => arctan (f x)) x :=
  times_cont_diff_arctan.TimesContDiffAt.comp x h

theorem TimesContDiff.arctan (h : TimesContDiff ℝ n f) : TimesContDiff ℝ n fun x => arctan (f x) :=
  times_cont_diff_arctan.comp h

theorem TimesContDiffWithinAt.arctan (h : TimesContDiffWithinAt ℝ n f s x) :
  TimesContDiffWithinAt ℝ n (fun x => arctan (f x)) s x :=
  times_cont_diff_arctan.comp_times_cont_diff_within_at h

theorem TimesContDiffOn.arctan (h : TimesContDiffOn ℝ n f s) : TimesContDiffOn ℝ n (fun x => arctan (f x)) s :=
  times_cont_diff_arctan.comp_times_cont_diff_on h

end fderiv

end 

