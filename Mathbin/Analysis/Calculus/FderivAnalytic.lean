import Mathbin.Analysis.Calculus.Deriv 
import Mathbin.Analysis.Analytic.Basic

/-!
# Frechet derivatives of analytic functions.

A function expressible as a power series at a point has a Frechet derivative there.
Also the special case in terms of `deriv` when the domain is 1-dimensional.
-/


open Filter Asymptotics

open_locale Ennreal

variable{𝕜 : Type _}[NondiscreteNormedField 𝕜]

variable{E : Type _}[NormedGroup E][NormedSpace 𝕜 E]

variable{F : Type _}[NormedGroup F][NormedSpace 𝕜 F]

section fderiv

variable{p : FormalMultilinearSeries 𝕜 E F}{r : ℝ≥0∞}

variable{f : E → F}{x : E}{s : Set E}

theorem HasFpowerSeriesAt.has_strict_fderiv_at (h : HasFpowerSeriesAt f p x) :
  HasStrictFderivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x :=
  by 
    refine' h.is_O_image_sub_norm_mul_norm_sub.trans_is_o (is_o.of_norm_right _)
    refine' is_o_iff_exists_eq_mul.2 ⟨fun y => ∥y - (x, x)∥, _, eventually_eq.rfl⟩
    refine' (continuous_id.sub continuous_const).norm.tendsto' _ _ _ 
    rw [_root_.id, sub_self, norm_zero]

theorem HasFpowerSeriesAt.has_fderiv_at (h : HasFpowerSeriesAt f p x) :
  HasFderivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x :=
  h.has_strict_fderiv_at.has_fderiv_at

theorem HasFpowerSeriesAt.differentiable_at (h : HasFpowerSeriesAt f p x) : DifferentiableAt 𝕜 f x :=
  h.has_fderiv_at.differentiable_at

theorem AnalyticAt.differentiable_at : AnalyticAt 𝕜 f x → DifferentiableAt 𝕜 f x
| ⟨p, hp⟩ => hp.differentiable_at

theorem AnalyticAt.differentiable_within_at (h : AnalyticAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x :=
  h.differentiable_at.differentiable_within_at

theorem HasFpowerSeriesAt.fderiv (h : HasFpowerSeriesAt f p x) :
  fderiv 𝕜 f x = continuousMultilinearCurryFin1 𝕜 E F (p 1) :=
  h.has_fderiv_at.fderiv

theorem HasFpowerSeriesOnBall.differentiable_on [CompleteSpace F] (h : HasFpowerSeriesOnBall f p x r) :
  DifferentiableOn 𝕜 f (Emetric.Ball x r) :=
  fun y hy => (h.analytic_at_of_mem hy).DifferentiableWithinAt

end fderiv

section deriv

variable{p : FormalMultilinearSeries 𝕜 𝕜 F}{r : ℝ≥0∞}

variable{f : 𝕜 → F}{x : 𝕜}

protected theorem HasFpowerSeriesAt.has_strict_deriv_at (h : HasFpowerSeriesAt f p x) :
  HasStrictDerivAt f (p 1 fun _ => 1) x :=
  h.has_strict_fderiv_at.has_strict_deriv_at

protected theorem HasFpowerSeriesAt.has_deriv_at (h : HasFpowerSeriesAt f p x) : HasDerivAt f (p 1 fun _ => 1) x :=
  h.has_strict_deriv_at.has_deriv_at

protected theorem HasFpowerSeriesAt.deriv (h : HasFpowerSeriesAt f p x) : deriv f x = p 1 fun _ => 1 :=
  h.has_deriv_at.deriv

end deriv

