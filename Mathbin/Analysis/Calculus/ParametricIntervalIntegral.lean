import Mathbin.Analysis.Calculus.ParametricIntegral 
import Mathbin.MeasureTheory.Integral.IntervalIntegral

/-!
# Derivatives of interval integrals depending on parameters

In this file we restate theorems about derivatives of integrals depending on parameters for interval
integrals.  -/


open TopologicalSpace MeasureTheory Filter Metric

open_locale TopologicalSpace Filter Interval

variable{α 𝕜 :
    Type
      _}[MeasurableSpace
      α][LinearOrderₓ
      α][TopologicalSpace
      α][OrderTopology
      α][OpensMeasurableSpace
      α]{μ :
    Measureₓ
      α}[IsROrC
      𝕜]{E :
    Type
      _}[NormedGroup
      E][NormedSpace ℝ
      E][NormedSpace 𝕜
      E][IsScalarTower ℝ 𝕜
      E][CompleteSpace
      E][second_countable_topology
      E][MeasurableSpace
      E][BorelSpace
      E]{H :
    Type _}[NormedGroup H][NormedSpace 𝕜 H][second_countable_topology$ H →L[𝕜] E]{a b : α}{bound : α → ℝ}{ε : ℝ}

namespace intervalIntegral

-- error in Analysis.Calculus.ParametricIntervalIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Differentiation under integral of `x ↦ ∫ t in a..b, F x t` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with a ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is ae-measurable
for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem has_fderiv_at_integral_of_dominated_loc_of_lip
{F : H → α → E}
{F' : α → «expr →L[ ] »(H, 𝕜, E)}
{x₀ : H}
(ε_pos : «expr < »(0, ε))
(hF_meas : «expr∀ᶠ in , »((x), expr𝓝() x₀, ae_measurable (F x) (μ.restrict (exprΙ() a b))))
(hF_int : interval_integrable (F x₀) μ a b)
(hF'_meas : ae_measurable F' (μ.restrict (exprΙ() a b)))
(h_lip : «expr∀ᵐ ∂ , »((t), μ, «expr ∈ »(t, exprΙ() a b) → lipschitz_on_with «expr $ »(real.nnabs, bound t) (λ
   x, F x t) (ball x₀ ε)))
(bound_integrable : interval_integrable bound μ a b)
(h_diff : «expr∀ᵐ ∂ , »((t), μ, «expr ∈ »(t, exprΙ() a b) → has_fderiv_at (λ
   x, F x t) (F' t) x₀)) : «expr ∧ »(interval_integrable F' μ a b, has_fderiv_at (λ
  x, «expr∫ in .. , ∂ »((t), a, b, F x t, μ)) «expr∫ in .. , ∂ »((t), a, b, F' t, μ) x₀) :=
begin
  simp [] [] ["only"] ["[", expr interval_integrable_iff, ",", expr interval_integral_eq_integral_interval_oc, ",", "<-", expr ae_restrict_iff' measurable_set_interval_oc, "]"] [] ["at", "*"],
  have [] [] [":=", expr has_fderiv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas h_lip bound_integrable h_diff],
  exact [expr ⟨this.1, this.2.const_smul _⟩]
end

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on a ball around `x₀` for ae `a` with
derivative norm uniformly bounded by an integrable function (the ball radius is independent of `a`),
and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem has_fderiv_at_integral_of_dominated_of_fderiv_le {F : H → α → E} {F' : H → α → H →L[𝕜] E} {x₀ : H}
  (ε_pos : 0 < ε) (hF_meas : ∀ᶠx in 𝓝 x₀, AeMeasurable (F x) (μ.restrict (Ι a b)))
  (hF_int : IntervalIntegrable (F x₀) μ a b) (hF'_meas : AeMeasurable (F' x₀) (μ.restrict (Ι a b)))
  (h_bound : ∀ᵐt ∂μ, t ∈ Ι a b → ∀ x (_ : x ∈ ball x₀ ε), ∥F' x t∥ ≤ bound t)
  (bound_integrable : IntervalIntegrable bound μ a b)
  (h_diff : ∀ᵐt ∂μ, t ∈ Ι a b → ∀ x (_ : x ∈ ball x₀ ε), HasFderivAt (fun x => F x t) (F' x t) x) :
  HasFderivAt (fun x => ∫t in a..b, F x t ∂μ) (∫t in a..b, F' x₀ t ∂μ) x₀ :=
  by 
    simp only [interval_integrable_iff, interval_integral_eq_integral_interval_oc,
      ←ae_restrict_iff' measurable_set_interval_oc] at *
    exact
      (has_fderiv_at_integral_of_dominated_of_fderiv_le ε_pos hF_meas hF_int hF'_meas h_bound bound_integrable
            h_diff).const_smul
        _

-- error in Analysis.Calculus.ParametricIntervalIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
assuming `F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is
ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem has_deriv_at_integral_of_dominated_loc_of_lip
{F : 𝕜 → α → E}
{F' : α → E}
{x₀ : 𝕜}
(ε_pos : «expr < »(0, ε))
(hF_meas : «expr∀ᶠ in , »((x), expr𝓝() x₀, ae_measurable (F x) (μ.restrict (exprΙ() a b))))
(hF_int : interval_integrable (F x₀) μ a b)
(hF'_meas : ae_measurable F' (μ.restrict (exprΙ() a b)))
(h_lipsch : «expr∀ᵐ ∂ , »((t), μ, «expr ∈ »(t, exprΙ() a b) → lipschitz_on_with «expr $ »(real.nnabs, bound t) (λ
   x, F x t) (ball x₀ ε)))
(bound_integrable : interval_integrable (bound : α → exprℝ()) μ a b)
(h_diff : «expr∀ᵐ ∂ , »((t), μ, «expr ∈ »(t, exprΙ() a b) → has_deriv_at (λ
   x, F x t) (F' t) x₀)) : «expr ∧ »(interval_integrable F' μ a b, has_deriv_at (λ
  x, «expr∫ in .. , ∂ »((t), a, b, F x t, μ)) «expr∫ in .. , ∂ »((t), a, b, F' t, μ) x₀) :=
begin
  simp [] [] ["only"] ["[", expr interval_integrable_iff, ",", expr interval_integral_eq_integral_interval_oc, ",", "<-", expr ae_restrict_iff' measurable_set_interval_oc, "]"] [] ["at", "*"],
  have [] [] [":=", expr has_deriv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas h_lipsch bound_integrable h_diff],
  exact [expr ⟨this.1, this.2.const_smul _⟩]
end

-- error in Analysis.Calculus.ParametricIntervalIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
assuming `F x₀` is integrable, `x ↦ F x a` is differentiable on an interval around `x₀` for ae `a`
(with interval radius independent of `a`) with derivative uniformly bounded by an integrable
function, and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem has_deriv_at_integral_of_dominated_loc_of_deriv_le
{F : 𝕜 → α → E}
{F' : 𝕜 → α → E}
{x₀ : 𝕜}
(ε_pos : «expr < »(0, ε))
(hF_meas : «expr∀ᶠ in , »((x), expr𝓝() x₀, ae_measurable (F x) (μ.restrict (exprΙ() a b))))
(hF_int : interval_integrable (F x₀) μ a b)
(hF'_meas : ae_measurable (F' x₀) (μ.restrict (exprΙ() a b)))
(h_bound : «expr∀ᵐ ∂ , »((t), μ, «expr ∈ »(t, exprΙ() a b) → ∀
  x «expr ∈ » ball x₀ ε, «expr ≤ »(«expr∥ ∥»(F' x t), bound t)))
(bound_integrable : interval_integrable bound μ a b)
(h_diff : «expr∀ᵐ ∂ , »((t), μ, «expr ∈ »(t, exprΙ() a b) → ∀
  x «expr ∈ » ball x₀ ε, has_deriv_at (λ
   x, F x t) (F' x t) x)) : «expr ∧ »(interval_integrable (F' x₀) μ a b, has_deriv_at (λ
  x, «expr∫ in .. , ∂ »((t), a, b, F x t, μ)) «expr∫ in .. , ∂ »((t), a, b, F' x₀ t, μ) x₀) :=
begin
  simp [] [] ["only"] ["[", expr interval_integrable_iff, ",", expr interval_integral_eq_integral_interval_oc, ",", "<-", expr ae_restrict_iff' measurable_set_interval_oc, "]"] [] ["at", "*"],
  have [] [] [":=", expr has_deriv_at_integral_of_dominated_loc_of_deriv_le ε_pos hF_meas hF_int hF'_meas h_bound bound_integrable h_diff],
  exact [expr ⟨this.1, this.2.const_smul _⟩]
end

end intervalIntegral

