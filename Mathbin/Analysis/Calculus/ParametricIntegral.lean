import Mathbin.MeasureTheory.Integral.SetIntegral 
import Mathbin.Analysis.Calculus.MeanValue

/-!
# Derivatives of integrals depending on parameters

A parametric integral is a function with shape `f = λ x : H, ∫ a : α, F x a ∂μ` for some
`F : H → α → E`, where `H` and `E` are normed spaces and `α` is a measured space with measure `μ`.

We already know from `continuous_of_dominated` in `measure_theory.integral.bochner` how to
guarantee that `f` is continuous using the dominated convergence theorem. In this file,
we want to express the derivative of `f` as the integral of the derivative of `F` with respect
to `x`.


## Main results

As explained above, all results express the derivative of a parametric integral as the integral of
a derivative. The variations come from the assumptions and from the different ways of expressing
derivative, especially Fréchet derivatives vs elementary derivative of function of one real
variable.

* `has_fderiv_at_integral_of_dominated_loc_of_lip`: this version assumes that
  - `F x` is ae-measurable for x near `x₀`,
  - `F x₀` is integrable,
  - `λ x, F x a` has derivative `F' a : H →L[ℝ] E` at `x₀` which is ae-measurable,
  - `λ x, F x a` is locally Lipschitz near `x₀` for almost every `a`, with a Lipschitz bound which
    is integrable with respect to `a`.

  A subtle point is that the "near x₀" in the last condition has to be uniform in `a`. This is
  controlled by a positive number `ε`.

* `has_fderiv_at_integral_of_dominated_of_fderiv_le`: this version assume `λ x, F x a` has
   derivative `F' x a` for `x` near `x₀` and `F' x` is bounded by an integrable function independent
   from `x` near `x₀`.


`has_deriv_at_integral_of_dominated_loc_of_lip` and
`has_deriv_at_integral_of_dominated_loc_of_deriv_le` are versions of the above two results that
assume `H = ℝ` or `H = ℂ` and use the high-school derivative `deriv` instead of Fréchet derivative
`fderiv`.

We also provide versions of these theorems for set integrals.

## Tags
integral, derivative
-/


noncomputable theory

open TopologicalSpace MeasureTheory Filter Metric

open_locale TopologicalSpace Filter

variable {α : Type _} [MeasurableSpace α] {μ : Measureₓ α} {𝕜 : Type _} [IsROrC 𝕜] {E : Type _} [NormedGroup E]
  [NormedSpace ℝ E] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E] [second_countable_topology E]
  [MeasurableSpace E] [BorelSpace E] {H : Type _} [NormedGroup H] [NormedSpace 𝕜 H]
  [second_countable_topology$ H →L[𝕜] E]

-- error in Analysis.Calculus.ParametricIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming `F x₀` is
integrable, `∥F x a - F x₀ a∥ ≤ bound a * ∥x - x₀∥` for `x` in a ball around `x₀` for ae `a` with
integrable Lipschitz bound `bound` (with a ball radius independent of `a`), and `F x` is
ae-measurable for `x` in the same ball. See `has_fderiv_at_integral_of_dominated_loc_of_lip` for a
slightly less general but usually more useful version. -/
theorem has_fderiv_at_integral_of_dominated_loc_of_lip'
{F : H → α → E}
{F' : α → «expr →L[ ] »(H, 𝕜, E)}
{x₀ : H}
{bound : α → exprℝ()}
{ε : exprℝ()}
(ε_pos : «expr < »(0, ε))
(hF_meas : ∀ x «expr ∈ » ball x₀ ε, ae_measurable (F x) μ)
(hF_int : integrable (F x₀) μ)
(hF'_meas : ae_measurable F' μ)
(h_lipsch : «expr∀ᵐ ∂ , »((a), μ, ∀
  x «expr ∈ » ball x₀ ε, «expr ≤ »(«expr∥ ∥»(«expr - »(F x a, F x₀ a)), «expr * »(bound a, «expr∥ ∥»(«expr - »(x, x₀))))))
(bound_integrable : integrable (bound : α → exprℝ()) μ)
(h_diff : «expr∀ᵐ ∂ , »((a), μ, has_fderiv_at (λ
   x, F x a) (F' a) x₀)) : «expr ∧ »(integrable F' μ, has_fderiv_at (λ
  x, «expr∫ , ∂ »((a), F x a, μ)) «expr∫ , ∂ »((a), F' a, μ) x₀) :=
begin
  letI [] [":", expr measurable_space 𝕜] [":=", expr borel 𝕜],
  haveI [] [":", expr opens_measurable_space 𝕜] [":=", expr ⟨le_rfl⟩],
  have [ident x₀_in] [":", expr «expr ∈ »(x₀, ball x₀ ε)] [":=", expr mem_ball_self ε_pos],
  have [ident nneg] [":", expr ∀
   x, «expr ≤ »(0, «expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))))] [":=", expr λ x, inv_nonneg.mpr (norm_nonneg _)],
  set [] [ident b] [":", expr α → exprℝ()] [":="] [expr λ a, «expr| |»(bound a)] [],
  have [ident b_int] [":", expr integrable b μ] [":=", expr bound_integrable.norm],
  have [ident b_nonneg] [":", expr ∀ a, «expr ≤ »(0, b a)] [":=", expr λ a, abs_nonneg _],
  replace [ident h_lipsch] [":", expr «expr∀ᵐ ∂ , »((a), μ, ∀
    x «expr ∈ » ball x₀ ε, «expr ≤ »(«expr∥ ∥»(«expr - »(F x a, F x₀ a)), «expr * »(b a, «expr∥ ∥»(«expr - »(x, x₀)))))] [],
  from [expr h_lipsch.mono (λ
    a ha x hx, «expr $ »((ha x hx).trans, mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)))],
  have [ident hF_int'] [":", expr ∀ x «expr ∈ » ball x₀ ε, integrable (F x) μ] [],
  { intros [ident x, ident x_in],
    have [] [":", expr «expr∀ᵐ ∂ , »((a), μ, «expr ≤ »(«expr∥ ∥»(«expr - »(F x₀ a, F x a)), «expr * »(ε, b a)))] [],
    { simp [] [] ["only"] ["[", expr norm_sub_rev (F x₀ _), "]"] [] [],
      refine [expr h_lipsch.mono (λ a ha, (ha x x_in).trans _)],
      rw [expr mul_comm ε] [],
      rw ["[", expr mem_ball, ",", expr dist_eq_norm, "]"] ["at", ident x_in],
      exact [expr mul_le_mul_of_nonneg_left x_in.le (b_nonneg _)] },
    exact [expr integrable_of_norm_sub_le (hF_meas x x_in) hF_int (integrable.const_mul bound_integrable.norm ε) this] },
  have [ident hF'_int] [":", expr integrable F' μ] [],
  { have [] [":", expr «expr∀ᵐ ∂ , »((a), μ, «expr ≤ »(«expr∥ ∥»(F' a), b a))] [],
    { apply [expr (h_diff.and h_lipsch).mono],
      rintros [ident a, "⟨", ident ha_diff, ",", ident ha_lip, "⟩"],
      refine [expr ha_diff.le_of_lip' (b_nonneg a) «expr $ »(mem_of_superset (ball_mem_nhds _ ε_pos), ha_lip)] },
    exact [expr b_int.mono' hF'_meas this] },
  refine [expr ⟨hF'_int, _⟩],
  have [ident h_ball] [":", expr «expr ∈ »(ball x₀ ε, expr𝓝() x₀)] [":=", expr ball_mem_nhds x₀ ε_pos],
  have [] [":", expr «expr∀ᶠ in , »((x), expr𝓝() x₀, «expr = »(«expr * »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr∥ ∥»(«expr - »(«expr - »(«expr∫ , ∂ »((a), F x a, μ), «expr∫ , ∂ »((a), F x₀ a, μ)), «expr∫ , ∂ »((a), F' a, μ) «expr - »(x, x₀)))), «expr∥ ∥»(«expr∫ , ∂ »((a), «expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(«expr - »(F x a, F x₀ a), F' a «expr - »(x, x₀))), μ))))] [],
  { apply [expr mem_of_superset (ball_mem_nhds _ ε_pos)],
    intros [ident x, ident x_in],
    rw ["[", expr set.mem_set_of_eq, ",", "<-", expr norm_smul_of_nonneg (nneg _), ",", expr integral_smul, ",", expr integral_sub, ",", expr integral_sub, ",", "<-", expr continuous_linear_map.integral_apply hF'_int, "]"] [],
    exacts ["[", expr hF_int' x x_in, ",", expr hF_int, ",", expr (hF_int' x x_in).sub hF_int, ",", expr hF'_int.apply_continuous_linear_map _, "]"] },
  rw ["[", expr has_fderiv_at_iff_tendsto, ",", expr tendsto_congr' this, ",", "<-", expr tendsto_zero_iff_norm_tendsto_zero, ",", "<-", expr show «expr = »(«expr∫ , ∂ »((a : α), «expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x₀, x₀))), «expr - »(«expr - »(F x₀ a, F x₀ a), F' a «expr - »(x₀, x₀))), μ), 0), by simp [] [] [] [] [] [], "]"] [],
  apply [expr tendsto_integral_filter_of_dominated_convergence],
  { filter_upwards ["[", expr h_ball, "]"] [],
    intros [ident x, ident x_in],
    apply [expr ae_measurable.const_smul],
    exact [expr ((hF_meas _ x_in).sub (hF_meas _ x₀_in)).sub (hF'_meas.apply_continuous_linear_map _)] },
  { apply [expr mem_of_superset h_ball],
    intros [ident x, ident hx],
    apply [expr (h_diff.and h_lipsch).mono],
    rintros [ident a, "⟨", ident ha_deriv, ",", ident ha_bound, "⟩"],
    show [expr «expr ≤ »(«expr∥ ∥»(«expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(«expr - »(F x a, F x₀ a), F' a «expr - »(x, x₀)))), «expr + »(b a, «expr∥ ∥»(F' a)))],
    replace [ident ha_bound] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(F x a, F x₀ a)), «expr * »(b a, «expr∥ ∥»(«expr - »(x, x₀))))] [":=", expr ha_bound x hx],
    calc
      «expr = »(«expr∥ ∥»(«expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(«expr - »(F x a, F x₀ a), F' a «expr - »(x, x₀)))), «expr∥ ∥»(«expr - »(«expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(F x a, F x₀ a)), «expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), F' a «expr - »(x, x₀))))) : by rw [expr smul_sub] []
      «expr ≤ »(..., «expr + »(«expr∥ ∥»(«expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(F x a, F x₀ a))), «expr∥ ∥»(«expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), F' a «expr - »(x, x₀))))) : norm_sub_le _ _
      «expr = »(..., «expr + »(«expr * »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr∥ ∥»(«expr - »(F x a, F x₀ a))), «expr * »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr∥ ∥»(F' a «expr - »(x, x₀))))) : by { rw ["[", expr norm_smul_of_nonneg, ",", expr norm_smul_of_nonneg, "]"] []; exact [expr nneg _] }
      «expr ≤ »(..., «expr + »(«expr * »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr * »(b a, «expr∥ ∥»(«expr - »(x, x₀)))), «expr * »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr * »(«expr∥ ∥»(F' a), «expr∥ ∥»(«expr - »(x, x₀)))))) : add_le_add _ _
      «expr ≤ »(..., «expr + »(b a, «expr∥ ∥»(F' a))) : _,
    exact [expr mul_le_mul_of_nonneg_left ha_bound (nneg _)],
    apply [expr mul_le_mul_of_nonneg_left ((F' a).le_op_norm _) (nneg _)],
    by_cases [expr h, ":", expr «expr = »(«expr∥ ∥»(«expr - »(x, x₀)), 0)],
    { simpa [] [] [] ["[", expr h, "]"] [] ["using", expr add_nonneg (b_nonneg a) (norm_nonneg (F' a))] },
    { field_simp [] ["[", expr h, "]"] [] [] } },
  { exact [expr b_int.add hF'_int.norm] },
  { apply [expr h_diff.mono],
    intros [ident a, ident ha],
    suffices [] [":", expr tendsto (λ
      x, «expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(«expr - »(F x a, F x₀ a), F' a «expr - »(x, x₀)))) (expr𝓝() x₀) (expr𝓝() 0)],
    by simpa [] [] [] [] [] [],
    rw [expr tendsto_zero_iff_norm_tendsto_zero] [],
    have [] [":", expr «expr = »(λ
      x, «expr * »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr∥ ∥»(«expr - »(«expr - »(F x a, F x₀ a), F' a «expr - »(x, x₀)))), λ
      x, «expr∥ ∥»(«expr • »(«expr ⁻¹»(«expr∥ ∥»(«expr - »(x, x₀))), «expr - »(«expr - »(F x a, F x₀ a), F' a «expr - »(x, x₀)))))] [],
    { ext [] [ident x] [],
      rw [expr norm_smul_of_nonneg (nneg _)] [] },
    rwa ["[", expr has_fderiv_at_iff_tendsto, ",", expr this, "]"] ["at", ident ha] }
end

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with a ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is ae-measurable
for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem has_fderiv_at_integral_of_dominated_loc_of_lip {F : H → α → E} {F' : α → H →L[𝕜] E} {x₀ : H} {bound : α → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε) (hF_meas : ∀ᶠx in 𝓝 x₀, AeMeasurable (F x) μ) (hF_int : integrable (F x₀) μ)
  (hF'_meas : AeMeasurable F' μ) (h_lip : ∀ᵐa ∂μ, LipschitzOnWith (Real.nnabs$ bound a) (fun x => F x a) (ball x₀ ε))
  (bound_integrable : integrable (bound : α → ℝ) μ) (h_diff : ∀ᵐa ∂μ, HasFderivAt (fun x => F x a) (F' a) x₀) :
  integrable F' μ ∧ HasFderivAt (fun x => ∫a, F x a ∂μ) (∫a, F' a ∂μ) x₀ :=
  by 
    obtain ⟨δ, δ_pos, hδ⟩ : ∃ (δ : _)(_ : δ > 0), ∀ x _ : x ∈ ball x₀ δ, AeMeasurable (F x) μ ∧ x ∈ ball x₀ ε 
    exact eventually_nhds_iff_ball.mp (hF_meas.and (ball_mem_nhds x₀ ε_pos))
    choose hδ_meas hδε using hδ 
    replace h_lip : ∀ᵐa : α ∂μ, ∀ x _ : x ∈ ball x₀ δ, ∥F x a - F x₀ a∥ ≤ |bound a|*∥x - x₀∥
    exact h_lip.mono fun a lip x hx => lip.norm_sub_le (hδε x hx) (mem_ball_self ε_pos)
    replace bound_integrable := bound_integrable.norm 
    apply has_fderiv_at_integral_of_dominated_loc_of_lip' δ_pos <;> assumption

-- error in Analysis.Calculus.ParametricIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on a ball around `x₀` for ae `a` with
derivative norm uniformly bounded by an integrable function (the ball radius is independent of `a`),
and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem has_fderiv_at_integral_of_dominated_of_fderiv_le
{F : H → α → E}
{F' : H → α → «expr →L[ ] »(H, 𝕜, E)}
{x₀ : H}
{bound : α → exprℝ()}
{ε : exprℝ()}
(ε_pos : «expr < »(0, ε))
(hF_meas : «expr∀ᶠ in , »((x), expr𝓝() x₀, ae_measurable (F x) μ))
(hF_int : integrable (F x₀) μ)
(hF'_meas : ae_measurable (F' x₀) μ)
(h_bound : «expr∀ᵐ ∂ , »((a), μ, ∀ x «expr ∈ » ball x₀ ε, «expr ≤ »(«expr∥ ∥»(F' x a), bound a)))
(bound_integrable : integrable (bound : α → exprℝ()) μ)
(h_diff : «expr∀ᵐ ∂ , »((a), μ, ∀
  x «expr ∈ » ball x₀ ε, has_fderiv_at (λ
   x, F x a) (F' x a) x)) : has_fderiv_at (λ x, «expr∫ , ∂ »((a), F x a, μ)) «expr∫ , ∂ »((a), F' x₀ a, μ) x₀ :=
begin
  letI [] [":", expr normed_space exprℝ() H] [":=", expr normed_space.restrict_scalars exprℝ() 𝕜 H],
  haveI [] [":", expr is_scalar_tower exprℝ() 𝕜 H] [":=", expr restrict_scalars.is_scalar_tower exprℝ() 𝕜 H],
  have [ident x₀_in] [":", expr «expr ∈ »(x₀, ball x₀ ε)] [":=", expr mem_ball_self ε_pos],
  have [ident diff_x₀] [":", expr «expr∀ᵐ ∂ , »((a), μ, has_fderiv_at (λ
     x, F x a) (F' x₀ a) x₀)] [":=", expr h_diff.mono (λ a ha, ha x₀ x₀_in)],
  have [] [":", expr «expr∀ᵐ ∂ , »((a), μ, lipschitz_on_with (real.nnabs (bound a)) (λ x, F x a) (ball x₀ ε))] [],
  { apply [expr (h_diff.and h_bound).mono],
    rintros [ident a, "⟨", ident ha_deriv, ",", ident ha_bound, "⟩"],
    refine [expr (convex_ball _ _).lipschitz_on_with_of_nnnorm_has_fderiv_within_le (λ
      x x_in, (ha_deriv x x_in).has_fderiv_within_at) (λ x x_in, _)],
    rw ["[", "<-", expr nnreal.coe_le_coe, ",", expr coe_nnnorm, ",", expr real.coe_nnabs, "]"] [],
    exact [expr (ha_bound x x_in).trans (le_abs_self _)] },
  exact [expr (has_fderiv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas this bound_integrable diff_x₀).2]
end

-- error in Analysis.Calculus.ParametricIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
assuming `F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is
ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem has_deriv_at_integral_of_dominated_loc_of_lip
{F : 𝕜 → α → E}
{F' : α → E}
{x₀ : 𝕜}
{ε : exprℝ()}
(ε_pos : «expr < »(0, ε))
(hF_meas : «expr∀ᶠ in , »((x), expr𝓝() x₀, ae_measurable (F x) μ))
(hF_int : integrable (F x₀) μ)
(hF'_meas : ae_measurable F' μ)
{bound : α → exprℝ()}
(h_lipsch : «expr∀ᵐ ∂ , »((a), μ, lipschitz_on_with «expr $ »(real.nnabs, bound a) (λ x, F x a) (ball x₀ ε)))
(bound_integrable : integrable (bound : α → exprℝ()) μ)
(h_diff : «expr∀ᵐ ∂ , »((a), μ, has_deriv_at (λ
   x, F x a) (F' a) x₀)) : «expr ∧ »(integrable F' μ, has_deriv_at (λ
  x, «expr∫ , ∂ »((a), F x a, μ)) «expr∫ , ∂ »((a), F' a, μ) x₀) :=
begin
  letI [] [":", expr measurable_space 𝕜] [":=", expr borel 𝕜],
  haveI [] [":", expr opens_measurable_space 𝕜] [":=", expr ⟨le_rfl⟩],
  set [] [ident L] [":", expr «expr →L[ ] »(E, 𝕜, «expr →L[ ] »(𝕜, 𝕜, E))] [":="] [expr continuous_linear_map.smul_rightL 𝕜 𝕜 E 1] [],
  replace [ident h_diff] [":", expr «expr∀ᵐ ∂ , »((a), μ, has_fderiv_at (λ
     x, F x a) (L (F' a)) x₀)] [":=", expr h_diff.mono (λ x hx, hx.has_fderiv_at)],
  have [ident hm] [":", expr ae_measurable «expr ∘ »(L, F') μ] [":=", expr L.continuous.measurable.comp_ae_measurable hF'_meas],
  cases [expr has_fderiv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int hm h_lipsch bound_integrable h_diff] ["with", ident hF'_int, ident key],
  replace [ident hF'_int] [":", expr integrable F' μ] [],
  { rw ["[", "<-", expr integrable_norm_iff hm, "]"] ["at", ident hF'_int],
    simpa [] [] ["only"] ["[", expr L, ",", expr («expr ∘ »), ",", expr integrable_norm_iff, ",", expr hF'_meas, ",", expr one_mul, ",", expr norm_one, ",", expr continuous_linear_map.comp_apply, ",", expr continuous_linear_map.coe_restrict_scalarsL', ",", expr continuous_linear_map.norm_restrict_scalars, ",", expr continuous_linear_map.norm_smul_rightL_apply, "]"] [] ["using", expr hF'_int] },
  refine [expr ⟨hF'_int, _⟩],
  simp_rw [expr has_deriv_at_iff_has_fderiv_at] ["at", ident h_diff, "⊢"],
  rwa [expr continuous_linear_map.integral_comp_comm _ hF'_int] ["at", ident key],
  all_goals { apply_instance }
end

-- error in Analysis.Calculus.ParametricIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : ℝ`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on an interval around `x₀` for ae `a`
(with interval radius independent of `a`) with derivative uniformly bounded by an integrable
function, and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem has_deriv_at_integral_of_dominated_loc_of_deriv_le
{F : 𝕜 → α → E}
{F' : 𝕜 → α → E}
{x₀ : 𝕜}
{ε : exprℝ()}
(ε_pos : «expr < »(0, ε))
(hF_meas : «expr∀ᶠ in , »((x), expr𝓝() x₀, ae_measurable (F x) μ))
(hF_int : integrable (F x₀) μ)
(hF'_meas : ae_measurable (F' x₀) μ)
{bound : α → exprℝ()}
(h_bound : «expr∀ᵐ ∂ , »((a), μ, ∀ x «expr ∈ » ball x₀ ε, «expr ≤ »(«expr∥ ∥»(F' x a), bound a)))
(bound_integrable : integrable bound μ)
(h_diff : «expr∀ᵐ ∂ , »((a), μ, ∀
  x «expr ∈ » ball x₀ ε, has_deriv_at (λ
   x, F x a) (F' x a) x)) : «expr ∧ »(integrable (F' x₀) μ, has_deriv_at (λ
  n, «expr∫ , ∂ »((a), F n a, μ)) «expr∫ , ∂ »((a), F' x₀ a, μ) x₀) :=
begin
  have [ident x₀_in] [":", expr «expr ∈ »(x₀, ball x₀ ε)] [":=", expr mem_ball_self ε_pos],
  have [ident diff_x₀] [":", expr «expr∀ᵐ ∂ , »((a), μ, has_deriv_at (λ
     x, F x a) (F' x₀ a) x₀)] [":=", expr h_diff.mono (λ a ha, ha x₀ x₀_in)],
  have [] [":", expr «expr∀ᵐ ∂ , »((a), μ, lipschitz_on_with (real.nnabs (bound a)) (λ x : 𝕜, F x a) (ball x₀ ε))] [],
  { apply [expr (h_diff.and h_bound).mono],
    rintros [ident a, "⟨", ident ha_deriv, ",", ident ha_bound, "⟩"],
    refine [expr (convex_ball _ _).lipschitz_on_with_of_nnnorm_has_deriv_within_le (λ
      x x_in, (ha_deriv x x_in).has_deriv_within_at) (λ x x_in, _)],
    rw ["[", "<-", expr nnreal.coe_le_coe, ",", expr coe_nnnorm, ",", expr real.coe_nnabs, "]"] [],
    exact [expr (ha_bound x x_in).trans (le_abs_self _)] },
  exact [expr has_deriv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas this bound_integrable diff_x₀]
end

