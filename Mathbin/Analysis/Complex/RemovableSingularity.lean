/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.complex.removable_singularity
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.FderivAnalytic
import Mathbin.Analysis.Asymptotics.SpecificAsymptotics
import Mathbin.Analysis.Complex.CauchyIntegral

/-!
# Removable singularity theorem

In this file we prove Riemann's removable singularity theorem: if `f : ℂ → E` is complex
differentiable in a punctured neighborhood of a point `c` and is bounded in a punctured neighborhood
of `c` (or, more generally, $f(z) - f(c)=o((z-c)^{-1})$), then it has a limit at `c` and the
function `function.update f c (lim (𝓝[≠] c) f)` is complex differentiable in a neighborhood of `c`.
-/


open TopologicalSpace Metric Set Filter Asymptotics Function

open Topology Filter Nnreal Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

namespace Complex

/-- **Removable singularity** theorem, weak version. If `f : ℂ → E` is differentiable in a punctured
neighborhood of a point and is continuous at this point, then it is analytic at this point. -/
theorem analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z) (hc : ContinuousAt f c) : AnalyticAt ℂ f c :=
  by
  rcases(nhdsWithin_hasBasis nhds_basis_closed_ball _).mem_iff.1 hd with ⟨R, hR0, hRs⟩
  lift R to ℝ≥0 using hR0.le
  replace hc : ContinuousOn f (closed_ball c R)
  · refine' fun z hz => ContinuousAt.continuousWithinAt _
    rcases eq_or_ne z c with (rfl | hne)
    exacts[hc, (hRs ⟨hz, hne⟩).ContinuousAt]
  exact
    (has_fpower_series_on_ball_of_differentiable_off_countable (countable_singleton c) hc
        (fun z hz => hRs (diff_subset_diff_left ball_subset_closed_ball hz)) hR0).AnalyticAt
#align complex.analytic_at_of_differentiable_on_punctured_nhds_of_continuous_at Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt

theorem differentiableOn_compl_singleton_and_continuousAt_iff {f : ℂ → E} {s : Set ℂ} {c : ℂ}
    (hs : s ∈ 𝓝 c) : DifferentiableOn ℂ f (s \ {c}) ∧ ContinuousAt f c ↔ DifferentiableOn ℂ f s :=
  by
  refine' ⟨_, fun hd => ⟨hd.mono (diff_subset _ _), (hd.DifferentiableAt hs).ContinuousAt⟩⟩
  rintro ⟨hd, hc⟩ x hx
  rcases eq_or_ne x c with (rfl | hne)
  · refine'
      (analytic_at_of_differentiable_on_punctured_nhds_of_continuous_at _
            hc).DifferentiableAt.DifferentiableWithinAt
    refine' eventually_nhdsWithin_iff.2 ((eventually_mem_nhds.2 hs).mono fun z hz hzx => _)
    exact hd.differentiable_at (inter_mem hz (is_open_ne.mem_nhds hzx))
  ·
    simpa only [DifferentiableWithinAt, HasFderivWithinAt, hne.nhds_within_diff_singleton] using
      hd x ⟨hx, hne⟩
#align complex.differentiable_on_compl_singleton_and_continuous_at_iff Complex.differentiableOn_compl_singleton_and_continuousAt_iff

theorem differentiableOn_dslope {f : ℂ → E} {s : Set ℂ} {c : ℂ} (hc : s ∈ 𝓝 c) :
    DifferentiableOn ℂ (dslope f c) s ↔ DifferentiableOn ℂ f s :=
  ⟨fun h => h.of_dslope, fun h =>
    (differentiableOn_compl_singleton_and_continuousAt_iff hc).mp <|
      ⟨Iff.mpr (differentiableOn_dslope_of_nmem fun h => h.2 rfl) (h.mono <| diff_subset _ _),
        continuousAt_dslope_same.2 <| h.DifferentiableAt hc⟩⟩
#align complex.differentiable_on_dslope Complex.differentiableOn_dslope

/-- **Removable singularity** theorem: if `s` is a neighborhood of `c : ℂ`, a function `f : ℂ → E`
is complex differentiable on `s \ {c}`, and $f(z) - f(c)=o((z-c)^{-1})$, then `f` redefined to be
equal to `lim (𝓝[≠] c) f` at `c` is complex differentiable on `s`. -/
theorem differentiableOn_update_limUnder_of_isOCat {f : ℂ → E} {s : Set ℂ} {c : ℂ} (hc : s ∈ 𝓝 c)
    (hd : DifferentiableOn ℂ f (s \ {c}))
    (ho : (fun z => f z - f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹) :
    DifferentiableOn ℂ (update f c (limUnder (𝓝[≠] c) f)) s :=
  by
  set F : ℂ → E := fun z => (z - c) • f z with hF
  suffices DifferentiableOn ℂ F (s \ {c}) ∧ ContinuousAt F c
    by
    rw [differentiable_on_compl_singleton_and_continuous_at_iff hc, ← differentiable_on_dslope hc,
        dslope_sub_smul] at this <;>
      try infer_instance
    have hc : tendsto f (𝓝[≠] c) (𝓝 (deriv F c)) :=
      continuous_at_update_same.mp (this.continuous_on.continuous_at hc)
    rwa [hc.lim_eq]
  refine' ⟨(differentiable_on_id.sub_const _).smul hd, _⟩
  rw [← continuousWithinAt_compl_self]
  have H := ho.tendsto_inv_smul_nhds_zero
  have H' : tendsto (fun z => (z - c) • f c) (𝓝[≠] c) (𝓝 (F c)) :=
    (continuous_within_at_id.tendsto.sub tendsto_const_nhds).smul tendsto_const_nhds
  simpa [← smul_add, ContinuousWithinAt] using H.add H'
#align complex.differentiable_on_update_lim_of_is_o Complex.differentiableOn_update_limUnder_of_isOCat

/-- **Removable singularity** theorem: if `s` is a punctured neighborhood of `c : ℂ`, a function
`f : ℂ → E` is complex differentiable on `s`, and $f(z) - f(c)=o((z-c)^{-1})$, then `f` redefined to
be equal to `lim (𝓝[≠] c) f` at `c` is complex differentiable on `{c} ∪ s`. -/
theorem differentiableOn_update_limUnder_insert_of_isOCat {f : ℂ → E} {s : Set ℂ} {c : ℂ}
    (hc : s ∈ 𝓝[≠] c) (hd : DifferentiableOn ℂ f s)
    (ho : (fun z => f z - f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹) :
    DifferentiableOn ℂ (update f c (limUnder (𝓝[≠] c) f)) (insert c s) :=
  differentiableOn_update_limUnder_of_isOCat (insert_mem_nhds_iff.2 hc)
    (hd.mono fun z hz => hz.1.resolve_left hz.2) ho
#align complex.differentiable_on_update_lim_insert_of_is_o Complex.differentiableOn_update_limUnder_insert_of_isOCat

/-- **Removable singularity** theorem: if `s` is a neighborhood of `c : ℂ`, a function `f : ℂ → E`
is complex differentiable and is bounded on `s \ {c}`, then `f` redefined to be equal to
`lim (𝓝[≠] c) f` at `c` is complex differentiable on `s`. -/
theorem differentiableOn_update_limUnder_of_bddAbove {f : ℂ → E} {s : Set ℂ} {c : ℂ} (hc : s ∈ 𝓝 c)
    (hd : DifferentiableOn ℂ f (s \ {c})) (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    DifferentiableOn ℂ (update f c (limUnder (𝓝[≠] c) f)) s :=
  differentiableOn_update_limUnder_of_isOCat hc hd <|
    IsBoundedUnder.isOCat_sub_self_inv <|
      let ⟨C, hC⟩ := hb
      ⟨C + ‖f c‖,
        eventually_map.2 <|
          mem_nhdsWithin_iff_exists_mem_nhds_inter.2
            ⟨s, hc, fun z hz => norm_sub_le_of_le (hC <| mem_image_of_mem _ hz) le_rfl⟩⟩
#align complex.differentiable_on_update_lim_of_bdd_above Complex.differentiableOn_update_limUnder_of_bddAbove

/-- **Removable singularity** theorem: if a function `f : ℂ → E` is complex differentiable on a
punctured neighborhood of `c` and $f(z) - f(c)=o((z-c)^{-1})$, then `f` has a limit at `c`. -/
theorem tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isOCat {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (ho : (fun z => f z - f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹) :
    Tendsto f (𝓝[≠] c) (𝓝 <| limUnder (𝓝[≠] c) f) :=
  by
  rw [eventually_nhdsWithin_iff] at hd
  have : DifferentiableOn ℂ f ({ z | z ≠ c → DifferentiableAt ℂ f z } \ {c}) := fun z hz =>
    (hz.1 hz.2).DifferentiableWithinAt
  have H := differentiable_on_update_lim_of_is_o hd this ho
  exact continuousAt_update_same.1 (H.differentiable_at hd).ContinuousAt
#align complex.tendsto_lim_of_differentiable_on_punctured_nhds_of_is_o Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isOCat

/-- **Removable singularity** theorem: if a function `f : ℂ → E` is complex differentiable and
bounded on a punctured neighborhood of `c`, then `f` has a limit at `c`. -/
theorem tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] c) fun z => ‖f z - f c‖) :
    Tendsto f (𝓝[≠] c) (𝓝 <| limUnder (𝓝[≠] c) f) :=
  tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isOCat hd hb.isOCat_sub_self_inv
#align complex.tendsto_lim_of_differentiable_on_punctured_nhds_of_bounded_under Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under

/-- The Cauchy formula for the derivative of a holomorphic function. -/
theorem two_pi_i_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable {U : Set ℂ}
    (hU : IsOpen U) {c w₀ : ℂ} {R : ℝ} {f : ℂ → E} (hc : closedBall c R ⊆ U)
    (hf : DifferentiableOn ℂ f U) (hw₀ : w₀ ∈ ball c R) :
    ((2 * π * i : ℂ)⁻¹ • ∮ z in C(c, R), ((z - w₀) ^ 2)⁻¹ • f z) = deriv f w₀ :=
  by
  -- We apply the removable singularity theorem and the Cauchy formula to `dslope f w₀`
  have hR : 0 < R := not_le.mp (ball_eq_empty.not.mp (nonempty_of_mem hw₀).ne_empty)
  have hf' : DifferentiableOn ℂ (dslope f w₀) U :=
    (differentiable_on_dslope (hU.mem_nhds ((ball_subset_closed_ball.trans hc) hw₀))).mpr hf
  have h0 := (hf'.diff_cont_on_cl_ball hc).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw₀
  rw [← dslope_same, ← h0]
  congr 1
  trans ∮ z in C(c, R), ((z - w₀) ^ 2)⁻¹ • (f z - f w₀)
  · have h1 : ContinuousOn (fun z : ℂ => ((z - w₀) ^ 2)⁻¹) (sphere c R) :=
      by
      refine' ((continuous_id'.sub continuous_const).pow 2).ContinuousOn.inv₀ fun w hw h => _
      exact sphere_disjoint_ball.ne_of_mem hw hw₀ (sub_eq_zero.mp (sq_eq_zero_iff.mp h))
    have h2 : CircleIntegrable (fun z : ℂ => ((z - w₀) ^ 2)⁻¹ • f z) c R :=
      by
      refine' ContinuousOn.circleIntegrable (pos_of_mem_ball hw₀).le _
      exact h1.smul (hf.continuous_on.mono (sphere_subset_closed_ball.trans hc))
    have h3 : CircleIntegrable (fun z : ℂ => ((z - w₀) ^ 2)⁻¹ • f w₀) c R :=
      ContinuousOn.circleIntegrable (pos_of_mem_ball hw₀).le (h1.smul continuousOn_const)
    have h4 : (∮ z : ℂ in C(c, R), ((z - w₀) ^ 2)⁻¹) = 0 := by
      simpa using circleIntegral.integral_sub_zpow_of_ne (by decide : (-2 : ℤ) ≠ -1) c w₀ R
    simp only [smul_sub, circleIntegral.integral_sub h2 h3, h4, circleIntegral.integral_smul_const,
      zero_smul, sub_zero]
  · refine' circleIntegral.integral_congr (pos_of_mem_ball hw₀).le fun z hz => _
    simp only [dslope_of_ne, metric.sphere_disjoint_ball.ne_of_mem hz hw₀, slope, ← smul_assoc, sq,
      mul_inv, Ne.def, not_false_iff, vsub_eq_sub, Algebra.id.smul_eq_mul]
#align complex.two_pi_I_inv_smul_circle_integral_sub_sq_inv_smul_of_differentiable Complex.two_pi_i_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable

end Complex

