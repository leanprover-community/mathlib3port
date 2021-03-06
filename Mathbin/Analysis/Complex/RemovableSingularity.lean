/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.Calculus.FderivAnalytic
import Mathbin.Analysis.Asymptotics.SpecificAsymptotics
import Mathbin.Analysis.Complex.CauchyIntegral

/-!
# Removable singularity theorem

In this file we prove Riemann's removable singularity theorem: if `f : β β E` is complex
differentiable in a punctured neighborhood of a point `c` and is bounded in a punctured neighborhood
of `c` (or, more generally, $f(z) - f(c)=o((z-c)^{-1})$), then it has a limit at `c` and the
function `function.update f c (lim (π[β ] c) f)` is complex differentiable in a neighborhood of `c`.
-/


open TopologicalSpace Metric Set Filter Asymptotics Function

open TopologicalSpace Filter Nnreal

universe u

variable {E : Type u} [NormedGroup E] [NormedSpace β E] [CompleteSpace E]

namespace Complex

/-- **Removable singularity** theorem, weak version. If `f : β β E` is differentiable in a punctured
neighborhood of a point and is continuous at this point, then it is analytic at this point. -/
theorem analytic_at_of_differentiable_on_punctured_nhds_of_continuous_at {f : β β E} {c : β}
    (hd : βαΆ  z in π[β ] c, DifferentiableAt β f z) (hc : ContinuousAt f c) : AnalyticAt β f c := by
  rcases(nhds_within_has_basis nhds_basis_closed_ball _).mem_iff.1 hd with β¨R, hR0, hRsβ©
  lift R to ββ₯0 using hR0.le
  replace hc : ContinuousOn f (closed_ball c R)
  Β· refine' fun z hz => ContinuousAt.continuous_within_at _
    rcases eq_or_ne z c with (rfl | hne)
    exacts[hc, (hRs β¨hz, hneβ©).ContinuousAt]
    
  exact
    (has_fpower_series_on_ball_of_differentiable_off_countable (countable_singleton c) hc
        (fun z hz => hRs (diff_subset_diff_left ball_subset_closed_ball hz)) hR0).AnalyticAt

theorem differentiable_on_compl_singleton_and_continuous_at_iff {f : β β E} {s : Set β} {c : β} (hs : s β π c) :
    DifferentiableOn β f (s \ {c}) β§ ContinuousAt f c β DifferentiableOn β f s := by
  refine' β¨_, fun hd => β¨hd.mono (diff_subset _ _), (hd.DifferentiableAt hs).ContinuousAtβ©β©
  rintro β¨hd, hcβ© x hx
  rcases eq_or_ne x c with (rfl | hne)
  Β· refine'
      (analytic_at_of_differentiable_on_punctured_nhds_of_continuous_at _ hc).DifferentiableAt.DifferentiableWithinAt
    refine' eventually_nhds_within_iff.2 ((eventually_mem_nhds.2 hs).mono fun z hz hzx => _)
    exact hd.differentiable_at (inter_mem hz (is_open_ne.mem_nhds hzx))
    
  Β· simpa only [β DifferentiableWithinAt, β HasFderivWithinAt, β hne.nhds_within_diff_singleton] using hd x β¨hx, hneβ©
    

theorem differentiable_on_dslope {f : β β E} {s : Set β} {c : β} (hc : s β π c) :
    DifferentiableOn β (dslope f c) s β DifferentiableOn β f s :=
  β¨fun h => h.of_dslope, fun h =>
    (differentiable_on_compl_singleton_and_continuous_at_iff hc).mp <|
      β¨Iff.mpr (differentiable_on_dslope_of_nmem fun h => h.2 rfl) (h.mono <| diff_subset _ _),
        continuous_at_dslope_same.2 <| h.DifferentiableAt hcβ©β©

/-- **Removable singularity** theorem: if `s` is a neighborhood of `c : β`, a function `f : β β E`
is complex differentiable on `s \ {c}`, and $f(z) - f(c)=o((z-c)^{-1})$, then `f` redefined to be
equal to `lim (π[β ] c) f` at `c` is complex differentiable on `s`. -/
theorem differentiable_on_update_lim_of_is_o {f : β β E} {s : Set β} {c : β} (hc : s β π c)
    (hd : DifferentiableOn β f (s \ {c})) (ho : (fun z => f z - f c) =o[π[β ] c] fun z => (z - c)β»ΒΉ) :
    DifferentiableOn β (update f c (limβ (π[β ] c) f)) s := by
  set F : β β E := fun z => (z - c) β’ f z with hF
  suffices DifferentiableOn β F (s \ {c}) β§ ContinuousAt F c by
    rw [differentiable_on_compl_singleton_and_continuous_at_iff hc, β differentiable_on_dslope hc, dslope_sub_smul] at
        this <;>
      try
        infer_instance
    have hc : tendsto f (π[β ] c) (π (deriv F c)) := continuous_at_update_same.mp (this.continuous_on.continuous_at hc)
    rwa [hc.lim_eq]
  refine' β¨(differentiable_on_id.sub_const _).smul hd, _β©
  rw [β continuous_within_at_compl_self]
  have H := ho.tendsto_inv_smul_nhds_zero
  have H' : tendsto (fun z => (z - c) β’ f c) (π[β ] c) (π (F c)) :=
    (continuous_within_at_id.tendsto.sub tendsto_const_nhds).smul tendsto_const_nhds
  simpa [smul_add, β ContinuousWithinAt] using H.add H'

/-- **Removable singularity** theorem: if `s` is a punctured neighborhood of `c : β`, a function
`f : β β E` is complex differentiable on `s`, and $f(z) - f(c)=o((z-c)^{-1})$, then `f` redefined to
be equal to `lim (π[β ] c) f` at `c` is complex differentiable on `{c} βͺ s`. -/
theorem differentiable_on_update_lim_insert_of_is_o {f : β β E} {s : Set β} {c : β} (hc : s β π[β ] c)
    (hd : DifferentiableOn β f s) (ho : (fun z => f z - f c) =o[π[β ] c] fun z => (z - c)β»ΒΉ) :
    DifferentiableOn β (update f c (limβ (π[β ] c) f)) (insert c s) :=
  differentiable_on_update_lim_of_is_o (insert_mem_nhds_iff.2 hc) (hd.mono fun z hz => hz.1.resolve_left hz.2) ho

/-- **Removable singularity** theorem: if `s` is a neighborhood of `c : β`, a function `f : β β E`
is complex differentiable and is bounded on `s \ {c}`, then `f` redefined to be equal to
`lim (π[β ] c) f` at `c` is complex differentiable on `s`. -/
theorem differentiable_on_update_lim_of_bdd_above {f : β β E} {s : Set β} {c : β} (hc : s β π c)
    (hd : DifferentiableOn β f (s \ {c})) (hb : BddAbove (norm β f '' (s \ {c}))) :
    DifferentiableOn β (update f c (limβ (π[β ] c) f)) s :=
  differentiable_on_update_lim_of_is_o hc hd <|
    is_bounded_under.is_o_sub_self_inv <|
      let β¨C, hCβ© := hb
      β¨C + β₯f cβ₯,
        eventually_map.2 <|
          mem_nhds_within_iff_exists_mem_nhds_inter.2
            β¨s, hc, fun z hz => norm_sub_le_of_le (hC <| mem_image_of_mem _ hz) le_rflβ©β©

/-- **Removable singularity** theorem: if a function `f : β β E` is complex differentiable on a
punctured neighborhood of `c` and $f(z) - f(c)=o((z-c)^{-1})$, then `f` has a limit at `c`. -/
theorem tendsto_lim_of_differentiable_on_punctured_nhds_of_is_o {f : β β E} {c : β}
    (hd : βαΆ  z in π[β ] c, DifferentiableAt β f z) (ho : (fun z => f z - f c) =o[π[β ] c] fun z => (z - c)β»ΒΉ) :
    Tendsto f (π[β ] c) (π <| limβ (π[β ] c) f) := by
  rw [eventually_nhds_within_iff] at hd
  have : DifferentiableOn β f ({ z | z β  c β DifferentiableAt β f z } \ {c}) := fun z hz =>
    (hz.1 hz.2).DifferentiableWithinAt
  have H := differentiable_on_update_lim_of_is_o hd this ho
  exact continuous_at_update_same.1 (H.differentiable_at hd).ContinuousAt

/-- **Removable singularity** theorem: if a function `f : β β E` is complex differentiable and
bounded on a punctured neighborhood of `c`, then `f` has a limit at `c`. -/
theorem tendsto_lim_of_differentiable_on_punctured_nhds_of_bounded_under {f : β β E} {c : β}
    (hd : βαΆ  z in π[β ] c, DifferentiableAt β f z) (hb : IsBoundedUnder (Β· β€ Β·) (π[β ] c) fun z => β₯f z - f cβ₯) :
    Tendsto f (π[β ] c) (π <| limβ (π[β ] c) f) :=
  tendsto_lim_of_differentiable_on_punctured_nhds_of_is_o hd hb.is_o_sub_self_inv

end Complex

