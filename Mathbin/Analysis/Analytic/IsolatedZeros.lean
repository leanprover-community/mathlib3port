/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara

! This file was ported from Lean 3 source module analysis.analytic.isolated_zeros
! leanprover-community/mathlib commit d3e8e0a0237c10c2627bf52c246b15ff8e7df4c0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Analytic.Basic
import Mathbin.Analysis.Calculus.Dslope
import Mathbin.Analysis.Calculus.FderivAnalytic
import Mathbin.Analysis.Calculus.FormalMultilinearSeries
import Mathbin.Topology.Algebra.InfiniteSum
import Mathbin.Analysis.Analytic.Uniqueness

/-!
# Principle of isolated zeros

This file proves the fact that the zeros of a non-constant analytic function of one variable are
isolated. It also introduces a little bit of API in the `has_fpower_series_at` namespace that is
useful in this setup.

## Main results

* `analytic_at.eventually_eq_zero_or_eventually_ne_zero` is the main statement that if a function is
  analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
  vanish in a punctured neighborhood of `z₀`.
* `analytic_on.eq_on_of_preconnected_of_frequently_eq` is the identity theorem for analytic
  functions: if a function `f` is analytic on a connected set `U` and is zero on a set with an
  accumulation point in `U` then `f` is identically `0` on `U`.
-/


open Classical

open Filter Function Nat FormalMultilinearSeries Emetric Set

open TopologicalSpace BigOperators

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}
  {y : Fin n → 𝕜}

namespace HasSum

variable {a : ℕ → E}

theorem has_sum_at_zero (a : ℕ → E) : HasSum (fun n => (0 : 𝕜) ^ n • a n) (a 0) := by
  convert has_sum_single 0 fun b h => _ <;> first |simp [Nat.pos_of_ne_zero h]|simp
#align has_sum.has_sum_at_zero HasSum.has_sum_at_zero

theorem exists_has_sum_smul_of_apply_eq_zero (hs : HasSum (fun m => z ^ m • a m) s)
    (ha : ∀ k < n, a k = 0) : ∃ t : E, z ^ n • t = s ∧ HasSum (fun m => z ^ m • a (m + n)) t :=
  by
  obtain rfl | hn := n.eq_zero_or_pos
  · simpa
  by_cases h : z = 0
  · have : s = 0 := hs.unique (by simpa [ha 0 hn, h] using has_sum_at_zero a)
    exact ⟨a n, by simp [h, hn, this], by simpa [h] using has_sum_at_zero fun m => a (m + n)⟩
  · refine' ⟨(z ^ n)⁻¹ • s, by field_simp [smul_smul] , _⟩
    have h1 : (∑ i in Finset.range n, z ^ i • a i) = 0 :=
      Finset.sum_eq_zero fun k hk => by simp [ha k (finset.mem_range.mp hk)]
    have h2 : HasSum (fun m => z ^ (m + n) • a (m + n)) s := by
      simpa [h1] using (has_sum_nat_add_iff' n).mpr hs
    convert @HasSum.const_smul E ℕ 𝕜 _ _ _ _ _ _ _ (z⁻¹ ^ n) h2
    · field_simp [pow_add, smul_smul]
    · simp only [inv_pow]
#align has_sum.exists_has_sum_smul_of_apply_eq_zero HasSum.exists_has_sum_smul_of_apply_eq_zero

end HasSum

namespace HasFpowerSeriesAt

theorem hasFpowerSeriesDslopeFslope (hp : HasFpowerSeriesAt f p z₀) :
    HasFpowerSeriesAt (dslope f z₀) p.fslope z₀ :=
  by
  have hpd : deriv f z₀ = p.coeff 1 := hp.deriv
  have hp0 : p.coeff 0 = f z₀ := hp.coeff_zero 1
  simp only [has_fpower_series_at_iff, apply_eq_pow_smul_coeff, coeff_fslope] at hp⊢
  refine' hp.mono fun x hx => _
  by_cases h : x = 0
  · convert has_sum_single 0 _ <;> intros <;> simp [*]
  · have hxx : ∀ n : ℕ, x⁻¹ * x ^ (n + 1) = x ^ n := fun n => by field_simp [h, pow_succ']
    suffices HasSum (fun n => x⁻¹ • x ^ (n + 1) • p.coeff (n + 1)) (x⁻¹ • (f (z₀ + x) - f z₀)) by
      simpa [dslope, slope, h, smul_smul, hxx] using this
    · simpa [hp0] using ((has_sum_nat_add_iff' 1).mpr hx).const_smul
#align
  has_fpower_series_at.has_fpower_series_dslope_fslope HasFpowerSeriesAt.hasFpowerSeriesDslopeFslope

theorem hasFpowerSeriesIterateDslopeFslope (n : ℕ) (hp : HasFpowerSeriesAt f p z₀) :
    HasFpowerSeriesAt ((swap dslope z₀^[n]) f) ((fslope^[n]) p) z₀ :=
  by
  induction' n with n ih generalizing f p
  · exact hp
  · simpa using ih (has_fpower_series_dslope_fslope hp)
#align
  has_fpower_series_at.has_fpower_series_iterate_dslope_fslope HasFpowerSeriesAt.hasFpowerSeriesIterateDslopeFslope

theorem iterate_dslope_fslope_ne_zero (hp : HasFpowerSeriesAt f p z₀) (h : p ≠ 0) :
    (swap dslope z₀^[p.order]) f z₀ ≠ 0 :=
  by
  rw [← coeff_zero (has_fpower_series_iterate_dslope_fslope p.order hp) 1]
  simpa [coeff_eq_zero] using apply_order_ne_zero h
#align
  has_fpower_series_at.iterate_dslope_fslope_ne_zero HasFpowerSeriesAt.iterate_dslope_fslope_ne_zero

theorem eq_pow_order_mul_iterate_dslope (hp : HasFpowerSeriesAt f p z₀) :
    ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ p.order • (swap dslope z₀^[p.order]) f z :=
  by
  have hq := has_fpower_series_at_iff'.mp (has_fpower_series_iterate_dslope_fslope p.order hp)
  filter_upwards [hq, has_fpower_series_at_iff'.mp hp] with x hx1 hx2
  have : ∀ k < p.order, p.coeff k = 0 := fun k hk => by
    simpa [coeff_eq_zero] using apply_eq_zero_of_lt_order hk
  obtain ⟨s, hs1, hs2⟩ := HasSum.exists_has_sum_smul_of_apply_eq_zero hx2 this
  convert hs1.symm
  simp only [coeff_iterate_fslope] at hx1
  exact hx1.unique hs2
#align
  has_fpower_series_at.eq_pow_order_mul_iterate_dslope HasFpowerSeriesAt.eq_pow_order_mul_iterate_dslope

theorem locally_ne_zero (hp : HasFpowerSeriesAt f p z₀) (h : p ≠ 0) : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 :=
  by
  rw [eventually_nhds_within_iff]
  have h2 := (has_fpower_series_iterate_dslope_fslope p.order hp).ContinuousAt
  have h3 := h2.eventually_ne (iterate_dslope_fslope_ne_zero hp h)
  filter_upwards [eq_pow_order_mul_iterate_dslope hp, h3] with z e1 e2 e3
  simpa [e1, e2, e3] using pow_ne_zero p.order (sub_ne_zero.mpr e3)
#align has_fpower_series_at.locally_ne_zero HasFpowerSeriesAt.locally_ne_zero

theorem locally_zero_iff (hp : HasFpowerSeriesAt f p z₀) : (∀ᶠ z in 𝓝 z₀, f z = 0) ↔ p = 0 :=
  ⟨fun hf => hp.eq_zero_of_eventually hf, fun h => eventually_eq_zero (by rwa [h] at hp)⟩
#align has_fpower_series_at.locally_zero_iff HasFpowerSeriesAt.locally_zero_iff

end HasFpowerSeriesAt

namespace AnalyticAt

/-- The *principle of isolated zeros* for an analytic function, local version: if a function is
analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
vanish in a punctured neighborhood of `z₀`. -/
theorem eventually_eq_zero_or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = 0) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 :=
  by
  rcases hf with ⟨p, hp⟩
  by_cases h : p = 0
  · exact Or.inl (HasFpowerSeriesAt.eventually_eq_zero (by rwa [h] at hp))
  · exact Or.inr (hp.locally_ne_zero h)
#align
  analytic_at.eventually_eq_zero_or_eventually_ne_zero AnalyticAt.eventually_eq_zero_or_eventually_ne_zero

theorem eventually_eq_or_eventually_ne (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = g z) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ g z := by
  simpa [sub_eq_zero] using (hf.sub hg).eventually_eq_zero_or_eventually_ne_zero
#align analytic_at.eventually_eq_or_eventually_ne AnalyticAt.eventually_eq_or_eventually_ne

theorem frequently_zero_iff_eventually_zero {f : 𝕜 → E} {w : 𝕜} (hf : AnalyticAt 𝕜 f w) :
    (∃ᶠ z in 𝓝[≠] w, f z = 0) ↔ ∀ᶠ z in 𝓝 w, f z = 0 :=
  ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h =>
    (h.filter_mono nhds_within_le_nhds).Frequently⟩
#align
  analytic_at.frequently_zero_iff_eventually_zero AnalyticAt.frequently_zero_iff_eventually_zero

theorem frequently_eq_iff_eventually_eq (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (∃ᶠ z in 𝓝[≠] z₀, f z = g z) ↔ ∀ᶠ z in 𝓝 z₀, f z = g z := by
  simpa [sub_eq_zero] using frequently_zero_iff_eventually_zero (hf.sub hg)
#align analytic_at.frequently_eq_iff_eventually_eq AnalyticAt.frequently_eq_iff_eventually_eq

end AnalyticAt

namespace AnalyticOn

variable {U : Set 𝕜}

/-- The *principle of isolated zeros* for an analytic function, global version: if a function is
analytic on a connected set `U` and vanishes in arbitrary neighborhoods of a point `z₀ ∈ U`, then
it is identically zero in `U`.
For higher-dimensional versions requiring that the function vanishes in a neighborhood of `z₀`,
see `eq_on_zero_of_preconnected_of_eventually_eq_zero`. -/
theorem eq_on_zero_of_preconnected_of_frequently_eq_zero (hf : AnalyticOn 𝕜 f U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfw : ∃ᶠ z in 𝓝[≠] z₀, f z = 0) : EqOn f 0 U :=
  hf.eq_on_zero_of_preconnected_of_eventually_eq_zero hU h₀
    ((hf z₀ h₀).frequently_zero_iff_eventually_zero.1 hfw)
#align
  analytic_on.eq_on_zero_of_preconnected_of_frequently_eq_zero AnalyticOn.eq_on_zero_of_preconnected_of_frequently_eq_zero

theorem eq_on_zero_of_preconnected_of_mem_closure (hf : AnalyticOn 𝕜 f U) (hU : IsPreconnected U)
    (h₀ : z₀ ∈ U) (hfz₀ : z₀ ∈ closure ({ z | f z = 0 } \ {z₀})) : EqOn f 0 U :=
  hf.eq_on_zero_of_preconnected_of_frequently_eq_zero hU h₀
    (mem_closure_ne_iff_frequently_within.mp hfz₀)
#align
  analytic_on.eq_on_zero_of_preconnected_of_mem_closure AnalyticOn.eq_on_zero_of_preconnected_of_mem_closure

/-- The *identity principle* for analytic functions, global version: if two functions are
analytic on a connected set `U` and coincide at points which accumulate to a point `z₀ ∈ U`, then
they coincide globally in `U`.
For higher-dimensional versions requiring that the functions coincide in a neighborhood of `z₀`,
see `eq_on_of_preconnected_of_eventually_eq`. -/
theorem eq_on_of_preconnected_of_frequently_eq (hf : AnalyticOn 𝕜 f U) (hg : AnalyticOn 𝕜 g U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : EqOn f g U :=
  by
  have hfg' : ∃ᶠ z in 𝓝[≠] z₀, (f - g) z = 0 :=
    hfg.mono fun z h => by rw [Pi.sub_apply, h, sub_self]
  simpa [sub_eq_zero] using fun z hz =>
    (hf.sub hg).eq_on_zero_of_preconnected_of_frequently_eq_zero hU h₀ hfg' hz
#align
  analytic_on.eq_on_of_preconnected_of_frequently_eq AnalyticOn.eq_on_of_preconnected_of_frequently_eq

theorem eq_on_of_preconnected_of_mem_closure (hf : AnalyticOn 𝕜 f U) (hg : AnalyticOn 𝕜 g U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfg : z₀ ∈ closure ({ z | f z = g z } \ {z₀})) :
    EqOn f g U :=
  hf.eq_on_of_preconnected_of_frequently_eq hg hU h₀ (mem_closure_ne_iff_frequently_within.mp hfg)
#align
  analytic_on.eq_on_of_preconnected_of_mem_closure AnalyticOn.eq_on_of_preconnected_of_mem_closure

end AnalyticOn

