/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.function.l2_space
! leanprover-community/mathlib commit 3f655f5297b030a87d641ad4e825af8d9679eb0b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.MeasureTheory.Integral.SetIntegral

/-! # `L^2` space

If `E` is an inner product space over `𝕜` (`ℝ` or `ℂ`), then `Lp E 2 μ` (defined in `lp_space.lean`)
is also an inner product space, with inner product defined as `inner f g = ∫ a, ⟪f a, g a⟫ ∂μ`.

### Main results

* `mem_L1_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `λ x, ⟪f x, g x⟫`
  belongs to `Lp 𝕜 1 μ`.
* `integrable_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `λ x, ⟪f x, g x⟫`
  is integrable.
* `L2.inner_product_space` : `Lp E 2 μ` is an inner product space.

-/


noncomputable section

open TopologicalSpace MeasureTheory MeasureTheory.lp

open NNReal ENNReal MeasureTheory

namespace MeasureTheory

section

variable {α F : Type _} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup F]

theorem Memℒp.integrable_sq {f : α → ℝ} (h : Memℒp f 2 μ) : Integrable (fun x => f x ^ 2) μ := by
  simpa [← mem_ℒp_one_iff_integrable] using h.norm_rpow two_ne_zero ENNReal.two_ne_top
#align measure_theory.mem_ℒp.integrable_sq MeasureTheory.Memℒp.integrable_sq

theorem memℒp_two_iff_integrable_sq_norm {f : α → F} (hf : AeStronglyMeasurable f μ) :
    Memℒp f 2 μ ↔ Integrable (fun x => ‖f x‖ ^ 2) μ :=
  by
  rw [← mem_ℒp_one_iff_integrable]
  convert(mem_ℒp_norm_rpow_iff hf two_ne_zero ENNReal.two_ne_top).symm
  · simp
  · rw [div_eq_mul_inv, ENNReal.mul_inv_cancel two_ne_zero ENNReal.two_ne_top]
#align measure_theory.mem_ℒp_two_iff_integrable_sq_norm MeasureTheory.memℒp_two_iff_integrable_sq_norm

theorem memℒp_two_iff_integrable_sq {f : α → ℝ} (hf : AeStronglyMeasurable f μ) :
    Memℒp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ :=
  by
  convert mem_ℒp_two_iff_integrable_sq_norm hf
  ext x
  simp
#align measure_theory.mem_ℒp_two_iff_integrable_sq MeasureTheory.memℒp_two_iff_integrable_sq

end

namespace L2

variable {α E F 𝕜 : Type _} [IsROrC 𝕜] [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

theorem snorm_rpow_two_norm_lt_top (f : lp F 2 μ) : snorm (fun x => ‖f x‖ ^ (2 : ℝ)) 1 μ < ∞ :=
  by
  have h_two : ENNReal.ofReal (2 : ℝ) = 2 := by simp [zero_le_one]
  rw [snorm_norm_rpow f zero_lt_two, one_mul, h_two]
  exact ENNReal.rpow_lt_top_of_nonneg zero_le_two (Lp.snorm_ne_top f)
#align measure_theory.L2.snorm_rpow_two_norm_lt_top MeasureTheory.L2.snorm_rpow_two_norm_lt_top

theorem snorm_inner_lt_top (f g : α →₂[μ] E) : snorm (fun x : α => ⟪f x, g x⟫) 1 μ < ∞ :=
  by
  have h : ∀ x, ‖⟪f x, g x⟫‖ ≤ ‖‖f x‖ ^ (2 : ℝ) + ‖g x‖ ^ (2 : ℝ)‖ :=
    by
    intro x
    rw [← @Nat.cast_two ℝ, Real.rpow_nat_cast, Real.rpow_nat_cast]
    calc
      ‖⟪f x, g x⟫‖ ≤ ‖f x‖ * ‖g x‖ := norm_inner_le_norm _ _
      _ ≤ 2 * ‖f x‖ * ‖g x‖ :=
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (norm_nonneg _) one_le_two)
          (norm_nonneg _))
      _ ≤ ‖‖f x‖ ^ 2 + ‖g x‖ ^ 2‖ := (two_mul_le_add_sq _ _).trans (le_abs_self _)
      
  refine' (snorm_mono_ae (ae_of_all _ h)).trans_lt ((snorm_add_le _ _ le_rfl).trans_lt _)
  · exact ((Lp.ae_strongly_measurable f).norm.AEMeasurable.pow_const _).AeStronglyMeasurable
  · exact ((Lp.ae_strongly_measurable g).norm.AEMeasurable.pow_const _).AeStronglyMeasurable
  rw [ENNReal.add_lt_top]
  exact ⟨snorm_rpow_two_norm_lt_top f, snorm_rpow_two_norm_lt_top g⟩
#align measure_theory.L2.snorm_inner_lt_top MeasureTheory.L2.snorm_inner_lt_top

section InnerProductSpace

open ComplexConjugate

include 𝕜

instance : HasInner 𝕜 (α →₂[μ] E) :=
  ⟨fun f g => ∫ a, ⟪f a, g a⟫ ∂μ⟩

theorem inner_def (f g : α →₂[μ] E) : ⟪f, g⟫ = ∫ a : α, ⟪f a, g a⟫ ∂μ :=
  rfl
#align measure_theory.L2.inner_def MeasureTheory.L2.inner_def

theorem integral_inner_eq_sq_snorm (f : α →₂[μ] E) :
    (∫ a, ⟪f a, f a⟫ ∂μ) = ENNReal.toReal (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂μ) :=
  by
  simp_rw [inner_self_eq_norm_sq_to_K]
  norm_cast
  rw [integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Filter.eventually_of_forall fun x => sq_nonneg _
  · exact ((Lp.ae_strongly_measurable f).norm.AEMeasurable.pow_const _).AeStronglyMeasurable
  congr
  ext1 x
  have h_two : (2 : ℝ) = ((2 : ℕ) : ℝ) := by simp
  rw [← Real.rpow_nat_cast _ 2, ← h_two, ←
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two, ofReal_norm_eq_coe_nnnorm]
  norm_cast
#align measure_theory.L2.integral_inner_eq_sq_snorm MeasureTheory.L2.integral_inner_eq_sq_snorm

private theorem norm_sq_eq_inner' (f : α →₂[μ] E) : ‖f‖ ^ 2 = IsROrC.re ⟪f, f⟫ :=
  by
  have h_two : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [inner_def, integral_inner_eq_sq_snorm, norm_def, ← ENNReal.toReal_pow, IsROrC.of_real_re,
    ENNReal.toReal_eq_toReal (ENNReal.pow_ne_top (Lp.snorm_ne_top f)) _]
  · rw [← ENNReal.rpow_nat_cast, snorm_eq_snorm' two_ne_zero ENNReal.two_ne_top, snorm', ←
      ENNReal.rpow_mul, one_div, h_two]
    simp
  · refine' (lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top zero_lt_two _).Ne
    rw [← h_two, ← snorm_eq_snorm' two_ne_zero ENNReal.two_ne_top]
    exact Lp.snorm_lt_top f
#align measure_theory.L2.norm_sq_eq_inner' measure_theory.L2.norm_sq_eq_inner'

theorem mem_L1_inner (f g : α →₂[μ] E) :
    AeEqFun.mk (fun x => ⟪f x, g x⟫)
        ((lp.aeStronglyMeasurable f).inner (lp.aeStronglyMeasurable g)) ∈
      lp 𝕜 1 μ :=
  by
  simp_rw [mem_Lp_iff_snorm_lt_top, snorm_ae_eq_fun]
  exact snorm_inner_lt_top f g
#align measure_theory.L2.mem_L1_inner MeasureTheory.L2.mem_L1_inner

theorem integrable_inner (f g : α →₂[μ] E) : Integrable (fun x : α => ⟪f x, g x⟫) μ :=
  (integrable_congr
        (AeEqFun.coeFn_mk (fun x => ⟪f x, g x⟫)
          ((lp.aeStronglyMeasurable f).inner (lp.aeStronglyMeasurable g)))).mp
    (AeEqFun.integrable_iff_mem_L1.mpr (mem_L1_inner f g))
#align measure_theory.L2.integrable_inner MeasureTheory.L2.integrable_inner

private theorem add_left' (f f' g : α →₂[μ] E) : ⟪f + f', g⟫ = inner f g + inner f' g :=
  by
  simp_rw [inner_def, ← integral_add (integrable_inner f g) (integrable_inner f' g), ←
    inner_add_left]
  refine' integral_congr_ae ((coe_fn_add f f').mono fun x hx => _)
  congr
  rwa [Pi.add_apply] at hx
#align measure_theory.L2.add_left' measure_theory.L2.add_left'

private theorem smul_left' (f g : α →₂[μ] E) (r : 𝕜) : ⟪r • f, g⟫ = conj r * inner f g :=
  by
  rw [inner_def, inner_def, ← smul_eq_mul, ← integral_smul]
  refine' integral_congr_ae ((coe_fn_smul r f).mono fun x hx => _)
  rw [smul_eq_mul, ← inner_smul_left]
  congr
  rwa [Pi.smul_apply] at hx
#align measure_theory.L2.smul_left' measure_theory.L2.smul_left'

instance innerProductSpace : InnerProductSpace 𝕜 (α →₂[μ] E)
    where
  norm_sq_eq_inner := norm_sq_eq_inner'
  conj_symm _ _ := by simp_rw [inner_def, ← integral_conj, inner_conj_symm]
  add_left := add_left'
  smul_left := smul_left'
#align measure_theory.L2.inner_product_space MeasureTheory.L2.innerProductSpace

end InnerProductSpace

section IndicatorConstLp

variable (𝕜) {s : Set α}

/-- The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs c` and `f` is
equal to the integral of the inner product over `s`: `∫ x in s, ⟪c, f x⟫ ∂μ`. -/
theorem inner_indicatorConstLp_eq_set_integral_inner (f : lp E 2 μ) (hs : MeasurableSet s) (c : E)
    (hμs : μ s ≠ ∞) : (⟪indicatorConstLp 2 hs hμs c, f⟫ : 𝕜) = ∫ x in s, ⟪c, f x⟫ ∂μ :=
  by
  rw [inner_def, ← integral_add_compl hs (L2.integrable_inner _ f)]
  have h_left : (∫ x in s, ⟪(indicator_const_Lp 2 hs hμs c) x, f x⟫ ∂μ) = ∫ x in s, ⟪c, f x⟫ ∂μ :=
    by
    suffices h_ae_eq : ∀ᵐ x ∂μ, x ∈ s → ⟪indicator_const_Lp 2 hs hμs c x, f x⟫ = ⟪c, f x⟫
    exact set_integral_congr_ae hs h_ae_eq
    have h_indicator : ∀ᵐ x : α ∂μ, x ∈ s → indicator_const_Lp 2 hs hμs c x = c :=
      indicator_const_Lp_coe_fn_mem
    refine' h_indicator.mono fun x hx hxs => _
    congr
    exact hx hxs
  have h_right : (∫ x in sᶜ, ⟪(indicator_const_Lp 2 hs hμs c) x, f x⟫ ∂μ) = 0 :=
    by
    suffices h_ae_eq : ∀ᵐ x ∂μ, x ∉ s → ⟪indicator_const_Lp 2 hs hμs c x, f x⟫ = 0
    · simp_rw [← Set.mem_compl_iff] at h_ae_eq
      suffices h_int_zero :
        (∫ x in sᶜ, inner (indicator_const_Lp 2 hs hμs c x) (f x) ∂μ) = ∫ x in sᶜ, (0 : 𝕜) ∂μ
      · rw [h_int_zero]
        simp
      exact set_integral_congr_ae hs.compl h_ae_eq
    have h_indicator : ∀ᵐ x : α ∂μ, x ∉ s → indicator_const_Lp 2 hs hμs c x = 0 :=
      indicator_const_Lp_coe_fn_nmem
    refine' h_indicator.mono fun x hx hxs => _
    rw [hx hxs]
    exact inner_zero_left _
  rw [h_left, h_right, add_zero]
#align measure_theory.L2.inner_indicator_const_Lp_eq_set_integral_inner MeasureTheory.L2.inner_indicatorConstLp_eq_set_integral_inner

/-- The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs c` and `f` is
equal to the inner product of the constant `c` and the integral of `f` over `s`. -/
theorem inner_indicatorConstLp_eq_inner_set_integral [CompleteSpace E] [NormedSpace ℝ E]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) (f : lp E 2 μ) :
    (⟪indicatorConstLp 2 hs hμs c, f⟫ : 𝕜) = ⟪c, ∫ x in s, f x ∂μ⟫ := by
  rw [← integral_inner (integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs),
    L2.inner_indicator_const_Lp_eq_set_integral_inner]
#align measure_theory.L2.inner_indicator_const_Lp_eq_inner_set_integral MeasureTheory.L2.inner_indicatorConstLp_eq_inner_set_integral

variable {𝕜}

/-- The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs (1 : 𝕜)` and
a real or complex function `f` is equal to the integral of `f` over `s`. -/
theorem inner_indicatorConstLp_one (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (f : lp 𝕜 2 μ) :
    ⟪indicatorConstLp 2 hs hμs (1 : 𝕜), f⟫ = ∫ x in s, f x ∂μ :=
  by
  rw [L2.inner_indicator_const_Lp_eq_inner_set_integral 𝕜 hs hμs (1 : 𝕜) f]
  simp
#align measure_theory.L2.inner_indicator_const_Lp_one MeasureTheory.L2.inner_indicatorConstLp_one

end IndicatorConstLp

end L2

section InnerContinuous

variable {α : Type _} [TopologicalSpace α] [MeasureSpace α] [BorelSpace α] {𝕜 : Type _} [IsROrC 𝕜]

variable (μ : Measure α) [IsFiniteMeasure μ]

open BoundedContinuousFunction ComplexConjugate

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 (α →₂[μ] 𝕜) _ x y

/-- For bounded continuous functions `f`, `g` on a finite-measure topological space `α`, the L^2
inner product is the integral of their pointwise inner product. -/
theorem BoundedContinuousFunction.inner_toLp (f g : α →ᵇ 𝕜) :
    ⟪BoundedContinuousFunction.toLp 2 μ 𝕜 f, BoundedContinuousFunction.toLp 2 μ 𝕜 g⟫ =
      ∫ x, conj (f x) * g x ∂μ :=
  by
  apply integral_congr_ae
  have hf_ae := f.coe_fn_to_Lp 2 μ 𝕜
  have hg_ae := g.coe_fn_to_Lp 2 μ 𝕜
  filter_upwards [hf_ae, hg_ae]with _ hf hg
  rw [hf, hg]
  simp
#align measure_theory.bounded_continuous_function.inner_to_Lp MeasureTheory.BoundedContinuousFunction.inner_toLp

variable [CompactSpace α]

/-- For continuous functions `f`, `g` on a compact, finite-measure topological space `α`, the L^2
inner product is the integral of their pointwise inner product. -/
theorem ContinuousMap.inner_toLp (f g : C(α, 𝕜)) :
    ⟪ContinuousMap.toLp 2 μ 𝕜 f, ContinuousMap.toLp 2 μ 𝕜 g⟫ = ∫ x, conj (f x) * g x ∂μ :=
  by
  apply integral_congr_ae
  have hf_ae := f.coe_fn_to_Lp μ
  have hg_ae := g.coe_fn_to_Lp μ
  filter_upwards [hf_ae, hg_ae]with _ hf hg
  rw [hf, hg]
  simp
#align measure_theory.continuous_map.inner_to_Lp MeasureTheory.ContinuousMap.inner_toLp

end InnerContinuous

end MeasureTheory

