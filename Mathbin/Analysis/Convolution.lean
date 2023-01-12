/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module analysis.convolution
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Group.Integration
import Mathbin.MeasureTheory.Group.Prod
import Mathbin.MeasureTheory.Function.LocallyIntegrable
import Mathbin.Analysis.Calculus.SpecificFunctions
import Mathbin.Analysis.Calculus.ParametricIntegral

/-!
# Convolution of functions

This file defines the convolution on two functions, i.e. `x ↦ ∫ f(t)g(x - t) ∂t`.
In the general case, these functions can be vector-valued, and have an arbitrary (additive)
group as domain. We use a continuous bilinear operation `L` on these function values as
"multiplication". The domain must be equipped with a Haar measure `μ`
(though many individual results have weaker conditions on `μ`).

For many applications we can take `L = lsmul ℝ ℝ` or `L = mul ℝ ℝ`.

We also define `convolution_exists` and `convolution_exists_at` to state that the convolution is
well-defined (everywhere or at a single point). These conditions are needed for pointwise
computations (e.g. `convolution_exists_at.distrib_add`), but are generally not stong enough for any
local (or global) properties of the convolution. For this we need stronger assumptions on `f`
and/or `g`, and generally if we impose stronger conditions on one of the functions, we can impose
weaker conditions on the other.
We have proven many of the properties of the convolution assuming one of these functions
has compact support (in which case the other function only needs to be locally integrable).
We still need to prove the properties for other pairs of conditions (e.g. both functions are
rapidly decreasing)

# Design Decisions

We use a bilinear map `L` to "multiply" the two functions in the integrand.
This generality has several advantages

* This allows us to compute the total derivative of the convolution, in case the functions are
  multivariate. The total derivative is again a convolution, but where the codomains of the
  functions can be higher-dimensional. See `has_compact_support.has_fderiv_at_convolution_right`.
* This allows us to use `@[to_additive]` everywhere (which would not be possible if we would use
  `mul`/`smul` in the integral, since `@[to_additive]` will incorrectly also try to additivize
  those definitions).
* We need to support the case where at least one of the functions is vector-valued, but if we use
  `smul` to multiply the functions, that would be an asymmetric definition.

# Main Definitions
* `convolution f g L μ x = (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ` is the convolution of
  `f` and `g` w.r.t. the continuous bilinear map `L` and measure `μ`.
* `convolution_exists_at f g x L μ` states that the convolution `(f ⋆[L, μ] g) x` is well-defined
  (i.e. the integral exists).
* `convolution_exists f g L μ` states that the convolution `f ⋆[L, μ] g` is well-defined at each
  point.

# Main Results
* `has_compact_support.has_fderiv_at_convolution_right` and
  `has_compact_support.has_fderiv_at_convolution_left`: we can compute the total derivative
  of the convolution as a convolution with the total derivative of the right (left) function.
* `has_compact_support.cont_diff_convolution_right` and
  `has_compact_support.cont_diff_convolution_left`: the convolution is `𝒞ⁿ` if one of the functions
  is `𝒞ⁿ` with compact support and the other function in locally integrable.

Versions of these statements for functions depending on a parameter are also given.

* `convolution_tendsto_right`: Given a sequence of nonnegative normalized functions whose support
  tends to a small neighborhood around `0`, the convolution tends to the right argument.
  This is specialized to bump functions in `cont_diff_bump_of_inner.convolution_tendsto_right`.

# Notation
The following notations are localized in the locale `convolution`:
* `f ⋆[L, μ] g` for the convolution. Note: you have to use parentheses to apply the convolution
  to an argument: `(f ⋆[L, μ] g) x`.
* `f ⋆[L] g := f ⋆[L, volume] g`
* `f ⋆ g := f ⋆[lsmul ℝ ℝ] g`

# To do
* Existence and (uniform) continuity of the convolution if
  one of the maps is in `ℒ^p` and the other in `ℒ^q` with `1 / p + 1 / q = 1`.
  This might require a generalization of `measure_theory.mem_ℒp.smul` where `smul` is generalized
  to a continuous bilinear map.
  (see e.g. [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2], 255K)
* The convolution is a `ae_strongly_measurable` function
  (see e.g. [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2], 255I).
* Prove properties about the convolution if both functions are rapidly decreasing.
* Use `@[to_additive]` everywhere
-/


open Set Function Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

open ContinuousLinearMap Metric

open Pointwise TopologicalSpace Nnreal Filter

universe u𝕜 uG uE uE' uE'' uF uF' uF'' uP

variable {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {E'' : Type uE''} {F : Type uF}
  {F' : Type uF'} {F'' : Type uF''} {P : Type uP}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup E'']
  [NormedAddCommGroup F] {f f' : G → E} {g g' : G → E'} {x x' : G} {y y' : E}

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E''] [NormedSpace 𝕜 F]

variable (L : E →L[𝕜] E' →L[𝕜] F)

section NoMeasurability

variable [AddGroup G] [TopologicalSpace G]

theorem convolution_integrand_bound_right_of_le_of_subset {C : ℝ} (hC : ∀ i, ‖g i‖ ≤ C) {x t : G}
    {s u : Set G} (hx : x ∈ s) (hu : -tsupport g + s ⊆ u) :
    ‖L (f t) (g (x - t))‖ ≤ u.indicator (fun t => ‖L‖ * ‖f t‖ * C) t :=
  by
  refine' le_indicator (fun t ht => _) (fun t ht => _) t
  · refine' (L.le_op_norm₂ _ _).trans _
    apply mul_le_mul_of_nonneg_left (hC _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · have : x - t ∉ support g := by
      refine' mt (fun hxt => _) ht
      apply hu
      refine' ⟨_, _, set.neg_mem_neg.mpr (subset_closure hxt), hx, _⟩
      rw [neg_sub, sub_add_cancel]
    rw [nmem_support.mp this, (L _).map_zero, norm_zero]
#align
  convolution_integrand_bound_right_of_le_of_subset convolution_integrand_bound_right_of_le_of_subset

theorem HasCompactSupport.convolution_integrand_bound_right_of_subset (hcg : HasCompactSupport g)
    (hg : Continuous g) {x t : G} {s u : Set G} (hx : x ∈ s) (hu : -tsupport g + s ⊆ u) :
    ‖L (f t) (g (x - t))‖ ≤ u.indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖) t :=
  by
  apply convolution_integrand_bound_right_of_le_of_subset _ (fun i => _) hx hu
  exact le_csupᵢ (hg.norm.bdd_above_range_of_has_compact_support hcg.norm) _
#align
  has_compact_support.convolution_integrand_bound_right_of_subset HasCompactSupport.convolution_integrand_bound_right_of_subset

theorem HasCompactSupport.convolution_integrand_bound_right (hcg : HasCompactSupport g)
    (hg : Continuous g) {x t : G} {s : Set G} (hx : x ∈ s) :
    ‖L (f t) (g (x - t))‖ ≤ (-tsupport g + s).indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖) t :=
  hcg.convolution_integrand_bound_right_of_subset L hg hx Subset.rfl
#align
  has_compact_support.convolution_integrand_bound_right HasCompactSupport.convolution_integrand_bound_right

theorem Continuous.convolution_integrand_fst [HasContinuousSub G] (hg : Continuous g) (t : G) :
    Continuous fun x => L (f t) (g (x - t)) :=
  L.continuous₂.comp₂ continuous_const <| hg.comp <| continuous_id.sub continuous_const
#align continuous.convolution_integrand_fst Continuous.convolution_integrand_fst

theorem HasCompactSupport.convolution_integrand_bound_left (hcf : HasCompactSupport f)
    (hf : Continuous f) {x t : G} {s : Set G} (hx : x ∈ s) :
    ‖L (f (x - t)) (g t)‖ ≤ (-tsupport f + s).indicator (fun t => (‖L‖ * ⨆ i, ‖f i‖) * ‖g t‖) t :=
  by
  convert hcf.convolution_integrand_bound_right L.flip hf hx
  simp_rw [L.op_norm_flip, mul_right_comm]
#align
  has_compact_support.convolution_integrand_bound_left HasCompactSupport.convolution_integrand_bound_left

end NoMeasurability

section Measurability

variable [MeasurableSpace G] {μ ν : Measure G}

/-- The convolution of `f` and `g` exists at `x` when the function `t ↦ L (f t) (g (x - t))` is
integrable. There are various conditions on `f` and `g` to prove this. -/
def ConvolutionExistsAt [Sub G] (f : G → E) (g : G → E') (x : G) (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  Integrable (fun t => L (f t) (g (x - t))) μ
#align convolution_exists_at ConvolutionExistsAt

/-- The convolution of `f` and `g` exists when the function `t ↦ L (f t) (g (x - t))` is integrable
for all `x : G`. There are various conditions on `f` and `g` to prove this. -/
def ConvolutionExists [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  ∀ x : G, ConvolutionExistsAt f g x L μ
#align convolution_exists ConvolutionExists

section ConvolutionExists

variable {L}

theorem ConvolutionExistsAt.integrable [Sub G] {x : G} (h : ConvolutionExistsAt f g x L μ) :
    Integrable (fun t => L (f t) (g (x - t))) μ :=
  h
#align convolution_exists_at.integrable ConvolutionExistsAt.integrable

variable (L)

section Group

variable [AddGroup G]

theorem MeasureTheory.AeStronglyMeasurable.convolutionIntegrand' [HasMeasurableAdd₂ G]
    [HasMeasurableNeg G] [SigmaFinite ν] (hf : AeStronglyMeasurable f ν)
    (hg : AeStronglyMeasurable g <| map (fun p : G × G => p.1 - p.2) (μ.Prod ν)) :
    AeStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.Prod ν) :=
  L.aeStronglyMeasurableComp₂ hf.snd <| hg.compMeasurable measurable_sub
#align
  measure_theory.ae_strongly_measurable.convolution_integrand' MeasureTheory.AeStronglyMeasurable.convolutionIntegrand'

section

variable [HasMeasurableAdd G] [HasMeasurableNeg G]

theorem MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSnd' (hf : AeStronglyMeasurable f μ)
    {x : G} (hg : AeStronglyMeasurable g <| map (fun t => x - t) μ) :
    AeStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  L.aeStronglyMeasurableComp₂ hf <| hg.compMeasurable <| measurable_id.const_sub x
#align
  measure_theory.ae_strongly_measurable.convolution_integrand_snd' MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSnd'

theorem MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSwapSnd' {x : G}
    (hf : AeStronglyMeasurable f <| map (fun t => x - t) μ) (hg : AeStronglyMeasurable g μ) :
    AeStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  L.aeStronglyMeasurableComp₂ (hf.compMeasurable <| measurable_id.const_sub x) hg
#align
  measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd' MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSwapSnd'

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that `f` is integrable on a set `s` and `g` is bounded and ae strongly measurable
on `x₀ - s` (note that both properties hold if `g` is continuous with compact support). -/
theorem BddAbove.convolutionExistsAt' {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ‖g i‖) '' ((fun t => -t + x₀) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ)
    (hmg : AeStronglyMeasurable g <| map (fun t => x₀ - t) (μ.restrict s)) :
    ConvolutionExistsAt f g x₀ L μ :=
  by
  rw [ConvolutionExistsAt, ← integrable_on_iff_integrable_of_support_subset h2s hs]
  set s' := (fun t => -t + x₀) ⁻¹' s
  have :
    ∀ᵐ t : G ∂μ.restrict s,
      ‖L (f t) (g (x₀ - t))‖ ≤ s.indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i : s', ‖g i‖) t :=
    by
    refine' eventually_of_forall _
    refine' le_indicator (fun t ht => _) fun t ht => _
    · refine' (L.le_op_norm₂ _ _).trans _
      refine'
        mul_le_mul_of_nonneg_left (le_csupᵢ_set hbg <| mem_preimage.mpr _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      rwa [neg_sub, sub_add_cancel]
    · have : t ∉ support fun t => L (f t) (g (x₀ - t)) := mt (fun h => h2s h) ht
      rw [nmem_support.mp this, norm_zero]
  refine' integrable.mono' _ _ this
  · rw [integrable_indicator_iff hs]
    exact ((hf.norm.const_mul _).mul_const _).IntegrableOn
  · exact hf.ae_strongly_measurable.convolution_integrand_snd' L hmg
#align bdd_above.convolution_exists_at' BddAbove.convolutionExistsAt'

/-- If `‖f‖ *[μ] ‖g‖` exists, then `f *[L, μ] g` exists. -/
theorem ConvolutionExistsAt.ofNorm' {x₀ : G}
    (h : ConvolutionExistsAt (fun x => ‖f x‖) (fun x => ‖g x‖) x₀ (mul ℝ ℝ) μ)
    (hmf : AeStronglyMeasurable f μ) (hmg : AeStronglyMeasurable g <| map (fun t => x₀ - t) μ) :
    ConvolutionExistsAt f g x₀ L μ :=
  by
  refine'
    (h.const_mul ‖L‖).mono' (hmf.convolution_integrand_snd' L hmg) (eventually_of_forall fun x => _)
  rw [mul_apply', ← mul_assoc]
  apply L.le_op_norm₂
#align convolution_exists_at.of_norm' ConvolutionExistsAt.ofNorm'

end

section Left

variable [HasMeasurableAdd₂ G] [HasMeasurableNeg G] [SigmaFinite μ] [IsAddRightInvariant μ]

theorem MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSnd (hf : AeStronglyMeasurable f μ)
    (hg : AeStronglyMeasurable g μ) (x : G) :
    AeStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  hf.convolutionIntegrandSnd' L <|
    hg.mono' <| (quasiMeasurePreservingSubLeftOfRightInvariant μ x).AbsolutelyContinuous
#align
  measure_theory.ae_strongly_measurable.convolution_integrand_snd MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSnd

theorem MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSwapSnd
    (hf : AeStronglyMeasurable f μ) (hg : AeStronglyMeasurable g μ) (x : G) :
    AeStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  (hf.mono'
        (quasiMeasurePreservingSubLeftOfRightInvariant μ
            x).AbsolutelyContinuous).convolutionIntegrandSwapSnd'
    L hg
#align
  measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSwapSnd

/-- If `‖f‖ *[μ] ‖g‖` exists, then `f *[L, μ] g` exists. -/
theorem ConvolutionExistsAt.ofNorm {x₀ : G}
    (h : ConvolutionExistsAt (fun x => ‖f x‖) (fun x => ‖g x‖) x₀ (mul ℝ ℝ) μ)
    (hmf : AeStronglyMeasurable f μ) (hmg : AeStronglyMeasurable g μ) :
    ConvolutionExistsAt f g x₀ L μ :=
  h.ofNorm' L hmf <|
    hmg.mono' (quasiMeasurePreservingSubLeftOfRightInvariant μ x₀).AbsolutelyContinuous
#align convolution_exists_at.of_norm ConvolutionExistsAt.ofNorm

end Left

section Right

variable [HasMeasurableAdd₂ G] [HasMeasurableNeg G] [SigmaFinite μ] [IsAddRightInvariant μ]
  [SigmaFinite ν]

theorem MeasureTheory.AeStronglyMeasurable.convolutionIntegrand (hf : AeStronglyMeasurable f ν)
    (hg : AeStronglyMeasurable g μ) :
    AeStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.Prod ν) :=
  hf.convolutionIntegrand' L <|
    hg.mono' (quasiMeasurePreservingSubOfRightInvariant μ ν).AbsolutelyContinuous
#align
  measure_theory.ae_strongly_measurable.convolution_integrand MeasureTheory.AeStronglyMeasurable.convolutionIntegrand

theorem MeasureTheory.Integrable.convolutionIntegrand (hf : Integrable f ν) (hg : Integrable g μ) :
    Integrable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.Prod ν) :=
  by
  have h_meas : ae_strongly_measurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
    hf.ae_strongly_measurable.convolution_integrand L hg.ae_strongly_measurable
  have h2_meas : ae_strongly_measurable (fun y : G => ∫ x : G, ‖L (f y) (g (x - y))‖ ∂μ) ν :=
    h_meas.prod_swap.norm.integral_prod_right'
  simp_rw [integrable_prod_iff' h_meas]
  refine' ⟨eventually_of_forall fun t => (L (f t)).integrable_comp (hg.comp_sub_right t), _⟩
  refine'
    integrable.mono' _ h2_meas
      (eventually_of_forall fun t => (_ : _ ≤ ‖L‖ * ‖f t‖ * ∫ x, ‖g (x - t)‖ ∂μ))
  · simp_rw [integral_sub_right_eq_self fun t => ‖g t‖]
    exact (hf.norm.const_mul _).mul_const _
  · simp_rw [← integral_mul_left]
    rw [Real.norm_of_nonneg]
    ·
      exact
        integral_mono_of_nonneg (eventually_of_forall fun t => norm_nonneg _)
          ((hg.comp_sub_right t).norm.const_mul _) (eventually_of_forall fun t => L.le_op_norm₂ _ _)
    exact integral_nonneg fun x => norm_nonneg _
#align measure_theory.integrable.convolution_integrand MeasureTheory.Integrable.convolutionIntegrand

theorem MeasureTheory.Integrable.ae_convolution_exists (hf : Integrable f ν) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, ConvolutionExistsAt f g x L ν :=
  ((integrable_prod_iff <|
          hf.AeStronglyMeasurable.convolutionIntegrand L hg.AeStronglyMeasurable).mp <|
      hf.convolutionIntegrand L hg).1
#align
  measure_theory.integrable.ae_convolution_exists MeasureTheory.Integrable.ae_convolution_exists

end Right

variable [TopologicalSpace G] [TopologicalAddGroup G] [BorelSpace G]

theorem HasCompactSupport.convolutionExistsAt {x₀ : G}
    (h : HasCompactSupport fun t => L (f t) (g (x₀ - t))) (hf : LocallyIntegrable f μ)
    (hg : Continuous g) : ConvolutionExistsAt f g x₀ L μ :=
  by
  let u := (Homeomorph.neg G).trans (Homeomorph.addRight x₀)
  let v := (Homeomorph.neg G).trans (Homeomorph.addLeft x₀)
  apply
    ((u.is_compact_preimage.mpr h).bdd_above_image hg.norm.continuous_on).convolutionExistsAt' L
      is_closed_closure.measurable_set subset_closure (hf.integrable_on_is_compact h)
  have A :
    ae_strongly_measurable (g ∘ ⇑v) (μ.restrict (tsupport fun t : G => (L (f t)) (g (x₀ - t)))) :=
    by
    apply (hg.comp v.continuous).ContinuousOn.aeStronglyMeasurableOfIsCompact h
    exact (is_closed_tsupport _).MeasurableSet
  convert
    ((v.continuous.measurable.measure_preserving
              (μ.restrict (tsupport fun t => L (f t) (g (x₀ - t))))).ae_strongly_measurable_comp_iff
          v.to_measurable_equiv.measurable_embedding).1
      A
  ext x
  simp only [Homeomorph.neg, sub_eq_add_neg, coe_toAddUnits, Homeomorph.trans_apply,
    Equiv.neg_apply, Equiv.toFun_as_coe, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk,
    Homeomorph.coe_add_left]
#align has_compact_support.convolution_exists_at HasCompactSupport.convolutionExistsAt

theorem HasCompactSupport.convolutionExistsRight (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : ConvolutionExists f g L μ :=
  by
  intro x₀
  refine' HasCompactSupport.convolutionExistsAt L _ hf hg
  refine' (hcg.comp_homeomorph (Homeomorph.subLeft x₀)).mono _
  refine' fun t => mt fun ht : g (x₀ - t) = 0 => _
  simp_rw [ht, (L _).map_zero]
#align has_compact_support.convolution_exists_right HasCompactSupport.convolutionExistsRight

theorem HasCompactSupport.convolutionExistsLeftOfContinuousRight (hcf : HasCompactSupport f)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : ConvolutionExists f g L μ :=
  by
  intro x₀
  refine' HasCompactSupport.convolutionExistsAt L _ hf hg
  refine' hcf.mono _
  refine' fun t => mt fun ht : f t = 0 => _
  simp_rw [ht, L.map_zero₂]
#align
  has_compact_support.convolution_exists_left_of_continuous_right HasCompactSupport.convolutionExistsLeftOfContinuousRight

end Group

section CommGroup

variable [AddCommGroup G]

section MeasurableGroup

variable [HasMeasurableNeg G] [IsAddLeftInvariant μ]

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that the integrand has compact support and `g` is bounded on this support (note that
both properties hold if `g` is continuous with compact support). We also require that `f` is
integrable on the support of the integrand, and that both functions are strongly measurable.

This is a variant of `bdd_above.convolution_exists_at'` in an abelian group with a left-invariant
measure. This allows us to state the boundedness and measurability of `g` in a more natural way. -/
theorem BddAbove.convolutionExistsAt [HasMeasurableAdd₂ G] [SigmaFinite μ] {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ‖g i‖) '' ((fun t => x₀ - t) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ)
    (hmg : AeStronglyMeasurable g μ) : ConvolutionExistsAt f g x₀ L μ :=
  by
  refine' BddAbove.convolutionExistsAt' L _ hs h2s hf _
  · simp_rw [← sub_eq_neg_add, hbg]
  · have : ae_strongly_measurable g (map (fun t : G => x₀ - t) μ) :=
      hmg.mono' (quasi_measure_preserving_sub_left_of_right_invariant μ x₀).AbsolutelyContinuous
    apply this.mono_measure
    exact
      map_mono_of_ae_measurable restrict_le_self (measurable_const.sub measurable_id').AeMeasurable
#align bdd_above.convolution_exists_at BddAbove.convolutionExistsAt

variable {L} [HasMeasurableAdd G] [IsNegInvariant μ]

theorem convolution_exists_at_flip :
    ConvolutionExistsAt g f x L.flip μ ↔ ConvolutionExistsAt f g x L μ := by
  simp_rw [ConvolutionExistsAt, ← integrable_comp_sub_left (fun t => L (f t) (g (x - t))) x,
    sub_sub_cancel, flip_apply]
#align convolution_exists_at_flip convolution_exists_at_flip

theorem ConvolutionExistsAt.integrableSwap (h : ConvolutionExistsAt f g x L μ) :
    Integrable (fun t => L (f (x - t)) (g t)) μ :=
  by
  convert h.comp_sub_left x
  simp_rw [sub_sub_self]
#align convolution_exists_at.integrable_swap ConvolutionExistsAt.integrableSwap

theorem convolution_exists_at_iff_integrable_swap :
    ConvolutionExistsAt f g x L μ ↔ Integrable (fun t => L (f (x - t)) (g t)) μ :=
  convolution_exists_at_flip.symm
#align convolution_exists_at_iff_integrable_swap convolution_exists_at_iff_integrable_swap

end MeasurableGroup

variable [TopologicalSpace G] [TopologicalAddGroup G] [BorelSpace G] [IsAddLeftInvariant μ]
  [IsNegInvariant μ]

theorem HasCompactSupport.convolutionExistsLeft (hcf : HasCompactSupport f) (hf : Continuous f)
    (hg : LocallyIntegrable g μ) : ConvolutionExists f g L μ := fun x₀ =>
  convolution_exists_at_flip.mp <| hcf.convolutionExistsRight L.flip hg hf x₀
#align has_compact_support.convolution_exists_left HasCompactSupport.convolutionExistsLeft

theorem HasCompactSupport.convolutionExistsRightOfContinuousLeft (hcg : HasCompactSupport g)
    (hf : Continuous f) (hg : LocallyIntegrable g μ) : ConvolutionExists f g L μ := fun x₀ =>
  convolution_exists_at_flip.mp <| hcg.convolutionExistsLeftOfContinuousRight L.flip hg hf x₀
#align
  has_compact_support.convolution_exists_right_of_continuous_left HasCompactSupport.convolutionExistsRightOfContinuousLeft

end CommGroup

end ConvolutionExists

variable [NormedSpace ℝ F] [CompleteSpace F]

/-- The convolution of two functions `f` and `g` with respect to a continuous bilinear map `L` and
measure `μ`. It is defined to be `(f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ`. -/
noncomputable def convolution [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by exact MeasureTheory.MeasureSpace.volume) : G → F := fun x =>
  ∫ t, L (f t) (g (x - t)) ∂μ
#align convolution convolution

-- mathport name: convolution
scoped[convolution] notation:67 f " ⋆[" L:67 ", " μ:67 "] " g:66 => convolution f g L μ

-- mathport name: convolution.volume
scoped[convolution]
  notation:67 f " ⋆[" L:67 "]" g:66 => convolution f g L MeasureTheory.MeasureSpace.volume

-- mathport name: convolution.lsmul
scoped[convolution]
  notation:67 f " ⋆ " g:66 =>
    convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.MeasureSpace.volume

theorem convolution_def [Sub G] : (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ :=
  rfl
#align convolution_def convolution_def

/-- The definition of convolution where the bilinear operator is scalar multiplication.
Note: it often helps the elaborator to give the type of the convolution explicitly. -/
theorem convolution_lsmul [Sub G] {f : G → 𝕜} {g : G → F} :
    (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f t • g (x - t) ∂μ :=
  rfl
#align convolution_lsmul convolution_lsmul

/-- The definition of convolution where the bilinear operator is multiplication. -/
theorem convolution_mul [Sub G] [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
    (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f t * g (x - t) ∂μ :=
  rfl
#align convolution_mul convolution_mul

section Group

variable {L} [AddGroup G]

theorem smul_convolution [SMulCommClass ℝ 𝕜 F] {y : 𝕜} : y • f ⋆[L, μ] g = y • (f ⋆[L, μ] g) :=
  by
  ext
  simp only [Pi.smul_apply, convolution_def, ← integral_smul, L.map_smul₂]
#align smul_convolution smul_convolution

theorem convolution_smul [SMulCommClass ℝ 𝕜 F] {y : 𝕜} : f ⋆[L, μ] y • g = y • (f ⋆[L, μ] g) :=
  by
  ext
  simp only [Pi.smul_apply, convolution_def, ← integral_smul, (L _).map_smul]
#align convolution_smul convolution_smul

@[simp]
theorem zero_convolution : 0 ⋆[L, μ] g = 0 := by
  ext
  simp_rw [convolution_def, Pi.zero_apply, L.map_zero₂, integral_zero]
#align zero_convolution zero_convolution

@[simp]
theorem convolution_zero : f ⋆[L, μ] 0 = 0 := by
  ext
  simp_rw [convolution_def, Pi.zero_apply, (L _).map_zero, integral_zero]
#align convolution_zero convolution_zero

theorem ConvolutionExistsAt.distrib_add {x : G} (hfg : ConvolutionExistsAt f g x L μ)
    (hfg' : ConvolutionExistsAt f g' x L μ) :
    (f ⋆[L, μ] (g + g')) x = (f ⋆[L, μ] g) x + (f ⋆[L, μ] g') x := by
  simp only [convolution_def, (L _).map_add, Pi.add_apply, integral_add hfg hfg']
#align convolution_exists_at.distrib_add ConvolutionExistsAt.distrib_add

theorem ConvolutionExists.distrib_add (hfg : ConvolutionExists f g L μ)
    (hfg' : ConvolutionExists f g' L μ) : f ⋆[L, μ] (g + g') = f ⋆[L, μ] g + f ⋆[L, μ] g' :=
  by
  ext
  exact (hfg x).distrib_add (hfg' x)
#align convolution_exists.distrib_add ConvolutionExists.distrib_add

theorem ConvolutionExistsAt.add_distrib {x : G} (hfg : ConvolutionExistsAt f g x L μ)
    (hfg' : ConvolutionExistsAt f' g x L μ) :
    ((f + f') ⋆[L, μ] g) x = (f ⋆[L, μ] g) x + (f' ⋆[L, μ] g) x := by
  simp only [convolution_def, L.map_add₂, Pi.add_apply, integral_add hfg hfg']
#align convolution_exists_at.add_distrib ConvolutionExistsAt.add_distrib

theorem ConvolutionExists.add_distrib (hfg : ConvolutionExists f g L μ)
    (hfg' : ConvolutionExists f' g L μ) : (f + f') ⋆[L, μ] g = f ⋆[L, μ] g + f' ⋆[L, μ] g :=
  by
  ext
  exact (hfg x).add_distrib (hfg' x)
#align convolution_exists.add_distrib ConvolutionExists.add_distrib

variable (L)

theorem convolution_congr [HasMeasurableAdd₂ G] [HasMeasurableNeg G] [SigmaFinite μ]
    [IsAddRightInvariant μ] (h1 : f =ᵐ[μ] f') (h2 : g =ᵐ[μ] g') : f ⋆[L, μ] g = f' ⋆[L, μ] g' :=
  by
  ext x
  apply integral_congr_ae
  exact
    (h1.prod_mk <|
          h2.comp_tendsto
            (quasi_measure_preserving_sub_left_of_right_invariant μ x).tendsto_ae).fun_comp
      ↿fun x y => L x y
#align convolution_congr convolution_congr

theorem support_convolution_subset_swap : support (f ⋆[L, μ] g) ⊆ support g + support f :=
  by
  intro x h2x
  by_contra hx
  apply h2x
  simp_rw [Set.mem_add, not_exists, not_and_or, nmem_support] at hx
  rw [convolution_def]
  convert integral_zero G F
  ext t
  rcases hx (x - t) t with (h | h | h)
  · rw [h, (L _).map_zero]
  · rw [h, L.map_zero₂]
  · exact (h <| sub_add_cancel x t).elim
#align support_convolution_subset_swap support_convolution_subset_swap

section

variable [HasMeasurableAdd₂ G] [HasMeasurableNeg G] [SigmaFinite μ] [IsAddRightInvariant μ]

theorem MeasureTheory.Integrable.integrableConvolution (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (f ⋆[L, μ] g) μ :=
  (hf.convolutionIntegrand L hg).integral_prod_left
#align
  measure_theory.integrable.integrable_convolution MeasureTheory.Integrable.integrableConvolution

end

variable [TopologicalSpace G]

variable [TopologicalAddGroup G]

theorem HasCompactSupport.convolution [T2Space G] (hcf : HasCompactSupport f)
    (hcg : HasCompactSupport g) : HasCompactSupport (f ⋆[L, μ] g) :=
  is_compact_of_is_closed_subset (hcg.IsCompact.add hcf) is_closed_closure <|
    closure_minimal
      ((support_convolution_subset_swap L).trans <| add_subset_add subset_closure subset_closure)
      (hcg.IsCompact.add hcf).IsClosed
#align has_compact_support.convolution HasCompactSupport.convolution

variable [BorelSpace G] [FirstCountableTopology G] [TopologicalSpace P] [FirstCountableTopology P]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in a subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
not assuming `t2_space G`. -/
theorem continuous_on_convolution_right_with_param' {g : P → G → E'} {s : Set P} {k : Set G}
    (hk : IsCompact k) (h'k : IsClosed k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContinuousOn (↿g) (s ×ˢ univ)) :
    ContinuousOn (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) :=
  by
  intro q₀ hq₀
  replace hq₀ : q₀.1 ∈ s
  · simpa only [mem_prod, mem_univ, and_true_iff] using hq₀
  have A : ∀ p ∈ s, Continuous (g p) := by
    intro p hp
    apply hg.comp_continuous (continuous_const.prod_mk continuous_id') fun x => _
    simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true_iff] using hp
  have B : ∀ p ∈ s, tsupport (g p) ⊆ k := fun p hp =>
    closure_minimal (support_subset_iff'.2 fun z hz => hgs _ _ hp hz) h'k
  /- We find a small neighborhood of `{q₀.1} × k` on which the function is uniformly bounded.
      This follows from the continuity at all points of the compact set `k`. -/
  obtain ⟨w, C, w_open, q₀w, Cnonneg, hw⟩ :
    ∃ w C, IsOpen w ∧ q₀.1 ∈ w ∧ 0 ≤ C ∧ ∀ p x, p ∈ w ∩ s → ‖g p x‖ ≤ C :=
    by
    have A : IsCompact ({q₀.1} ×ˢ k) := is_compact_singleton.prod hk
    obtain ⟨t, kt, t_open, ht⟩ :
      ∃ t, {q₀.1} ×ˢ k ⊆ t ∧ IsOpen t ∧ bounded (↿g '' (t ∩ s ×ˢ univ)) :=
      by
      apply exists_is_open_bounded_image_inter_of_is_compact_of_continuous_on A _ hg
      simp only [prod_subset_prod_iff, hq₀, singleton_subset_iff, subset_univ, and_self_iff,
        true_or_iff]
    obtain ⟨C, Cpos, hC⟩ : ∃ C, 0 < C ∧ ↿g '' (t ∩ s ×ˢ univ) ⊆ closed_ball (0 : E') C
    exact ht.subset_ball_lt 0 0
    obtain ⟨w, w_open, q₀w, hw⟩ : ∃ w, IsOpen w ∧ q₀.1 ∈ w ∧ w ×ˢ k ⊆ t :=
      by
      obtain ⟨w, v, w_open, v_open, hw, hv, hvw⟩ :
        ∃ (w : Set P)(v : Set G), IsOpen w ∧ IsOpen v ∧ {q₀.fst} ⊆ w ∧ k ⊆ v ∧ w ×ˢ v ⊆ t
      exact generalized_tube_lemma is_compact_singleton hk t_open kt
      exact ⟨w, w_open, singleton_subset_iff.1 hw, subset.trans (Set.prod_mono subset.rfl hv) hvw⟩
    refine' ⟨w, C, w_open, q₀w, Cpos.le, _⟩
    rintro p x ⟨hp, hps⟩
    by_cases hx : x ∈ k
    · have H : (p, x) ∈ t := by
        apply hw
        simp only [prod_mk_mem_set_prod_eq, hp, hx, and_true_iff]
      have H' : (p, x) ∈ (s ×ˢ univ : Set (P × G)) := by
        simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true_iff] using hps
      have : g p x ∈ closed_ball (0 : E') C := hC (mem_image_of_mem _ ⟨H, H'⟩)
      rwa [mem_closed_ball_zero_iff] at this
    · have : g p x = 0 := hgs _ _ hps hx
      rw [this]
      simpa only [norm_zero] using Cpos.le
  have I1 :
    ∀ᶠ q : P × G in 𝓝[s ×ˢ univ] q₀,
      ae_strongly_measurable (fun a : G => L (f a) (g q.1 (q.2 - a))) μ :=
    by
    filter_upwards [self_mem_nhds_within]
    rintro ⟨p, x⟩ ⟨hp, hx⟩
    refine' (HasCompactSupport.convolutionExistsRight L _ hf (A _ hp) _).1
    exact is_compact_of_is_closed_subset hk (is_closed_tsupport _) (B p hp)
  let K' := -k + {q₀.2}
  have hK' : IsCompact K' := hk.neg.add is_compact_singleton
  obtain ⟨U, U_open, K'U, hU⟩ : ∃ U, IsOpen U ∧ K' ⊆ U ∧ integrable_on f U μ
  exact hf.integrable_on_nhds_is_compact hK'
  let bound : G → ℝ := indicator U fun a => ‖L‖ * ‖f a‖ * C
  have I2 : ∀ᶠ q : P × G in 𝓝[s ×ˢ univ] q₀, ∀ᵐ a ∂μ, ‖L (f a) (g q.1 (q.2 - a))‖ ≤ bound a :=
    by
    obtain ⟨V, V_mem, hV⟩ : ∃ (V : Set G)(H : V ∈ 𝓝 (0 : G)), K' + V ⊆ U
    exact compact_open_separated_add_right hK' U_open K'U
    have : ((w ∩ s) ×ˢ ({q₀.2} + V) : Set (P × G)) ∈ 𝓝[s ×ˢ univ] q₀ :=
      by
      conv_rhs => rw [← @Prod.mk.eta _ _ q₀, nhds_within_prod_eq, nhds_within_univ]
      refine' Filter.prod_mem_prod _ (singleton_add_mem_nhds_of_nhds_zero q₀.2 V_mem)
      exact mem_nhds_within_iff_exists_mem_nhds_inter.2 ⟨w, w_open.mem_nhds q₀w, subset.rfl⟩
    filter_upwards [this]
    rintro ⟨p, x⟩ hpx
    simp only [prod_mk_mem_set_prod_eq] at hpx
    apply eventually_of_forall fun a => _
    apply convolution_integrand_bound_right_of_le_of_subset _ _ hpx.2 _
    · intro x
      exact hw _ _ hpx.1
    · rw [← add_assoc]
      apply subset.trans (add_subset_add_right (add_subset_add_right _)) hV
      rw [neg_subset_neg]
      exact B p hpx.1.2
  have I3 : integrable bound μ :=
    by
    rw [integrable_indicator_iff U_open.measurable_set]
    exact (hU.norm.const_mul _).mul_const _
  have I4 :
    ∀ᵐ a : G ∂μ, ContinuousWithinAt (fun q : P × G => L (f a) (g q.1 (q.2 - a))) (s ×ˢ univ) q₀ :=
    by
    apply eventually_of_forall fun a => _
    suffices H : ContinuousWithinAt (fun q : P × G => (f a, g q.1 (q.2 - a))) (s ×ˢ univ) q₀
    exact L.continuous₂.continuous_at.comp_continuous_within_at H
    apply continuous_within_at_const.prod
    change ContinuousWithinAt (fun q : P × G => (↿g) (q.1, q.2 - a)) (s ×ˢ univ) q₀
    have : ContinuousAt (fun q : P × G => (q.1, q.2 - a)) (q₀.1, q₀.2) :=
      (continuous_fst.prod_mk (continuous_snd.sub continuous_const)).ContinuousAt
    rw [← @Prod.mk.eta _ _ q₀]
    have h'q₀ : (q₀.1, q₀.2 - a) ∈ (s ×ˢ univ : Set (P × G)) := ⟨hq₀, mem_univ _⟩
    refine' ContinuousWithinAt.comp (hg _ h'q₀) this.continuous_within_at _
    rintro ⟨q, x⟩ ⟨hq, hx⟩
    exact ⟨hq, mem_univ _⟩
  exact continuous_within_at_of_dominated I1 I2 I3 I4
#align continuous_on_convolution_right_with_param' continuous_on_convolution_right_with_param'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in a subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`). -/
theorem continuous_on_convolution_right_with_param [T2Space G] {g : P → G → E'} {s : Set P}
    {k : Set G} (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContinuousOn (↿g) (s ×ˢ univ)) :
    ContinuousOn (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) :=
  continuous_on_convolution_right_with_param' L hk hk.IsClosed hgs hf hg
#align continuous_on_convolution_right_with_param continuous_on_convolution_right_with_param

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in an open subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of compositions with an additional continuous map.
Version not assuming `t2_space G`. -/
theorem continuous_on_convolution_right_with_param_comp' {s : Set P} {v : P → G}
    (hv : ContinuousOn v s) {g : P → G → E'} {k : Set G} (hk : IsCompact k) (h'k : IsClosed k)
    (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContinuousOn (↿g) (s ×ˢ univ)) : ContinuousOn (fun x => (f ⋆[L, μ] g x) (v x)) s :=
  by
  apply
    (continuous_on_convolution_right_with_param' L hk h'k hgs hf hg).comp (continuous_on_id.prod hv)
  intro x hx
  simp only [hx, prod_mk_mem_set_prod_eq, mem_univ, and_self_iff, id.def]
#align
  continuous_on_convolution_right_with_param_comp' continuous_on_convolution_right_with_param_comp'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in an open subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of compositions with an additional continuous map. -/
theorem continuous_on_convolution_right_with_param_comp [T2Space G] {s : Set P} {v : P → G}
    (hv : ContinuousOn v s) {g : P → G → E'} {k : Set G} (hk : IsCompact k)
    (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContinuousOn (↿g) (s ×ˢ univ)) : ContinuousOn (fun x => (f ⋆[L, μ] g x) (v x)) s :=
  continuous_on_convolution_right_with_param_comp' L hv hk hk.IsClosed hgs hf hg
#align
  continuous_on_convolution_right_with_param_comp continuous_on_convolution_right_with_param_comp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The convolution is continuous if one function is locally integrable and the other has compact
support and is continuous. -/
theorem HasCompactSupport.continuous_convolution_right (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : Continuous (f ⋆[L, μ] g) :=
  by
  rw [continuous_iff_continuous_on_univ]
  let g' : G → G → E' := fun p q => g q
  have : ContinuousOn (↿g') (univ ×ˢ univ) := (hg.comp continuous_snd).ContinuousOn
  exact
    continuous_on_convolution_right_with_param_comp' L
      (continuous_iff_continuous_on_univ.1 continuous_id) hcg (is_closed_tsupport _)
      (fun p x hp hx => image_eq_zero_of_nmem_tsupport hx) hf this
#align
  has_compact_support.continuous_convolution_right HasCompactSupport.continuous_convolution_right

/-- The convolution is continuous if one function is integrable and the other is bounded and
continuous. -/
theorem BddAbove.continuous_convolution_right_of_integrable [SecondCountableTopology G]
    (hbg : BddAbove (range fun x => ‖g x‖)) (hf : Integrable f μ) (hg : Continuous g) :
    Continuous (f ⋆[L, μ] g) :=
  by
  refine' continuous_iff_continuous_at.mpr fun x₀ => _
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t : G ∂μ, ‖L (f t) (g (x - t))‖ ≤ ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖ :=
    by
    refine' eventually_of_forall fun x => eventually_of_forall fun t => _
    refine' (L.le_op_norm₂ _ _).trans _
    exact
      mul_le_mul_of_nonneg_left (le_csupᵢ hbg <| x - t) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  refine' continuous_at_of_dominated _ this _ _
  ·
    exact
      eventually_of_forall fun x =>
        hf.ae_strongly_measurable.convolution_integrand_snd' L hg.ae_strongly_measurable
  · exact (hf.norm.const_mul _).mul_const _
  ·
    exact
      eventually_of_forall fun t =>
        (L.continuous₂.comp₂ continuous_const <|
            hg.comp <| continuous_id.sub <| by apply continuous_const).ContinuousAt
#align
  bdd_above.continuous_convolution_right_of_integrable BddAbove.continuous_convolution_right_of_integrable

end Group

section CommGroup

variable [AddCommGroup G]

theorem support_convolution_subset : support (f ⋆[L, μ] g) ⊆ support f + support g :=
  (support_convolution_subset_swap L).trans (add_comm _ _).Subset
#align support_convolution_subset support_convolution_subset

variable [IsAddLeftInvariant μ] [IsNegInvariant μ]

section Measurable

variable [HasMeasurableNeg G]

variable [HasMeasurableAdd G]

variable (L)

/-- Commutativity of convolution -/
theorem convolution_flip : g ⋆[L.flip, μ] f = f ⋆[L, μ] g :=
  by
  ext1 x
  simp_rw [convolution_def]
  rw [← integral_sub_left_eq_self _ μ x]
  simp_rw [sub_sub_self, flip_apply]
#align convolution_flip convolution_flip

/-- The symmetric definition of convolution. -/
theorem convolution_eq_swap : (f ⋆[L, μ] g) x = ∫ t, L (f (x - t)) (g t) ∂μ :=
  by
  rw [← convolution_flip]
  rfl
#align convolution_eq_swap convolution_eq_swap

/-- The symmetric definition of convolution where the bilinear operator is scalar multiplication. -/
theorem convolution_lsmul_swap {f : G → 𝕜} {g : G → F} :
    (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f (x - t) • g t ∂μ :=
  convolution_eq_swap _
#align convolution_lsmul_swap convolution_lsmul_swap

/-- The symmetric definition of convolution where the bilinear operator is multiplication. -/
theorem convolution_mul_swap [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
    (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f (x - t) * g t ∂μ :=
  convolution_eq_swap _
#align convolution_mul_swap convolution_mul_swap

/-- The convolution of two even functions is also even. -/
theorem convolution_neg_of_neg_eq (h1 : ∀ᵐ x ∂μ, f (-x) = f x) (h2 : ∀ᵐ x ∂μ, g (-x) = g x) :
    (f ⋆[L, μ] g) (-x) = (f ⋆[L, μ] g) x :=
  calc
    (∫ t : G, (L (f t)) (g (-x - t)) ∂μ) = ∫ t : G, (L (f (-t))) (g (x + t)) ∂μ :=
      by
      apply integral_congr_ae
      filter_upwards [h1, (eventually_add_left_iff μ x).2 h2] with t ht h't
      simp_rw [ht, ← h't, neg_add']
    _ = ∫ t : G, (L (f t)) (g (x - t)) ∂μ :=
      by
      rw [← integral_neg_eq_self]
      simp only [neg_neg, ← sub_eq_add_neg]
    
#align convolution_neg_of_neg_eq convolution_neg_of_neg_eq

end Measurable

variable [TopologicalSpace G]

variable [TopologicalAddGroup G]

variable [BorelSpace G]

theorem HasCompactSupport.continuous_convolution_left [FirstCountableTopology G]
    (hcf : HasCompactSupport f) (hf : Continuous f) (hg : LocallyIntegrable g μ) :
    Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hcf.continuous_convolution_right L.flip hg hf
#align has_compact_support.continuous_convolution_left HasCompactSupport.continuous_convolution_left

theorem BddAbove.continuous_convolution_left_of_integrable [SecondCountableTopology G]
    (hbf : BddAbove (range fun x => ‖f x‖)) (hf : Continuous f) (hg : Integrable g μ) :
    Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hbf.continuous_convolution_right_of_integrable L.flip hg hf
#align
  bdd_above.continuous_convolution_left_of_integrable BddAbove.continuous_convolution_left_of_integrable

end CommGroup

section NormedAddCommGroup

variable [SeminormedAddCommGroup G]

/-- Compute `(f ⋆ g) x₀` if the support of the `f` is within `metric.ball 0 R`, and `g` is constant
on `metric.ball x₀ R`.

We can simplify the RHS further if we assume `f` is integrable, but also if `L = (•)` or more
generally if `L` has a `antilipschitz_with`-condition. -/
theorem convolution_eq_right' {x₀ : G} {R : ℝ} (hf : support f ⊆ ball (0 : G) R)
    (hg : ∀ x ∈ ball x₀ R, g x = g x₀) : (f ⋆[L, μ] g) x₀ = ∫ t, L (f t) (g x₀) ∂μ :=
  by
  have h2 : ∀ t, L (f t) (g (x₀ - t)) = L (f t) (g x₀) :=
    by
    intro t
    by_cases ht : t ∈ support f
    · have h2t := hf ht
      rw [mem_ball_zero_iff] at h2t
      specialize hg (x₀ - t)
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg
      rw [hg h2t]
    · rw [nmem_support] at ht
      simp_rw [ht, L.map_zero₂]
  simp_rw [convolution_def, h2]
#align convolution_eq_right' convolution_eq_right'

variable [BorelSpace G] [SecondCountableTopology G]

variable [IsAddLeftInvariant μ] [SigmaFinite μ]

/-- Approximate `(f ⋆ g) x₀` if the support of the `f` is bounded within a ball, and `g` is near
`g x₀` on a ball with the same radius around `x₀`. See `dist_convolution_le` for a special case.

We can simplify the second argument of `dist` further if we add some extra type-classes on `E`
and `𝕜` or if `L` is scalar multiplication. -/
theorem dist_convolution_le' {x₀ : G} {R ε : ℝ} {z₀ : E'} (hε : 0 ≤ ε) (hif : Integrable f μ)
    (hf : support f ⊆ ball (0 : G) R) (hmg : AeStronglyMeasurable g μ)
    (hg : ∀ x ∈ ball x₀ R, dist (g x) z₀ ≤ ε) :
    dist ((f ⋆[L, μ] g : G → F) x₀) (∫ t, L (f t) z₀ ∂μ) ≤ (‖L‖ * ∫ x, ‖f x‖ ∂μ) * ε :=
  by
  have hfg : ConvolutionExistsAt f g x₀ L μ :=
    by
    refine'
      BddAbove.convolutionExistsAt L _ metric.is_open_ball.measurable_set (subset_trans _ hf)
        hif.integrable_on hmg
    swap
    · refine' fun t => mt fun ht : f t = 0 => _
      simp_rw [ht, L.map_zero₂]
    rw [bddAbove_def]
    refine' ⟨‖z₀‖ + ε, _⟩
    rintro _ ⟨x, hx, rfl⟩
    refine' norm_le_norm_add_const_of_dist_le (hg x _)
    rwa [mem_ball_iff_norm, norm_sub_rev, ← mem_ball_zero_iff]
  have h2 : ∀ t, dist (L (f t) (g (x₀ - t))) (L (f t) z₀) ≤ ‖L (f t)‖ * ε :=
    by
    intro t
    by_cases ht : t ∈ support f
    · have h2t := hf ht
      rw [mem_ball_zero_iff] at h2t
      specialize hg (x₀ - t)
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg
      refine' ((L (f t)).dist_le_op_norm _ _).trans _
      exact mul_le_mul_of_nonneg_left (hg h2t) (norm_nonneg _)
    · rw [nmem_support] at ht
      simp_rw [ht, L.map_zero₂, L.map_zero, norm_zero, zero_mul, dist_self]
  simp_rw [convolution_def]
  simp_rw [dist_eq_norm] at h2⊢
  rw [← integral_sub hfg.integrable]
  swap
  · exact (L.flip z₀).integrable_comp hif
  refine'
    (norm_integral_le_of_norm_le ((L.integrable_comp hif).norm.mul_const ε)
          (eventually_of_forall h2)).trans
      _
  rw [integral_mul_right]
  refine' mul_le_mul_of_nonneg_right _ hε
  have h3 : ∀ t, ‖L (f t)‖ ≤ ‖L‖ * ‖f t‖ := by
    intro t
    exact L.le_op_norm (f t)
  refine' (integral_mono (L.integrable_comp hif).norm (hif.norm.const_mul _) h3).trans_eq _
  rw [integral_mul_left]
#align dist_convolution_le' dist_convolution_le'

variable [NormedSpace ℝ E] [NormedSpace ℝ E'] [CompleteSpace E']

/-- Approximate `f ⋆ g` if the support of the `f` is bounded within a ball, and `g` is near `g x₀`
on a ball with the same radius around `x₀`.

This is a special case of `dist_convolution_le'` where `L` is `(•)`, `f` has integral 1 and `f` is
nonnegative. -/
theorem dist_convolution_le {f : G → ℝ} {x₀ : G} {R ε : ℝ} {z₀ : E'} (hε : 0 ≤ ε)
    (hf : support f ⊆ ball (0 : G) R) (hnf : ∀ x, 0 ≤ f x) (hintf : (∫ x, f x ∂μ) = 1)
    (hmg : AeStronglyMeasurable g μ) (hg : ∀ x ∈ ball x₀ R, dist (g x) z₀ ≤ ε) :
    dist ((f ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) z₀ ≤ ε :=
  by
  have hif : integrable f μ := by
    by_contra hif
    exact zero_ne_one ((integral_undef hif).symm.trans hintf)
  convert (dist_convolution_le' _ hε hif hf hmg hg).trans _
  · simp_rw [lsmul_apply, integral_smul_const, hintf, one_smul]
  · simp_rw [Real.norm_of_nonneg (hnf _), hintf, mul_one]
    exact (mul_le_mul_of_nonneg_right op_norm_lsmul_le hε).trans_eq (one_mul ε)
#align dist_convolution_le dist_convolution_le

/-- `(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of nonnegative functions with integral `1` as `i` tends to `l`;
* The support of `φ` tends to small neighborhoods around `(0 : G)` as `i` tends to `l`;
* `g i` is `mu`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ᶠ 𝓝 x₀`;
* `k i` tends to `x₀`.

See also `cont_diff_bump_of_inner.convolution_tendsto_right`.
-/
theorem convolution_tendsto_right {ι} {g : ι → G → E'} {l : Filter ι} {x₀ : G} {z₀ : E'}
    {φ : ι → G → ℝ} {k : ι → G} (hnφ : ∀ᶠ i in l, ∀ x, 0 ≤ φ i x)
    (hiφ : ∀ᶠ i in l, (∫ x, φ i x ∂μ) = 1)
    -- todo: we could weaken this to "the integral tends to 1"
    (hφ : Tendsto (fun n => support (φ n)) l (𝓝 0).smallSets)
    (hmg : ∀ᶠ i in l, AeStronglyMeasurable (g i) μ) (hcg : Tendsto (uncurry g) (l ×ᶠ 𝓝 x₀) (𝓝 z₀))
    (hk : Tendsto k l (𝓝 x₀)) :
    Tendsto (fun i : ι => (φ i ⋆[lsmul ℝ ℝ, μ] g i : G → E') (k i)) l (𝓝 z₀) :=
  by
  simp_rw [tendsto_small_sets_iff] at hφ
  rw [Metric.tendsto_nhds] at hcg⊢
  simp_rw [Metric.eventually_prod_nhds_iff] at hcg
  intro ε hε
  have h2ε : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨p, hp, δ, hδ, hgδ⟩ := hcg _ h2ε
  dsimp only [uncurry] at hgδ
  have h2k := hk.eventually (ball_mem_nhds x₀ <| half_pos hδ)
  have h2φ := hφ (ball (0 : G) _) <| ball_mem_nhds _ (half_pos hδ)
  filter_upwards [hp, h2k, h2φ, hnφ, hiφ, hmg] with i hpi hki hφi hnφi hiφi hmgi
  have hgi : dist (g i (k i)) z₀ < ε / 3 := hgδ hpi (hki.trans <| half_lt_self hδ)
  have h1 : ∀ x' ∈ ball (k i) (δ / 2), dist (g i x') (g i (k i)) ≤ ε / 3 + ε / 3 :=
    by
    intro x' hx'
    refine' (dist_triangle_right _ _ _).trans (add_le_add (hgδ hpi _).le hgi.le)
    exact ((dist_triangle _ _ _).trans_lt (add_lt_add hx'.out hki)).trans_eq (add_halves δ)
  have := dist_convolution_le (add_pos h2ε h2ε).le hφi hnφi hiφi hmgi h1
  refine' ((dist_triangle _ _ _).trans_lt (add_lt_add_of_le_of_lt this hgi)).trans_eq _
  field_simp
  ring_nf
#align convolution_tendsto_right convolution_tendsto_right

end NormedAddCommGroup

namespace ContDiffBumpOfInner

variable {n : ℕ∞}

variable [NormedSpace ℝ E']

variable [InnerProductSpace ℝ G]

variable [CompleteSpace E']

variable {a : G} {φ : ContDiffBumpOfInner (0 : G)}

/-- If `φ` is a bump function, compute `(φ ⋆ g) x₀` if `g` is constant on `metric.ball x₀ φ.R`. -/
theorem convolution_eq_right {x₀ : G} (hg : ∀ x ∈ ball x₀ φ.r, g x = g x₀) :
    (φ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = integral μ φ • g x₀ := by
  simp_rw [convolution_eq_right' _ φ.support_eq.subset hg, lsmul_apply, integral_smul_const]
#align cont_diff_bump_of_inner.convolution_eq_right ContDiffBumpOfInner.convolution_eq_right

variable [BorelSpace G]

variable [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure μ]

variable [FiniteDimensional ℝ G]

/-- If `φ` is a normed bump function, compute `φ ⋆ g` if `g` is constant on `metric.ball x₀ φ.R`. -/
theorem normed_convolution_eq_right {x₀ : G} (hg : ∀ x ∈ ball x₀ φ.r, g x = g x₀) :
    (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = g x₀ :=
  by
  simp_rw [convolution_eq_right' _ φ.support_normed_eq.subset hg, lsmul_apply]
  exact integral_normed_smul φ μ (g x₀)
#align
  cont_diff_bump_of_inner.normed_convolution_eq_right ContDiffBumpOfInner.normed_convolution_eq_right

variable [IsAddLeftInvariant μ]

/-- If `φ` is a normed bump function, approximate `(φ ⋆ g) x₀` if `g` is near `g x₀` on a ball with
radius `φ.R` around `x₀`. -/
theorem dist_normed_convolution_le {x₀ : G} {ε : ℝ} (hmg : AeStronglyMeasurable g μ)
    (hg : ∀ x ∈ ball x₀ φ.r, dist (g x) (g x₀) ≤ ε) :
    dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) (g x₀) ≤ ε :=
  dist_convolution_le (by simp_rw [← dist_self (g x₀), hg x₀ (mem_ball_self φ.R_pos)])
    φ.support_normed_eq.Subset φ.nonneg_normed φ.integral_normed hmg hg
#align
  cont_diff_bump_of_inner.dist_normed_convolution_le ContDiffBumpOfInner.dist_normed_convolution_le

/-- `(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of normed bump functions such that `(φ i).R` tends to `0` as `i` tends to `l`;
* `g i` is `mu`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ᶠ 𝓝 x₀`;
* `k i` tends to `x₀`. -/
theorem convolution_tendsto_right {ι} {φ : ι → ContDiffBumpOfInner (0 : G)} {g : ι → G → E'}
    {k : ι → G} {x₀ : G} {z₀ : E'} {l : Filter ι} (hφ : Tendsto (fun i => (φ i).r) l (𝓝 0))
    (hig : ∀ᶠ i in l, AeStronglyMeasurable (g i) μ) (hcg : Tendsto (uncurry g) (l ×ᶠ 𝓝 x₀) (𝓝 z₀))
    (hk : Tendsto k l (𝓝 x₀)) :
    Tendsto (fun i => ((fun x => (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g i : G → E') (k i)) l (𝓝 z₀) :=
  convolution_tendsto_right (eventually_of_forall fun i => (φ i).nonneg_normed)
    (eventually_of_forall fun i => (φ i).integral_normed) (tendsto_support_normed_small_sets hφ) hig
    hcg hk
#align
  cont_diff_bump_of_inner.convolution_tendsto_right ContDiffBumpOfInner.convolution_tendsto_right

/-- Special case of `cont_diff_bump_of_inner.convolution_tendsto_right` where `g` is continuous,
  and the limit is taken only in the first function. -/
theorem convolution_tendsto_right_of_continuous {ι} {φ : ι → ContDiffBumpOfInner (0 : G)}
    {l : Filter ι} (hφ : Tendsto (fun i => (φ i).r) l (𝓝 0)) (hg : Continuous g) (x₀ : G) :
    Tendsto (fun i => ((fun x => (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) :=
  convolution_tendsto_right hφ (eventually_of_forall fun _ => hg.AeStronglyMeasurable)
    ((hg.Tendsto x₀).comp tendsto_snd) tendsto_const_nhds
#align
  cont_diff_bump_of_inner.convolution_tendsto_right_of_continuous ContDiffBumpOfInner.convolution_tendsto_right_of_continuous

end ContDiffBumpOfInner

end Measurability

end NontriviallyNormedField

open convolution

section IsROrC

variable [IsROrC 𝕜]

variable [NormedSpace 𝕜 E]

variable [NormedSpace 𝕜 E']

variable [NormedSpace 𝕜 E'']

variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]

variable {n : ℕ∞}

variable [CompleteSpace F]

variable [MeasurableSpace G] {μ ν : Measure G}

variable (L : E →L[𝕜] E' →L[𝕜] F)

section Assoc

variable [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [CompleteSpace F']

variable [NormedAddCommGroup F''] [NormedSpace ℝ F''] [NormedSpace 𝕜 F''] [CompleteSpace F'']

variable {k : G → E''}

variable (L₂ : F →L[𝕜] E'' →L[𝕜] F')

variable (L₃ : E →L[𝕜] F'' →L[𝕜] F')

variable (L₄ : E' →L[𝕜] E'' →L[𝕜] F'')

variable [AddGroup G]

variable [SigmaFinite μ] [SigmaFinite ν] [IsAddRightInvariant μ]

theorem integral_convolution [HasMeasurableAdd₂ G] [HasMeasurableNeg G] [NormedSpace ℝ E]
    [NormedSpace ℝ E'] [CompleteSpace E] [CompleteSpace E'] (hf : Integrable f ν)
    (hg : Integrable g μ) : (∫ x, (f ⋆[L, ν] g) x ∂μ) = L (∫ x, f x ∂ν) (∫ x, g x ∂μ) :=
  by
  refine' (integral_integral_swap (by apply hf.convolution_integrand L hg)).trans _
  simp_rw [integral_comp_comm _ (hg.comp_sub_right _), integral_sub_right_eq_self]
  exact (L.flip (∫ x, g x ∂μ)).integral_comp_comm hf
#align integral_convolution integral_convolution

variable [HasMeasurableAdd₂ G] [IsAddRightInvariant ν] [HasMeasurableNeg G]

/-- Convolution is associative. This has a weak but inconvenient integrability condition.
See also `convolution_assoc`. -/
theorem convolution_assoc' (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z))
    {x₀ : G} (hfg : ∀ᵐ y ∂μ, ConvolutionExistsAt f g y L ν)
    (hgk : ∀ᵐ x ∂ν, ConvolutionExistsAt g k x L₄ μ)
    (hi : Integrable (uncurry fun x y => (L₃ (f y)) ((L₄ (g (x - y))) (k (x₀ - x)))) (μ.Prod ν)) :
    ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀ :=
  calc
    ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = ∫ t, L₂ (∫ s, L (f s) (g (t - s)) ∂ν) (k (x₀ - t)) ∂μ := rfl
    _ = ∫ t, ∫ s, L₂ (L (f s) (g (t - s))) (k (x₀ - t)) ∂ν ∂μ :=
      integral_congr_ae (hfg.mono fun t ht => ((L₂.flip (k (x₀ - t))).integral_comp_comm ht).symm)
    _ = ∫ t, ∫ s, L₃ (f s) (L₄ (g (t - s)) (k (x₀ - t))) ∂ν ∂μ := by simp_rw [hL]
    _ = ∫ s, ∫ t, L₃ (f s) (L₄ (g (t - s)) (k (x₀ - t))) ∂μ ∂ν := by rw [integral_integral_swap hi]
    _ = ∫ s, ∫ u, L₃ (f s) (L₄ (g u) (k (x₀ - s - u))) ∂μ ∂ν :=
      by
      congr ; ext t
      rw [eq_comm, ← integral_sub_right_eq_self _ t]
      · simp_rw [sub_sub_sub_cancel_right]
      · infer_instance
    _ = ∫ s, L₃ (f s) (∫ u, L₄ (g u) (k (x₀ - s - u)) ∂μ) ∂ν :=
      by
      refine' integral_congr_ae _
      refine'
        ((quasi_measure_preserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht => _
      exact (L₃ (f t)).integral_comp_comm ht
    _ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀ := rfl
    
#align convolution_assoc' convolution_assoc'

/-- Convolution is associative. This requires that
* all maps are a.e. strongly measurable w.r.t one of the measures
* `f ⋆[L, ν] g` exists almost everywhere
* `‖g‖ ⋆[μ] ‖k‖` exists almost everywhere
* `‖f‖ ⋆[ν] (‖g‖ ⋆[μ] ‖k‖)` exists at `x₀` -/
theorem convolution_assoc (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z)) {x₀ : G}
    (hf : AeStronglyMeasurable f ν) (hg : AeStronglyMeasurable g μ) (hk : AeStronglyMeasurable k μ)
    (hfg : ∀ᵐ y ∂μ, ConvolutionExistsAt f g y L ν)
    (hgk : ∀ᵐ x ∂ν, ConvolutionExistsAt (fun x => ‖g x‖) (fun x => ‖k x‖) x (mul ℝ ℝ) μ)
    (hfgk :
      ConvolutionExistsAt (fun x => ‖f x‖) ((fun x => ‖g x‖) ⋆[mul ℝ ℝ, μ] fun x => ‖k x‖) x₀
        (mul ℝ ℝ) ν) :
    ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀ :=
  by
  refine' convolution_assoc' L L₂ L₃ L₄ hL hfg (hgk.mono fun x hx => hx.ofNorm L₄ hg hk) _
  -- the following is similar to `integrable.convolution_integrand`
  have h_meas :
    ae_strongly_measurable (uncurry fun x y => L₃ (f y) (L₄ (g x) (k (x₀ - y - x)))) (μ.prod ν) :=
    by
    refine' L₃.ae_strongly_measurable_comp₂ hf.snd _
    refine' L₄.ae_strongly_measurable_comp₂ hg.fst _
    refine' (hk.mono' _).compMeasurable ((measurable_const.sub measurable_snd).sub measurable_fst)
    refine' quasi_measure_preserving.absolutely_continuous _
    refine'
      quasi_measure_preserving.prod_of_left
        ((measurable_const.sub measurable_snd).sub measurable_fst) (eventually_of_forall fun y => _)
    dsimp only
    exact quasi_measure_preserving_sub_left_of_right_invariant μ _
  have h2_meas :
    ae_strongly_measurable (fun y => ∫ x, ‖L₃ (f y) (L₄ (g x) (k (x₀ - y - x)))‖ ∂μ) ν :=
    h_meas.prod_swap.norm.integral_prod_right'
  have h3 : map (fun z : G × G => (z.1 - z.2, z.2)) (μ.prod ν) = μ.prod ν :=
    (measure_preserving_sub_prod μ ν).map_eq
  suffices integrable (uncurry fun x y => L₃ (f y) (L₄ (g x) (k (x₀ - y - x)))) (μ.prod ν)
    by
    rw [← h3] at this
    convert this.comp_measurable (measurable_sub.prod_mk measurable_snd)
    ext ⟨x, y⟩
    simp_rw [uncurry, Function.comp_apply, sub_sub_sub_cancel_right]
  simp_rw [integrable_prod_iff' h_meas]
  refine'
    ⟨((quasi_measure_preserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht =>
        (L₃ (f t)).integrable_comp <| ht.ofNorm L₄ hg hk,
      _⟩
  refine'
    (hfgk.const_mul (‖L₃‖ * ‖L₄‖)).mono' h2_meas
      (((quasi_measure_preserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht => _)
  · simp_rw [convolution_def, mul_apply', mul_mul_mul_comm ‖L₃‖ ‖L₄‖, ← integral_mul_left]
    rw [Real.norm_of_nonneg]
    · refine'
        integral_mono_of_nonneg (eventually_of_forall fun t => norm_nonneg _)
          ((ht.const_mul _).const_mul _) (eventually_of_forall fun s => _)
      refine' (L₃.le_op_norm₂ _ _).trans _
      refine' mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      rw [← mul_assoc]
      apply L₄.le_op_norm₂
    exact integral_nonneg fun x => norm_nonneg _
#align convolution_assoc convolution_assoc

end Assoc

variable [NormedAddCommGroup G] [BorelSpace G]

theorem convolution_precompR_apply {g : G → E'' →L[𝕜] E'} (hf : LocallyIntegrable f μ)
    (hcg : HasCompactSupport g) (hg : Continuous g) (x₀ : G) (x : E'') :
    (f ⋆[L.precompR E'', μ] g) x₀ x = (f ⋆[L, μ] fun a => g a x) x₀ :=
  by
  have := hcg.convolution_exists_right (L.precompR E'' : _) hf hg x₀
  simp_rw [convolution_def, ContinuousLinearMap.integral_apply this]
  rfl
#align convolution_precompR_apply convolution_precompR_apply

variable [NormedSpace 𝕜 G] [SigmaFinite μ] [IsAddLeftInvariant μ]

/-- Compute the total derivative of `f ⋆ g` if `g` is `C^1` with compact support and `f` is locally
integrable. To write down the total derivative as a convolution, we use
`continuous_linear_map.precompR`. -/
theorem HasCompactSupport.hasFderivAtConvolutionRight (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : ContDiff 𝕜 1 g) (x₀ : G) :
    HasFderivAt (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x₀) x₀ :=
  by
  rcases hcg.eq_zero_or_finite_dimensional 𝕜 hg.continuous with (rfl | fin_dim)
  · have : fderiv 𝕜 (0 : G → E') = 0 := fderiv_const (0 : E')
    simp only [this, convolution_zero, Pi.zero_apply]
    exact hasFderivAtConst (0 : F) x₀
  skip
  have : ProperSpace G := FiniteDimensional.proper_is_R_or_C 𝕜 G
  set L' := L.precompR G
  have h1 : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (fun t => L (f t) (g (x - t))) μ :=
    eventually_of_forall
      (hf.ae_strongly_measurable.convolution_integrand_snd L hg.continuous.ae_strongly_measurable)
  have h2 : ∀ x, ae_strongly_measurable (fun t => L' (f t) (fderiv 𝕜 g (x - t))) μ :=
    hf.ae_strongly_measurable.convolution_integrand_snd L'
      (hg.continuous_fderiv le_rfl).AeStronglyMeasurable
  have h3 : ∀ x t, HasFderivAt (fun x => g (x - t)) (fderiv 𝕜 g (x - t)) x :=
    by
    intro x t
    simpa using
      (hg.differentiable le_rfl).DifferentiableAt.HasFderivAt.comp x
        ((hasFderivAtId x).sub (hasFderivAtConst t x))
  let K' := -tsupport (fderiv 𝕜 g) + closed_ball x₀ 1
  have hK' : IsCompact K' := (hcg.fderiv 𝕜).neg.add (is_compact_closed_ball x₀ 1)
  refine' hasFderivAtIntegralOfDominatedOfFderivLe zero_lt_one h1 _ (h2 x₀) _ _ _
  · exact K'.indicator fun t => ‖L'‖ * ‖f t‖ * ⨆ x, ‖fderiv 𝕜 g x‖
  · exact hcg.convolution_exists_right L hf hg.continuous x₀
  · refine' eventually_of_forall fun t x hx => _
    exact
      (hcg.fderiv 𝕜).convolution_integrand_bound_right L' (hg.continuous_fderiv le_rfl)
        (ball_subset_closed_ball hx)
  · rw [integrable_indicator_iff hK'.measurable_set]
    exact ((hf.integrable_on_is_compact hK').norm.const_mul _).mul_const _
  · exact eventually_of_forall fun t x hx => (L _).HasFderivAt.comp x (h3 x t)
#align
  has_compact_support.has_fderiv_at_convolution_right HasCompactSupport.hasFderivAtConvolutionRight

theorem HasCompactSupport.hasFderivAtConvolutionLeft [IsNegInvariant μ] (hcf : HasCompactSupport f)
    (hf : ContDiff 𝕜 1 f) (hg : LocallyIntegrable g μ) (x₀ : G) :
    HasFderivAt (f ⋆[L, μ] g) ((fderiv 𝕜 f ⋆[L.precompL G, μ] g) x₀) x₀ :=
  by
  simp (config := { singlePass := true }) only [← convolution_flip]
  exact hcf.has_fderiv_at_convolution_right L.flip hg hf x₀
#align
  has_compact_support.has_fderiv_at_convolution_left HasCompactSupport.hasFderivAtConvolutionLeft

end IsROrC

section Real

/-! The one-variable case -/


variable [IsROrC 𝕜]

variable [NormedSpace 𝕜 E]

variable [NormedSpace 𝕜 E']

variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]

variable {f₀ : 𝕜 → E} {g₀ : 𝕜 → E'}

variable {n : ℕ∞}

variable (L : E →L[𝕜] E' →L[𝕜] F)

variable [CompleteSpace F]

variable {μ : Measure 𝕜}

variable [IsAddLeftInvariant μ] [SigmaFinite μ]

theorem HasCompactSupport.has_deriv_at_convolution_right (hf : LocallyIntegrable f₀ μ)
    (hcg : HasCompactSupport g₀) (hg : ContDiff 𝕜 1 g₀) (x₀ : 𝕜) :
    HasDerivAt (f₀ ⋆[L, μ] g₀) ((f₀ ⋆[L, μ] deriv g₀) x₀) x₀ :=
  by
  convert (hcg.has_fderiv_at_convolution_right L hf hg x₀).HasDerivAt
  rw [convolution_precompR_apply L hf (hcg.fderiv 𝕜) (hg.continuous_fderiv le_rfl)]
  rfl
#align
  has_compact_support.has_deriv_at_convolution_right HasCompactSupport.has_deriv_at_convolution_right

theorem HasCompactSupport.has_deriv_at_convolution_left [IsNegInvariant μ]
    (hcf : HasCompactSupport f₀) (hf : ContDiff 𝕜 1 f₀) (hg : LocallyIntegrable g₀ μ) (x₀ : 𝕜) :
    HasDerivAt (f₀ ⋆[L, μ] g₀) ((deriv f₀ ⋆[L, μ] g₀) x₀) x₀ :=
  by
  simp (config := { singlePass := true }) only [← convolution_flip]
  exact hcf.has_deriv_at_convolution_right L.flip hg hf x₀
#align
  has_compact_support.has_deriv_at_convolution_left HasCompactSupport.has_deriv_at_convolution_left

end Real

section WithParam

variable [IsROrC 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E''] [NormedSpace ℝ F]
  [NormedSpace 𝕜 F] [CompleteSpace F] [MeasurableSpace G] [NormedAddCommGroup G] [BorelSpace G]
  [NormedSpace 𝕜 G] [NormedAddCommGroup P] [NormedSpace 𝕜 P] {μ : Measure G}
  (L : E →L[𝕜] E' →L[𝕜] F)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The derivative of the convolution `f * g` is given by `f * Dg`, when `f` is locally integrable
and `g` is `C^1` and compactly supported. Version where `g` depends on an additional parameter in an
open subset `s` of a parameter space `P` (and the compact support `k` is independent of the
parameter in `s`). -/
theorem hasFderivAtConvolutionRightWithParam {g : P → G → E'} {s : Set P} {k : Set G}
    (hs : IsOpen s) (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContDiffOn 𝕜 1 (↿g) (s ×ˢ univ)) (q₀ : P × G)
    (hq₀ : q₀.1 ∈ s) :
    HasFderivAt (fun q : P × G => (f ⋆[L, μ] g q.1) q.2)
      ((f ⋆[L.precompR (P × G), μ] fun x : G => fderiv 𝕜 (↿g) (q₀.1, x)) q₀.2) q₀ :=
  by
  let g' := fderiv 𝕜 ↿g
  have A : ∀ p ∈ s, Continuous (g p) := by
    intro p hp
    apply hg.continuous_on.comp_continuous (continuous_const.prod_mk continuous_id') fun x => _
    simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true_iff] using hp
  have A' : ∀ q : P × G, q.1 ∈ s → s ×ˢ univ ∈ 𝓝 q :=
    by
    intro q hq
    apply (hs.prod is_open_univ).mem_nhds
    simpa only [mem_prod, mem_univ, and_true_iff] using hq
  -- The derivative of `g` vanishes away from `k`.
  have g'_zero : ∀ p x, p ∈ s → x ∉ k → g' (p, x) = 0 :=
    by
    intro p x hp hx
    refine' (hasFderivAtZeroOfEventuallyConst 0 _).fderiv
    have M2 : kᶜ ∈ 𝓝 x := IsOpen.mem_nhds hk.is_closed.is_open_compl hx
    have M1 : s ∈ 𝓝 p := hs.mem_nhds hp
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod M1 M2]
    rintro ⟨p, y⟩ ⟨hp, hy⟩
    exact hgs p y hp hy
  /- We find a small neighborhood of `{q₀.1} × k` on which the derivative is uniformly bounded. This
    follows from the continuity at all points of the compact set `k`. -/
  obtain ⟨ε, C, εpos, Cnonneg, h₀ε, hε⟩ :
    ∃ ε C, 0 < ε ∧ 0 ≤ C ∧ ball q₀.1 ε ⊆ s ∧ ∀ p x, ‖p - q₀.1‖ < ε → ‖g' (p, x)‖ ≤ C :=
    by
    have A : IsCompact ({q₀.1} ×ˢ k) := is_compact_singleton.prod hk
    obtain ⟨t, kt, t_open, ht⟩ : ∃ t, {q₀.1} ×ˢ k ⊆ t ∧ IsOpen t ∧ bounded (g' '' t) :=
      by
      have B : ContinuousOn g' (s ×ˢ univ) :=
        hg.continuous_on_fderiv_of_open (hs.prod is_open_univ) le_rfl
      apply exists_is_open_bounded_image_of_is_compact_of_continuous_on A (hs.prod is_open_univ) _ B
      simp only [prod_subset_prod_iff, hq₀, singleton_subset_iff, subset_univ, and_self_iff,
        true_or_iff]
    obtain ⟨ε, εpos, hε, h'ε⟩ :
      ∃ ε : ℝ, 0 < ε ∧ thickening ε ({q₀.fst} ×ˢ k) ⊆ t ∧ ball q₀.1 ε ⊆ s :=
      by
      obtain ⟨ε, εpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ thickening ε ({q₀.fst} ×ˢ k) ⊆ t
      exact A.exists_thickening_subset_open t_open kt
      obtain ⟨δ, δpos, hδ⟩ : ∃ (δ : ℝ)(H : 0 < δ), ball q₀.1 δ ⊆ s
      exact Metric.is_open_iff.1 hs _ hq₀
      refine' ⟨min ε δ, lt_min εpos δpos, _, _⟩
      · exact subset.trans (thickening_mono (min_le_left _ _) _) hε
      · exact subset.trans (ball_subset_ball (min_le_right _ _)) hδ
    obtain ⟨C, Cpos, hC⟩ : ∃ C, 0 < C ∧ g' '' t ⊆ closed_ball 0 C
    exact ht.subset_ball_lt 0 0
    refine' ⟨ε, C, εpos, Cpos.le, h'ε, fun p x hp => _⟩
    have hps : p ∈ s := h'ε (mem_ball_iff_norm.2 hp)
    by_cases hx : x ∈ k
    · have H : (p, x) ∈ t := by
        apply hε
        refine' mem_thickening_iff.2 ⟨(q₀.1, x), _, _⟩
        ·
          simp only [hx, singleton_prod, mem_image, Prod.mk.inj_iff, eq_self_iff_true, true_and_iff,
            exists_eq_right]
        · rw [← dist_eq_norm] at hp
          simpa only [Prod.dist_eq, εpos, dist_self, max_lt_iff, and_true_iff] using hp
      have : g' (p, x) ∈ closed_ball (0 : P × G →L[𝕜] E') C := hC (mem_image_of_mem _ H)
      rwa [mem_closed_ball_zero_iff] at this
    · have : g' (p, x) = 0 := g'_zero _ _ hps hx
      rw [this]
      simpa only [norm_zero] using Cpos.le
  /- Now, we wish to apply a theorem on differentiation of integrals. For this, we need to check
    trivial measurability or integrability assumptions (in `I1`, `I2`, `I3`), as well as a uniform
    integrability assumption over the derivative (in `I4` and `I5`) and pointwise differentiability
    in `I6`. -/
  have I1 :
    ∀ᶠ x : P × G in 𝓝 q₀, ae_strongly_measurable (fun a : G => L (f a) (g x.1 (x.2 - a))) μ :=
    by
    filter_upwards [A' q₀ hq₀]
    rintro ⟨p, x⟩ ⟨hp, hx⟩
    refine' (HasCompactSupport.convolutionExistsRight L _ hf (A _ hp) _).1
    apply is_compact_of_is_closed_subset hk (is_closed_tsupport _)
    exact closure_minimal (support_subset_iff'.2 fun z hz => hgs _ _ hp hz) hk.is_closed
  have I2 : integrable (fun a : G => L (f a) (g q₀.1 (q₀.2 - a))) μ :=
    by
    have M : HasCompactSupport (g q₀.1) := HasCompactSupport.intro hk fun x hx => hgs q₀.1 x hq₀ hx
    apply M.convolution_exists_right L hf (A q₀.1 hq₀) q₀.2
  have I3 : ae_strongly_measurable (fun a : G => (L (f a)).comp (g' (q₀.fst, q₀.snd - a))) μ :=
    by
    have T : HasCompactSupport fun y => g' (q₀.1, y) :=
      HasCompactSupport.intro hk fun x hx => g'_zero q₀.1 x hq₀ hx
    apply (HasCompactSupport.convolutionExistsRight (L.precompR (P × G) : _) T hf _ q₀.2).1
    have : ContinuousOn g' (s ×ˢ univ) :=
      hg.continuous_on_fderiv_of_open (hs.prod is_open_univ) le_rfl
    apply this.comp_continuous (continuous_const.prod_mk continuous_id')
    intro x
    simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true_iff] using hq₀
  set K' := -k + {q₀.2} with K'_def
  have hK' : IsCompact K' := hk.neg.add is_compact_singleton
  obtain ⟨U, U_open, K'U, hU⟩ : ∃ U, IsOpen U ∧ K' ⊆ U ∧ integrable_on f U μ
  exact hf.integrable_on_nhds_is_compact hK'
  obtain ⟨δ, δpos, δε, hδ⟩ : ∃ δ, (0 : ℝ) < δ ∧ δ ≤ ε ∧ K' + ball 0 δ ⊆ U :=
    by
    obtain ⟨V, V_mem, hV⟩ : ∃ (V : Set G)(V_mem : V ∈ 𝓝 (0 : G)), K' + V ⊆ U
    exact compact_open_separated_add_right hK' U_open K'U
    rcases Metric.mem_nhds_iff.1 V_mem with ⟨δ, δpos, hδ⟩
    refine' ⟨min δ ε, lt_min δpos εpos, min_le_right _ _, _⟩
    exact (add_subset_add_left ((ball_subset_ball (min_le_left _ _)).trans hδ)).trans hV
  let bound : G → ℝ := indicator U fun a => ‖L.precompR (P × G)‖ * ‖f a‖ * C
  have I4 :
    ∀ᵐ a : G ∂μ,
      ∀ x : P × G, dist x q₀ < δ → ‖L.precompR (P × G) (f a) (g' (x.fst, x.snd - a))‖ ≤ bound a :=
    by
    apply eventually_of_forall
    intro a x hx
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm] at hx
    have : (-tsupport fun a => g' (x.1, a)) + ball q₀.2 δ ⊆ U :=
      by
      apply subset.trans _ hδ
      rw [K'_def, add_assoc]
      apply add_subset_add
      · rw [neg_subset_neg]
        apply closure_minimal (support_subset_iff'.2 fun z hz => _) hk.is_closed
        apply g'_zero x.1 z (h₀ε _) hz
        rw [mem_ball_iff_norm]
        exact ((le_max_left _ _).trans_lt hx).trans_le δε
      · simp only [add_ball, thickening_singleton, zero_vadd]
    apply convolution_integrand_bound_right_of_le_of_subset _ _ _ this
    · intro y
      exact hε _ _ (((le_max_left _ _).trans_lt hx).trans_le δε)
    · rw [mem_ball_iff_norm]
      exact (le_max_right _ _).trans_lt hx
  have I5 : integrable bound μ :=
    by
    rw [integrable_indicator_iff U_open.measurable_set]
    exact (hU.norm.const_mul _).mul_const _
  have I6 :
    ∀ᵐ a : G ∂μ,
      ∀ x : P × G,
        dist x q₀ < δ →
          HasFderivAt (fun x : P × G => L (f a) (g x.1 (x.2 - a)))
            ((L (f a)).comp (g' (x.fst, x.snd - a))) x :=
    by
    apply eventually_of_forall
    intro a x hx
    apply (L _).HasFderivAt.comp x
    have N : s ×ˢ univ ∈ 𝓝 (x.1, x.2 - a) := by
      apply A'
      apply h₀ε
      rw [Prod.dist_eq] at hx
      exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hx) δε
    have Z := ((hg.differentiable_on le_rfl).DifferentiableAt N).HasFderivAt
    have Z' : HasFderivAt (fun x : P × G => (x.1, x.2 - a)) (ContinuousLinearMap.id 𝕜 (P × G)) x :=
      by
      have : (fun x : P × G => (x.1, x.2 - a)) = id - fun x => (0, a) := by
        ext x <;> simp only [Pi.sub_apply, id.def, Prod.fst_sub, sub_zero, Prod.snd_sub]
      simp_rw [this]
      exact (hasFderivAtId x).sub_const (0, a)
    exact Z.comp x Z'
  exact hasFderivAtIntegralOfDominatedOfFderivLe δpos I1 I2 I3 I4 I5 I6
#align has_fderiv_at_convolution_right_with_param hasFderivAtConvolutionRightWithParam

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The convolution `f * g` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`).
In this version, all the types belong to the same universe (to get an induction working in the
proof). Use instead `cont_diff_on_convolution_right_with_param`, which removes this restriction. -/
theorem cont_diff_on_convolution_right_with_param_aux {G : Type uP} {E' : Type uP} {F : Type uP}
    {P : Type uP} [NormedAddCommGroup E'] [NormedAddCommGroup F] [NormedSpace 𝕜 E']
    [NormedSpace ℝ F] [NormedSpace 𝕜 F] [CompleteSpace F] [MeasurableSpace G] {μ : Measure G}
    [NormedAddCommGroup G] [BorelSpace G] [NormedSpace 𝕜 G] [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    {f : G → E} {n : ℕ∞} (L : E →L[𝕜] E' →L[𝕜] F) {g : P → G → E'} {s : Set P} {k : Set G}
    (hs : IsOpen s) (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContDiffOn 𝕜 n (↿g) (s ×ˢ univ)) :
    ContDiffOn 𝕜 n (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) :=
  by
  /- We have a formula for the derivation of `f * g`, which is of the same form, thanks to
    `has_fderiv_at_convolution_right_with_param`. Therefore, we can prove the result by induction on
    `n` (but for this we need the spaces at the different steps of the induction to live in the same
    universe, which is why we make the assumption in the lemma that all the relevant spaces
    come from the same universe). -/
  induction' n using Enat.nat_induction with n ih ih generalizing g E' F
  · rw [cont_diff_on_zero] at hg⊢
    exact continuous_on_convolution_right_with_param L hk hgs hf hg
  · let f' : P → G → P × G →L[𝕜] F := fun p a =>
      (f ⋆[L.precompR (P × G), μ] fun x : G => fderiv 𝕜 (uncurry g) (p, x)) a
    have A :
      ∀ q₀ : P × G,
        q₀.1 ∈ s → HasFderivAt (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (f' q₀.1 q₀.2) q₀ :=
      hasFderivAtConvolutionRightWithParam L hs hk hgs hf hg.one_of_succ
    rw [cont_diff_on_succ_iff_fderiv_of_open (hs.prod (@is_open_univ G _))] at hg⊢
    constructor
    · rintro ⟨p, x⟩ ⟨hp, hx⟩
      exact (A (p, x) hp).DifferentiableAt.DifferentiableWithinAt
    · suffices H : ContDiffOn 𝕜 n (↿f') (s ×ˢ univ)
      · apply H.congr
        rintro ⟨p, x⟩ ⟨hp, hx⟩
        exact (A (p, x) hp).fderiv
      have B : ∀ (p : P) (x : G), p ∈ s → x ∉ k → fderiv 𝕜 (uncurry g) (p, x) = 0 :=
        by
        intro p x hp hx
        apply (hasFderivAtZeroOfEventuallyConst (0 : E') _).fderiv
        have M2 : kᶜ ∈ 𝓝 x := IsOpen.mem_nhds hk.is_closed.is_open_compl hx
        have M1 : s ∈ 𝓝 p := hs.mem_nhds hp
        rw [nhds_prod_eq]
        filter_upwards [prod_mem_prod M1 M2]
        rintro ⟨p, y⟩ ⟨hp, hy⟩
        exact hgs p y hp hy
      apply ih (L.precompR (P × G) : _) B
      convert hg.2
      apply funext
      rintro ⟨p, x⟩
      rfl
  · rw [cont_diff_on_top] at hg⊢
    intro n
    exact ih n L hgs (hg n)
#align cont_diff_on_convolution_right_with_param_aux cont_diff_on_convolution_right_with_param_aux

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The convolution `f * g` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`). -/
theorem cont_diff_on_convolution_right_with_param {f : G → E} {n : ℕ∞} (L : E →L[𝕜] E' →L[𝕜] F)
    {g : P → G → E'} {s : Set P} {k : Set G} (hs : IsOpen s) (hk : IsCompact k)
    (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContDiffOn 𝕜 n (↿g) (s ×ˢ univ)) :
    ContDiffOn 𝕜 n (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) :=
  by
  /- The result is known when all the universes are the same, from
    `cont_diff_on_convolution_right_with_param_aux`. We reduce to this situation by pushing
    everything through `ulift` continuous linear equivalences. -/
  let eG : Type max uG uE' uF uP := ULift G
  borelize eG
  let eE' : Type max uE' uG uF uP := ULift E'
  let eF : Type max uF uG uE' uP := ULift F
  let eP : Type max uP uG uE' uF := ULift P
  have isoG : eG ≃L[𝕜] G := ContinuousLinearEquiv.ulift
  have isoE' : eE' ≃L[𝕜] E' := ContinuousLinearEquiv.ulift
  have isoF : eF ≃L[𝕜] F := ContinuousLinearEquiv.ulift
  have isoP : eP ≃L[𝕜] P := ContinuousLinearEquiv.ulift
  let ef := f ∘ isoG
  let eμ : Measure eG := measure.map isoG.symm μ
  let eg : eP → eG → eE' := fun ep ex => isoE'.symm (g (isoP ep) (isoG ex))
  let eL :=
    ContinuousLinearMap.comp
      ((ContinuousLinearEquiv.arrowCongr isoE' isoF).symm : (E' →L[𝕜] F) →L[𝕜] eE' →L[𝕜] eF) L
  let R := fun q : eP × eG => (ef ⋆[eL, eμ] eg q.1) q.2
  have R_contdiff : ContDiffOn 𝕜 n R ((isoP ⁻¹' s) ×ˢ univ) :=
    by
    have hek : IsCompact (isoG ⁻¹' k) := isoG.to_homeomorph.closed_embedding.is_compact_preimage hk
    have hes : IsOpen (isoP ⁻¹' s) := isoP.continuous.is_open_preimage _ hs
    refine' cont_diff_on_convolution_right_with_param_aux eL hes hek _ _ _
    · intro p x hp hx
      simp only [comp_app, ContinuousLinearEquiv.prod_apply, LinearIsometryEquiv.coe_coe,
        ContinuousLinearEquiv.map_eq_zero_iff]
      exact hgs _ _ hp hx
    · apply (locally_integrable_map_homeomorph isoG.symm.to_homeomorph).2
      convert hf
      ext1 x
      simp only [ef, ContinuousLinearEquiv.coe_to_homeomorph, comp_app,
        ContinuousLinearEquiv.apply_symm_apply]
    · apply isoE'.symm.cont_diff.comp_cont_diff_on
      apply hg.comp (isoP.prod isoG).ContDiff.ContDiffOn
      rintro ⟨p, x⟩ ⟨hp, hx⟩
      simpa only [mem_preimage, ContinuousLinearEquiv.prod_apply, prod_mk_mem_set_prod_eq, mem_univ,
        and_true_iff] using hp
  have A : ContDiffOn 𝕜 n (isoF ∘ R ∘ (isoP.prod isoG).symm) (s ×ˢ univ) :=
    by
    apply isoF.cont_diff.comp_cont_diff_on
    apply R_contdiff.comp (ContinuousLinearEquiv.cont_diff _).ContDiffOn
    rintro ⟨p, x⟩ ⟨hp, hx⟩
    simpa only [mem_preimage, mem_prod, mem_univ, and_true_iff, ContinuousLinearEquiv.prod_symm,
      ContinuousLinearEquiv.prod_apply, ContinuousLinearEquiv.apply_symm_apply] using hp
  have : isoF ∘ R ∘ (isoP.prod isoG).symm = fun q : P × G => (f ⋆[L, μ] g q.1) q.2 :=
    by
    apply funext
    rintro ⟨p, x⟩
    simp only [R, LinearIsometryEquiv.coe_coe, comp_app, ContinuousLinearEquiv.prod_symm,
      ContinuousLinearEquiv.prod_apply]
    simp only [convolution, eL, coe_comp', ContinuousLinearEquiv.coe_coe, comp_app, eμ]
    rw [ClosedEmbedding.integral_map, ← isoF.integral_comp_comm]
    swap
    · exact isoG.symm.to_homeomorph.closed_embedding
    congr 1
    ext1 a
    simp only [ef, eg, comp_app, ContinuousLinearEquiv.apply_symm_apply, coe_comp',
      ContinuousLinearEquiv.prod_apply, ContinuousLinearEquiv.map_sub,
      ContinuousLinearEquiv.arrowCongr, ContinuousLinearEquiv.arrow_congrSL_symm_apply,
      ContinuousLinearEquiv.coe_coe, comp_app, ContinuousLinearEquiv.apply_symm_apply]
  simp_rw [this] at A
  exact A
#align cont_diff_on_convolution_right_with_param cont_diff_on_convolution_right_with_param

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The convolution `f * g` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of composition with an additional smooth function. -/
theorem cont_diff_on_convolution_right_with_param_comp {n : ℕ∞} (L : E →L[𝕜] E' →L[𝕜] F) {s : Set P}
    {v : P → G} (hv : ContDiffOn 𝕜 n v s) {f : G → E} {g : P → G → E'} {k : Set G} (hs : IsOpen s)
    (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContDiffOn 𝕜 n (↿g) (s ×ˢ univ)) : ContDiffOn 𝕜 n (fun x => (f ⋆[L, μ] g x) (v x)) s :=
  by
  apply (cont_diff_on_convolution_right_with_param L hs hk hgs hf hg).comp (cont_diff_on_id.prod hv)
  intro x hx
  simp only [hx, mem_preimage, prod_mk_mem_set_prod_eq, mem_univ, and_self_iff, id.def]
#align cont_diff_on_convolution_right_with_param_comp cont_diff_on_convolution_right_with_param_comp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The convolution `g * f` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`). -/
theorem cont_diff_on_convolution_left_with_param [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (L : E' →L[𝕜] E →L[𝕜] F) {f : G → E} {n : ℕ∞} {g : P → G → E'} {s : Set P} {k : Set G}
    (hs : IsOpen s) (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContDiffOn 𝕜 n (↿g) (s ×ˢ univ)) :
    ContDiffOn 𝕜 n (fun q : P × G => (g q.1 ⋆[L, μ] f) q.2) (s ×ˢ univ) := by
  simpa only [convolution_flip] using
    cont_diff_on_convolution_right_with_param L.flip hs hk hgs hf hg
#align cont_diff_on_convolution_left_with_param cont_diff_on_convolution_left_with_param

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The convolution `g * f` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of composition with additional smooth functions. -/
theorem cont_diff_on_convolution_left_with_param_comp [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (L : E' →L[𝕜] E →L[𝕜] F) {s : Set P} {n : ℕ∞} {v : P → G} (hv : ContDiffOn 𝕜 n v s) {f : G → E}
    {g : P → G → E'} {k : Set G} (hs : IsOpen s) (hk : IsCompact k)
    (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContDiffOn 𝕜 n (↿g) (s ×ˢ univ)) : ContDiffOn 𝕜 n (fun x => (g x ⋆[L, μ] f) (v x)) s :=
  by
  apply (cont_diff_on_convolution_left_with_param L hs hk hgs hf hg).comp (cont_diff_on_id.prod hv)
  intro x hx
  simp only [hx, mem_preimage, prod_mk_mem_set_prod_eq, mem_univ, and_self_iff, id.def]
#align cont_diff_on_convolution_left_with_param_comp cont_diff_on_convolution_left_with_param_comp

theorem HasCompactSupport.cont_diff_convolution_right {n : ℕ∞} (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n (f ⋆[L, μ] g) :=
  by
  rcases exists_compact_iff_has_compact_support.2 hcg with ⟨k, hk, h'k⟩
  rw [← cont_diff_on_univ]
  exact
    cont_diff_on_convolution_right_with_param_comp L cont_diff_on_id is_open_univ hk
      (fun p x hp hx => h'k x hx) hf (hg.comp cont_diff_snd).ContDiffOn
#align has_compact_support.cont_diff_convolution_right HasCompactSupport.cont_diff_convolution_right

theorem HasCompactSupport.cont_diff_convolution_left [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    {n : ℕ∞} (hcf : HasCompactSupport f) (hf : ContDiff 𝕜 n f) (hg : LocallyIntegrable g μ) :
    ContDiff 𝕜 n (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hcf.cont_diff_convolution_right L.flip hg hf
#align has_compact_support.cont_diff_convolution_left HasCompactSupport.cont_diff_convolution_left

end WithParam

