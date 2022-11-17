/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
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

variable {𝕜 G E E' E'' F F' F'' : Type _}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup E''] [NormedAddCommGroup F] {f f' : G → E}
  {g g' : G → E'} {x x' : G} {y y' : E}

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E''] [NormedSpace 𝕜 F]

variable (L : E →L[𝕜] E' →L[𝕜] F)

section NoMeasurability

variable [AddGroup G] [TopologicalSpace G]

theorem HasCompactSupport.convolution_integrand_bound_right (hcg : HasCompactSupport g) (hg : Continuous g) {x t : G}
    {s : Set G} (hx : x ∈ s) :
    ∥L (f t) (g (x - t))∥ ≤ (-tsupport g + s).indicator (fun t => ∥L∥ * ∥f t∥ * ⨆ i, ∥g i∥) t := by
  refine' le_indicator (fun t ht => _) (fun t ht => _) t
  · refine' (L.le_op_norm₂ _ _).trans _
    exact
      mul_le_mul_of_nonneg_left (le_csupr (hg.norm.bdd_above_range_of_has_compact_support hcg.norm) $ x - t)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    
  · have : x - t ∉ support g := by
      refine' mt (fun hxt => _) ht
      refine' ⟨_, _, set.neg_mem_neg.mpr (subset_closure hxt), hx, _⟩
      rw [neg_sub, sub_add_cancel]
    rw [nmem_support.mp this, (L _).map_zero, norm_zero]
    
#align has_compact_support.convolution_integrand_bound_right HasCompactSupport.convolution_integrand_bound_right

theorem Continuous.convolution_integrand_fst [HasContinuousSub G] (hg : Continuous g) (t : G) :
    Continuous fun x => L (f t) (g (x - t)) :=
  L.continuous₂.comp₂ continuous_const $ hg.comp $ continuous_id.sub continuous_const
#align continuous.convolution_integrand_fst Continuous.convolution_integrand_fst

theorem HasCompactSupport.convolution_integrand_bound_left (hcf : HasCompactSupport f) (hf : Continuous f) {x t : G}
    {s : Set G} (hx : x ∈ s) :
    ∥L (f (x - t)) (g t)∥ ≤ (-tsupport f + s).indicator (fun t => (∥L∥ * ⨆ i, ∥f i∥) * ∥g t∥) t := by
  convert hcf.convolution_integrand_bound_right L.flip hf hx
  simp_rw [L.op_norm_flip, mul_right_comm]
#align has_compact_support.convolution_integrand_bound_left HasCompactSupport.convolution_integrand_bound_left

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

variable [HasMeasurableAdd₂ G] [HasMeasurableNeg G]

theorem MeasureTheory.AeStronglyMeasurable.convolutionIntegrand' [SigmaFinite ν] (hf : AeStronglyMeasurable f ν)
    (hg : AeStronglyMeasurable g $ map (fun p : G × G => p.1 - p.2) (μ.Prod ν)) :
    AeStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.Prod ν) :=
  L.aeStronglyMeasurableComp₂ hf.snd $ hg.compMeasurable measurableSub
#align
  measure_theory.ae_strongly_measurable.convolution_integrand' MeasureTheory.AeStronglyMeasurable.convolutionIntegrand'

theorem MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSnd' (hf : AeStronglyMeasurable f μ) {x : G}
    (hg : AeStronglyMeasurable g $ map (fun t => x - t) μ) : AeStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  L.aeStronglyMeasurableComp₂ hf $ hg.compMeasurable $ measurableId.const_sub x
#align
  measure_theory.ae_strongly_measurable.convolution_integrand_snd' MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSnd'

theorem MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSwapSnd' {x : G}
    (hf : AeStronglyMeasurable f $ map (fun t => x - t) μ) (hg : AeStronglyMeasurable g μ) :
    AeStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  L.aeStronglyMeasurableComp₂ (hf.compMeasurable $ measurableId.const_sub x) hg
#align
  measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd' MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSwapSnd'

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that the integrand has compact support and `g` is bounded on this support (note that
both properties hold if `g` is continuous with compact support). We also require that `f` is
integrable on the support of the integrand, and that both functions are strongly measurable.

Note: we could weaken the measurability condition to hold only for `μ.restrict s`. -/
theorem BddAbove.convolutionExistsAt' {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ∥g i∥) '' ((fun t => -t + x₀) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ) (hmf : AeStronglyMeasurable f μ)
    (hmg : AeStronglyMeasurable g $ map (fun t => x₀ - t) μ) : ConvolutionExistsAt f g x₀ L μ := by
  set s' := (fun t => -t + x₀) ⁻¹' s
  have : ∀ᵐ t : G ∂μ, ∥L (f t) (g (x₀ - t))∥ ≤ s.indicator (fun t => ∥L∥ * ∥f t∥ * ⨆ i : s', ∥g i∥) t := by
    refine' eventually_of_forall _
    refine' le_indicator (fun t ht => _) fun t ht => _
    · refine' (L.le_op_norm₂ _ _).trans _
      refine'
        mul_le_mul_of_nonneg_left (le_csupr_set hbg $ mem_preimage.mpr _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      rwa [neg_sub, sub_add_cancel]
      
    · have : t ∉ support fun t => L (f t) (g (x₀ - t)) := mt (fun h => h2s h) ht
      rw [nmem_support.mp this, norm_zero]
      
  refine' integrable.mono' _ _ this
  · rw [integrable_indicator_iff hs]
    exact (hf.norm.const_mul _).mul_const _
    
  · exact hmf.convolution_integrand_snd' L hmg
    
#align bdd_above.convolution_exists_at' BddAbove.convolutionExistsAt'

/-- If `∥f∥ *[μ] ∥g∥` exists, then `f *[L, μ] g` exists. -/
theorem ConvolutionExistsAt.ofNorm' {x₀ : G} (h : ConvolutionExistsAt (fun x => ∥f x∥) (fun x => ∥g x∥) x₀ (mul ℝ ℝ) μ)
    (hmf : AeStronglyMeasurable f μ) (hmg : AeStronglyMeasurable g $ map (fun t => x₀ - t) μ) :
    ConvolutionExistsAt f g x₀ L μ := by
  refine' (h.const_mul ∥L∥).mono' (hmf.convolution_integrand_snd' L hmg) (eventually_of_forall $ fun x => _)
  rw [mul_apply', ← mul_assoc]
  apply L.le_op_norm₂
#align convolution_exists_at.of_norm' ConvolutionExistsAt.ofNorm'

section Left

variable [SigmaFinite μ] [IsAddRightInvariant μ]

theorem MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSnd (hf : AeStronglyMeasurable f μ)
    (hg : AeStronglyMeasurable g μ) (x : G) : AeStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  hf.convolutionIntegrandSnd' L $ hg.mono' $ (quasiMeasurePreservingSubLeftOfRightInvariant μ x).AbsolutelyContinuous
#align
  measure_theory.ae_strongly_measurable.convolution_integrand_snd MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSnd

theorem MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSwapSnd (hf : AeStronglyMeasurable f μ)
    (hg : AeStronglyMeasurable g μ) (x : G) : AeStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  (hf.mono' (quasiMeasurePreservingSubLeftOfRightInvariant μ x).AbsolutelyContinuous).convolutionIntegrandSwapSnd' L hg
#align
  measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd MeasureTheory.AeStronglyMeasurable.convolutionIntegrandSwapSnd

/-- If `∥f∥ *[μ] ∥g∥` exists, then `f *[L, μ] g` exists. -/
theorem ConvolutionExistsAt.ofNorm {x₀ : G} (h : ConvolutionExistsAt (fun x => ∥f x∥) (fun x => ∥g x∥) x₀ (mul ℝ ℝ) μ)
    (hmf : AeStronglyMeasurable f μ) (hmg : AeStronglyMeasurable g μ) : ConvolutionExistsAt f g x₀ L μ :=
  h.ofNorm' L hmf $ hmg.mono' (quasiMeasurePreservingSubLeftOfRightInvariant μ x₀).AbsolutelyContinuous
#align convolution_exists_at.of_norm ConvolutionExistsAt.ofNorm

end Left

section Right

variable [SigmaFinite μ] [IsAddRightInvariant μ] [SigmaFinite ν]

theorem MeasureTheory.AeStronglyMeasurable.convolutionIntegrand (hf : AeStronglyMeasurable f ν)
    (hg : AeStronglyMeasurable g μ) : AeStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.Prod ν) :=
  hf.convolutionIntegrand' L $ hg.mono' (quasiMeasurePreservingSubOfRightInvariant μ ν).AbsolutelyContinuous
#align
  measure_theory.ae_strongly_measurable.convolution_integrand MeasureTheory.AeStronglyMeasurable.convolutionIntegrand

theorem MeasureTheory.Integrable.convolutionIntegrand (hf : Integrable f ν) (hg : Integrable g μ) :
    Integrable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.Prod ν) := by
  have h_meas : ae_strongly_measurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
    hf.ae_strongly_measurable.convolution_integrand L hg.ae_strongly_measurable
  have h2_meas : ae_strongly_measurable (fun y : G => ∫ x : G, ∥L (f y) (g (x - y))∥ ∂μ) ν :=
    h_meas.prod_swap.norm.integral_prod_right'
  simp_rw [integrable_prod_iff' h_meas]
  refine' ⟨eventually_of_forall fun t => (L (f t)).integrable_comp (hg.comp_sub_right t), _⟩
  refine' integrable.mono' _ h2_meas (eventually_of_forall $ fun t => (_ : _ ≤ ∥L∥ * ∥f t∥ * ∫ x, ∥g (x - t)∥ ∂μ))
  · simp_rw [integral_sub_right_eq_self fun t => ∥g t∥]
    exact (hf.norm.const_mul _).mul_const _
    
  · simp_rw [← integral_mul_left]
    rw [Real.norm_of_nonneg]
    · exact
        integral_mono_of_nonneg (eventually_of_forall $ fun t => norm_nonneg _) ((hg.comp_sub_right t).norm.const_mul _)
          (eventually_of_forall $ fun t => L.le_op_norm₂ _ _)
      
    exact integral_nonneg fun x => norm_nonneg _
    
#align measure_theory.integrable.convolution_integrand MeasureTheory.Integrable.convolutionIntegrand

theorem MeasureTheory.Integrable.ae_convolution_exists (hf : Integrable f ν) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, ConvolutionExistsAt f g x L ν :=
  ((integrable_prod_iff $ hf.AeStronglyMeasurable.convolutionIntegrand L hg.AeStronglyMeasurable).mp $
      hf.convolutionIntegrand L hg).1
#align measure_theory.integrable.ae_convolution_exists MeasureTheory.Integrable.ae_convolution_exists

end Right

variable [TopologicalSpace G] [TopologicalAddGroup G] [BorelSpace G] [SecondCountableTopology G] [SigmaCompactSpace G]

theorem HasCompactSupport.convolutionExistsAt {x₀ : G} (h : HasCompactSupport fun t => L (f t) (g (x₀ - t)))
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : ConvolutionExistsAt f g x₀ L μ :=
  ((((Homeomorph.neg G).trans $ Homeomorph.addRight x₀).is_compact_preimage.mpr h).bdd_above_image
        hg.norm.ContinuousOn).convolutionExistsAt'
    L isClosedClosure.MeasurableSet subset_closure (hf h) hf.AeStronglyMeasurable hg.AeStronglyMeasurable
#align has_compact_support.convolution_exists_at HasCompactSupport.convolutionExistsAt

theorem HasCompactSupport.convolutionExistsRight (hcg : HasCompactSupport g) (hf : LocallyIntegrable f μ)
    (hg : Continuous g) : ConvolutionExists f g L μ := by
  intro x₀
  refine' HasCompactSupport.convolutionExistsAt L _ hf hg
  refine' (hcg.comp_homeomorph (Homeomorph.subLeft x₀)).mono _
  refine' fun t => mt fun ht : g (x₀ - t) = 0 => _
  simp_rw [ht, (L _).map_zero]
#align has_compact_support.convolution_exists_right HasCompactSupport.convolutionExistsRight

theorem HasCompactSupport.convolutionExistsLeftOfContinuousRight (hcf : HasCompactSupport f)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : ConvolutionExists f g L μ := by
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

variable [HasMeasurableAdd₂ G] [HasMeasurableNeg G] [IsAddLeftInvariant μ]

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that the integrand has compact support and `g` is bounded on this support (note that
both properties hold if `g` is continuous with compact support). We also require that `f` is
integrable on the support of the integrand, and that both functions are strongly measurable.

This is a variant of `bdd_above.convolution_exists_at'` in an abelian group with a left-invariant
measure. This allows us to state the boundedness and measurability of `g` in a more natural way. -/
theorem BddAbove.convolutionExistsAt [SigmaFinite μ] {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ∥g i∥) '' ((fun t => x₀ - t) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ) (hmf : AeStronglyMeasurable f μ)
    (hmg : AeStronglyMeasurable g μ) : ConvolutionExistsAt f g x₀ L μ := by
  refine' BddAbove.convolutionExistsAt' L _ hs h2s hf hmf _
  · simp_rw [← sub_eq_neg_add, hbg]
    
  · exact hmg.mono' (quasi_measure_preserving_sub_left_of_right_invariant μ x₀).AbsolutelyContinuous
    
#align bdd_above.convolution_exists_at BddAbove.convolutionExistsAt

variable {L} [IsNegInvariant μ]

theorem convolution_exists_at_flip : ConvolutionExistsAt g f x L.flip μ ↔ ConvolutionExistsAt f g x L μ := by
  simp_rw [ConvolutionExistsAt, ← integrable_comp_sub_left (fun t => L (f t) (g (x - t))) x, sub_sub_cancel, flip_apply]
#align convolution_exists_at_flip convolution_exists_at_flip

theorem ConvolutionExistsAt.integrableSwap (h : ConvolutionExistsAt f g x L μ) :
    Integrable (fun t => L (f (x - t)) (g t)) μ := by
  convert h.comp_sub_left x
  simp_rw [sub_sub_self]
#align convolution_exists_at.integrable_swap ConvolutionExistsAt.integrableSwap

theorem convolution_exists_at_iff_integrable_swap :
    ConvolutionExistsAt f g x L μ ↔ Integrable (fun t => L (f (x - t)) (g t)) μ :=
  convolution_exists_at_flip.symm
#align convolution_exists_at_iff_integrable_swap convolution_exists_at_iff_integrable_swap

end MeasurableGroup

variable [TopologicalSpace G] [TopologicalAddGroup G] [BorelSpace G] [SecondCountableTopology G] [IsAddLeftInvariant μ]
  [IsNegInvariant μ] [SigmaCompactSpace G]

theorem HasCompactSupport.convolutionExistsLeft (hcf : HasCompactSupport f) (hf : Continuous f)
    (hg : LocallyIntegrable g μ) : ConvolutionExists f g L μ := fun x₀ =>
  convolution_exists_at_flip.mp $ hcf.convolutionExistsRight L.flip hg hf x₀
#align has_compact_support.convolution_exists_left HasCompactSupport.convolutionExistsLeft

theorem HasCompactSupport.convolutionExistsRightOfContinuousLeft (hcg : HasCompactSupport g) (hf : Continuous f)
    (hg : LocallyIntegrable g μ) : ConvolutionExists f g L μ := fun x₀ =>
  convolution_exists_at_flip.mp $ hcg.convolutionExistsLeftOfContinuousRight L.flip hg hf x₀
#align
  has_compact_support.convolution_exists_right_of_continuous_left HasCompactSupport.convolutionExistsRightOfContinuousLeft

end CommGroup

end ConvolutionExists

variable [NormedSpace ℝ F] [CompleteSpace F]

/-- The convolution of two functions `f` and `g` with respect to a continuous bilinear map `L` and
measure `μ`. It is defined to be `(f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ`. -/
noncomputable def convolution [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by exact MeasureTheory.MeasureSpace.volume) : G → F := fun x => ∫ t, L (f t) (g (x - t)) ∂μ
#align convolution convolution

-- mathport name: convolution
scoped[convolution] notation:67 f " ⋆[" L:67 ", " μ:67 "] " g:66 => convolution f g L μ

-- mathport name: convolution.volume
scoped[convolution] notation:67 f " ⋆[" L:67 "]" g:66 => convolution f g L MeasureTheory.MeasureSpace.volume

-- mathport name: convolution.lsmul
scoped[convolution]
  notation:67 f " ⋆ " g:66 => convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.MeasureSpace.volume

theorem convolution_def [Sub G] : (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ :=
  rfl
#align convolution_def convolution_def

/-- The definition of convolution where the bilinear operator is scalar multiplication.
Note: it often helps the elaborator to give the type of the convolution explicitly. -/
theorem convolution_lsmul [Sub G] {f : G → 𝕜} {g : G → F} : (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f t • g (x - t) ∂μ :=
  rfl
#align convolution_lsmul convolution_lsmul

/-- The definition of convolution where the bilinear operator is multiplication. -/
theorem convolution_mul [Sub G] [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
    (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f t * g (x - t) ∂μ :=
  rfl
#align convolution_mul convolution_mul

section Group

variable {L} [AddGroup G]

theorem smul_convolution [SmulCommClass ℝ 𝕜 F] {y : 𝕜} : y • f ⋆[L, μ] g = y • (f ⋆[L, μ] g) := by
  ext
  simp only [Pi.smul_apply, convolution_def, ← integral_smul, L.map_smul₂]
#align smul_convolution smul_convolution

theorem convolution_smul [SmulCommClass ℝ 𝕜 F] {y : 𝕜} : f ⋆[L, μ] y • g = y • (f ⋆[L, μ] g) := by
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
    (hfg' : ConvolutionExistsAt f g' x L μ) : (f ⋆[L, μ] (g + g')) x = (f ⋆[L, μ] g) x + (f ⋆[L, μ] g') x := by
  simp only [convolution_def, (L _).map_add, Pi.add_apply, integral_add hfg hfg']
#align convolution_exists_at.distrib_add ConvolutionExistsAt.distrib_add

theorem ConvolutionExists.distrib_add (hfg : ConvolutionExists f g L μ) (hfg' : ConvolutionExists f g' L μ) :
    f ⋆[L, μ] (g + g') = f ⋆[L, μ] g + f ⋆[L, μ] g' := by
  ext
  exact (hfg x).distrib_add (hfg' x)
#align convolution_exists.distrib_add ConvolutionExists.distrib_add

theorem ConvolutionExistsAt.add_distrib {x : G} (hfg : ConvolutionExistsAt f g x L μ)
    (hfg' : ConvolutionExistsAt f' g x L μ) : ((f + f') ⋆[L, μ] g) x = (f ⋆[L, μ] g) x + (f' ⋆[L, μ] g) x := by
  simp only [convolution_def, L.map_add₂, Pi.add_apply, integral_add hfg hfg']
#align convolution_exists_at.add_distrib ConvolutionExistsAt.add_distrib

theorem ConvolutionExists.add_distrib (hfg : ConvolutionExists f g L μ) (hfg' : ConvolutionExists f' g L μ) :
    (f + f') ⋆[L, μ] g = f ⋆[L, μ] g + f' ⋆[L, μ] g := by
  ext
  exact (hfg x).add_distrib (hfg' x)
#align convolution_exists.add_distrib ConvolutionExists.add_distrib

variable (L)

theorem convolution_congr [HasMeasurableAdd₂ G] [HasMeasurableNeg G] [SigmaFinite μ] [IsAddRightInvariant μ]
    (h1 : f =ᵐ[μ] f') (h2 : g =ᵐ[μ] g') : f ⋆[L, μ] g = f' ⋆[L, μ] g' := by
  ext x
  apply integral_congr_ae
  exact
    (h1.prod_mk $ h2.comp_tendsto (quasi_measure_preserving_sub_left_of_right_invariant μ x).tendsto_ae).fun_comp
      ↿fun x y => L x y
#align convolution_congr convolution_congr

theorem support_convolution_subset_swap : support (f ⋆[L, μ] g) ⊆ support g + support f := by
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
    
  · exact (h $ sub_add_cancel x t).elim
    
#align support_convolution_subset_swap support_convolution_subset_swap

section

variable [HasMeasurableAdd₂ G] [HasMeasurableNeg G] [SigmaFinite μ] [IsAddRightInvariant μ]

theorem MeasureTheory.Integrable.integrableConvolution (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (f ⋆[L, μ] g) μ :=
  (hf.convolutionIntegrand L hg).integralProdLeft
#align measure_theory.integrable.integrable_convolution MeasureTheory.Integrable.integrableConvolution

end

variable [TopologicalSpace G]

variable [TopologicalAddGroup G]

theorem HasCompactSupport.convolution [T2Space G] (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    HasCompactSupport (f ⋆[L, μ] g) :=
  is_compact_of_is_closed_subset (hcg.IsCompact.add hcf) isClosedClosure $
    closure_minimal ((support_convolution_subset_swap L).trans $ add_subset_add subset_closure subset_closure)
      (hcg.IsCompact.add hcf).IsClosed
#align has_compact_support.convolution HasCompactSupport.convolution

variable [BorelSpace G] [SecondCountableTopology G]

/-- The convolution is continuous if one function is locally integrable and the other has compact
support and is continuous. -/
theorem HasCompactSupport.continuous_convolution_right [LocallyCompactSpace G] [T2Space G] (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : Continuous (f ⋆[L, μ] g) := by
  refine' continuous_iff_continuous_at.mpr fun x₀ => _
  obtain ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x₀
  let K' := -tsupport g + K
  have hK' : IsCompact K' := hcg.neg.add hK
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t : G ∂μ, ∥L (f t) (g (x - t))∥ ≤ K'.indicator (fun t => ∥L∥ * ∥f t∥ * ⨆ i, ∥g i∥) t :=
    eventually_of_mem h2K fun x hx => eventually_of_forall $ fun t => hcg.convolution_integrand_bound_right L hg hx
  refine' continuous_at_of_dominated _ this _ _
  · exact eventually_of_forall fun x => hf.ae_strongly_measurable.convolution_integrand_snd' L hg.ae_strongly_measurable
    
  · rw [integrable_indicator_iff hK'.measurable_set]
    exact ((hf hK').norm.const_mul _).mul_const _
    
  · exact
      eventually_of_forall fun t =>
        (L.continuous₂.comp₂ continuous_const $ hg.comp $ continuous_id.sub $ by apply continuous_const).ContinuousAt
    
#align has_compact_support.continuous_convolution_right HasCompactSupport.continuous_convolution_right

/-- The convolution is continuous if one function is integrable and the other is bounded and
continuous. -/
theorem BddAbove.continuous_convolution_right_of_integrable (hbg : BddAbove (range fun x => ∥g x∥))
    (hf : Integrable f μ) (hg : Continuous g) : Continuous (f ⋆[L, μ] g) := by
  refine' continuous_iff_continuous_at.mpr fun x₀ => _
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t : G ∂μ, ∥L (f t) (g (x - t))∥ ≤ ∥L∥ * ∥f t∥ * ⨆ i, ∥g i∥ := by
    refine' eventually_of_forall fun x => eventually_of_forall $ fun t => _
    refine' (L.le_op_norm₂ _ _).trans _
    exact mul_le_mul_of_nonneg_left (le_csupr hbg $ x - t) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  refine' continuous_at_of_dominated _ this _ _
  · exact eventually_of_forall fun x => hf.ae_strongly_measurable.convolution_integrand_snd' L hg.ae_strongly_measurable
    
  · exact (hf.norm.const_mul _).mul_const _
    
  · exact
      eventually_of_forall fun t =>
        (L.continuous₂.comp₂ continuous_const $ hg.comp $ continuous_id.sub $ by apply continuous_const).ContinuousAt
    
#align bdd_above.continuous_convolution_right_of_integrable BddAbove.continuous_convolution_right_of_integrable

/-- A version of `has_compact_support.continuous_convolution_right` that works if `G` is
not locally compact but requires that `g` is integrable. -/
theorem HasCompactSupport.continuous_convolution_right_of_integrable (hcg : HasCompactSupport g) (hf : Integrable f μ)
    (hg : Continuous g) : Continuous (f ⋆[L, μ] g) :=
  (hg.norm.bdd_above_range_of_has_compact_support hcg.norm).continuous_convolution_right_of_integrable L hf hg
#align
  has_compact_support.continuous_convolution_right_of_integrable HasCompactSupport.continuous_convolution_right_of_integrable

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
theorem convolution_flip : g ⋆[L.flip, μ] f = f ⋆[L, μ] g := by
  ext1 x
  simp_rw [convolution_def]
  rw [← integral_sub_left_eq_self _ μ x]
  simp_rw [sub_sub_self, flip_apply]
#align convolution_flip convolution_flip

/-- The symmetric definition of convolution. -/
theorem convolution_eq_swap : (f ⋆[L, μ] g) x = ∫ t, L (f (x - t)) (g t) ∂μ := by
  rw [← convolution_flip]
  rfl
#align convolution_eq_swap convolution_eq_swap

/-- The symmetric definition of convolution where the bilinear operator is scalar multiplication. -/
theorem convolution_lsmul_swap {f : G → 𝕜} {g : G → F} : (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f (x - t) • g t ∂μ :=
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
    (∫ t : G, (L (f t)) (g (-x - t)) ∂μ) = ∫ t : G, (L (f (-t))) (g (x + t)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [h1, (eventually_add_left_iff μ x).2 h2] with t ht h't
      simp_rw [ht, ← h't, neg_add']
    _ = ∫ t : G, (L (f t)) (g (x - t)) ∂μ := by
      rw [← integral_neg_eq_self]
      simp only [neg_neg, ← sub_eq_add_neg]
    
#align convolution_neg_of_neg_eq convolution_neg_of_neg_eq

end Measurable

variable [TopologicalSpace G]

variable [TopologicalAddGroup G]

variable [BorelSpace G]

variable [SecondCountableTopology G]

theorem HasCompactSupport.continuous_convolution_left [LocallyCompactSpace G] [T2Space G] (hcf : HasCompactSupport f)
    (hf : Continuous f) (hg : LocallyIntegrable g μ) : Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hcf.continuous_convolution_right L.flip hg hf
#align has_compact_support.continuous_convolution_left HasCompactSupport.continuous_convolution_left

theorem BddAbove.continuous_convolution_left_of_integrable (hbf : BddAbove (range fun x => ∥f x∥)) (hf : Continuous f)
    (hg : Integrable g μ) : Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hbf.continuous_convolution_right_of_integrable L.flip hg hf
#align bdd_above.continuous_convolution_left_of_integrable BddAbove.continuous_convolution_left_of_integrable

/-- A version of `has_compact_support.continuous_convolution_left` that works if `G` is
not locally compact but requires that `g` is integrable. -/
theorem HasCompactSupport.continuous_convolution_left_of_integrable (hcf : HasCompactSupport f) (hf : Continuous f)
    (hg : Integrable g μ) : Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hcf.continuous_convolution_right_of_integrable L.flip hg hf
#align
  has_compact_support.continuous_convolution_left_of_integrable HasCompactSupport.continuous_convolution_left_of_integrable

end CommGroup

section NormedAddCommGroup

variable [SeminormedAddCommGroup G]

/-- Compute `(f ⋆ g) x₀` if the support of the `f` is within `metric.ball 0 R`, and `g` is constant
on `metric.ball x₀ R`.

We can simplify the RHS further if we assume `f` is integrable, but also if `L = (•)` or more
generally if `L` has a `antilipschitz_with`-condition. -/
theorem convolution_eq_right' {x₀ : G} {R : ℝ} (hf : support f ⊆ ball (0 : G) R) (hg : ∀ x ∈ ball x₀ R, g x = g x₀) :
    (f ⋆[L, μ] g) x₀ = ∫ t, L (f t) (g x₀) ∂μ := by
  have h2 : ∀ t, L (f t) (g (x₀ - t)) = L (f t) (g x₀) := by
    intro t
    by_cases ht:t ∈ support f
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
    (hf : support f ⊆ ball (0 : G) R) (hmg : AeStronglyMeasurable g μ) (hg : ∀ x ∈ ball x₀ R, dist (g x) z₀ ≤ ε) :
    dist ((f ⋆[L, μ] g : G → F) x₀) (∫ t, L (f t) z₀ ∂μ) ≤ (∥L∥ * ∫ x, ∥f x∥ ∂μ) * ε := by
  have hfg : ConvolutionExistsAt f g x₀ L μ := by
    refine'
      BddAbove.convolutionExistsAt L _ metric.is_open_ball.measurable_set (subset_trans _ hf) hif.integrable_on
        hif.ae_strongly_measurable hmg
    swap
    · refine' fun t => mt fun ht : f t = 0 => _
      simp_rw [ht, L.map_zero₂]
      
    rw [bdd_above_def]
    refine' ⟨∥z₀∥ + ε, _⟩
    rintro _ ⟨x, hx, rfl⟩
    refine' norm_le_norm_add_const_of_dist_le (hg x _)
    rwa [mem_ball_iff_norm, norm_sub_rev, ← mem_ball_zero_iff]
  have h2 : ∀ t, dist (L (f t) (g (x₀ - t))) (L (f t) z₀) ≤ ∥L (f t)∥ * ε := by
    intro t
    by_cases ht:t ∈ support f
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
    
  refine' (norm_integral_le_of_norm_le ((L.integrable_comp hif).norm.mul_const ε) (eventually_of_forall h2)).trans _
  rw [integral_mul_right]
  refine' mul_le_mul_of_nonneg_right _ hε
  have h3 : ∀ t, ∥L (f t)∥ ≤ ∥L∥ * ∥f t∥ := by
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
theorem dist_convolution_le {f : G → ℝ} {x₀ : G} {R ε : ℝ} {z₀ : E'} (hε : 0 ≤ ε) (hf : support f ⊆ ball (0 : G) R)
    (hnf : ∀ x, 0 ≤ f x) (hintf : (∫ x, f x ∂μ) = 1) (hmg : AeStronglyMeasurable g μ)
    (hg : ∀ x ∈ ball x₀ R, dist (g x) z₀ ≤ ε) : dist ((f ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) z₀ ≤ ε := by
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
theorem convolution_tendsto_right {ι} {g : ι → G → E'} {l : Filter ι} {x₀ : G} {z₀ : E'} {φ : ι → G → ℝ} {k : ι → G}
    (hnφ : ∀ᶠ i in l, ∀ x, 0 ≤ φ i x) (hiφ : ∀ᶠ i in l, (∫ x, φ i x ∂μ) = 1)
    -- todo: we could weaken this to "the integral tends to 1"
    (hφ : Tendsto (fun n => support (φ n)) l (𝓝 0).smallSets)
    (hmg : ∀ᶠ i in l, AeStronglyMeasurable (g i) μ) (hcg : Tendsto (uncurry g) (l ×ᶠ 𝓝 x₀) (𝓝 z₀))
    (hk : Tendsto k l (𝓝 x₀)) : Tendsto (fun i : ι => (φ i ⋆[lsmul ℝ ℝ, μ] g i : G → E') (k i)) l (𝓝 z₀) := by
  simp_rw [tendsto_small_sets_iff] at hφ
  rw [Metric.tendsto_nhds] at hcg⊢
  simp_rw [Metric.eventually_prod_nhds_iff] at hcg
  intro ε hε
  have h2ε : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨p, hp, δ, hδ, hgδ⟩ := hcg _ h2ε
  dsimp only [uncurry] at hgδ
  have h2k := hk.eventually (ball_mem_nhds x₀ $ half_pos hδ)
  have h2φ := hφ (ball (0 : G) _) $ ball_mem_nhds _ (half_pos hδ)
  filter_upwards [hp, h2k, h2φ, hnφ, hiφ, hmg] with i hpi hki hφi hnφi hiφi hmgi
  have hgi : dist (g i (k i)) z₀ < ε / 3 := hgδ hpi (hki.trans $ half_lt_self hδ)
  have h1 : ∀ x' ∈ ball (k i) (δ / 2), dist (g i x') (g i (k i)) ≤ ε / 3 + ε / 3 := by
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
    (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = g x₀ := by
  simp_rw [convolution_eq_right' _ φ.support_normed_eq.subset hg, lsmul_apply]
  exact integral_normed_smul φ μ (g x₀)
#align cont_diff_bump_of_inner.normed_convolution_eq_right ContDiffBumpOfInner.normed_convolution_eq_right

variable [IsAddLeftInvariant μ]

/-- If `φ` is a normed bump function, approximate `(φ ⋆ g) x₀` if `g` is near `g x₀` on a ball with
radius `φ.R` around `x₀`. -/
theorem dist_normed_convolution_le {x₀ : G} {ε : ℝ} (hmg : AeStronglyMeasurable g μ)
    (hg : ∀ x ∈ ball x₀ φ.r, dist (g x) (g x₀) ≤ ε) : dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) (g x₀) ≤ ε :=
  dist_convolution_le (by simp_rw [← dist_self (g x₀), hg x₀ (mem_ball_self φ.R_pos)]) φ.support_normed_eq.Subset
    φ.nonneg_normed φ.integral_normed hmg hg
#align cont_diff_bump_of_inner.dist_normed_convolution_le ContDiffBumpOfInner.dist_normed_convolution_le

/-- `(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of normed bump functions such that `(φ i).R` tends to `0` as `i` tends to `l`;
* `g i` is `mu`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ᶠ 𝓝 x₀`;
* `k i` tends to `x₀`. -/
theorem convolution_tendsto_right {ι} {φ : ι → ContDiffBumpOfInner (0 : G)} {g : ι → G → E'} {k : ι → G} {x₀ : G}
    {z₀ : E'} {l : Filter ι} (hφ : Tendsto (fun i => (φ i).r) l (𝓝 0)) (hig : ∀ᶠ i in l, AeStronglyMeasurable (g i) μ)
    (hcg : Tendsto (uncurry g) (l ×ᶠ 𝓝 x₀) (𝓝 z₀)) (hk : Tendsto k l (𝓝 x₀)) :
    Tendsto (fun i => ((fun x => (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g i : G → E') (k i)) l (𝓝 z₀) :=
  convolution_tendsto_right (eventually_of_forall $ fun i => (φ i).nonneg_normed)
    (eventually_of_forall $ fun i => (φ i).integral_normed) (tendsto_support_normed_small_sets hφ) hig hcg hk
#align cont_diff_bump_of_inner.convolution_tendsto_right ContDiffBumpOfInner.convolution_tendsto_right

/-- Special case of `cont_diff_bump_of_inner.convolution_tendsto_right` where `g` is continuous,
  and the limit is taken only in the first function. -/
theorem convolution_tendsto_right_of_continuous {ι} {φ : ι → ContDiffBumpOfInner (0 : G)} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).r) l (𝓝 0)) (hg : Continuous g) (x₀ : G) :
    Tendsto (fun i => ((fun x => (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) :=
  convolution_tendsto_right hφ (eventually_of_forall $ fun _ => hg.AeStronglyMeasurable)
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

theorem integral_convolution [HasMeasurableAdd₂ G] [HasMeasurableNeg G] [NormedSpace ℝ E] [NormedSpace ℝ E']
    [CompleteSpace E] [CompleteSpace E'] (hf : Integrable f ν) (hg : Integrable g μ) :
    (∫ x, (f ⋆[L, ν] g) x ∂μ) = L (∫ x, f x ∂ν) (∫ x, g x ∂μ) := by
  refine' (integral_integral_swap (by apply hf.convolution_integrand L hg)).trans _
  simp_rw [integral_comp_comm _ (hg.comp_sub_right _), integral_sub_right_eq_self]
  exact (L.flip (∫ x, g x ∂μ)).integral_comp_comm hf
#align integral_convolution integral_convolution

variable [HasMeasurableAdd₂ G] [IsAddRightInvariant ν] [HasMeasurableNeg G]

/-- Convolution is associative. This has a weak but inconvenient integrability condition.
See also `convolution_assoc`. -/
theorem convolution_assoc' (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z)) {x₀ : G}
    (hfg : ∀ᵐ y ∂μ, ConvolutionExistsAt f g y L ν) (hgk : ∀ᵐ x ∂ν, ConvolutionExistsAt g k x L₄ μ)
    (hi : Integrable (uncurry fun x y => (L₃ (f y)) ((L₄ (g (x - y))) (k (x₀ - x)))) (μ.Prod ν)) :
    ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀ :=
  calc
    ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = ∫ t, L₂ (∫ s, L (f s) (g (t - s)) ∂ν) (k (x₀ - t)) ∂μ := rfl
    _ = ∫ t, ∫ s, L₂ (L (f s) (g (t - s))) (k (x₀ - t)) ∂ν ∂μ :=
      integral_congr_ae (hfg.mono $ fun t ht => ((L₂.flip (k (x₀ - t))).integral_comp_comm ht).symm)
    _ = ∫ t, ∫ s, L₃ (f s) (L₄ (g (t - s)) (k (x₀ - t))) ∂ν ∂μ := by simp_rw [hL]
    _ = ∫ s, ∫ t, L₃ (f s) (L₄ (g (t - s)) (k (x₀ - t))) ∂μ ∂ν := by rw [integral_integral_swap hi]
    _ = ∫ s, ∫ u, L₃ (f s) (L₄ (g u) (k (x₀ - s - u))) ∂μ ∂ν := by
      congr
      ext t
      rw [eq_comm, ← integral_sub_right_eq_self _ t]
      · simp_rw [sub_sub_sub_cancel_right]
        
      · infer_instance
        
    _ = ∫ s, L₃ (f s) (∫ u, L₄ (g u) (k (x₀ - s - u)) ∂μ) ∂ν := by
      refine' integral_congr_ae _
      refine' ((quasi_measure_preserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht => _
      exact (L₃ (f t)).integral_comp_comm ht
    _ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀ := rfl
    
#align convolution_assoc' convolution_assoc'

/-- Convolution is associative. This requires that
* all maps are a.e. strongly measurable w.r.t one of the measures
* `f ⋆[L, ν] g` exists almost everywhere
* `∥g∥ ⋆[μ] ∥k∥` exists almost everywhere
* `∥f∥ ⋆[ν] (∥g∥ ⋆[μ] ∥k∥)` exists at `x₀` -/
theorem convolution_assoc (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z)) {x₀ : G}
    (hf : AeStronglyMeasurable f ν) (hg : AeStronglyMeasurable g μ) (hk : AeStronglyMeasurable k μ)
    (hfg : ∀ᵐ y ∂μ, ConvolutionExistsAt f g y L ν)
    (hgk : ∀ᵐ x ∂ν, ConvolutionExistsAt (fun x => ∥g x∥) (fun x => ∥k x∥) x (mul ℝ ℝ) μ)
    (hfgk : ConvolutionExistsAt (fun x => ∥f x∥) ((fun x => ∥g x∥) ⋆[mul ℝ ℝ, μ] fun x => ∥k x∥) x₀ (mul ℝ ℝ) ν) :
    ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀ := by
  refine' convolution_assoc' L L₂ L₃ L₄ hL hfg (hgk.mono $ fun x hx => hx.ofNorm L₄ hg hk) _
  -- the following is similar to `integrable.convolution_integrand`
  have h_meas : ae_strongly_measurable (uncurry fun x y => L₃ (f y) (L₄ (g x) (k (x₀ - y - x)))) (μ.prod ν) := by
    refine' L₃.ae_strongly_measurable_comp₂ hf.snd _
    refine' L₄.ae_strongly_measurable_comp₂ hg.fst _
    refine' (hk.mono' _).compMeasurable ((measurable_const.sub measurableSnd).sub measurableFst)
    refine' quasi_measure_preserving.absolutely_continuous _
    refine'
      quasi_measure_preserving.prod_of_left ((measurable_const.sub measurableSnd).sub measurableFst)
        (eventually_of_forall $ fun y => _)
    dsimp only
    exact quasi_measure_preserving_sub_left_of_right_invariant μ _
  have h2_meas : ae_strongly_measurable (fun y => ∫ x, ∥L₃ (f y) (L₄ (g x) (k (x₀ - y - x)))∥ ∂μ) ν :=
    h_meas.prod_swap.norm.integral_prod_right'
  have h3 : map (fun z : G × G => (z.1 - z.2, z.2)) (μ.prod ν) = μ.prod ν := (measure_preserving_sub_prod μ ν).map_eq
  suffices integrable (uncurry fun x y => L₃ (f y) (L₄ (g x) (k (x₀ - y - x)))) (μ.prod ν) by
    rw [← h3] at this
    convert this.comp_measurable (measurable_sub.prod_mk measurableSnd)
    ext ⟨x, y⟩
    simp_rw [uncurry, Function.comp_apply, sub_sub_sub_cancel_right]
  simp_rw [integrable_prod_iff' h_meas]
  refine'
    ⟨((quasi_measure_preserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht =>
        (L₃ (f t)).integrable_comp $ ht.ofNorm L₄ hg hk,
      _⟩
  refine'
    (hfgk.const_mul (∥L₃∥ * ∥L₄∥)).mono' h2_meas
      (((quasi_measure_preserving_sub_left_of_right_invariant ν x₀).ae hgk).mono $ fun t ht => _)
  · simp_rw [convolution_def, mul_apply', mul_mul_mul_comm ∥L₃∥ ∥L₄∥, ← integral_mul_left]
    rw [Real.norm_of_nonneg]
    · refine'
        integral_mono_of_nonneg (eventually_of_forall $ fun t => norm_nonneg _) ((ht.const_mul _).const_mul _)
          (eventually_of_forall $ fun s => _)
      refine' (L₃.le_op_norm₂ _ _).trans _
      refine' mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      rw [← mul_assoc]
      apply L₄.le_op_norm₂
      
    exact integral_nonneg fun x => norm_nonneg _
    
#align convolution_assoc convolution_assoc

end Assoc

variable [NormedAddCommGroup G] [BorelSpace G] [NormedSpace 𝕜 G]

theorem convolution_precompR_apply {g : G → E'' →L[𝕜] E'} (hf : LocallyIntegrable f μ) (hcg : HasCompactSupport g)
    (hg : Continuous g) (x₀ : G) (x : E'') : (f ⋆[L.precompR E'', μ] g) x₀ x = (f ⋆[L, μ] fun a => g a x) x₀ := by
  rcases hcg.eq_zero_or_finite_dimensional 𝕜 hg with (rfl | fin_dim)
  · simp only [convolution, Pi.zero_apply, integral_const, smul_zero, zero_apply, _root_.map_zero]
    
  skip
  have : ProperSpace G := FiniteDimensional.properIsROrC 𝕜 G
  have := hcg.convolution_exists_right (L.precompR E'' : _) hf hg x₀
  simp_rw [convolution_def, ContinuousLinearMap.integral_apply this]
  rfl
#align convolution_precompR_apply convolution_precompR_apply

variable [SigmaFinite μ] [IsAddLeftInvariant μ]

/-- Compute the total derivative of `f ⋆ g` if `g` is `C^1` with compact support and `f` is locally
integrable. To write down the total derivative as a convolution, we use
`continuous_linear_map.precompR`. -/
theorem HasCompactSupport.hasFderivAtConvolutionRight (hcg : HasCompactSupport g) (hf : LocallyIntegrable f μ)
    (hg : ContDiff 𝕜 1 g) (x₀ : G) : HasFderivAt (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x₀) x₀ := by
  rcases hcg.eq_zero_or_finite_dimensional 𝕜 hg.continuous with (rfl | fin_dim)
  · have : fderiv 𝕜 (0 : G → E') = 0 := fderiv_const (0 : E')
    simp only [this, convolution_zero, Pi.zero_apply]
    exact hasFderivAtConst (0 : F) x₀
    
  skip
  have : ProperSpace G := FiniteDimensional.properIsROrC 𝕜 G
  set L' := L.precompR G
  have h1 : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (fun t => L (f t) (g (x - t))) μ :=
    eventually_of_forall (hf.ae_strongly_measurable.convolution_integrand_snd L hg.continuous.ae_strongly_measurable)
  have h2 : ∀ x, ae_strongly_measurable (fun t => L' (f t) (fderiv 𝕜 g (x - t))) μ :=
    hf.ae_strongly_measurable.convolution_integrand_snd L' (hg.continuous_fderiv le_rfl).AeStronglyMeasurable
  have h3 : ∀ x t, HasFderivAt (fun x => g (x - t)) (fderiv 𝕜 g (x - t)) x := by
    intro x t
    simpa using
      (hg.differentiable le_rfl).DifferentiableAt.HasFderivAt.comp x ((hasFderivAtId x).sub (hasFderivAtConst t x))
  let K' := -tsupport (fderiv 𝕜 g) + closed_ball x₀ 1
  have hK' : IsCompact K' := (hcg.fderiv 𝕜).neg.add (is_compact_closed_ball x₀ 1)
  refine' hasFderivAtIntegralOfDominatedOfFderivLe zero_lt_one h1 _ (h2 x₀) _ _ _
  · exact K'.indicator fun t => ∥L'∥ * ∥f t∥ * ⨆ x, ∥fderiv 𝕜 g x∥
    
  · exact hcg.convolution_exists_right L hf hg.continuous x₀
    
  · refine' eventually_of_forall fun t x hx => _
    exact (hcg.fderiv 𝕜).convolution_integrand_bound_right L' (hg.continuous_fderiv le_rfl) (ball_subset_closed_ball hx)
    
  · rw [integrable_indicator_iff hK'.measurable_set]
    exact ((hf hK').norm.const_mul _).mul_const _
    
  · exact eventually_of_forall fun t x hx => (L _).HasFderivAt.comp x (h3 x t)
    
#align has_compact_support.has_fderiv_at_convolution_right HasCompactSupport.hasFderivAtConvolutionRight

theorem HasCompactSupport.hasFderivAtConvolutionLeft [IsNegInvariant μ] (hcf : HasCompactSupport f)
    (hf : ContDiff 𝕜 1 f) (hg : LocallyIntegrable g μ) (x₀ : G) :
    HasFderivAt (f ⋆[L, μ] g) ((fderiv 𝕜 f ⋆[L.precompL G, μ] g) x₀) x₀ := by
  simp (config := { singlePass := true }) only [← convolution_flip]
  exact hcf.has_fderiv_at_convolution_right L.flip hg hf x₀
#align has_compact_support.has_fderiv_at_convolution_left HasCompactSupport.hasFderivAtConvolutionLeft

theorem HasCompactSupport.contDiffConvolutionRight (hcg : HasCompactSupport g) (hf : LocallyIntegrable f μ)
    (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n (f ⋆[L, μ] g) := by
  rcases hcg.eq_zero_or_finite_dimensional 𝕜 hg.continuous with (rfl | fin_dim)
  · simp only [convolution_zero]
    exact contDiffZeroFun
    
  skip
  have : ProperSpace G := FiniteDimensional.properIsROrC 𝕜 G
  induction' n using Enat.nat_induction with n ih ih generalizing g
  · rw [cont_diff_zero] at hg⊢
    exact hcg.continuous_convolution_right L hf hg
    
  · have h : ∀ x, HasFderivAt (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x) x :=
      hcg.has_fderiv_at_convolution_right L hf hg.one_of_succ
    rw [cont_diff_succ_iff_fderiv_apply]
    constructor
    · exact fun x₀ => ⟨_, h x₀⟩
      
    · simp_rw [fderiv_eq h, convolution_precompR_apply L hf (hcg.fderiv 𝕜) (hg.one_of_succ.continuous_fderiv le_rfl)]
      intro x
      refine' ih _ _
      · refine'
          @HasCompactSupport.comp_left _ _ _ _ _ _ (fun G : _ →L[𝕜] _ => G x) _ (hcg.fderiv 𝕜)
            (ContinuousLinearMap.zero_apply x)
        
      · revert x
        rw [← cont_diff_clm_apply]
        exact (cont_diff_succ_iff_fderiv.mp hg).2
        
      
    
  · rw [cont_diff_top] at hg⊢
    exact fun n => ih n hcg (hg n)
    
#align has_compact_support.cont_diff_convolution_right HasCompactSupport.contDiffConvolutionRight

theorem HasCompactSupport.contDiffConvolutionLeft [IsNegInvariant μ] (hcf : HasCompactSupport f) (hf : ContDiff 𝕜 n f)
    (hg : LocallyIntegrable g μ) : ContDiff 𝕜 n (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hcf.cont_diff_convolution_right L.flip hg hf
#align has_compact_support.cont_diff_convolution_left HasCompactSupport.contDiffConvolutionLeft

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

theorem HasCompactSupport.hasDerivAtConvolutionRight (hf : LocallyIntegrable f₀ μ) (hcg : HasCompactSupport g₀)
    (hg : ContDiff 𝕜 1 g₀) (x₀ : 𝕜) : HasDerivAt (f₀ ⋆[L, μ] g₀) ((f₀ ⋆[L, μ] deriv g₀) x₀) x₀ := by
  convert (hcg.has_fderiv_at_convolution_right L hf hg x₀).HasDerivAt
  rw [convolution_precompR_apply L hf (hcg.fderiv 𝕜) (hg.continuous_fderiv le_rfl)]
  rfl
#align has_compact_support.has_deriv_at_convolution_right HasCompactSupport.hasDerivAtConvolutionRight

theorem HasCompactSupport.hasDerivAtConvolutionLeft [IsNegInvariant μ] (hcf : HasCompactSupport f₀)
    (hf : ContDiff 𝕜 1 f₀) (hg : LocallyIntegrable g₀ μ) (x₀ : 𝕜) :
    HasDerivAt (f₀ ⋆[L, μ] g₀) ((deriv f₀ ⋆[L, μ] g₀) x₀) x₀ := by
  simp (config := { singlePass := true }) only [← convolution_flip]
  exact hcf.has_deriv_at_convolution_right L.flip hg hf x₀
#align has_compact_support.has_deriv_at_convolution_left HasCompactSupport.hasDerivAtConvolutionLeft

end Real

