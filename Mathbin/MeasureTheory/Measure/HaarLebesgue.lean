/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.measure.haar_lebesgue
! leanprover-community/mathlib commit 57ac39bd365c2f80589a700f9fbb664d3a1a30c2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.Lebesgue
import Mathbin.MeasureTheory.Measure.Haar
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.Analysis.NormedSpace.Pointwise
import Mathbin.MeasureTheory.Group.Pointwise
import Mathbin.MeasureTheory.Measure.Doubling

/-!
# Relationship between the Haar and Lebesgue measures

We prove that the Haar measure and Lebesgue measure are equal on `ℝ` and on `ℝ^ι`, in
`measure_theory.add_haar_measure_eq_volume` and `measure_theory.add_haar_measure_eq_volume_pi`.

We deduce basic properties of any Haar measure on a finite dimensional real vector space:
* `map_linear_map_add_haar_eq_smul_add_haar`: a linear map rescales the Haar measure by the
  absolute value of its determinant.
* `add_haar_preimage_linear_map` : when `f` is a linear map with nonzero determinant, the measure
  of `f ⁻¹' s` is the measure of `s` multiplied by the absolute value of the inverse of the
  determinant of `f`.
* `add_haar_image_linear_map` : when `f` is a linear map, the measure of `f '' s` is the
  measure of `s` multiplied by the absolute value of the determinant of `f`.
* `add_haar_submodule` : a strict submodule has measure `0`.
* `add_haar_smul` : the measure of `r • s` is `|r| ^ dim * μ s`.
* `add_haar_ball`: the measure of `ball x r` is `r ^ dim * μ (ball 0 1)`.
* `add_haar_closed_ball`: the measure of `closed_ball x r` is `r ^ dim * μ (ball 0 1)`.
* `add_haar_sphere`: spheres have zero measure.

This makes it possible to associate a Lebesgue measure to an `n`-alternating map in dimension `n`.
This measure is called `alternating_map.measure`. Its main property is
`ω.measure_parallelepiped v`, stating that the associated measure of the parallelepiped spanned
by vectors `v₁, ..., vₙ` is given by `|ω v|`.

We also show that a Lebesgue density point `x` of a set `s` (with respect to closed balls) has
density one for the rescaled copies `{x} + r • t` of a given set `t` with positive measure, in
`tendsto_add_haar_inter_smul_one_of_density_one`. In particular, `s` intersects `{x} + r • t` for
small `r`, see `eventually_nonempty_inter_smul_of_density_one`.
-/


open TopologicalSpace Set Filter Metric

open ENNReal Pointwise Topology NNReal

/-- The interval `[0,1]` as a compact set with non-empty interior. -/
def TopologicalSpace.PositiveCompacts.icc01 : PositiveCompacts ℝ
    where
  carrier := Icc 0 1
  is_compact' := isCompact_Icc
  interior_nonempty' := by simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]
#align topological_space.positive_compacts.Icc01 TopologicalSpace.PositiveCompacts.icc01

universe u

/-- The set `[0,1]^ι` as a compact set with non-empty interior. -/
def TopologicalSpace.PositiveCompacts.piIcc01 (ι : Type _) [Fintype ι] : PositiveCompacts (ι → ℝ)
    where
  carrier := pi univ fun i => Icc 0 1
  is_compact' := isCompact_univ_pi fun i => isCompact_Icc
  interior_nonempty' := by
    simp only [interior_pi_set, Set.toFinite, interior_Icc, univ_pi_nonempty_iff, nonempty_Ioo,
      imp_true_iff, zero_lt_one]
#align topological_space.positive_compacts.pi_Icc01 TopologicalSpace.PositiveCompacts.piIcc01

namespace MeasureTheory

open Measure TopologicalSpace.PositiveCompacts FiniteDimensional

/-!
### The Lebesgue measure is a Haar measure on `ℝ` and on `ℝ^ι`.
-/


/-- The Haar measure equals the Lebesgue measure on `ℝ`. -/
theorem add_haar_measure_eq_volume : add_haar_measure icc01 = volume :=
  by
  convert (add_haar_measure_unique volume Icc01).symm
  simp [Icc01]
#align measure_theory.add_haar_measure_eq_volume MeasureTheory.add_haar_measure_eq_volume

/-- The Haar measure equals the Lebesgue measure on `ℝ^ι`. -/
theorem add_haar_measure_eq_volume_pi (ι : Type _) [Fintype ι] :
    add_haar_measure (piIcc01 ι) = volume :=
  by
  convert (add_haar_measure_unique volume (pi_Icc01 ι)).symm
  simp only [pi_Icc01, volume_pi_pi fun i => Icc (0 : ℝ) 1, positive_compacts.coe_mk,
    compacts.coe_mk, Finset.prod_const_one, ENNReal.ofReal_one, Real.volume_Icc, one_smul, sub_zero]
#align measure_theory.add_haar_measure_eq_volume_pi MeasureTheory.add_haar_measure_eq_volume_pi

instance isAddHaarMeasureVolumePi (ι : Type _) [Fintype ι] :
    IsAddHaarMeasure (volume : Measure (ι → ℝ)) :=
  by
  rw [← add_haar_measure_eq_volume_pi]
  infer_instance
#align measure_theory.is_add_haar_measure_volume_pi MeasureTheory.isAddHaarMeasureVolumePi

namespace Measure

/-!
### Strict subspaces have zero measure
-/


/-- If a set is disjoint of its translates by infinitely many bounded vectors, then it has measure
zero. This auxiliary lemma proves this assuming additionally that the set is bounded. -/
theorem add_haar_eq_zero_of_disjoint_translates_aux {E : Type _} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [IsAddHaarMeasure μ] {s : Set E} (u : ℕ → E) (sb : Bounded s) (hu : Bounded (range u))
    (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) : μ s = 0 :=
  by
  by_contra h
  apply lt_irrefl ∞
  calc
    ∞ = ∑' n : ℕ, μ s := (ENNReal.tsum_const_eq_top_of_ne_zero h).symm
    _ = ∑' n : ℕ, μ ({u n} + s) := by
      congr 1
      ext1 n
      simp only [image_add_left, measure_preimage_add, singleton_add]
    _ = μ (⋃ n, {u n} + s) := by
      rw [measure_Union hs fun n => by
          simpa only [image_add_left, singleton_add] using measurable_id.const_add _ h's]
    _ = μ (range u + s) := by rw [← Union_add, Union_singleton_eq_range]
    _ < ∞ := bounded.measure_lt_top (hu.add sb)
    
#align measure_theory.measure.add_haar_eq_zero_of_disjoint_translates_aux MeasureTheory.Measure.add_haar_eq_zero_of_disjoint_translates_aux

/-- If a set is disjoint of its translates by infinitely many bounded vectors, then it has measure
zero. -/
theorem add_haar_eq_zero_of_disjoint_translates {E : Type _} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [IsAddHaarMeasure μ] {s : Set E} (u : ℕ → E) (hu : Bounded (range u))
    (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) : μ s = 0 :=
  by
  suffices H : ∀ R, μ (s ∩ closed_ball 0 R) = 0
  · apply le_antisymm _ (zero_le _)
    calc
      μ s ≤ ∑' n : ℕ, μ (s ∩ closed_ball 0 n) :=
        by
        conv_lhs => rw [← Union_inter_closed_ball_nat s 0]
        exact measure_Union_le _
      _ = 0 := by simp only [H, tsum_zero]
      
  intro R
  apply
    add_haar_eq_zero_of_disjoint_translates_aux μ u
      (bounded.mono (inter_subset_right _ _) bounded_closed_ball) hu _
      (h's.inter measurableSet_closedBall)
  apply pairwise_disjoint_mono hs fun n => _
  exact add_subset_add (subset.refl _) (inter_subset_left _ _)
#align measure_theory.measure.add_haar_eq_zero_of_disjoint_translates MeasureTheory.Measure.add_haar_eq_zero_of_disjoint_translates

/-- A strict vector subspace has measure zero. -/
theorem add_haar_submodule {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] (s : Submodule ℝ E)
    (hs : s ≠ ⊤) : μ s = 0 :=
  by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ s := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne.def, not_forall] using hs
  obtain ⟨c, cpos, cone⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  have A : bounded (range fun n : ℕ => c ^ n • x) :=
    haveI : tendsto (fun n : ℕ => c ^ n • x) at_top (𝓝 ((0 : ℝ) • x)) :=
      (tendsto_pow_atTop_nhds_0_of_lt_1 cpos.le cone).smul_const x
    bounded_range_of_tendsto _ this
  apply
    add_haar_eq_zero_of_disjoint_translates μ _ A _
      (Submodule.closed_of_finiteDimensional s).MeasurableSet
  intro m n hmn
  simp only [Function.onFun, image_add_left, singleton_add, disjoint_left, mem_preimage,
    SetLike.mem_coe]
  intro y hym hyn
  have A : (c ^ n - c ^ m) • x ∈ s := by
    convert s.sub_mem hym hyn
    simp only [sub_smul, neg_sub_neg, add_sub_add_right_eq_sub]
  have H : c ^ n - c ^ m ≠ 0 := by
    simpa only [sub_eq_zero, Ne.def] using (strictAnti_pow cpos cone).Injective.Ne hmn.symm
  have : x ∈ s := by
    convert s.smul_mem (c ^ n - c ^ m)⁻¹ A
    rw [smul_smul, inv_mul_cancel H, one_smul]
  exact hx this
#align measure_theory.measure.add_haar_submodule MeasureTheory.Measure.add_haar_submodule

/-- A strict affine subspace has measure zero. -/
theorem add_haar_affineSubspace {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
    (s : AffineSubspace ℝ E) (hs : s ≠ ⊤) : μ s = 0 :=
  by
  rcases s.eq_bot_or_nonempty with (rfl | hne)
  · rw [AffineSubspace.bot_coe, measure_empty]
  rw [Ne.def, ← AffineSubspace.direction_eq_top_iff_of_nonempty hne] at hs
  rcases hne with ⟨x, hx : x ∈ s⟩
  simpa only [AffineSubspace.coe_direction_eq_vsub_set_right hx, vsub_eq_sub, sub_eq_add_neg,
    image_add_right, neg_neg, measure_preimage_add_right] using add_haar_submodule μ s.direction hs
#align measure_theory.measure.add_haar_affine_subspace MeasureTheory.Measure.add_haar_affineSubspace

/-!
### Applying a linear map rescales Haar measure by the determinant

We first prove this on `ι → ℝ`, using that this is already known for the product Lebesgue
measure (thanks to matrices computations). Then, we extend this to any finite-dimensional real
vector space by using a linear equiv with a space of the form `ι → ℝ`, and arguing that such a
linear equiv maps Haar measure to Haar measure.
-/


theorem map_linearMap_add_haar_pi_eq_smul_add_haar {ι : Type _} [Finite ι] {f : (ι → ℝ) →ₗ[ℝ] ι → ℝ}
    (hf : f.det ≠ 0) (μ : Measure (ι → ℝ)) [IsAddHaarMeasure μ] :
    Measure.map f μ = ENNReal.ofReal (abs f.det⁻¹) • μ :=
  by
  cases nonempty_fintype ι
  /- We have already proved the result for the Lebesgue product measure, using matrices.
    We deduce it for any Haar measure by uniqueness (up to scalar multiplication). -/
  have := add_haar_measure_unique μ (pi_Icc01 ι)
  rw [this, add_haar_measure_eq_volume_pi, measure.map_smul,
    Real.map_linearMap_volume_pi_eq_smul_volume_pi hf, smul_comm]
#align measure_theory.measure.map_linear_map_add_haar_pi_eq_smul_add_haar MeasureTheory.Measure.map_linearMap_add_haar_pi_eq_smul_add_haar

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {F : Type _} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

theorem map_linearMap_add_haar_eq_smul_add_haar {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) :
    Measure.map f μ = ENNReal.ofReal (abs f.det⁻¹) • μ :=
  by
  -- we reduce to the case of `E = ι → ℝ`, for which we have already proved the result using
  -- matrices in `map_linear_map_add_haar_pi_eq_smul_add_haar`.
  let ι := Fin (finrank ℝ E)
  haveI : FiniteDimensional ℝ (ι → ℝ) := by infer_instance
  have : finrank ℝ E = finrank ℝ (ι → ℝ) := by simp
  have e : E ≃ₗ[ℝ] ι → ℝ := linear_equiv.of_finrank_eq E (ι → ℝ) this
  -- next line is to avoid `g` getting reduced by `simp`.
  obtain ⟨g, hg⟩ : ∃ g, g = (e : E →ₗ[ℝ] ι → ℝ).comp (f.comp (e.symm : (ι → ℝ) →ₗ[ℝ] E)) := ⟨_, rfl⟩
  have gdet : g.det = f.det := by
    rw [hg]
    exact LinearMap.det_conj f e
  rw [← gdet] at hf⊢
  have fg : f = (e.symm : (ι → ℝ) →ₗ[ℝ] E).comp (g.comp (e : E →ₗ[ℝ] ι → ℝ)) :=
    by
    ext x
    simp only [LinearEquiv.coe_coe, Function.comp_apply, LinearMap.coe_comp,
      LinearEquiv.symm_apply_apply, hg]
  simp only [fg, LinearEquiv.coe_coe, LinearMap.coe_comp]
  have Ce : Continuous e := (e : E →ₗ[ℝ] ι → ℝ).continuous_of_finiteDimensional
  have Cg : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have Cesymm : Continuous e.symm := (e.symm : (ι → ℝ) →ₗ[ℝ] E).continuous_of_finiteDimensional
  rw [← map_map Cesymm.measurable (Cg.comp Ce).Measurable, ← map_map Cg.measurable Ce.measurable]
  haveI : is_add_haar_measure (map e μ) := (e : E ≃+ (ι → ℝ)).is_add_haar_measure_map μ Ce Cesymm
  have ecomp : e.symm ∘ e = id := by
    ext x
    simp only [id.def, Function.comp_apply, LinearEquiv.symm_apply_apply]
  rw [map_linear_map_add_haar_pi_eq_smul_add_haar hf (map e μ), measure.map_smul,
    map_map Cesymm.measurable Ce.measurable, ecomp, measure.map_id]
#align measure_theory.measure.map_linear_map_add_haar_eq_smul_add_haar MeasureTheory.Measure.map_linearMap_add_haar_eq_smul_add_haar

/-- The preimage of a set `s` under a linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem add_haar_preimage_linearMap {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal (abs f.det⁻¹) * μ s :=
  calc
    μ (f ⁻¹' s) = Measure.map f μ s :=
      ((f.equivOfDetNeZero hf).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.map_apply
          s).symm
    _ = ENNReal.ofReal (abs f.det⁻¹) * μ s :=
      by
      rw [map_linear_map_add_haar_eq_smul_add_haar μ hf]
      rfl
    
#align measure_theory.measure.add_haar_preimage_linear_map MeasureTheory.Measure.add_haar_preimage_linearMap

/-- The preimage of a set `s` under a continuous linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem add_haar_preimage_continuousLinearMap {f : E →L[ℝ] E}
    (hf : LinearMap.det (f : E →ₗ[ℝ] E) ≠ 0) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal (abs (LinearMap.det (f : E →ₗ[ℝ] E))⁻¹) * μ s :=
  add_haar_preimage_linearMap μ hf s
#align measure_theory.measure.add_haar_preimage_continuous_linear_map MeasureTheory.Measure.add_haar_preimage_continuousLinearMap

/-- The preimage of a set `s` under a linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem add_haar_preimage_linearEquiv (f : E ≃ₗ[ℝ] E) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal (abs (f.symm : E →ₗ[ℝ] E).det) * μ s :=
  by
  have A : (f : E →ₗ[ℝ] E).det ≠ 0 := (LinearEquiv.isUnit_det' f).NeZero
  convert add_haar_preimage_linear_map μ A s
  simp only [LinearEquiv.det_coe_symm]
#align measure_theory.measure.add_haar_preimage_linear_equiv MeasureTheory.Measure.add_haar_preimage_linearEquiv

/-- The preimage of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem add_haar_preimage_continuousLinearEquiv (f : E ≃L[ℝ] E) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal (abs (f.symm : E →ₗ[ℝ] E).det) * μ s :=
  add_haar_preimage_linearEquiv μ _ s
#align measure_theory.measure.add_haar_preimage_continuous_linear_equiv MeasureTheory.Measure.add_haar_preimage_continuousLinearEquiv

/-- The image of a set `s` under a linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
theorem add_haar_image_linearMap (f : E →ₗ[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal (abs f.det) * μ s :=
  by
  rcases ne_or_eq f.det 0 with (hf | hf)
  · let g := (f.equiv_of_det_ne_zero hf).toContinuousLinearEquiv
    change μ (g '' s) = _
    rw [ContinuousLinearEquiv.image_eq_preimage g s, add_haar_preimage_continuous_linear_equiv]
    congr
    ext x
    simp only [LinearEquiv.coe_toContinuousLinearEquiv, LinearEquiv.ofIsUnitDet_apply,
      LinearEquiv.coe_coe, ContinuousLinearEquiv.symm_symm]
  · simp only [hf, zero_mul, ENNReal.ofReal_zero, abs_zero]
    have : μ f.range = 0 := add_haar_submodule μ _ (LinearMap.range_lt_top_of_det_eq_zero hf).Ne
    exact le_antisymm (le_trans (measure_mono (image_subset_range _ _)) this.le) (zero_le _)
#align measure_theory.measure.add_haar_image_linear_map MeasureTheory.Measure.add_haar_image_linearMap

/-- The image of a set `s` under a continuous linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
theorem add_haar_image_continuousLinearMap (f : E →L[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal (abs (f : E →ₗ[ℝ] E).det) * μ s :=
  add_haar_image_linearMap μ _ s
#align measure_theory.measure.add_haar_image_continuous_linear_map MeasureTheory.Measure.add_haar_image_continuousLinearMap

/-- The image of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
theorem add_haar_image_continuousLinearEquiv (f : E ≃L[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal (abs (f : E →ₗ[ℝ] E).det) * μ s :=
  μ.add_haar_image_linearMap (f : E →ₗ[ℝ] E) s
#align measure_theory.measure.add_haar_image_continuous_linear_equiv MeasureTheory.Measure.add_haar_image_continuousLinearEquiv

/-!
### Basic properties of Haar measures on real vector spaces
-/


theorem map_add_haar_smul {r : ℝ} (hr : r ≠ 0) :
    Measure.map ((· • ·) r) μ = ENNReal.ofReal (abs (r ^ finrank ℝ E)⁻¹) • μ :=
  by
  let f : E →ₗ[ℝ] E := r • 1
  change measure.map f μ = _
  have hf : f.det ≠ 0 :=
    by
    simp only [mul_one, LinearMap.det_smul, Ne.def, MonoidHom.map_one]
    intro h
    exact hr (pow_eq_zero h)
  simp only [map_linear_map_add_haar_eq_smul_add_haar μ hf, mul_one, LinearMap.det_smul,
    MonoidHom.map_one]
#align measure_theory.measure.map_add_haar_smul MeasureTheory.Measure.map_add_haar_smul

@[simp]
theorem add_haar_preimage_smul {r : ℝ} (hr : r ≠ 0) (s : Set E) :
    μ ((· • ·) r ⁻¹' s) = ENNReal.ofReal (abs (r ^ finrank ℝ E)⁻¹) * μ s :=
  calc
    μ ((· • ·) r ⁻¹' s) = Measure.map ((· • ·) r) μ s :=
      ((Homeomorph.smul (isUnit_iff_ne_zero.2 hr).Unit).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs (r ^ finrank ℝ E)⁻¹) * μ s :=
      by
      rw [map_add_haar_smul μ hr]
      rfl
    
#align measure_theory.measure.add_haar_preimage_smul MeasureTheory.Measure.add_haar_preimage_smul

/-- Rescaling a set by a factor `r` multiplies its measure by `abs (r ^ dim)`. -/
@[simp]
theorem add_haar_smul (r : ℝ) (s : Set E) :
    μ (r • s) = ENNReal.ofReal (abs (r ^ finrank ℝ E)) * μ s :=
  by
  rcases ne_or_eq r 0 with (h | rfl)
  · rw [← preimage_smul_inv₀ h, add_haar_preimage_smul μ (inv_ne_zero h), inv_pow, inv_inv]
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp only [measure_empty, mul_zero, smul_set_empty]
  rw [zero_smul_set hs, ← singleton_zero]
  by_cases h : finrank ℝ E = 0
  · haveI : Subsingleton E := finrank_zero_iff.1 h
    simp only [h, one_mul, ENNReal.ofReal_one, abs_one, Subsingleton.eq_univ_of_nonempty hs,
      pow_zero, Subsingleton.eq_univ_of_nonempty (singleton_nonempty (0 : E))]
  · haveI : Nontrivial E := nontrivial_of_finrank_pos (bot_lt_iff_ne_bot.2 h)
    simp only [h, zero_mul, ENNReal.ofReal_zero, abs_zero, Ne.def, not_false_iff, zero_pow',
      measure_singleton]
#align measure_theory.measure.add_haar_smul MeasureTheory.Measure.add_haar_smul

@[simp]
theorem add_haar_image_homothety (x : E) (r : ℝ) (s : Set E) :
    μ (AffineMap.homothety x r '' s) = ENNReal.ofReal (abs (r ^ finrank ℝ E)) * μ s :=
  calc
    μ (AffineMap.homothety x r '' s) = μ ((fun y => y + x) '' (r • (fun y => y + -x) '' s)) :=
      by
      simp only [← image_smul, image_image, ← sub_eq_add_neg]
      rfl
    _ = ENNReal.ofReal (abs (r ^ finrank ℝ E)) * μ s := by
      simp only [image_add_right, measure_preimage_add_right, add_haar_smul]
    
#align measure_theory.measure.add_haar_image_homothety MeasureTheory.Measure.add_haar_image_homothety

/-- The integral of `f (R • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
theorem integral_comp_smul (f : E → F) (R : ℝ) :
    (∫ x, f (R • x) ∂μ) = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ :=
  by
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp only [zero_smul, integral_const]
    rcases Nat.eq_zero_or_pos (finrank ℝ E) with (hE | hE)
    · have : Subsingleton E := finrank_zero_iff.1 hE
      have : f = fun x => f 0 := by
        ext x
        rw [Subsingleton.elim x 0]
      conv_rhs => rw [this]
      simp only [hE, pow_zero, inv_one, abs_one, one_smul, integral_const]
    · have : Nontrivial E := finrank_pos_iff.1 hE
      simp only [zero_pow hE, measure_univ_of_is_add_left_invariant, ENNReal.top_toReal, zero_smul,
        inv_zero, abs_zero]
  ·
    calc
      (∫ x, f (R • x) ∂μ) = ∫ y, f y ∂measure.map (fun x => R • x) μ :=
        (integral_map_equiv (Homeomorph.smul (isUnit_iff_ne_zero.2 hR).Unit).toMeasurableEquiv
            f).symm
      _ = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ := by
        simp only [map_add_haar_smul μ hR, integral_smul_measure, ENNReal.toReal_ofReal, abs_nonneg]
      
#align measure_theory.measure.integral_comp_smul MeasureTheory.Measure.integral_comp_smul

/-- The integral of `f (R • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
theorem integral_comp_smul_of_nonneg (f : E → F) (R : ℝ) {hR : 0 ≤ R} :
    (∫ x, f (R • x) ∂μ) = (R ^ finrank ℝ E)⁻¹ • ∫ x, f x ∂μ := by
  rw [integral_comp_smul μ f R, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR _))]
#align measure_theory.measure.integral_comp_smul_of_nonneg MeasureTheory.Measure.integral_comp_smul_of_nonneg

/-- The integral of `f (R⁻¹ • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
theorem integral_comp_inv_smul (f : E → F) (R : ℝ) :
    (∫ x, f (R⁻¹ • x) ∂μ) = |R ^ finrank ℝ E| • ∫ x, f x ∂μ := by
  rw [integral_comp_smul μ f R⁻¹, inv_pow, inv_inv]
#align measure_theory.measure.integral_comp_inv_smul MeasureTheory.Measure.integral_comp_inv_smul

/-- The integral of `f (R⁻¹ • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
theorem integral_comp_inv_smul_of_nonneg (f : E → F) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x, f (R⁻¹ • x) ∂μ) = R ^ finrank ℝ E • ∫ x, f x ∂μ := by
  rw [integral_comp_inv_smul μ f R, abs_of_nonneg (pow_nonneg hR _)]
#align measure_theory.measure.integral_comp_inv_smul_of_nonneg MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg

/-! We don't need to state `map_add_haar_neg` here, because it has already been proved for
general Haar measures on general commutative groups. -/


/-! ### Measure of balls -/


theorem add_haar_ball_center {E : Type _} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : ℝ) : μ (ball x r) = μ (ball (0 : E) r) :=
  by
  have : ball (0 : E) r = (· + ·) x ⁻¹' ball x r := by simp [preimage_add_ball]
  rw [this, measure_preimage_add]
#align measure_theory.measure.add_haar_ball_center MeasureTheory.Measure.add_haar_ball_center

theorem add_haar_closedBall_center {E : Type _} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : ℝ) :
    μ (closedBall x r) = μ (closedBall (0 : E) r) :=
  by
  have : closed_ball (0 : E) r = (· + ·) x ⁻¹' closed_ball x r := by simp [preimage_add_closedBall]
  rw [this, measure_preimage_add]
#align measure_theory.measure.add_haar_closed_ball_center MeasureTheory.Measure.add_haar_closedBall_center

theorem add_haar_ball_mul_of_pos (x : E) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    μ (ball x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 s) :=
  by
  have : ball (0 : E) (r * s) = r • ball 0 s := by
    simp only [smul_ball hr.ne' (0 : E) s, Real.norm_eq_abs, abs_of_nonneg hr.le, smul_zero]
  simp only [this, add_haar_smul, abs_of_nonneg hr.le, add_haar_ball_center, abs_pow]
#align measure_theory.measure.add_haar_ball_mul_of_pos MeasureTheory.Measure.add_haar_ball_mul_of_pos

theorem add_haar_ball_of_pos (x : E) {r : ℝ} (hr : 0 < r) :
    μ (ball x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rw [← add_haar_ball_mul_of_pos μ x hr, mul_one]
#align measure_theory.measure.add_haar_ball_of_pos MeasureTheory.Measure.add_haar_ball_of_pos

theorem add_haar_ball_mul [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    μ (ball x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 s) :=
  by
  rcases LE.le.eq_or_lt hr with (h | h)
  · simp only [← h, zero_pow finrank_pos, measure_empty, zero_mul, ENNReal.ofReal_zero, ball_zero]
  · exact add_haar_ball_mul_of_pos μ x h s
#align measure_theory.measure.add_haar_ball_mul MeasureTheory.Measure.add_haar_ball_mul

theorem add_haar_ball [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (ball x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rw [← add_haar_ball_mul μ x hr, mul_one]
#align measure_theory.measure.add_haar_ball MeasureTheory.Measure.add_haar_ball

theorem add_haar_closedBall_mul_of_pos (x : E) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    μ (closedBall x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 s) :=
  by
  have : closed_ball (0 : E) (r * s) = r • closed_ball 0 s := by
    simp [smul_closed_ball' hr.ne' (0 : E), abs_of_nonneg hr.le]
  simp only [this, add_haar_smul, abs_of_nonneg hr.le, add_haar_closed_ball_center, abs_pow]
#align measure_theory.measure.add_haar_closed_ball_mul_of_pos MeasureTheory.Measure.add_haar_closedBall_mul_of_pos

theorem add_haar_closedBall_mul (x : E) {r : ℝ} (hr : 0 ≤ r) {s : ℝ} (hs : 0 ≤ s) :
    μ (closedBall x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 s) :=
  by
  have : closed_ball (0 : E) (r * s) = r • closed_ball 0 s := by
    simp [smul_closedBall r (0 : E) hs, abs_of_nonneg hr]
  simp only [this, add_haar_smul, abs_of_nonneg hr, add_haar_closed_ball_center, abs_pow]
#align measure_theory.measure.add_haar_closed_ball_mul MeasureTheory.Measure.add_haar_closedBall_mul

/-- The measure of a closed ball can be expressed in terms of the measure of the closed unit ball.
Use instead `add_haar_closed_ball`, which uses the measure of the open unit ball as a standard
form. -/
theorem add_haar_closed_ball' (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (closedBall x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 1) := by
  rw [← add_haar_closed_ball_mul μ x hr zero_le_one, mul_one]
#align measure_theory.measure.add_haar_closed_ball' MeasureTheory.Measure.add_haar_closed_ball'

theorem add_haar_closed_unit_ball_eq_add_haar_unit_ball : μ (closedBall (0 : E) 1) = μ (ball 0 1) :=
  by
  apply le_antisymm _ (measure_mono ball_subset_closed_ball)
  have A :
    tendsto (fun r : ℝ => ENNReal.ofReal (r ^ finrank ℝ E) * μ (closed_ball (0 : E) 1)) (𝓝[<] 1)
      (𝓝 (ENNReal.ofReal (1 ^ finrank ℝ E) * μ (closed_ball (0 : E) 1))) :=
    by
    refine' ENNReal.Tendsto.mul _ (by simp) tendsto_const_nhds (by simp)
    exact ENNReal.tendsto_ofReal ((tendsto_id'.2 nhdsWithin_le_nhds).pow _)
  simp only [one_pow, one_mul, ENNReal.ofReal_one] at A
  refine' le_of_tendsto A _
  refine' mem_nhdsWithin_Iio_iff_exists_Ioo_subset.2 ⟨(0 : ℝ), by simp, fun r hr => _⟩
  dsimp
  rw [← add_haar_closed_ball' μ (0 : E) hr.1.le]
  exact measure_mono (closed_ball_subset_ball hr.2)
#align measure_theory.measure.add_haar_closed_unit_ball_eq_add_haar_unit_ball MeasureTheory.Measure.add_haar_closed_unit_ball_eq_add_haar_unit_ball

theorem add_haar_closedBall (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (closedBall x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rw [add_haar_closed_ball' μ x hr, add_haar_closed_unit_ball_eq_add_haar_unit_ball]
#align measure_theory.measure.add_haar_closed_ball MeasureTheory.Measure.add_haar_closedBall

theorem add_haar_closedBall_eq_add_haar_ball [Nontrivial E] (x : E) (r : ℝ) :
    μ (closedBall x r) = μ (ball x r) :=
  by
  by_cases h : r < 0
  · rw [metric.closed_ball_eq_empty.mpr h, metric.ball_eq_empty.mpr h.le]
  push_neg  at h
  rw [add_haar_closed_ball μ x h, add_haar_ball μ x h]
#align measure_theory.measure.add_haar_closed_ball_eq_add_haar_ball MeasureTheory.Measure.add_haar_closedBall_eq_add_haar_ball

theorem add_haar_sphere_of_ne_zero (x : E) {r : ℝ} (hr : r ≠ 0) : μ (sphere x r) = 0 :=
  by
  rcases hr.lt_or_lt with (h | h)
  · simp only [empty_diff, measure_empty, ← closed_ball_diff_ball, closed_ball_eq_empty.2 h]
  ·
    rw [← closed_ball_diff_ball,
        measure_diff ball_subset_closed_ball measurableSet_ball measure_ball_lt_top.ne,
        add_haar_ball_of_pos μ _ h, add_haar_closed_ball μ _ h.le, tsub_self] <;>
      infer_instance
#align measure_theory.measure.add_haar_sphere_of_ne_zero MeasureTheory.Measure.add_haar_sphere_of_ne_zero

theorem add_haar_sphere [Nontrivial E] (x : E) (r : ℝ) : μ (sphere x r) = 0 :=
  by
  rcases eq_or_ne r 0 with (rfl | h)
  · rw [sphere_zero, measure_singleton]
  · exact add_haar_sphere_of_ne_zero μ x h
#align measure_theory.measure.add_haar_sphere MeasureTheory.Measure.add_haar_sphere

theorem add_haar_singleton_add_smul_div_singleton_add_smul {r : ℝ} (hr : r ≠ 0) (x y : E)
    (s t : Set E) : μ ({x} + r • s) / μ ({y} + r • t) = μ s / μ t :=
  calc
    μ ({x} + r • s) / μ ({y} + r • t) =
        ENNReal.ofReal (|r| ^ finrank ℝ E) * μ s * (ENNReal.ofReal (|r| ^ finrank ℝ E) * μ t)⁻¹ :=
      by
      simp only [div_eq_mul_inv, add_haar_smul, image_add_left, measure_preimage_add, abs_pow,
        singleton_add]
    _ =
        ENNReal.ofReal (|r| ^ finrank ℝ E) * (ENNReal.ofReal (|r| ^ finrank ℝ E))⁻¹ *
          (μ s * (μ t)⁻¹) :=
      by
      rw [ENNReal.mul_inv]
      · ring
      · simp only [pow_pos (abs_pos.mpr hr), ENNReal.ofReal_eq_zero, not_le, Ne.def, true_or_iff]
      · simp only [ENNReal.ofReal_ne_top, true_or_iff, Ne.def, not_false_iff]
    _ = μ s / μ t := by
      rw [ENNReal.mul_inv_cancel, one_mul, div_eq_mul_inv]
      · simp only [pow_pos (abs_pos.mpr hr), ENNReal.ofReal_eq_zero, not_le, Ne.def]
      · simp only [ENNReal.ofReal_ne_top, Ne.def, not_false_iff]
    
#align measure_theory.measure.add_haar_singleton_add_smul_div_singleton_add_smul MeasureTheory.Measure.add_haar_singleton_add_smul_div_singleton_add_smul

instance (priority := 100) isDoublingMeasureOfIsAddHaarMeasure : IsDoublingMeasure μ :=
  by
  refine' ⟨⟨(2 : ℝ≥0) ^ finrank ℝ E, _⟩⟩
  filter_upwards [self_mem_nhdsWithin]with r hr x
  rw [add_haar_closed_ball_mul μ x zero_le_two (le_of_lt hr), add_haar_closed_ball_center μ x,
    ENNReal.ofReal, Real.toNNReal_pow zero_le_two]
  simp only [[anonymous], Real.toNNReal_one, le_refl]
#align measure_theory.measure.is_doubling_measure_of_is_add_haar_measure MeasureTheory.Measure.isDoublingMeasureOfIsAddHaarMeasure

section

/-!
### The Lebesgue measure associated to an alternating map
-/


variable {ι G : Type _} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G]

theorem addHaar_parallelepiped (b : Basis ι ℝ G) (v : ι → G) :
    b.add_haar (parallelepiped v) = ENNReal.ofReal (|b.det v|) :=
  by
  have : FiniteDimensional ℝ G := FiniteDimensional.of_fintype_basis b
  have A : parallelepiped v = b.constr ℕ v '' parallelepiped b :=
    by
    rw [image_parallelepiped]
    congr 1 with i
    exact (b.constr_basis ℕ v i).symm
  rw [A, add_haar_image_linear_map, Basis.addHaar_self, mul_one, ← LinearMap.det_toMatrix b, ←
    Basis.toMatrix_eq_toMatrix_constr]
  rfl
#align measure_theory.measure.add_haar_parallelepiped MeasureTheory.Measure.addHaar_parallelepiped

variable [FiniteDimensional ℝ G] {n : ℕ} [_i : Fact (finrank ℝ G = n)]

include _i

/-- The Lebesgue measure associated to an alternating map. It gives measure `|ω v|` to the
parallelepiped spanned by the vectors `v₁, ..., vₙ`. Note that it is not always a Haar measure,
as it can be zero, but it is always locally finite and translation invariant. -/
noncomputable irreducible_def AlternatingMap.measure (ω : AlternatingMap ℝ G ℝ (Fin n)) :
  Measure G :=
  ‖ω (finBasisOfFinrankEq ℝ G _i.out)‖₊ • (finBasisOfFinrankEq ℝ G _i.out).add_haar
#align alternating_map.measure AlternatingMap.measure

theorem AlternatingMap.measure_parallelepiped (ω : AlternatingMap ℝ G ℝ (Fin n)) (v : Fin n → G) :
    ω.Measure (parallelepiped v) = ENNReal.ofReal (|ω v|) :=
  by
  conv_rhs => rw [ω.eq_smul_basis_det (fin_basis_of_finrank_eq ℝ G _i.out)]
  simp only [add_haar_parallelepiped, AlternatingMap.measure, coe_nnreal_smul_apply,
    AlternatingMap.smul_apply, Algebra.id.smul_eq_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
    Real.ennnorm_eq_ofReal_abs]
#align alternating_map.measure_parallelepiped AlternatingMap.measure_parallelepiped

instance (ω : AlternatingMap ℝ G ℝ (Fin n)) : IsAddLeftInvariant ω.Measure :=
  by
  rw [AlternatingMap.measure]
  infer_instance

instance (ω : AlternatingMap ℝ G ℝ (Fin n)) : IsLocallyFiniteMeasure ω.Measure :=
  by
  rw [AlternatingMap.measure]
  infer_instance

end

/-!
### Density points

Besicovitch covering theorem ensures that, for any locally finite measure on a finite-dimensional
real vector space, almost every point of a set `s` is a density point, i.e.,
`μ (s ∩ closed_ball x r) / μ (closed_ball x r)` tends to `1` as `r` tends to `0`
(see `besicovitch.ae_tendsto_measure_inter_div`).
When `μ` is a Haar measure, one can deduce the same property for any rescaling sequence of sets,
of the form `{x} + r • t` where `t` is a set with positive finite measure, instead of the sequence
of closed balls.

We argue first for the dual property, i.e., if `s` has density `0` at `x`, then
`μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)` tends to `0`. First when `t` is contained in the ball
of radius `1`, in `tendsto_add_haar_inter_smul_zero_of_density_zero_aux1`,
(by arguing by inclusion). Then when `t` is bounded, reducing to the previous one by rescaling, in
`tendsto_add_haar_inter_smul_zero_of_density_zero_aux2`.
Then for a general set `t`, by cutting it into a bounded part and a part with small measure, in
`tendsto_add_haar_inter_smul_zero_of_density_zero`.
Going to the complement, one obtains the desired property at points of density `1`, first when
`s` is measurable in `tendsto_add_haar_inter_smul_one_of_density_one_aux`, and then without this
assumption in `tendsto_add_haar_inter_smul_one_of_density_one` by applying the previous lemma to
the measurable hull `to_measurable μ s`
-/


theorem tendsto_add_haar_inter_smul_zero_of_density_zero_aux1 (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E)
    (u : Set E) (h'u : μ u ≠ 0) (t_bound : t ⊆ closedBall 0 1) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • u)) (𝓝[>] 0) (𝓝 0) :=
  by
  have A : tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ (closed_ball x r)) (𝓝[>] 0) (𝓝 0) :=
    by
    apply
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
        (eventually_of_forall fun b => zero_le _)
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    apply mul_le_mul_right' (measure_mono (inter_subset_inter_right _ _)) _
    intro y hy
    have : y - x ∈ r • closed_ball (0 : E) 1 :=
      by
      apply smul_set_mono t_bound
      simpa [neg_add_eq_sub] using hy
    simpa only [smul_closedBall _ _ zero_le_one, Real.norm_of_nonneg rpos.le,
      mem_closedBall_iff_norm, mul_one, sub_zero, smul_zero]
  have B :
    tendsto (fun r : ℝ => μ (closed_ball x r) / μ ({x} + r • u)) (𝓝[>] 0)
      (𝓝 (μ (closed_ball x 1) / μ ({x} + u))) :=
    by
    apply tendsto_const_nhds.congr' _
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    have : closed_ball x r = {x} + r • closed_ball 0 1 := by
      simp only [_root_.smul_closed_ball, Real.norm_of_nonneg rpos.le, zero_le_one, add_zero,
        mul_one, singleton_add_closedBall, smul_zero]
    simp only [this, add_haar_singleton_add_smul_div_singleton_add_smul μ rpos.ne']
    simp only [add_haar_closed_ball_center, image_add_left, measure_preimage_add, singleton_add]
  have C :
    tendsto
      (fun r : ℝ =>
        μ (s ∩ ({x} + r • t)) / μ (closed_ball x r) * (μ (closed_ball x r) / μ ({x} + r • u)))
      (𝓝[>] 0) (𝓝 (0 * (μ (closed_ball x 1) / μ ({x} + u)))) :=
    by
    apply ENNReal.Tendsto.mul A _ B (Or.inr ENNReal.zero_ne_top)
    simp only [ENNReal.div_eq_top, h'u, measure_closed_ball_lt_top.ne, false_or_iff, image_add_left,
      eq_self_iff_true, not_true, Ne.def, not_false_iff, measure_preimage_add, singleton_add,
      and_false_iff, false_and_iff]
  simp only [zero_mul] at C
  apply C.congr' _
  filter_upwards [self_mem_nhdsWithin]
  rintro r (rpos : 0 < r)
  calc
    μ (s ∩ ({x} + r • t)) / μ (closed_ball x r) * (μ (closed_ball x r) / μ ({x} + r • u)) =
        μ (closed_ball x r) * (μ (closed_ball x r))⁻¹ * (μ (s ∩ ({x} + r • t)) / μ ({x} + r • u)) :=
      by
      simp only [div_eq_mul_inv]
      ring
    _ = μ (s ∩ ({x} + r • t)) / μ ({x} + r • u) := by
      rw [ENNReal.mul_inv_cancel (measure_closed_ball_pos μ x rpos).ne'
          measure_closed_ball_lt_top.ne,
        one_mul]
    
#align measure_theory.measure.tendsto_add_haar_inter_smul_zero_of_density_zero_aux1 MeasureTheory.Measure.tendsto_add_haar_inter_smul_zero_of_density_zero_aux1

theorem tendsto_add_haar_inter_smul_zero_of_density_zero_aux2 (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E)
    (u : Set E) (h'u : μ u ≠ 0) (R : ℝ) (Rpos : 0 < R) (t_bound : t ⊆ closedBall 0 R) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • u)) (𝓝[>] 0) (𝓝 0) :=
  by
  set t' := R⁻¹ • t with ht'
  set u' := R⁻¹ • u with hu'
  have A : tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t')) / μ ({x} + r • u')) (𝓝[>] 0) (𝓝 0) :=
    by
    apply tendsto_add_haar_inter_smul_zero_of_density_zero_aux1 μ s x h t' u'
    ·
      simp only [h'u, (pow_pos Rpos _).ne', abs_nonpos_iff, add_haar_smul, not_false_iff,
        ENNReal.ofReal_eq_zero, inv_eq_zero, inv_pow, Ne.def, or_self_iff, mul_eq_zero]
    · convert smul_set_mono t_bound
      rw [smul_closedBall _ _ Rpos.le, smul_zero, Real.norm_of_nonneg (inv_nonneg.2 Rpos.le),
        inv_mul_cancel Rpos.ne']
  have B : tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] (R * 0)) :=
    by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (tendsto_const_nhds.mul tendsto_id).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin]
      intro r rpos
      rw [mul_zero]
      exact mul_pos Rpos rpos
  rw [mul_zero] at B
  apply (A.comp B).congr' _
  filter_upwards [self_mem_nhdsWithin]
  rintro r (rpos : 0 < r)
  have T : (R * r) • t' = r • t := by
    rw [mul_comm, ht', smul_smul, mul_assoc, mul_inv_cancel Rpos.ne', mul_one]
  have U : (R * r) • u' = r • u := by
    rw [mul_comm, hu', smul_smul, mul_assoc, mul_inv_cancel Rpos.ne', mul_one]
  dsimp
  rw [T, U]
#align measure_theory.measure.tendsto_add_haar_inter_smul_zero_of_density_zero_aux2 MeasureTheory.Measure.tendsto_add_haar_inter_smul_zero_of_density_zero_aux2

/-- Consider a point `x` at which a set `s` has density zero, with respect to closed balls. Then it
also has density zero with respect to any measurable set `t`: the proportion of points in `s`
belonging to a rescaled copy `{x} + r • t` of `t` tends to zero as `r` tends to zero. -/
theorem tendsto_add_haar_inter_smul_zero_of_density_zero (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E)
    (ht : MeasurableSet t) (h''t : μ t ≠ ∞) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 0) :=
  by
  refine' tendsto_order.2 ⟨fun a' ha' => (ENNReal.not_lt_zero ha').elim, fun ε (εpos : 0 < ε) => _⟩
  rcases eq_or_ne (μ t) 0 with (h't | h't)
  · apply eventually_of_forall fun r => _
    suffices H : μ (s ∩ ({x} + r • t)) = 0
    · rw [H]
      simpa only [ENNReal.zero_div] using εpos
    apply le_antisymm _ (zero_le _)
    calc
      μ (s ∩ ({x} + r • t)) ≤ μ ({x} + r • t) := measure_mono (inter_subset_right _ _)
      _ = 0 := by
        simp only [h't, add_haar_smul, image_add_left, measure_preimage_add, singleton_add,
          mul_zero]
      
  obtain ⟨n, npos, hn⟩ : ∃ n : ℕ, 0 < n ∧ μ (t \ closed_ball 0 n) < ε / 2 * μ t :=
    by
    have A :
      tendsto (fun n : ℕ => μ (t \ closed_ball 0 n)) at_top
        (𝓝 (μ (⋂ n : ℕ, t \ closed_ball 0 n))) :=
      by
      have N : ∃ n : ℕ, μ (t \ closed_ball 0 n) ≠ ∞ :=
        ⟨0, ((measure_mono (diff_subset t _)).trans_lt h''t.lt_top).Ne⟩
      refine' tendsto_measure_Inter (fun n => ht.diff measurableSet_closedBall) (fun m n hmn => _) N
      exact diff_subset_diff subset.rfl (closed_ball_subset_closed_ball (Nat.cast_le.2 hmn))
    have : (⋂ n : ℕ, t \ closed_ball 0 n) = ∅ := by
      simp_rw [diff_eq, ← inter_Inter, Inter_eq_compl_Union_compl, compl_compl,
        Union_closed_ball_nat, compl_univ, inter_empty]
    simp only [this, measure_empty] at A
    have I : 0 < ε / 2 * μ t := ENNReal.mul_pos (ENNReal.half_pos εpos.ne').ne' h't
    exact (eventually.and (Ioi_mem_at_top 0) ((tendsto_order.1 A).2 _ I)).exists
  have L :
    tendsto (fun r : ℝ => μ (s ∩ ({x} + r • (t ∩ closed_ball 0 n))) / μ ({x} + r • t)) (𝓝[>] 0)
      (𝓝 0) :=
    tendsto_add_haar_inter_smul_zero_of_density_zero_aux2 μ s x h _ t h't n (Nat.cast_pos.2 npos)
      (inter_subset_right _ _)
  filter_upwards [(tendsto_order.1 L).2 _ (ENNReal.half_pos εpos.ne'), self_mem_nhdsWithin]
  rintro r hr (rpos : 0 < r)
  have I :
    μ (s ∩ ({x} + r • t)) ≤
      μ (s ∩ ({x} + r • (t ∩ closed_ball 0 n))) + μ ({x} + r • (t \ closed_ball 0 n)) :=
    calc
      μ (s ∩ ({x} + r • t)) =
          μ (s ∩ ({x} + r • (t ∩ closed_ball 0 n)) ∪ s ∩ ({x} + r • (t \ closed_ball 0 n))) :=
        by rw [← inter_union_distrib_left, ← add_union, ← smul_set_union, inter_union_diff]
      _ ≤ μ (s ∩ ({x} + r • (t ∩ closed_ball 0 n))) + μ (s ∩ ({x} + r • (t \ closed_ball 0 n))) :=
        (measure_union_le _ _)
      _ ≤ μ (s ∩ ({x} + r • (t ∩ closed_ball 0 n))) + μ ({x} + r • (t \ closed_ball 0 n)) :=
        add_le_add le_rfl (measure_mono (inter_subset_right _ _))
      
  calc
    μ (s ∩ ({x} + r • t)) / μ ({x} + r • t) ≤
        (μ (s ∩ ({x} + r • (t ∩ closed_ball 0 n))) + μ ({x} + r • (t \ closed_ball 0 n))) /
          μ ({x} + r • t) :=
      mul_le_mul_right' I _
    _ < ε / 2 + ε / 2 := by
      rw [ENNReal.add_div]
      apply ENNReal.add_lt_add hr _
      rwa [add_haar_singleton_add_smul_div_singleton_add_smul μ rpos.ne',
        ENNReal.div_lt_iff (Or.inl h't) (Or.inl h''t)]
    _ = ε := ENNReal.add_halves _
    
#align measure_theory.measure.tendsto_add_haar_inter_smul_zero_of_density_zero MeasureTheory.Measure.tendsto_add_haar_inter_smul_zero_of_density_zero

theorem tendsto_add_haar_inter_smul_one_of_density_one_aux (s : Set E) (hs : MeasurableSet s)
    (x : E) (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1))
    (t : Set E) (ht : MeasurableSet t) (h't : μ t ≠ 0) (h''t : μ t ≠ ∞) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) :=
  by
  have I :
    ∀ u v, μ u ≠ 0 → μ u ≠ ∞ → MeasurableSet v → μ u / μ u - μ (vᶜ ∩ u) / μ u = μ (v ∩ u) / μ u :=
    by
    intro u v uzero utop vmeas
    simp_rw [div_eq_mul_inv]
    rw [← ENNReal.sub_mul]
    swap
    · simp only [uzero, ENNReal.inv_eq_top, imp_true_iff, Ne.def, not_false_iff]
    congr 1
    apply
      ENNReal.sub_eq_of_add_eq (ne_top_of_le_ne_top utop (measure_mono (inter_subset_right _ _)))
    rw [inter_comm _ u, inter_comm _ u]
    exact measure_inter_add_diff u vmeas
  have L : tendsto (fun r => μ (sᶜ ∩ closed_ball x r) / μ (closed_ball x r)) (𝓝[>] 0) (𝓝 0) :=
    by
    have A : tendsto (fun r => μ (closed_ball x r) / μ (closed_ball x r)) (𝓝[>] 0) (𝓝 1) :=
      by
      apply tendsto_const_nhds.congr' _
      filter_upwards [self_mem_nhdsWithin]
      intro r hr
      rw [div_eq_mul_inv, ENNReal.mul_inv_cancel]
      · exact (measure_closed_ball_pos μ _ hr).ne'
      · exact measure_closed_ball_lt_top.ne
    have B := ENNReal.Tendsto.sub A h (Or.inl ENNReal.one_ne_top)
    simp only [tsub_self] at B
    apply B.congr' _
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    convert
      I (closed_ball x r) (sᶜ) (measure_closed_ball_pos μ _ rpos).ne' measure_closed_ball_lt_top.Ne
        hs.compl
    rw [compl_compl]
  have L' : tendsto (fun r : ℝ => μ (sᶜ ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_add_haar_inter_smul_zero_of_density_zero μ (sᶜ) x L t ht h''t
  have L'' : tendsto (fun r : ℝ => μ ({x} + r • t) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) :=
    by
    apply tendsto_const_nhds.congr' _
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    rw [add_haar_singleton_add_smul_div_singleton_add_smul μ rpos.ne', ENNReal.div_self h't h''t]
  have := ENNReal.Tendsto.sub L'' L' (Or.inl ENNReal.one_ne_top)
  simp only [tsub_zero] at this
  apply this.congr' _
  filter_upwards [self_mem_nhdsWithin]
  rintro r (rpos : 0 < r)
  refine' I ({x} + r • t) s _ _ hs
  ·
    simp only [h't, abs_of_nonneg rpos.le, pow_pos rpos, add_haar_smul, image_add_left,
      ENNReal.ofReal_eq_zero, not_le, or_false_iff, Ne.def, measure_preimage_add, abs_pow,
      singleton_add, mul_eq_zero]
  ·
    simp only [h''t, ENNReal.ofReal_ne_top, add_haar_smul, image_add_left, WithTop.mul_eq_top_iff,
      Ne.def, not_false_iff, measure_preimage_add, singleton_add, and_false_iff, false_and_iff,
      or_self_iff]
#align measure_theory.measure.tendsto_add_haar_inter_smul_one_of_density_one_aux MeasureTheory.Measure.tendsto_add_haar_inter_smul_one_of_density_one_aux

/-- Consider a point `x` at which a set `s` has density one, with respect to closed balls (i.e.,
a Lebesgue density point of `s`). Then `s` has also density one at `x` with respect to any
measurable set `t`: the proportion of points in `s` belonging to a rescaled copy `{x} + r • t`
of `t` tends to one as `r` tends to zero. -/
theorem tendsto_add_haar_inter_smul_one_of_density_one (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) (t : Set E)
    (ht : MeasurableSet t) (h't : μ t ≠ 0) (h''t : μ t ≠ ∞) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) :=
  by
  have :
    tendsto (fun r : ℝ => μ (to_measurable μ s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) :=
    by
    apply
      tendsto_add_haar_inter_smul_one_of_density_one_aux μ _ (measurable_set_to_measurable _ _) _ _
        t ht h't h''t
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h tendsto_const_nhds
    · refine' eventually_of_forall fun r => mul_le_mul_right' _ _
      exact measure_mono (inter_subset_inter_left _ (subset_to_measurable _ _))
    · filter_upwards [self_mem_nhdsWithin]
      rintro r (rpos : 0 < r)
      apply ENNReal.div_le_of_le_mul
      rw [one_mul]
      exact measure_mono (inter_subset_right _ _)
  apply this.congr fun r => _
  congr 1
  apply measure_to_measurable_inter_of_sigma_finite
  simp only [image_add_left, singleton_add]
  apply (continuous_add_left (-x)).Measurable (ht.const_smul₀ r)
#align measure_theory.measure.tendsto_add_haar_inter_smul_one_of_density_one MeasureTheory.Measure.tendsto_add_haar_inter_smul_one_of_density_one

/-- Consider a point `x` at which a set `s` has density one, with respect to closed balls (i.e.,
a Lebesgue density point of `s`). Then `s` intersects the rescaled copies `{x} + r • t` of a given
set `t` with positive measure, for any small enough `r`. -/
theorem eventually_nonempty_inter_smul_of_density_one (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) (t : Set E)
    (ht : MeasurableSet t) (h't : μ t ≠ 0) : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • t)).Nonempty :=
  by
  obtain ⟨t', t'_meas, t't, t'pos, t'top⟩ : ∃ t', MeasurableSet t' ∧ t' ⊆ t ∧ 0 < μ t' ∧ μ t' < ⊤ :=
    exists_subset_measure_lt_top ht h't.bot_lt
  filter_upwards [(tendsto_order.1
          (tendsto_add_haar_inter_smul_one_of_density_one μ s x h t' t'_meas t'pos.ne' t'top.ne)).1
      0 zero_lt_one]
  intro r hr
  have : μ (s ∩ ({x} + r • t')) ≠ 0 := fun h' => by
    simpa only [ENNReal.not_lt_zero, ENNReal.zero_div, h'] using hr
  have : (s ∩ ({x} + r • t')).Nonempty := nonempty_of_measure_ne_zero this
  apply this.mono (inter_subset_inter subset.rfl _)
  exact add_subset_add subset.rfl (smul_set_mono t't)
#align measure_theory.measure.eventually_nonempty_inter_smul_of_density_one MeasureTheory.Measure.eventually_nonempty_inter_smul_of_density_one

end Measure

end MeasureTheory

