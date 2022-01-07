import Mathbin.MeasureTheory.Measure.Lebesgue
import Mathbin.MeasureTheory.Measure.Haar
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.Analysis.NormedSpace.Pointwise

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
* `add_haar_image_linear_map` :  when `f` is a linear map, the measure of `f '' s` is the
  measure of `s` multiplied by the absolute value of the determinant of `f`.
* `add_haar_submodule` : a strict submodule has measure `0`.
* `add_haar_smul` : the measure of `r • s` is `|r| ^ dim * μ s`.
* `add_haar_ball`: the measure of `ball x r` is `r ^ dim * μ (ball 0 1)`.
* `add_haar_closed_ball`: the measure of `closed_ball x r` is `r ^ dim * μ (ball 0 1)`.
* `add_haar_sphere`: spheres have zero measure.

-/


open TopologicalSpace Set Filter Metric

open_locale Ennreal Pointwise TopologicalSpace

/-- The interval `[0,1]` as a compact set with non-empty interior. -/
def TopologicalSpace.PositiveCompacts.icc01 : positive_compacts ℝ :=
  ⟨Icc 0 1, is_compact_Icc, by
    simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]⟩

universe u

/-- The set `[0,1]^ι` as a compact set with non-empty interior. -/
def TopologicalSpace.PositiveCompacts.piIcc01 (ι : Type _) [Fintype ι] : positive_compacts (ι → ℝ) :=
  ⟨Set.Pi Set.Univ fun i => Icc 0 1, is_compact_univ_pi fun i => is_compact_Icc, by
    simp only [interior_pi_set, finite.of_fintype, interior_Icc, univ_pi_nonempty_iff, nonempty_Ioo, implies_true_iff,
      zero_lt_one]⟩

namespace MeasureTheory

open Measureₓ TopologicalSpace.PositiveCompacts FiniteDimensional

/-!
### The Lebesgue measure is a Haar measure on `ℝ` and on `ℝ^ι`.
-/


theorem is_add_left_invariant_real_volume : is_add_left_invariant (⇑(volume : Measureₓ ℝ)) := by
  simp [← map_add_left_eq_self, Real.map_volume_add_left]

/-- The Haar measure equals the Lebesgue measure on `ℝ`. -/
theorem add_haar_measure_eq_volume : add_haar_measure Icc01 = volume := by
  convert (add_haar_measure_unique _ Icc01).symm
  · simp [Icc01]
    
  · infer_instance
    
  · exact is_add_left_invariant_real_volume
    

instance : is_add_haar_measure (volume : Measureₓ ℝ) := by
  rw [← add_haar_measure_eq_volume]
  infer_instance

theorem is_add_left_invariant_real_volume_pi (ι : Type _) [Fintype ι] :
    is_add_left_invariant (⇑(volume : Measureₓ (ι → ℝ))) := by
  simp [← map_add_left_eq_self, Real.map_volume_pi_add_left]

/-- The Haar measure equals the Lebesgue measure on `ℝ^ι`. -/
theorem add_haar_measure_eq_volume_pi (ι : Type _) [Fintype ι] : add_haar_measure (pi_Icc01 ι) = volume := by
  convert (add_haar_measure_unique _ (pi_Icc01 ι)).symm
  · simp only [pi_Icc01, volume_pi_pi fun i => Icc (0 : ℝ) 1, Finset.prod_const_one, Ennreal.of_real_one,
      Real.volume_Icc, one_smul, sub_zero]
    
  · infer_instance
    
  · exact is_add_left_invariant_real_volume_pi ι
    

instance is_add_haar_measure_volume_pi (ι : Type _) [Fintype ι] : is_add_haar_measure (volume : Measureₓ (ι → ℝ)) := by
  rw [← add_haar_measure_eq_volume_pi]
  infer_instance

namespace Measureₓ

/-!
### Strict subspaces have zero measure
-/


/-- If a set is disjoint of its translates by infinitely many bounded vectors, then it has measure
zero. This auxiliary lemma proves this assuming additionally that the set is bounded. -/
theorem add_haar_eq_zero_of_disjoint_translates_aux {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measureₓ E) [is_add_haar_measure μ] {s : Set E} (u : ℕ → E)
    (sb : Bounded s) (hu : Bounded (range u)) (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) :
    μ s = 0 := by
  by_contra h
  apply lt_irreflₓ ∞
  calc ∞ = ∑' n : ℕ, μ s := (Ennreal.tsum_const_eq_top_of_ne_zero h).symm _ = ∑' n : ℕ, μ ({u n} + s) := by
      congr 1
      ext1 n
      simp only [image_add_left, add_haar_preimage_add, singleton_add]_ = μ (⋃ n, {u n} + s) := by
      rw
        [measure_Union hs fun n => by
          simpa only [image_add_left, singleton_add] using measurable_id.const_add _ h's]_ = μ (range u + s) :=
      by
      rw [← Union_add, Union_singleton_eq_range]_ < ∞ := bounded.measure_lt_top (hu.add sb)

/-- If a set is disjoint of its translates by infinitely many bounded vectors, then it has measure
zero. -/
theorem add_haar_eq_zero_of_disjoint_translates {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measureₓ E) [is_add_haar_measure μ] {s : Set E} (u : ℕ → E)
    (hu : Bounded (range u)) (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) : μ s = 0 := by
  suffices H : ∀ R, μ (s ∩ closed_ball 0 R) = 0
  · apply le_antisymmₓ _ (zero_le _)
    have : s ⊆ ⋃ n : ℕ, s ∩ closed_ball 0 n := by
      intro x hx
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ∥x∥ ≤ n := exists_nat_ge ∥x∥
      exact mem_Union.2 ⟨n, ⟨hx, mem_closed_ball_zero_iff.2 hn⟩⟩
    calc μ s ≤ μ (⋃ n : ℕ, s ∩ closed_ball 0 n) := measure_mono this _ ≤ ∑' n : ℕ, μ (s ∩ closed_ball 0 n) :=
        measure_Union_le _ _ = 0 := by
        simp only [H, tsum_zero]
    
  intro R
  apply
    add_haar_eq_zero_of_disjoint_translates_aux μ u (bounded.mono (inter_subset_right _ _) bounded_closed_ball) hu _
      (h's.inter measurable_set_closed_ball)
  rw [← pairwise_univ] at hs⊢
  apply pairwise_disjoint.mono hs fun n => _
  exact add_subset_add (subset.refl _) (inter_subset_left _ _)

/-- A strict vector subspace has measure zero. -/
theorem add_haar_submodule {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measureₓ E) [is_add_haar_measure μ] (s : Submodule ℝ E) (hs : s ≠ ⊤) : μ s = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ s := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne.def, not_forall] using hs
  obtain ⟨c, cpos, cone⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 :=
    ⟨1 / 2, by
      norm_num, by
      norm_num⟩
  have A : Bounded (range fun n : ℕ => c ^ n • x) :=
    have : tendsto (fun n : ℕ => c ^ n • x) at_top (𝓝 ((0 : ℝ) • x)) :=
      (tendsto_pow_at_top_nhds_0_of_lt_1 cpos.le cone).smul_const x
    bounded_range_of_tendsto _ this
  apply add_haar_eq_zero_of_disjoint_translates μ _ A _ (Submodule.closed_of_finite_dimensional s).MeasurableSet
  intro m n hmn
  simp only [Function.onFun, image_add_left, singleton_add, disjoint_left, mem_preimage, SetLike.mem_coe]
  intro y hym hyn
  have A : (c ^ n - c ^ m) • x ∈ s := by
    convert s.sub_mem hym hyn
    simp only [sub_smul, neg_sub_neg, add_sub_add_right_eq_sub]
  have H : c ^ n - c ^ m ≠ 0 := by
    simpa only [sub_eq_zero, Ne.def] using (strict_anti_pow cpos cone).Injective.Ne hmn.symm
  have : x ∈ s := by
    convert s.smul_mem ((c ^ n - c ^ m)⁻¹) A
    rw [smul_smul, inv_mul_cancel H, one_smul]
  exact hx this

/-!
### Applying a linear map rescales Haar measure by the determinant

We first prove this on `ι → ℝ`, using that this is already known for the product Lebesgue
measure (thanks to matrices computations). Then, we extend this to any finite-dimensional real
vector space by using a linear equiv with a space of the form `ι → ℝ`, and arguing that such a
linear equiv maps Haar measure to Haar measure.
-/


theorem map_linear_map_add_haar_pi_eq_smul_add_haar {ι : Type _} [Fintype ι] {f : (ι → ℝ) →ₗ[ℝ] ι → ℝ} (hf : f.det ≠ 0)
    (μ : Measureₓ (ι → ℝ)) [is_add_haar_measure μ] : measure.map f μ = Ennreal.ofReal (abs (f.det⁻¹)) • μ := by
  have := add_haar_measure_unique (is_add_left_invariant_add_haar μ) (pi_Icc01 ι)
  rw [this]
  simp [add_haar_measure_eq_volume_pi, Real.map_linear_map_volume_pi_eq_smul_volume_pi hf, smul_smul, mul_commₓ]

theorem map_linear_map_add_haar_eq_smul_add_haar {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measureₓ E) [is_add_haar_measure μ] {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) :
    measure.map f μ = Ennreal.ofReal (abs (f.det⁻¹)) • μ := by
  let ι := Finₓ (finrank ℝ E)
  have : FiniteDimensional ℝ (ι → ℝ) := by
    infer_instance
  have : finrank ℝ E = finrank ℝ (ι → ℝ) := by
    simp
  have e : E ≃ₗ[ℝ] ι → ℝ := linear_equiv.of_finrank_eq E (ι → ℝ) this
  obtain ⟨g, hg⟩ : ∃ g, g = (e : E →ₗ[ℝ] ι → ℝ).comp (f.comp (e.symm : (ι → ℝ) →ₗ[ℝ] E)) := ⟨_, rfl⟩
  have gdet : g.det = f.det := by
    rw [hg]
    exact LinearMap.det_conj f e
  rw [← gdet] at hf⊢
  have fg : f = (e.symm : (ι → ℝ) →ₗ[ℝ] E).comp (g.comp (e : E →ₗ[ℝ] ι → ℝ)) := by
    ext x
    simp only [LinearEquiv.coe_coe, Function.comp_app, LinearMap.coe_comp, LinearEquiv.symm_apply_apply, hg]
  simp only [fg, LinearEquiv.coe_coe, LinearMap.coe_comp]
  have Ce : Continuous e := (e : E →ₗ[ℝ] ι → ℝ).continuous_of_finite_dimensional
  have Cg : Continuous g := LinearMap.continuous_of_finite_dimensional g
  have Cesymm : Continuous e.symm := (e.symm : (ι → ℝ) →ₗ[ℝ] E).continuous_of_finite_dimensional
  rw [← map_map Cesymm.measurable (Cg.comp Ce).Measurable, ← map_map Cg.measurable Ce.measurable]
  have : is_add_haar_measure (map e μ) := is_add_haar_measure_map μ e.to_add_equiv Ce Cesymm
  have ecomp : e.symm ∘ e = id := by
    ext x
    simp only [id.def, Function.comp_app, LinearEquiv.symm_apply_apply]
  rw [map_linear_map_add_haar_pi_eq_smul_add_haar hf (map e μ), LinearMap.map_smul,
    map_map Cesymm.measurable Ce.measurable, ecomp, measure.map_id]

/-- The preimage of a set `s` under a linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem add_haar_preimage_linear_map {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measureₓ E) [is_add_haar_measure μ] {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) (s : Set E) :
    μ (f ⁻¹' s) = Ennreal.ofReal (abs (f.det⁻¹)) * μ s :=
  calc
    μ (f ⁻¹' s) = measure.map f μ s :=
      ((f.equiv_of_det_ne_zero hf).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.map_apply s).symm
    _ = Ennreal.ofReal (abs (f.det⁻¹)) * μ s := by
      rw [map_linear_map_add_haar_eq_smul_add_haar μ hf]
      rfl
    

/-- The preimage of a set `s` under a continuous linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem add_haar_preimage_continuous_linear_map {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measureₓ E) [is_add_haar_measure μ] {f : E →L[ℝ] E}
    (hf : LinearMap.det (f : E →ₗ[ℝ] E) ≠ 0) (s : Set E) :
    μ (f ⁻¹' s) = Ennreal.ofReal (abs (LinearMap.det (f : E →ₗ[ℝ] E)⁻¹)) * μ s :=
  add_haar_preimage_linear_map μ hf s

/-- The preimage of a set `s` under a linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem add_haar_preimage_linear_equiv {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measureₓ E) [is_add_haar_measure μ] (f : E ≃ₗ[ℝ] E) (s : Set E) :
    μ (f ⁻¹' s) = Ennreal.ofReal (abs (f.symm : E →ₗ[ℝ] E).det) * μ s := by
  have A : (f : E →ₗ[ℝ] E).det ≠ 0 := (LinearEquiv.is_unit_det' f).ne_zero
  convert add_haar_preimage_linear_map μ A s
  simp only [LinearEquiv.det_coe_symm]

/-- The preimage of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
theorem add_haar_preimage_continuous_linear_equiv {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measureₓ E) [is_add_haar_measure μ] (f : E ≃L[ℝ] E) (s : Set E) :
    μ (f ⁻¹' s) = Ennreal.ofReal (abs (f.symm : E →ₗ[ℝ] E).det) * μ s :=
  add_haar_preimage_linear_equiv μ _ s

/-- The image of a set `s` under a linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
theorem add_haar_image_linear_map {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measureₓ E) [is_add_haar_measure μ] (f : E →ₗ[ℝ] E) (s : Set E) :
    μ (f '' s) = Ennreal.ofReal (abs f.det) * μ s := by
  rcases ne_or_eq f.det 0 with (hf | hf)
  · let g := (f.equiv_of_det_ne_zero hf).toContinuousLinearEquiv
    change μ (g '' s) = _
    rw [ContinuousLinearEquiv.image_eq_preimage g s, add_haar_preimage_continuous_linear_equiv]
    congr
    ext x
    simp only [LinearEquiv.of_is_unit_det_apply, LinearEquiv.to_continuous_linear_equiv_apply,
      ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
      LinearEquiv.to_fun_eq_coe, coe_coe]
    
  · simp only [hf, zero_mul, Ennreal.of_real_zero, abs_zero]
    have : μ f.range = 0 := add_haar_submodule μ _ (LinearMap.range_lt_top_of_det_eq_zero hf).Ne
    exact le_antisymmₓ (le_transₓ (measure_mono (image_subset_range _ _)) this.le) (zero_le _)
    

/-- The image of a set `s` under a continuous linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
theorem add_haar_image_continuous_linear_map {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measureₓ E) [is_add_haar_measure μ] (f : E →L[ℝ] E) (s : Set E) :
    μ (f '' s) = Ennreal.ofReal (abs (f : E →ₗ[ℝ] E).det) * μ s :=
  add_haar_image_linear_map μ _ s

/-- The image of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
theorem add_haar_image_continuous_linear_equiv {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measureₓ E) [is_add_haar_measure μ] (f : E ≃L[ℝ] E) (s : Set E) :
    μ (f '' s) = Ennreal.ofReal (abs (f : E →ₗ[ℝ] E).det) * μ s :=
  add_haar_image_linear_map μ _ s

/-!
### Basic properties of Haar measures on real vector spaces
-/


variable {E : Type _} [NormedGroup E] [MeasurableSpace E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  (μ : Measureₓ E) [is_add_haar_measure μ]

theorem map_add_haar_smul {r : ℝ} (hr : r ≠ 0) :
    measure.map ((· • ·) r) μ = Ennreal.ofReal (abs ((r ^ finrank ℝ E)⁻¹)) • μ := by
  let f : E →ₗ[ℝ] E := r • 1
  change measure.map f μ = _
  have hf : f.det ≠ 0 := by
    simp only [mul_oneₓ, LinearMap.det_smul, Ne.def, MonoidHom.map_one]
    intro h
    exact hr (pow_eq_zero h)
  simp only [map_linear_map_add_haar_eq_smul_add_haar μ hf, mul_oneₓ, LinearMap.det_smul, MonoidHom.map_one]

@[simp]
theorem add_haar_preimage_smul {r : ℝ} (hr : r ≠ 0) (s : Set E) :
    μ ((· • ·) r ⁻¹' s) = Ennreal.ofReal (abs ((r ^ finrank ℝ E)⁻¹)) * μ s :=
  calc
    μ ((· • ·) r ⁻¹' s) = measure.map ((· • ·) r) μ s :=
      ((Homeomorph.smul (is_unit_iff_ne_zero.2 hr).Unit).toMeasurableEquiv.map_apply s).symm
    _ = Ennreal.ofReal (abs ((r ^ finrank ℝ E)⁻¹)) * μ s := by
      rw [map_add_haar_smul μ hr]
      rfl
    

/-- Rescaling a set by a factor `r` multiplies its measure by `abs (r ^ dim)`. -/
@[simp]
theorem add_haar_smul (r : ℝ) (s : Set E) : μ (r • s) = Ennreal.ofReal (abs (r ^ finrank ℝ E)) * μ s := by
  rcases ne_or_eq r 0 with (h | rfl)
  · rw [← preimage_smul_inv₀ h, add_haar_preimage_smul μ (inv_ne_zero h), inv_pow₀, inv_inv₀]
    
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp only [measure_empty, mul_zero, smul_set_empty]
    
  rw [zero_smul_set hs, ← singleton_zero]
  by_cases' h : finrank ℝ E = 0
  · have : Subsingleton E := finrank_zero_iff.1 h
    simp only [h, one_mulₓ, Ennreal.of_real_one, abs_one, Subsingleton.eq_univ_of_nonempty hs, pow_zeroₓ,
      Subsingleton.eq_univ_of_nonempty (singleton_nonempty (0 : E))]
    
  · have : Nontrivial E := nontrivial_of_finrank_pos (bot_lt_iff_ne_bot.2 h)
    simp only [h, zero_mul, Ennreal.of_real_zero, abs_zero, Ne.def, not_false_iff, zero_pow', measure_singleton]
    

/-! We don't need to state `map_add_haar_neg` here, because it has already been proved for
general Haar measures on general commutative groups. -/


/-! ### Measure of balls -/


theorem add_haar_ball_center {E : Type _} [NormedGroup E] [MeasurableSpace E] [BorelSpace E] (μ : Measureₓ E)
    [is_add_haar_measure μ] (x : E) (r : ℝ) : μ (ball x r) = μ (ball (0 : E) r) := by
  have : ball (0 : E) r = (· + ·) x ⁻¹' ball x r := by
    simp [preimage_add_ball]
  rw [this, add_haar_preimage_add]

theorem add_haar_closed_ball_center {E : Type _} [NormedGroup E] [MeasurableSpace E] [BorelSpace E] (μ : Measureₓ E)
    [is_add_haar_measure μ] (x : E) (r : ℝ) : μ (closed_ball x r) = μ (closed_ball (0 : E) r) := by
  have : closed_ball (0 : E) r = (· + ·) x ⁻¹' closed_ball x r := by
    simp [preimage_add_closed_ball]
  rw [this, add_haar_preimage_add]

theorem add_haar_ball_pos {E : Type _} [NormedGroup E] [MeasurableSpace E] (μ : Measureₓ E) [is_add_haar_measure μ]
    (x : E) {r : ℝ} (hr : 0 < r) : 0 < μ (ball x r) :=
  is_open_ball.add_haar_pos μ (nonempty_ball.2 hr)

theorem add_haar_closed_ball_pos {E : Type _} [NormedGroup E] [MeasurableSpace E] (μ : Measureₓ E)
    [is_add_haar_measure μ] (x : E) {r : ℝ} (hr : 0 < r) : 0 < μ (closed_ball x r) :=
  lt_of_lt_of_leₓ (add_haar_ball_pos μ x hr) (measure_mono ball_subset_closed_ball)

theorem add_haar_ball_of_pos (x : E) {r : ℝ} (hr : 0 < r) :
    μ (ball x r) = Ennreal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  have : ball (0 : E) r = r • ball 0 1 := by
    simp [smul_ball hr.ne' (0 : E) 1, Real.norm_eq_abs, abs_of_nonneg hr.le]
  simp [this, add_haar_smul, abs_of_nonneg hr.le, add_haar_ball_center]

theorem add_haar_ball [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (ball x r) = Ennreal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rcases LE.le.eq_or_lt hr with (h | h)
  · simp [← h, zero_pow finrank_pos]
    
  · exact add_haar_ball_of_pos μ x h
    

/-- The measure of a closed ball can be expressed in terms of the measure of the closed unit ball.
Use instead `add_haar_closed_ball`, which uses the measure of the open unit ball as a standard
form. -/
theorem add_haar_closed_ball' (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (closed_ball x r) = Ennreal.ofReal (r ^ finrank ℝ E) * μ (closed_ball 0 1) := by
  have : closed_ball (0 : E) r = r • closed_ball 0 1 := by
    simp [smul_closed_ball r (0 : E) zero_le_one, Real.norm_eq_abs, abs_of_nonneg hr]
  simp [this, add_haar_smul, abs_of_nonneg hr, add_haar_closed_ball_center]

theorem add_haar_closed_unit_ball_eq_add_haar_unit_ball : μ (closed_ball (0 : E) 1) = μ (ball 0 1) := by
  apply le_antisymmₓ _ (measure_mono ball_subset_closed_ball)
  have A :
    tendsto (fun r : ℝ => Ennreal.ofReal (r ^ finrank ℝ E) * μ (closed_ball (0 : E) 1)) (𝓝[<] 1)
      (𝓝 (Ennreal.ofReal (1 ^ finrank ℝ E) * μ (closed_ball (0 : E) 1))) :=
    by
    refine'
      Ennreal.Tendsto.mul _
        (by
          simp )
        tendsto_const_nhds
        (by
          simp )
    exact Ennreal.tendsto_of_real ((tendsto_id' nhds_within_le_nhds).pow _)
  simp only [one_pow, one_mulₓ, Ennreal.of_real_one] at A
  refine' le_of_tendsto A _
  refine'
    mem_nhds_within_Iio_iff_exists_Ioo_subset.2
      ⟨(0 : ℝ), by
        simp , fun r hr => _⟩
  dsimp
  rw [← add_haar_closed_ball' μ (0 : E) hr.1.le]
  exact measure_mono (closed_ball_subset_ball hr.2)

theorem add_haar_closed_ball (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (closed_ball x r) = Ennreal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rw [add_haar_closed_ball' μ x hr, add_haar_closed_unit_ball_eq_add_haar_unit_ball]

theorem add_haar_sphere_of_ne_zero (x : E) {r : ℝ} (hr : r ≠ 0) : μ (sphere x r) = 0 := by
  rcases lt_trichotomyₓ r 0 with (h | rfl | h)
  · simp only [empty_diff, measure_empty, ← closed_ball_diff_ball, closed_ball_eq_empty.2 h]
    
  · exact (hr rfl).elim
    
  · rw [← closed_ball_diff_ball,
        measure_diff ball_subset_closed_ball measurable_set_closed_ball measurable_set_ball measure_ball_lt_top.ne,
        add_haar_ball_of_pos μ _ h, add_haar_closed_ball μ _ h.le, tsub_self] <;>
      infer_instance
    

theorem add_haar_sphere [Nontrivial E] (x : E) (r : ℝ) : μ (sphere x r) = 0 := by
  rcases eq_or_ne r 0 with (rfl | h)
  · simp only [← closed_ball_diff_ball, diff_empty, closed_ball_zero, ball_zero, measure_singleton]
    
  · exact add_haar_sphere_of_ne_zero μ x h
    

end Measureₓ

end MeasureTheory

