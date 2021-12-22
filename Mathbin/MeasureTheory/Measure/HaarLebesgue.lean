import Mathbin.MeasureTheory.Measure.Lebesgue
import Mathbin.MeasureTheory.Measure.Haar
import Mathbin.LinearAlgebra.FiniteDimensional

/-!
# Relationship between the Haar and Lebesgue measures

We prove that the Haar measure and Lebesgue measure are equal on `ℝ` and on `ℝ^ι`, in
`measure_theory.add_haar_measure_eq_volume` and `measure_theory.add_haar_measure_eq_volume_pi`.

We deduce basic properties of any Haar measure on a finite dimensional real vector space:
* `map_linear_map_add_haar_eq_smul_add_haar`: a linear map rescales the Haar measure by the
  absolute value of its determinant.
* `add_haar_smul` : the measure of `r • s` is `|r| ^ dim * μ s`.
* `add_haar_ball`: the measure of `ball x r` is `r ^ dim * μ (ball 0 1)`.
* `add_haar_closed_ball`: the measure of `closed_ball x r` is `r ^ dim * μ (ball 0 1)`.
* `add_haar_sphere`: spheres have zero measure.

-/


open TopologicalSpace Set Filter Metric

open_locale Ennreal Pointwise TopologicalSpace

/--  The interval `[0,1]` as a compact set with non-empty interior. -/
def TopologicalSpace.PositiveCompacts.icc01 : positive_compacts ℝ :=
  ⟨Icc 0 1, is_compact_Icc, by
    simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]⟩

universe u

/--  The set `[0,1]^ι` as a compact set with non-empty interior. -/
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

/--  The Haar measure equals the Lebesgue measure on `ℝ`. -/
theorem add_haar_measure_eq_volume : add_haar_measure Icc01 = volume := by
  convert (add_haar_measure_unique _ Icc01).symm
  ·
    simp [Icc01]
  ·
    infer_instance
  ·
    exact is_add_left_invariant_real_volume

instance : is_add_haar_measure (volume : Measureₓ ℝ) := by
  rw [← add_haar_measure_eq_volume]
  infer_instance

theorem is_add_left_invariant_real_volume_pi (ι : Type _) [Fintype ι] :
    is_add_left_invariant (⇑(volume : Measureₓ (ι → ℝ))) := by
  simp [← map_add_left_eq_self, Real.map_volume_pi_add_left]

/--  The Haar measure equals the Lebesgue measure on `ℝ^ι`. -/
theorem add_haar_measure_eq_volume_pi (ι : Type _) [Fintype ι] : add_haar_measure (pi_Icc01 ι) = volume := by
  convert (add_haar_measure_unique _ (pi_Icc01 ι)).symm
  ·
    simp only [pi_Icc01, volume_pi_pi fun i => Icc (0 : ℝ) 1, Finset.prod_const_one, Ennreal.of_real_one,
      Real.volume_Icc, one_smul, sub_zero]
  ·
    infer_instance
  ·
    exact is_add_left_invariant_real_volume_pi ι

instance is_add_haar_measure_volume_pi (ι : Type _) [Fintype ι] : is_add_haar_measure (volume : Measureₓ (ι → ℝ)) := by
  rw [← add_haar_measure_eq_volume_pi]
  infer_instance

namespace Measureₓ

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
  conv_lhs => rw [this]
  conv_rhs => rw [this]
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
    ·
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
  have ecomp : (e.symm ∘ e) = id := by
    ·
      ext x
      simp only [id.def, Function.comp_app, LinearEquiv.symm_apply_apply]
  rw [map_linear_map_add_haar_pi_eq_smul_add_haar hf (map e μ), LinearMap.map_smul,
    map_map Cesymm.measurable Ce.measurable, ecomp, measure.map_id]

@[simp]
theorem haar_preimage_linear_map {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measureₓ E) [is_add_haar_measure μ] {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) (s : Set E) :
    μ (f ⁻¹' s) = Ennreal.ofReal (abs (f.det⁻¹))*μ s :=
  calc μ (f ⁻¹' s) = measure.map f μ s :=
    ((f.equiv_of_det_ne_zero hf).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.map_apply s).symm
    _ = Ennreal.ofReal (abs (f.det⁻¹))*μ s := by
    rw [map_linear_map_add_haar_eq_smul_add_haar μ hf]
    rfl
    

/-!
### Basic properties of Haar measures on real vector spaces
-/


variable {E : Type _} [NormedGroup E] [MeasurableSpace E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  (μ : Measureₓ E) [is_add_haar_measure μ]

theorem map_add_haar_smul {r : ℝ} (hr : r ≠ 0) :
    measure.map ((· • ·) r) μ = Ennreal.ofReal (abs ((r^finrank ℝ E)⁻¹)) • μ := by
  let f : E →ₗ[ℝ] E := r • 1
  change measure.map f μ = _
  have hf : f.det ≠ 0 := by
    simp only [mul_oneₓ, LinearMap.det_smul, Ne.def, MonoidHom.map_one]
    intro h
    exact hr (pow_eq_zero h)
  simp only [map_linear_map_add_haar_eq_smul_add_haar μ hf, mul_oneₓ, LinearMap.det_smul, MonoidHom.map_one]

theorem add_haar_preimage_smul {r : ℝ} (hr : r ≠ 0) (s : Set E) :
    μ ((· • ·) r ⁻¹' s) = Ennreal.ofReal (abs ((r^finrank ℝ E)⁻¹))*μ s :=
  calc μ ((· • ·) r ⁻¹' s) = measure.map ((· • ·) r) μ s :=
    ((Homeomorph.smul (is_unit_iff_ne_zero.2 hr).Unit).toMeasurableEquiv.map_apply s).symm
    _ = Ennreal.ofReal (abs ((r^finrank ℝ E)⁻¹))*μ s := by
    rw [map_add_haar_smul μ hr]
    rfl
    

/--  Rescaling a set by a factor `r` multiplies its measure by `abs (r ^ dim)`. -/
theorem add_haar_smul (r : ℝ) (s : Set E) : μ (r • s) = Ennreal.ofReal (abs (r^finrank ℝ E))*μ s := by
  rcases ne_or_eq r 0 with (h | rfl)
  ·
    rw [← preimage_smul_inv₀ h, add_haar_preimage_smul μ (inv_ne_zero h), inv_pow₀, inv_inv₀]
  rcases eq_empty_or_nonempty s with (rfl | hs)
  ·
    simp only [measure_empty, mul_zero, smul_set_empty]
  rw [zero_smul_set hs, ← singleton_zero]
  by_cases' h : finrank ℝ E = 0
  ·
    have : Subsingleton E := finrank_zero_iff.1 h
    simp only [h, one_mulₓ, Ennreal.of_real_one, abs_one, Subsingleton.eq_univ_of_nonempty hs, pow_zeroₓ,
      Subsingleton.eq_univ_of_nonempty (singleton_nonempty (0 : E))]
  ·
    have : Nontrivial E := nontrivial_of_finrank_pos (bot_lt_iff_ne_bot.2 h)
    simp only [h, zero_mul, Ennreal.of_real_zero, abs_zero, Ne.def, not_false_iff, zero_pow', measure_singleton]

/-! We don't need to state `map_add_haar_neg` here, because it has already been proved for
general Haar measures on general commutative groups. -/


/-! ### Measure of balls -/


theorem add_haar_ball_center {E : Type _} [NormedGroup E] [MeasurableSpace E] [BorelSpace E] (μ : Measureₓ E)
    [is_add_haar_measure μ] (x : E) (r : ℝ) : μ (ball x r) = μ (ball (0 : E) r) := by
  have : ball (0 : E) r = (·+·) x ⁻¹' ball x r := by
    simp [preimage_add_ball]
  rw [this, add_haar_preimage_add]

theorem add_haar_closed_ball_center {E : Type _} [NormedGroup E] [MeasurableSpace E] [BorelSpace E] (μ : Measureₓ E)
    [is_add_haar_measure μ] (x : E) (r : ℝ) : μ (closed_ball x r) = μ (closed_ball (0 : E) r) := by
  have : closed_ball (0 : E) r = (·+·) x ⁻¹' closed_ball x r := by
    simp [preimage_add_closed_ball]
  rw [this, add_haar_preimage_add]

theorem add_haar_ball_pos {E : Type _} [NormedGroup E] [MeasurableSpace E] (μ : Measureₓ E) [is_add_haar_measure μ]
    (x : E) {r : ℝ} (hr : 0 < r) : 0 < μ (ball x r) :=
  is_open_ball.add_haar_pos μ (nonempty_ball.2 hr)

theorem add_haar_closed_ball_pos {E : Type _} [NormedGroup E] [MeasurableSpace E] (μ : Measureₓ E)
    [is_add_haar_measure μ] (x : E) {r : ℝ} (hr : 0 < r) : 0 < μ (closed_ball x r) :=
  lt_of_lt_of_leₓ (add_haar_ball_pos μ x hr) (measure_mono ball_subset_closed_ball)

theorem add_haar_ball_of_pos (x : E) {r : ℝ} (hr : 0 < r) :
    μ (ball x r) = Ennreal.ofReal (r^finrank ℝ E)*μ (ball 0 1) := by
  have : ball (0 : E) r = r • ball 0 1 := by
    simp [smul_ball hr.ne' (0 : E) 1, Real.norm_eq_abs, abs_of_nonneg hr.le]
  simp [this, add_haar_smul, abs_of_nonneg hr.le, add_haar_ball_center]

theorem add_haar_ball [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (ball x r) = Ennreal.ofReal (r^finrank ℝ E)*μ (ball 0 1) := by
  rcases LE.le.eq_or_lt hr with (h | h)
  ·
    simp [← h, zero_pow finrank_pos]
  ·
    exact add_haar_ball_of_pos μ x h

/--  The measure of a closed ball can be expressed in terms of the measure of the closed unit ball.
Use instead `add_haar_closed_ball`, which uses the measure of the open unit ball as a standard
form. -/
theorem add_haar_closed_ball' (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (closed_ball x r) = Ennreal.ofReal (r^finrank ℝ E)*μ (closed_ball 0 1) := by
  have : closed_ball (0 : E) r = r • closed_ball 0 1 := by
    simp [smul_closed_ball r (0 : E) zero_le_one, Real.norm_eq_abs, abs_of_nonneg hr]
  simp [this, add_haar_smul, abs_of_nonneg hr, add_haar_closed_ball_center]

theorem add_haar_closed_unit_ball_eq_add_haar_unit_ball : μ (closed_ball (0 : E) 1) = μ (ball 0 1) := by
  apply le_antisymmₓ _ (measure_mono ball_subset_closed_ball)
  have A :
    tendsto (fun r : ℝ => Ennreal.ofReal (r^finrank ℝ E)*μ (closed_ball (0 : E) 1)) (𝓝[<] 1)
      (𝓝 (Ennreal.ofReal (1^finrank ℝ E)*μ (closed_ball (0 : E) 1))) :=
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
    μ (closed_ball x r) = Ennreal.ofReal (r^finrank ℝ E)*μ (ball 0 1) := by
  rw [add_haar_closed_ball' μ x hr, add_haar_closed_unit_ball_eq_add_haar_unit_ball]

theorem add_haar_sphere_of_ne_zero (x : E) {r : ℝ} (hr : r ≠ 0) : μ (sphere x r) = 0 := by
  rcases lt_trichotomyₓ r 0 with (h | rfl | h)
  ·
    simp only [empty_diff, measure_empty, ← closed_ball_diff_ball, closed_ball_eq_empty.2 h]
  ·
    exact (hr rfl).elim
  ·
    rw [← closed_ball_diff_ball,
        measure_diff ball_subset_closed_ball measurable_set_closed_ball measurable_set_ball measure_ball_lt_top.ne,
        add_haar_ball_of_pos μ _ h, add_haar_closed_ball μ _ h.le, tsub_self] <;>
      infer_instance

theorem add_haar_sphere [Nontrivial E] (x : E) (r : ℝ) : μ (sphere x r) = 0 := by
  rcases eq_or_ne r 0 with (rfl | h)
  ·
    simp only [← closed_ball_diff_ball, diff_empty, closed_ball_zero, ball_zero, measure_singleton]
  ·
    exact add_haar_sphere_of_ne_zero μ x h

end Measureₓ

end MeasureTheory

