import Mathbin.Analysis.NormedSpace.OperatorNorm 
import Mathbin.Analysis.Complex.Basic

/-!
# Normed spaces over R or C

This file is about results on normed spaces over the fields `ℝ` and `ℂ`.

## Main definitions

None.

## Main theorems

* `continuous_linear_map.op_norm_bound_of_ball_bound`: A bound on the norms of values of a linear
  map in a ball yields a bound on the operator norm.

## Notes

This file exists mainly to avoid importing `is_R_or_C` in the main normed space theory files.
-/


open Metric

@[simp]
theorem IsROrC.norm_coe_norm {𝕜 : Type _} [IsROrC 𝕜] {E : Type _} [NormedGroup E] {z : E} : ∥(∥z∥ : 𝕜)∥ = ∥z∥ :=
  by 
    unfoldCoes 
    simp only [norm_algebra_map_eq, RingHom.to_fun_eq_coe, norm_norm]

variable{𝕜 : Type _}[IsROrC 𝕜]{E : Type _}[NormedGroup E][NormedSpace 𝕜 E]

theorem LinearMap.bound_of_sphere_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] 𝕜)
  (h : ∀ z _ : z ∈ sphere (0 : E) r, ∥f z∥ ≤ c) (z : E) : ∥f z∥ ≤ (c / r)*∥z∥ :=
  by 
    byCases' z_zero : z = 0
    ·
      rw [z_zero]
      simp only [LinearMap.map_zero, norm_zero, mul_zero]
    set z₁ := (r*∥z∥⁻¹ : 𝕜) • z with hz₁ 
    have norm_f_z₁ : ∥f z₁∥ ≤ c
    ·
      apply h z₁ 
      rw [mem_sphere_zero_iff_norm, hz₁, norm_smul, NormedField.norm_mul]
      simp only [NormedField.norm_inv, IsROrC.norm_coe_norm]
      rw [mul_assocₓ, inv_mul_cancel (norm_pos_iff.mpr z_zero).Ne.symm, mul_oneₓ]
      unfoldCoes 
      simp only [norm_algebra_map_eq, RingHom.to_fun_eq_coe]
      exact abs_of_pos r_pos 
    have r_ne_zero : (r : 𝕜) ≠ 0 := (algebraMap ℝ 𝕜).map_ne_zero.mpr r_pos.ne.symm 
    have eq : f z = (∥z∥ / r)*f z₁
    ·
      rw [hz₁, LinearMap.map_smul, smul_eq_mul]
      rw [←mul_assocₓ, ←mul_assocₓ, div_mul_cancel _ r_ne_zero, mul_inv_cancel, one_mulₓ]
      simp only [z_zero, IsROrC.of_real_eq_zero, norm_eq_zero, Ne.def, not_false_iff]
    rw [Eq, NormedField.norm_mul, NormedField.norm_div, IsROrC.norm_coe_norm, IsROrC.norm_of_nonneg r_pos.le,
      div_mul_eq_mul_div, div_mul_eq_mul_div, mul_commₓ]
    apply div_le_div _ _ r_pos rfl.ge
    ·
      exact mul_nonneg ((norm_nonneg _).trans norm_f_z₁) (norm_nonneg z)
    apply mul_le_mul norm_f_z₁ rfl.le (norm_nonneg z) ((norm_nonneg _).trans norm_f_z₁)

theorem LinearMap.bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] 𝕜)
  (h : ∀ z _ : z ∈ closed_ball (0 : E) r, ∥f z∥ ≤ c) : ∀ z : E, ∥f z∥ ≤ (c / r)*∥z∥ :=
  by 
    apply LinearMap.bound_of_sphere_bound r_pos c f 
    exact fun z hz => h z hz.le

theorem ContinuousLinearMap.op_norm_bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →L[𝕜] 𝕜)
  (h : ∀ z _ : z ∈ closed_ball (0 : E) r, ∥f z∥ ≤ c) : ∥f∥ ≤ c / r :=
  by 
    apply ContinuousLinearMap.op_norm_le_bound
    ·
      apply div_nonneg _ r_pos.le 
      exact
        (norm_nonneg _).trans
          (h 0
            (by 
              simp only [norm_zero, mem_closed_ball, dist_zero_left, r_pos.le]))
    apply LinearMap.bound_of_ball_bound r_pos 
    exact fun z hz => h z hz

