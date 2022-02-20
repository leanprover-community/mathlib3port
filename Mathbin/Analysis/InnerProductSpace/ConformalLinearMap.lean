/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import Mathbin.Analysis.NormedSpace.ConformalLinearMap
import Mathbin.Analysis.InnerProductSpace.Basic

/-!
# Conformal maps between inner product spaces

In an inner product space, a map is conformal iff it preserves inner products up to a scalar factor.
-/


variable {E F : Type _} [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

open LinearIsometry ContinuousLinearMap

open_locale RealInnerProductSpace

theorem is_conformal_map_iff (f' : E →L[ℝ] F) :
    IsConformalMap f' ↔ ∃ c : ℝ, 0 < c ∧ ∀ u v : E, ⟪f' u, f' v⟫ = (c : ℝ) * ⟪u, v⟫ := by
  constructor
  · rintro ⟨c₁, hc₁, li, h⟩
    refine' ⟨c₁ * c₁, mul_self_pos.2 hc₁, fun u v => _⟩
    simp only [h, Pi.smul_apply, inner_map_map, real_inner_smul_left, real_inner_smul_right, mul_assoc]
    
  · rintro ⟨c₁, hc₁, huv⟩
    let c := Real.sqrt c₁⁻¹
    have hc : c ≠ 0 := fun w => by
      simp only [c] at w <;> exact (real.sqrt_ne_zero'.mpr <| inv_pos.mpr hc₁) w
    let f₁ := c • f'
    have minor : (f₁ : E → F) = c • f' := rfl
    have minor' : (f' : E → F) = c⁻¹ • f₁ := by
      ext <;> simp_rw [minor, Pi.smul_apply] <;> rw [smul_smul, inv_mul_cancel hc, one_smul]
    refine' ⟨c⁻¹, inv_ne_zero hc, f₁.to_linear_map.isometry_of_inner fun u v => _, minor'⟩
    simp_rw [to_linear_map_eq_coe, ContinuousLinearMap.coe_coe, minor, Pi.smul_apply]
    rw [real_inner_smul_left, real_inner_smul_right, huv u v, ← mul_assoc, ← mul_assoc,
      Real.mul_self_sqrt <| le_of_ltₓ <| inv_pos.mpr hc₁, inv_mul_cancel <| ne_of_gtₓ hc₁, one_mulₓ]
    

