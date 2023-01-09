/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang

! This file was ported from Lean 3 source module analysis.complex.conformal
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.Isometry
import Mathbin.Analysis.NormedSpace.ConformalLinearMap

/-!
# Conformal maps between complex vector spaces

We prove the sufficient and necessary conditions for a real-linear map between complex vector spaces
to be conformal.

## Main results

* `is_conformal_map_complex_linear`: a nonzero complex linear map into an arbitrary complex
                                     normed space is conformal.
* `is_conformal_map_complex_linear_conj`: the composition of a nonzero complex linear map with
                                          `conj` is complex linear.
* `is_conformal_map_iff_is_complex_or_conj_linear`: a real linear map between the complex
                                                            plane is conformal iff it's complex
                                                            linear or the composition of
                                                            some complex linear map and `conj`.

## Warning

Antiholomorphic functions such as the complex conjugate are considered as conformal functions in
this file.
-/


noncomputable section

open Complex ContinuousLinearMap

open ComplexConjugate

theorem isConformalMapConj : IsConformalMap (conjLie : ℂ →L[ℝ] ℂ) :=
  conjLie.toLinearIsometry.IsConformalMap
#align is_conformal_map_conj isConformalMapConj

section ConformalIntoComplexNormed

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] {z : ℂ}
  {g : ℂ →L[ℝ] E} {f : ℂ → E}

theorem isConformalMapComplexLinear {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) :
    IsConformalMap (map.restrictScalars ℝ) :=
  by
  have minor₁ : ‖map 1‖ ≠ 0 := by simpa only [ext_ring_iff, Ne.def, norm_eq_zero] using nonzero
  refine' ⟨‖map 1‖, minor₁, ⟨‖map 1‖⁻¹ • map, _⟩, _⟩
  · intro x
    simp only [LinearMap.smul_apply]
    have : x = x • 1 := by rw [smul_eq_mul, mul_one]
    nth_rw 1 [this]
    rw [_root_.coe_coe map, LinearMap.coe_coe_is_scalar_tower]
    simp only [map.coe_coe, map.map_smul, norm_smul, norm_inv, norm_norm]
    field_simp only [one_mul]
  · ext1
    simp only [minor₁, LinearMap.smul_apply, _root_.coe_coe, LinearMap.coe_coe_is_scalar_tower,
      ContinuousLinearMap.coe_coe, coe_restrict_scalars', coe_smul',
      LinearIsometry.coe_to_continuous_linear_map, LinearIsometry.coe_mk, Pi.smul_apply,
      smul_inv_smul₀, Ne.def, not_false_iff]
#align is_conformal_map_complex_linear isConformalMapComplexLinear

theorem isConformalMapComplexLinearConj {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) :
    IsConformalMap ((map.restrictScalars ℝ).comp (conjCle : ℂ →L[ℝ] ℂ)) :=
  (isConformalMapComplexLinear nonzero).comp isConformalMapConj
#align is_conformal_map_complex_linear_conj isConformalMapComplexLinearConj

end ConformalIntoComplexNormed

section ConformalIntoComplexPlane

open ContinuousLinearMap

variable {f : ℂ → ℂ} {z : ℂ} {g : ℂ →L[ℝ] ℂ}

theorem IsConformalMap.is_complex_or_conj_linear (h : IsConformalMap g) :
    (∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g) ∨
      ∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g ∘L ↑conj_cle :=
  by
  rcases h with ⟨c, hc, li, rfl⟩
  obtain ⟨li, rfl⟩ : ∃ li' : ℂ ≃ₗᵢ[ℝ] ℂ, li'.toLinearIsometry = li
  exact
    ⟨li.to_linear_isometry_equiv rfl, by
      ext1
      rfl⟩
  rcases linear_isometry_complex li with ⟨a, rfl | rfl⟩
  -- let rot := c • (a : ℂ) • continuous_linear_map.id ℂ ℂ,
  · refine' Or.inl ⟨c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ, _⟩
    ext1
    simp only [coe_restrict_scalars', smul_apply, LinearIsometry.coe_to_continuous_linear_map,
      LinearIsometryEquiv.coe_to_linear_isometry, rotation_apply, id_apply, smul_eq_mul]
  · refine' Or.inr ⟨c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ, _⟩
    ext1
    simp only [coe_restrict_scalars', smul_apply, LinearIsometry.coe_to_continuous_linear_map,
      LinearIsometryEquiv.coe_to_linear_isometry, rotation_apply, id_apply, smul_eq_mul, comp_apply,
      LinearIsometryEquiv.trans_apply, ContinuousLinearEquiv.coe_coe, conj_cle_apply,
      conj_lie_apply, conj_conj]
#align is_conformal_map.is_complex_or_conj_linear IsConformalMap.is_complex_or_conj_linear

/-- A real continuous linear map on the complex plane is conformal if and only if the map or its
    conjugate is complex linear, and the map is nonvanishing. -/
theorem is_conformal_map_iff_is_complex_or_conj_linear :
    IsConformalMap g ↔
      ((∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g) ∨
          ∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g ∘L ↑conj_cle) ∧
        g ≠ 0 :=
  by
  constructor
  · exact fun h => ⟨h.is_complex_or_conj_linear, h.NeZero⟩
  · rintro ⟨⟨map, rfl⟩ | ⟨map, hmap⟩, h₂⟩
    · refine' isConformalMapComplexLinear _
      contrapose! h₂ with w
      simp only [w, restrict_scalars_zero]
    · have minor₁ : g = map.restrict_scalars ℝ ∘L ↑conj_cle :=
        by
        ext1
        simp only [hmap, coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply,
          conj_cle_apply, starRingEnd_self_apply]
      rw [minor₁] at h₂⊢
      refine' isConformalMapComplexLinearConj _
      contrapose! h₂ with w
      simp only [w, restrict_scalars_zero, zero_comp]
#align is_conformal_map_iff_is_complex_or_conj_linear is_conformal_map_iff_is_complex_or_conj_linear

end ConformalIntoComplexPlane

