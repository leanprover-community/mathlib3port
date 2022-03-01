/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Analysis.NormedSpace.Star.Basic
import Mathbin.Analysis.NormedSpace.Spectrum

/-! # Spectral properties in C⋆-algebras
In this file, we establish various propreties related to the spectrum of elements in C⋆-algebras.
-/


open_locale TopologicalSpace Ennreal

open Filter Ennreal Spectrum

section UnitarySpectrum

variable {𝕜 : Type _} [NormedField 𝕜] {E : Type _} [NormedRing E] [StarRing E] [CstarRing E] [NormedAlgebra 𝕜 E]
  [CompleteSpace E] [Nontrivial E]

theorem unitary.spectrum_subset_circle (u : unitary E) : Spectrum 𝕜 (u : E) ⊆ Metric.Sphere 0 1 := by
  refine' fun k hk => mem_sphere_zero_iff_norm.mpr (le_antisymmₓ _ _)
  · simpa only [CstarRing.norm_coe_unitary u] using norm_le_norm_of_mem hk
    
  · rw [← unitary.coe_to_units_apply u] at hk
    have hnk := ne_zero_of_mem_of_unit hk
    rw [← inv_invₓ (unitary.toUnits u), ← Spectrum.map_inv, Set.mem_inv] at hk
    have : ∥k∥⁻¹ ≤ ∥↑(unitary.toUnits u)⁻¹∥
    simpa only [norm_inv] using norm_le_norm_of_mem hk
    simpa using inv_le_of_inv_le (norm_pos_iff.mpr hnk) this
    

theorem Spectrum.subset_circle_of_unitary {u : E} (h : u ∈ unitary E) : Spectrum 𝕜 u ⊆ Metric.Sphere 0 1 :=
  unitary.spectrum_subset_circle ⟨u, h⟩

end UnitarySpectrum

section ComplexScalars

variable {A : Type _} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [CstarRing A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [TopologicalSpace.SecondCountableTopology A]

theorem spectral_radius_eq_nnnorm_of_self_adjoint {a : A} (ha : a ∈ selfAdjoint A) : spectralRadius ℂ a = ∥a∥₊ := by
  have hconst : tendsto (fun n : ℕ => (∥a∥₊ : ℝ≥0∞)) at_top _ := tendsto_const_nhds
  refine' tendsto_nhds_unique _ hconst
  convert
    (Spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a : A)).comp
      (Nat.tendsto_pow_at_top_at_top_of_one_lt
        (by
          linarith : 1 < 2))
  refine' funext fun n => _
  rw [Function.comp_app, nnnorm_pow_two_pow_of_self_adjoint ha, Ennreal.coe_pow, ← rpow_nat_cast, ← rpow_mul]
  simp

theorem selfAdjoint.coe_spectral_radius_eq_nnnorm (a : selfAdjoint A) : spectralRadius ℂ (a : A) = ∥(a : A)∥₊ :=
  spectral_radius_eq_nnnorm_of_self_adjoint a.property

end ComplexScalars

