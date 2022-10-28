/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Analysis.NormedSpace.Star.Basic
import Mathbin.Analysis.NormedSpace.Spectrum
import Mathbin.Algebra.Star.Module
import Mathbin.Analysis.NormedSpace.Star.Exponential
import Mathbin.Algebra.Star.StarAlgHom

/-! # Spectral properties in C⋆-algebras
In this file, we establish various propreties related to the spectrum of elements in C⋆-algebras.
-/


-- mathport name: «expr ⋆»
local postfix:max "⋆" => star

section

open TopologicalSpace Ennreal

open Filter Ennreal Spectrum CstarRing

section UnitarySpectrum

variable {𝕜 : Type _} [NormedField 𝕜] {E : Type _} [NormedRing E] [StarRing E] [CstarRing E] [NormedAlgebra 𝕜 E]
  [CompleteSpace E]

theorem unitary.spectrum_subset_circle (u : unitary E) : Spectrum 𝕜 (u : E) ⊆ Metric.Sphere 0 1 := by
  nontriviality E
  refine' fun k hk => mem_sphere_zero_iff_norm.mpr (le_antisymm _ _)
  · simpa only [CstarRing.norm_coe_unitary u] using norm_le_norm_of_mem hk
    
  · rw [← unitary.coe_to_units_apply u] at hk
    have hnk := ne_zero_of_mem_of_unit hk
    rw [← inv_inv (unitary.toUnits u), ← Spectrum.map_inv, Set.mem_inv] at hk
    have : ∥k∥⁻¹ ≤ ∥↑(unitary.toUnits u)⁻¹∥
    simpa only [norm_inv] using norm_le_norm_of_mem hk
    simpa using inv_le_of_inv_le (norm_pos_iff.mpr hnk) this
    

theorem Spectrum.subset_circle_of_unitary {u : E} (h : u ∈ unitary E) : Spectrum 𝕜 u ⊆ Metric.Sphere 0 1 :=
  unitary.spectrum_subset_circle ⟨u, h⟩

end UnitarySpectrum

section ComplexScalars

open Complex

variable {A : Type _} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A] [CstarRing A]

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap ℂ A

theorem IsSelfAdjoint.spectral_radius_eq_nnnorm {a : A} (ha : IsSelfAdjoint a) : spectralRadius ℂ a = ∥a∥₊ := by
  have hconst : tendsto (fun n : ℕ => (∥a∥₊ : ℝ≥0∞)) at_top _ := tendsto_const_nhds
  refine' tendsto_nhds_unique _ hconst
  convert
    (Spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a : A)).comp
      (Nat.tendsto_pow_at_top_at_top_of_one_lt one_lt_two)
  refine' funext fun n => _
  rw [Function.comp_app, ha.nnnorm_pow_two_pow, Ennreal.coe_pow, ← rpow_nat_cast, ← rpow_mul]
  simp

theorem IsStarNormal.spectral_radius_eq_nnnorm (a : A) [IsStarNormal a] : spectralRadius ℂ a = ∥a∥₊ := by
  refine' (Ennreal.pow_strict_mono two_ne_zero).Injective _
  have heq :
    (fun n : ℕ => (∥(a⋆ * a) ^ n∥₊ ^ (1 / n : ℝ) : ℝ≥0∞)) =
      (fun x => x ^ 2) ∘ fun n : ℕ => (∥a ^ n∥₊ ^ (1 / n : ℝ) : ℝ≥0∞) :=
    by
    funext
    rw [Function.comp_apply, ← rpow_nat_cast, ← rpow_mul, mul_comm, rpow_mul, rpow_nat_cast, ← coe_pow, sq, ←
      nnnorm_star_mul_self, Commute.mul_pow (star_comm_self' a), star_pow]
  have h₂ :=
    ((Ennreal.continuous_pow 2).Tendsto (spectralRadius ℂ a)).comp
      (Spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius a)
  rw [← HEq] at h₂
  convert tendsto_nhds_unique h₂ (pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a⋆ * a))
  rw [(IsSelfAdjoint.star_mul_self a).spectral_radius_eq_nnnorm, sq, nnnorm_star_mul_self, coe_mul]

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem IsSelfAdjoint.mem_spectrum_eq_re [StarModule ℂ A] {a : A} (ha : IsSelfAdjoint a) {z : ℂ}
    (hz : z ∈ Spectrum ℂ a) : z = z.re := by
  let Iu := Units.mk0 I I_ne_zero
  have : exp ℂ (I • z) ∈ Spectrum ℂ (exp ℂ (I • a)) := by
    simpa only [Units.smul_def, Units.coe_mk0] using Spectrum.exp_mem_exp (Iu • a) (smul_mem_smul_iff.mpr hz)
  exact
    Complex.ext (of_real_re _)
      (by
        simpa only [← Complex.exp_eq_exp_ℂ, mem_sphere_zero_iff_norm, norm_eq_abs, abs_exp, Real.exp_eq_one_iff,
          smul_eq_mul, I_mul, neg_eq_zero] using Spectrum.subset_circle_of_unitary ha.exp_i_smul_unitary this)

/-- Any element of the spectrum of a selfadjoint is real. -/
theorem selfAdjoint.mem_spectrum_eq_re [StarModule ℂ A] (a : selfAdjoint A) {z : ℂ} (hz : z ∈ Spectrum ℂ (a : A)) :
    z = z.re :=
  a.Prop.mem_spectrum_eq_re hz

/-- The spectrum of a selfadjoint is real -/
theorem IsSelfAdjoint.coe_re_map_spectrum [StarModule ℂ A] {a : A} (ha : IsSelfAdjoint a) :
    Spectrum ℂ a = (coe ∘ re '' Spectrum ℂ a : Set ℂ) :=
  le_antisymm (fun z hz => ⟨z, hz, (ha.mem_spectrum_eq_re hz).symm⟩) fun z => by
    rintro ⟨z, hz, rfl⟩
    simpa only [(ha.mem_spectrum_eq_re hz).symm, Function.comp_app] using hz

/-- The spectrum of a selfadjoint is real -/
theorem selfAdjoint.coe_re_map_spectrum [StarModule ℂ A] (a : selfAdjoint A) :
    Spectrum ℂ (a : A) = (coe ∘ re '' Spectrum ℂ (a : A) : Set ℂ) :=
  a.property.coe_re_map_spectrum

end ComplexScalars

namespace StarAlgHom

variable {F A B : Type _} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A] [CstarRing A] [NormedRing B]
  [NormedAlgebra ℂ B] [CompleteSpace B] [StarRing B] [CstarRing B] [hF : StarAlgHomClass F ℂ A B] (φ : F)

include hF

/-- A star algebra homomorphism of complex C⋆-algebras is norm contractive. -/
theorem nnnorm_apply_le (a : A) : ∥(φ a : B)∥₊ ≤ ∥a∥₊ := by
  suffices ∀ s : A, IsSelfAdjoint s → ∥φ s∥₊ ≤ ∥s∥₊ by
    exact
      nonneg_le_nonneg_of_sq_le_sq zero_le'
        (by simpa only [nnnorm_star_mul_self, map_star, map_mul] using this _ (IsSelfAdjoint.star_mul_self a))
  · intro s hs
    simpa only [hs.spectral_radius_eq_nnnorm, (hs.star_hom_apply φ).spectral_radius_eq_nnnorm, coe_le_coe] using
      show spectralRadius ℂ (φ s) ≤ spectralRadius ℂ s from supr_le_supr_of_subset (AlgHom.spectrum_apply_subset φ s)
    

/-- A star algebra homomorphism of complex C⋆-algebras is norm contractive. -/
theorem norm_apply_le (a : A) : ∥(φ a : B)∥ ≤ ∥a∥ :=
  nnnorm_apply_le φ a

/-- Star algebra homomorphisms between C⋆-algebras are continuous linear maps.
See note [lower instance priority] -/
noncomputable instance (priority := 100) : ContinuousLinearMapClass F ℂ A B :=
  { AlgHomClass.linearMapClass with
    map_continuous := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ 1 (by simpa only [one_mul] using nnnorm_apply_le φ) }

end StarAlgHom

end

namespace WeakDual

open ContinuousMap Complex

open ComplexStarModule

variable {F A : Type _} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A] [CstarRing A] [StarModule ℂ A]
  [hF : AlgHomClass F ℂ A ℂ]

include hF

/-- This instance is provided instead of `star_alg_hom_class` to avoid type class inference loops.
See note [lower instance priority] -/
noncomputable instance (priority := 100) : StarHomClass F A ℂ where
  coe φ := φ
  coe_injective' := FunLike.coe_injective'
  map_star φ a := by
    suffices hsa : ∀ s : selfAdjoint A, (φ s)⋆ = φ s
    · rw [← real_part_add_I_smul_imaginary_part a]
      simp only [map_add, map_smul, star_add, star_smul, hsa, selfAdjoint.star_coe_eq]
      
    · intro s
      have := AlgHom.apply_mem_spectrum φ (s : A)
      rw [selfAdjoint.coe_re_map_spectrum s] at this
      rcases this with ⟨⟨_, _⟩, _, heq⟩
      rw [← HEq, IsROrC.star_def, IsROrC.conj_of_real]
      

/-- This is not an instance to avoid type class inference loops. See
`weak_dual.complex.star_hom_class`. -/
noncomputable def _root_.alg_hom_class.star_alg_hom_class : StarAlgHomClass F ℂ A ℂ :=
  { hF, WeakDual.Complex.starHomClass with }

end WeakDual

