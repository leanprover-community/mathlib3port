import Mathbin.Algebra.Algebra.Spectrum
import Mathbin.Analysis.SpecialFunctions.Pow
import Mathbin.Analysis.Complex.CauchyIntegral
import Mathbin.Analysis.Analytic.RadiusLiminf

/-!
# The spectrum of elements in a complete normed algebra

This file contains the basic theory for the resolvent and spectrum of a Banach algebra.

## Main definitions

* `spectral_radius : ℝ≥0∞`: supremum of `∥k∥₊` for all `k ∈ spectrum 𝕜 a`

## Main statements

* `spectrum.is_open_resolvent_set`: the resolvent set is open.
* `spectrum.is_closed`: the spectrum is closed.
* `spectrum.subset_closed_ball_norm`: the spectrum is a subset of closed disk of radius
  equal to the norm.
* `spectrum.is_compact`: the spectrum is compact.
* `spectrum.spectral_radius_le_nnnorm`: the spectral radius is bounded above by the norm.
* `spectrum.has_deriv_at_resolvent`: the resolvent function is differentiable on the resolvent set.
* `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius`: Gelfand's formula for the
  spectral radius in Banach algebras over `ℂ`.


## TODO

* after we have Liouville's theorem, prove that the spectrum is nonempty when the
  scalar field is ℂ.
* compute all derivatives of `resolvent a`.

-/


open_locale Ennreal

/-- The *spectral radius* is the supremum of the `nnnorm` (`∥⬝∥₊`) of elements in the spectrum,
    coerced into an element of `ℝ≥0∞`. Note that it is possible for `spectrum 𝕜 a = ∅`. In this
    case, `spectral_radius a = 0`.  It is also possible that `spectrum 𝕜 a` be unbounded (though
    not for Banach algebras, see `spectrum.is_bounded`, below).  In this case,
    `spectral_radius a = ∞`. -/
noncomputable def spectralRadius (𝕜 : Type _) {A : Type _} [NormedField 𝕜] [Ringₓ A] [Algebra 𝕜 A] (a : A) : ℝ≥0∞ :=
  ⨆ k ∈ Spectrum 𝕜 a, ∥k∥₊

variable {𝕜 : Type _} {A : Type _}

namespace Spectrum

section SpectrumCompact

variable [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

local notation "σ" => Spectrum 𝕜

local notation "ρ" => ResolventSet 𝕜

local notation "↑ₐ" => algebraMap 𝕜 A

theorem mem_resolvent_set_of_spectral_radius_lt {a : A} {k : 𝕜} (h : spectralRadius 𝕜 a < ∥k∥₊) : k ∈ ρ a :=
  not_not.mp fun hn => (lt_self_iff_false _).mp (lt_of_le_of_ltₓ (le_bsupr k hn) h)

variable [CompleteSpace A]

theorem is_open_resolvent_set (a : A) : IsOpen (ρ a) :=
  Units.is_open.Preimage ((algebra_map_isometry 𝕜 A).Continuous.sub continuous_const)

theorem IsClosed (a : A) : IsClosed (σ a) :=
  (is_open_resolvent_set a).is_closed_compl

theorem mem_resolvent_of_norm_lt {a : A} {k : 𝕜} (h : ∥a∥ < ∥k∥) : k ∈ ρ a := by
  rw [ResolventSet, Set.mem_set_of_eq, Algebra.algebra_map_eq_smul_one]
  have hk : k ≠ 0 :=
    ne_zero_of_norm_ne_zero
      (by
        linarith [norm_nonneg a])
  let ku := Units.map ↑ₐ.toMonoidHom (Units.mk0 k hk)
  have hku : ∥-a∥ < ∥(↑ku⁻¹ : A)∥⁻¹ := by
    simpa [ku, algebra_map_isometry] using h
  simpa [ku, sub_eq_add_neg, Algebra.algebra_map_eq_smul_one] using (ku.add (-a) hku).IsUnit

theorem norm_le_norm_of_mem {a : A} {k : 𝕜} (hk : k ∈ σ a) : ∥k∥ ≤ ∥a∥ :=
  le_of_not_ltₓ <| mt mem_resolvent_of_norm_lt hk

theorem subset_closed_ball_norm (a : A) : σ a ⊆ Metric.ClosedBall (0 : 𝕜) ∥a∥ := fun k hk => by
  simp [norm_le_norm_of_mem hk]

theorem is_bounded (a : A) : Metric.Bounded (σ a) :=
  (Metric.bounded_iff_subset_ball 0).mpr ⟨∥a∥, subset_closed_ball_norm a⟩

theorem IsCompact [ProperSpace 𝕜] (a : A) : IsCompact (σ a) :=
  Metric.is_compact_of_is_closed_bounded (is_closed a) (is_bounded a)

theorem spectral_radius_le_nnnorm (a : A) : spectralRadius 𝕜 a ≤ ∥a∥₊ := by
  refine' bsupr_le fun k hk => _
  exact_mod_cast norm_le_norm_of_mem hk

open Ennreal Polynomial

variable (𝕜)

theorem spectral_radius_le_pow_nnnorm_pow_one_div (a : A) (n : ℕ) :
    spectralRadius 𝕜 a ≤ ∥a ^ (n + 1)∥₊ ^ (1 / (n + 1) : ℝ) := by
  refine' bsupr_le fun k hk => _
  have pow_mem : k ^ (n + 1) ∈ σ (a ^ (n + 1)) := by
    simpa only [one_mulₓ, Algebra.algebra_map_eq_smul_one, one_smul, aeval_monomial, one_mulₓ, eval_monomial] using
      subset_polynomial_aeval a (monomial (n + 1) (1 : 𝕜)) ⟨k, hk, rfl⟩
  have nnnorm_pow_le : (↑(∥k∥₊ ^ (n + 1)) : ℝ≥0∞) ≤ ↑∥a ^ (n + 1)∥₊ := by
    simpa only [norm_to_nnreal, NormedField.nnnorm_pow k (n + 1)] using
      coe_mono (Real.to_nnreal_mono (norm_le_norm_of_mem pow_mem))
  have hn : 0 < (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos'
  convert monotone_rpow_of_nonneg (one_div_pos.mpr hn).le nnnorm_pow_le
  erw [coe_pow, ← rpow_nat_cast, ← rpow_mul, mul_one_div_cancel hn.ne', rpow_one]

end SpectrumCompact

section ResolventDeriv

variable [NondiscreteNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "ρ" => ResolventSet 𝕜

local notation "↑ₐ" => algebraMap 𝕜 A

theorem has_deriv_at_resolvent {a : A} {k : 𝕜} (hk : k ∈ ρ a) : HasDerivAt (resolvent a) (-(resolvent a k ^ 2)) k := by
  have H₁ : HasFderivAt Ring.inverse _ (↑ₐ k - a) := has_fderiv_at_ring_inverse hk.unit
  have H₂ : HasDerivAt (fun k => ↑ₐ k - a) 1 k := by
    simpa using (Algebra.linearMap 𝕜 A).HasDerivAt.sub_const a
  simpa [resolvent, sq, hk.unit_spec, ← Ring.inverse_unit hk.unit] using H₁.comp_has_deriv_at k H₂

end ResolventDeriv

section OneSubSmul

open ContinuousMultilinearMap Ennreal FormalMultilinearSeries

open_locale Nnreal Ennreal

variable [NondiscreteNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

variable (𝕜)

/-- In a Banach algebra `A` over a nondiscrete normed field `𝕜`, for any `a : A` the
power series with coefficients `a ^ n` represents the function `(1 - z • a)⁻¹` in a disk of
radius `∥a∥₊⁻¹`. -/
theorem has_fpower_series_on_ball_inverse_one_sub_smul [CompleteSpace A] (a : A) :
    HasFpowerSeriesOnBall (fun z : 𝕜 => Ring.inverse (1 - z • a))
      (fun n => ContinuousMultilinearMap.mkPiField 𝕜 (Finₓ n) (a ^ n)) 0 ∥a∥₊⁻¹ :=
  { r_le := by
      refine' le_of_forall_nnreal_lt fun r hr => le_radius_of_bound_nnreal _ (max 1 ∥(1 : A)∥₊) fun n => _
      rw [← norm_to_nnreal, norm_mk_pi_field, norm_to_nnreal]
      cases n
      · simp only [le_reflₓ, mul_oneₓ, or_trueₓ, le_max_iff, pow_zeroₓ]
        
      · refine'
          le_transₓ (le_transₓ (mul_le_mul_right' (nnnorm_pow_le' a n.succ_pos) (r ^ n.succ)) _) (le_max_leftₓ _ _)
        · by_cases' ∥a∥₊ = 0
          · simp only [h, zero_mul, zero_le', pow_succₓ]
            
          · rw [← coe_inv h, coe_lt_coe, Nnreal.lt_inv_iff_mul_lt h] at hr
            simpa only [← mul_powₓ, mul_comm] using pow_le_one' hr.le n.succ
            
          
        ,
    r_pos := Ennreal.inv_pos.mpr coe_ne_top,
    HasSum := fun y hy => by
      have norm_lt : ∥y • a∥ < 1 := by
        by_cases' h : ∥a∥₊ = 0
        · simp only [nnnorm_eq_zero.mp h, norm_zero, zero_lt_one, smul_zero]
          
        · have nnnorm_lt : ∥y∥₊ < ∥a∥₊⁻¹ := by
            simpa only [← coe_inv h, mem_ball_zero_iff, Metric.emetric_ball_nnreal] using hy
          rwa [← coe_nnnorm, ← Real.lt_to_nnreal_iff_coe_lt, Real.to_nnreal_one, nnnorm_smul, ←
            Nnreal.lt_inv_iff_mul_lt h]
          
      simpa [← smul_pow, (NormedRing.summable_geometric_of_norm_lt_1 _ norm_lt).has_sum_iff] using
        (NormedRing.inverse_one_sub _ norm_lt).symm }

variable {𝕜}

theorem is_unit_one_sub_smul_of_lt_inv_radius {a : A} {z : 𝕜} (h : ↑∥z∥₊ < (spectralRadius 𝕜 a)⁻¹) :
    IsUnit (1 - z • a) := by
  by_cases' hz : z = 0
  · simp only [hz, is_unit_one, sub_zero, zero_smul]
    
  · let u := Units.mk0 z hz
    suffices hu : IsUnit (u⁻¹ • 1 - a)
    · rwa [IsUnit.smul_sub_iff_sub_inv_smul, inv_invₓ u] at hu
      
    · rw [Units.smul_def, ← Algebra.algebra_map_eq_smul_one, ← mem_resolvent_set_iff]
      refine' mem_resolvent_set_of_spectral_radius_lt _
      rwa [Units.coe_inv', NormedField.nnnorm_inv,
        coe_inv (nnnorm_ne_zero_iff.mpr (Units.coe_mk0 hz ▸ hz : (u : 𝕜) ≠ 0)), lt_inv_iff_lt_inv]
      
    

/-- In a Banach algebra `A` over `𝕜`, for `a : A` the function `λ z, (1 - z • a)⁻¹` is
differentiable on any closed ball centered at zero of radius `r < (spectral_radius 𝕜 a)⁻¹`. -/
theorem differentiable_on_inverse_one_sub_smul [CompleteSpace A] {a : A} {r : ℝ≥0 }
    (hr : (r : ℝ≥0∞) < (spectralRadius 𝕜 a)⁻¹) :
    DifferentiableOn 𝕜 (fun z : 𝕜 => Ring.inverse (1 - z • a)) (Metric.ClosedBall 0 r) := by
  intro z z_mem
  apply DifferentiableAt.differentiable_within_at
  have hu : IsUnit (1 - z • a) := by
    refine' is_unit_one_sub_smul_of_lt_inv_radius (lt_of_le_of_ltₓ (coe_mono _) hr)
    simpa only [norm_to_nnreal, Real.to_nnreal_coe] using Real.to_nnreal_mono (mem_closed_ball_zero_iff.mp z_mem)
  have H₁ : Differentiable 𝕜 fun w : 𝕜 => 1 - w • a := (differentiable_id.smul_const a).const_sub 1
  exact DifferentiableAt.comp z (differentiable_at_inverse hu.unit) H₁.differentiable_at

end OneSubSmul

section GelfandFormula

open Filter Ennreal ContinuousMultilinearMap

open_locale TopologicalSpace

variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace.SecondCountableTopology A]

/-- The `limsup` relationship for the spectral radius used to prove `spectrum.gelfand_formula`. -/
theorem limsup_pow_nnnorm_pow_one_div_le_spectral_radius (a : A) :
    (limsupₓ atTop fun n : ℕ => ↑∥a ^ n∥₊ ^ (1 / n : ℝ)) ≤ spectralRadius ℂ a := by
  refine' ennreal.inv_le_inv.mp (le_of_forall_pos_nnreal_lt fun r r_pos r_lt => _)
  simp_rw [inv_limsup, ← one_div]
  let p : FormalMultilinearSeries ℂ ℂ A := fun n => ContinuousMultilinearMap.mkPiField ℂ (Finₓ n) (a ^ n)
  suffices h : (r : ℝ≥0∞) ≤ p.radius
  · convert h
    simp only [p.radius_eq_liminf, ← norm_to_nnreal, norm_mk_pi_field]
    refine' congr_argₓ _ (funext fun n => congr_argₓ _ _)
    rw [norm_to_nnreal, Ennreal.coe_rpow_def ∥a ^ n∥₊ (1 / n : ℝ), if_neg]
    exact fun ha => by
      linarith [ha.2, (one_div_nonneg.mpr n.cast_nonneg : 0 ≤ (1 / n : ℝ))]
    
  · have H₁ := (differentiable_on_inverse_one_sub_smul r_lt).HasFpowerSeriesOnBall r_pos
    exact ((has_fpower_series_on_ball_inverse_one_sub_smul ℂ a).exchange_radius H₁).r_le
    

/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectral_radius` of `a` is the limit of the sequence `∥a ^ n∥₊ ^ (1 / n)` -/
theorem pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a : A) :
    Tendsto (fun n : ℕ => (∥a ^ n∥₊ ^ (1 / n : ℝ) : ℝ≥0∞)) atTop (𝓝 (spectralRadius ℂ a)) := by
  refine'
    tendsto_of_le_liminf_of_limsup_le _ _
      (by
        infer_auto_param)
      (by
        infer_auto_param)
  · rw [← liminf_nat_add _ 1, liminf_eq_supr_infi_of_nat]
    refine' le_transₓ _ (le_supr _ 0)
    exact le_binfi fun i hi => spectral_radius_le_pow_nnnorm_pow_one_div ℂ a i
    
  · exact limsup_pow_nnnorm_pow_one_div_le_spectral_radius a
    

/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectral_radius` of `a` is the limit of the sequence `∥a ^ n∥₊ ^ (1 / n)` -/
theorem pow_norm_pow_one_div_tendsto_nhds_spectral_radius (a : A) :
    Tendsto (fun n : ℕ => Ennreal.ofReal (∥a ^ n∥ ^ (1 / n : ℝ))) atTop (𝓝 (spectralRadius ℂ a)) := by
  convert pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius a
  ext1
  rw [← of_real_rpow_of_nonneg (norm_nonneg _) _, ← coe_nnnorm, coe_nnreal_eq]
  exact
    one_div_nonneg.mpr
      (by
        exact_mod_cast zero_le _)

end GelfandFormula

end Spectrum

namespace AlgHom

section NormedField

variable [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "↑ₐ" => algebraMap 𝕜 A

/-- An algebra homomorphism into the base field, as a continuous linear map (since it is
automatically bounded). -/
@[simps]
def to_continuous_linear_map (φ : A →ₐ[𝕜] 𝕜) : A →L[𝕜] 𝕜 :=
  φ.toLinearMap.mkContinuousOfExistsBound <|
    ⟨1, fun a => (one_mulₓ ∥a∥).symm ▸ Spectrum.norm_le_norm_of_mem (φ.apply_mem_spectrum _)⟩

theorem Continuous (φ : A →ₐ[𝕜] 𝕜) : Continuous φ :=
  φ.toContinuousLinearMap.Continuous

end NormedField

section NondiscreteNormedField

variable [NondiscreteNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "↑ₐ" => algebraMap 𝕜 A

@[simp]
theorem to_continuous_linear_map_norm [NormOneClass A] (φ : A →ₐ[𝕜] 𝕜) : ∥φ.toContinuousLinearMap∥ = 1 :=
  ContinuousLinearMap.op_norm_eq_of_bounds zero_le_one
    (fun a => (one_mulₓ ∥a∥).symm ▸ Spectrum.norm_le_norm_of_mem (φ.apply_mem_spectrum _)) fun _ _ h => by
    simpa only [to_continuous_linear_map_apply, mul_oneₓ, map_one, norm_one] using h 1

end NondiscreteNormedField

end AlgHom

