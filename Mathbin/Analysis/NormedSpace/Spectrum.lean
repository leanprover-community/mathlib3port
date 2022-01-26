import Mathbin.Algebra.Algebra.Spectrum
import Mathbin.Analysis.Calculus.Deriv
import Mathbin.Analysis.SpecialFunctions.Pow

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

variable [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "σ" => Spectrum 𝕜

local notation "ρ" => ResolventSet 𝕜

local notation "↑ₐ" => algebraMap 𝕜 A

theorem is_open_resolvent_set (a : A) : IsOpen (ρ a) :=
  Units.is_open.Preimage ((algebra_map_isometry 𝕜 A).Continuous.sub continuous_const)

theorem IsClosed (a : A) : IsClosed (σ a) :=
  (is_open_resolvent_set a).is_closed_compl

theorem mem_resolvent_of_norm_lt {a : A} {k : 𝕜} (h : ∥a∥ < ∥k∥) : k ∈ ρ a := by
  rw [ResolventSet, Set.mem_set_of_eq, Algebra.algebra_map_eq_smul_one]
  have hk : k ≠ 0 :=
    ne_zero_of_norm_pos
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
  Metric.is_compact_of_is_closed_bounded (IsClosed a) (is_bounded a)

theorem spectral_radius_le_nnnorm (a : A) : spectralRadius 𝕜 a ≤ ∥a∥₊ := by
  refine' bsupr_le fun k hk => _
  exact_mod_cast norm_le_norm_of_mem hk

open Ennreal Polynomial

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

end Spectrum

namespace AlgHom

section NormedField

variable [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "↑ₐ" => algebraMap 𝕜 A

/-- An algebra homomorphism into the base field, as a continuous linear map (since it is
automatically bounded). -/
@[simps]
def to_continuous_linear_map (φ : A →ₐ[𝕜] 𝕜) : A →L[𝕜] 𝕜 :=
  φ.to_linear_map.mk_continuous_of_exists_bound <|
    ⟨1, fun a => (one_mulₓ ∥a∥).symm ▸ Spectrum.norm_le_norm_of_mem (φ.apply_mem_spectrum _)⟩

theorem Continuous (φ : A →ₐ[𝕜] 𝕜) : Continuous φ :=
  φ.to_continuous_linear_map.continuous

end NormedField

section NondiscreteNormedField

variable [NondiscreteNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "↑ₐ" => algebraMap 𝕜 A

@[simp]
theorem to_continuous_linear_map_norm [NormOneClass A] (φ : A →ₐ[𝕜] 𝕜) : ∥φ.to_continuous_linear_map∥ = 1 :=
  ContinuousLinearMap.op_norm_eq_of_bounds zero_le_one
    (fun a => (one_mulₓ ∥a∥).symm ▸ Spectrum.norm_le_norm_of_mem (φ.apply_mem_spectrum _)) fun _ _ h => by
    simpa only [to_continuous_linear_map_apply, mul_oneₓ, map_one, norm_one] using h 1

end NondiscreteNormedField

end AlgHom

