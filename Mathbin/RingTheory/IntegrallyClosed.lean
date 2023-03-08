/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module ring_theory.integrally_closed
! leanprover-community/mathlib commit 7a030ab8eb5d99f05a891dccc49c5b5b90c947d3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.FieldTheory.SplittingField
import Mathbin.RingTheory.IntegralClosure
import Mathbin.RingTheory.Localization.Integral

/-!
# Integrally closed rings

An integrally closed domain `R` contains all the elements of `Frac(R)` that are
integral over `R`. A special case of integrally closed domains are the Dedekind domains.

## Main definitions

* `is_integrally_closed R` states `R` contains all integral elements of `Frac(R)`

## Main results

* `is_integrally_closed_iff K`, where `K` is a fraction field of `R`, states `R`
  is integrally closed iff it is the integral closure of `R` in `K`
* `eq_map_mul_C_of_dvd`: if `K = Frac(R)` and `g : K[X]` divides a monic polynomial with
  coefficients in `R`, then `g * (C g.leading_coeff⁻¹)` has coefficients in `R`
-/


open nonZeroDivisors Polynomial

open Polynomial

/-- `R` is integrally closed if all integral elements of `Frac(R)` are also elements of `R`.

This definition uses `fraction_ring R` to denote `Frac(R)`. See `is_integrally_closed_iff`
if you want to choose another field of fractions for `R`.
-/
class IsIntegrallyClosed (R : Type _) [CommRing R] [IsDomain R] : Prop where
  algebraMap_eq_of_integral :
    ∀ {x : FractionRing R}, IsIntegral R x → ∃ y, algebraMap R (FractionRing R) y = x
#align is_integrally_closed IsIntegrallyClosed

section Iff

variable {R : Type _} [CommRing R] [IsDomain R]

variable (K : Type _) [Field K] [Algebra R K] [IsFractionRing R K]

/-- `R` is integrally closed iff all integral elements of its fraction field `K`
are also elements of `R`. -/
theorem isIntegrallyClosed_iff :
    IsIntegrallyClosed R ↔ ∀ {x : K}, IsIntegral R x → ∃ y, algebraMap R K y = x :=
  by
  let e : K ≃ₐ[R] FractionRing R := IsLocalization.algEquiv R⁰ _ _
  constructor
  · rintro ⟨cl⟩
    refine' fun x hx => _
    obtain ⟨y, hy⟩ := cl ((isIntegral_algEquiv e).mpr hx)
    exact ⟨y, e.algebra_map_eq_apply.mp hy⟩
  · rintro cl
    refine' ⟨fun x hx => _⟩
    obtain ⟨y, hy⟩ := cl ((isIntegral_algEquiv e.symm).mpr hx)
    exact ⟨y, e.symm.algebra_map_eq_apply.mp hy⟩
#align is_integrally_closed_iff isIntegrallyClosed_iff

/-- `R` is integrally closed iff it is the integral closure of itself in its field of fractions. -/
theorem isIntegrallyClosed_iff_isIntegralClosure : IsIntegrallyClosed R ↔ IsIntegralClosure R R K :=
  (isIntegrallyClosed_iff K).trans <|
    by
    let e : K ≃ₐ[R] FractionRing R := IsLocalization.algEquiv R⁰ _ _
    constructor
    · intro cl
      refine' ⟨IsFractionRing.injective _ _, fun x => ⟨cl, _⟩⟩
      rintro ⟨y, y_eq⟩
      rw [← y_eq]
      exact isIntegral_algebraMap
    · rintro ⟨-, cl⟩ x hx
      exact cl.mp hx
#align is_integrally_closed_iff_is_integral_closure isIntegrallyClosed_iff_isIntegralClosure

end Iff

namespace IsIntegrallyClosed

variable {R : Type _} [CommRing R] [id : IsDomain R] [iic : IsIntegrallyClosed R]

variable {K : Type _} [Field K] [Algebra R K] [ifr : IsFractionRing R K]

include iic ifr

instance : IsIntegralClosure R R K :=
  (isIntegrallyClosed_iff_isIntegralClosure K).mp iic

theorem isIntegral_iff {x : K} : IsIntegral R x ↔ ∃ y : R, algebraMap R K y = x :=
  IsIntegralClosure.isIntegral_iff
#align is_integrally_closed.is_integral_iff IsIntegrallyClosed.isIntegral_iff

theorem exists_algebraMap_eq_of_isIntegral_pow {x : K} {n : ℕ} (hn : 0 < n)
    (hx : IsIntegral R <| x ^ n) : ∃ y : R, algebraMap R K y = x :=
  isIntegral_iff.mp <| isIntegral_of_pow hn hx
#align is_integrally_closed.exists_algebra_map_eq_of_is_integral_pow IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow

omit iic ifr

theorem exists_algebraMap_eq_of_pow_mem_subalgebra {K : Type _} [Field K] [Algebra R K]
    {S : Subalgebra R K} [IsIntegrallyClosed S] [IsFractionRing S K] {x : K} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n ∈ S) : ∃ y : S, algebraMap S K y = x :=
  exists_algebraMap_eq_of_isIntegral_pow hn <| isIntegral_iff.mpr ⟨⟨x ^ n, hx⟩, rfl⟩
#align is_integrally_closed.exists_algebra_map_eq_of_pow_mem_subalgebra IsIntegrallyClosed.exists_algebraMap_eq_of_pow_mem_subalgebra

include id ifr

variable {R} (K)

theorem integralClosure_eq_bot_iff : integralClosure R K = ⊥ ↔ IsIntegrallyClosed R :=
  by
  refine' eq_bot_iff.trans _
  constructor
  · rw [isIntegrallyClosed_iff K]
    intro h x hx
    exact set.mem_range.mp (algebra.mem_bot.mp (h hx))
    assumption
  · intro h x hx
    rw [Algebra.mem_bot, Set.mem_range]
    exact is_integral_iff.mp hx
#align is_integrally_closed.integral_closure_eq_bot_iff IsIntegrallyClosed.integralClosure_eq_bot_iff

include iic

variable (R K)

@[simp]
theorem integralClosure_eq_bot : integralClosure R K = ⊥ :=
  (integralClosure_eq_bot_iff K).mpr ‹_›
#align is_integrally_closed.integral_closure_eq_bot IsIntegrallyClosed.integralClosure_eq_bot

end IsIntegrallyClosed

namespace integralClosure

open IsIntegrallyClosed

variable {R : Type _} [CommRing R]

variable (K : Type _) [Field K] [Algebra R K]

theorem mem_lifts_of_monic_of_dvd_map {f : R[X]} (hf : f.Monic) {g : K[X]} (hg : g.Monic)
    (hd : g ∣ f.map (algebraMap R K)) : g ∈ lifts (algebraMap (integralClosure R K) K) :=
  by
  haveI : IsScalarTower R K g.splitting_field := splitting_field_aux.is_scalar_tower _ _ _
  have :=
    mem_lift_of_splits_of_roots_mem_range (integralClosure R g.splitting_field)
      ((splits_id_iff_splits _).2 <| splitting_field.splits g) (hg.map _) fun a ha =>
      (set_like.ext_iff.mp (integralClosure R g.splitting_field).range_algebraMap _).mpr <|
        roots_mem_integralClosure hf _
  · rw [lifts_iff_coeff_lifts, ← RingHom.coe_range, Subalgebra.range_algebraMap] at this
    refine' (lifts_iff_coeff_lifts _).2 fun n => _
    rw [← RingHom.coe_range, Subalgebra.range_algebraMap]
    obtain ⟨p, hp, he⟩ := set_like.mem_coe.mp (this n)
    use p, hp
    rw [IsScalarTower.algebraMap_eq R K, coeff_map, ← eval₂_map, eval₂_at_apply] at he
    rw [eval₂_eq_eval_map]
    apply (injective_iff_map_eq_zero _).1 _ _ he
    · apply RingHom.injective
  rw [IsScalarTower.algebraMap_eq R K _, ← map_map]
  refine' Multiset.mem_of_le (roots.le_of_dvd ((hf.map _).map _).NeZero _) ha
  · infer_instance
  · exact map_dvd (algebraMap K g.splitting_field) hd
  · apply splitting_field_aux.is_scalar_tower
#align integral_closure.mem_lifts_of_monic_of_dvd_map integralClosure.mem_lifts_of_monic_of_dvd_map

variable [IsDomain R] [IsFractionRing R K]

variable {L : Type _} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

-- Can't be an instance because you need to supply `K`.
theorem isIntegrallyClosedOfFiniteExtension [FiniteDimensional K L] :
    IsIntegrallyClosed (integralClosure R L) :=
  letI : IsFractionRing (integralClosure R L) L := is_fraction_ring_of_finite_extension K L
  (integral_closure_eq_bot_iff L).mp integralClosure_idem
#align integral_closure.is_integrally_closed_of_finite_extension integralClosure.isIntegrallyClosedOfFiniteExtension

end integralClosure

namespace IsIntegrallyClosed

open integralClosure

variable {R : Type _} [CommRing R] [IsDomain R]

variable (K : Type _) [Field K] [Algebra R K] [IsFractionRing R K]

/-- If `K = Frac(R)` and `g : K[X]` divides a monic polynomial with coefficients in `R`, then
    `g * (C g.leading_coeff⁻¹)` has coefficients in `R` -/
theorem eq_map_mul_c_of_dvd [IsIntegrallyClosed R] {f : R[X]} (hf : f.Monic) {g : K[X]}
    (hg : g ∣ f.map (algebraMap R K)) :
    ∃ g' : R[X], g'.map (algebraMap R K) * (C <| leadingCoeff g) = g :=
  by
  have g_ne_0 : g ≠ 0 := ne_zero_of_dvd_ne_zero (monic.ne_zero <| hf.map (algebraMap R K)) hg
  suffices lem : ∃ g' : R[X], g'.map (algebraMap R K) = g * C g.leading_coeff⁻¹
  · obtain ⟨g', hg'⟩ := lem
    use g'
    rw [hg', mul_assoc, ← C_mul, inv_mul_cancel (leading_coeff_ne_zero.mpr g_ne_0), C_1, mul_one]
  have g_mul_dvd : g * C g.leading_coeff⁻¹ ∣ f.map (algebraMap R K) :=
    by
    rwa [Associated.dvd_iff_dvd_left (show Associated (g * C g.leading_coeff⁻¹) g from _)]
    rw [associated_mul_isUnit_left_iff]
    exact is_unit_C.mpr (inv_ne_zero <| leading_coeff_ne_zero.mpr g_ne_0).IsUnit
  let algeq :=
    (Subalgebra.equivOfEq _ _ <| integral_closure_eq_bot R _).trans
      (Algebra.botEquivOfInjective <| IsFractionRing.injective R <| K)
  have :
    (algebraMap R _).comp algeq.to_alg_hom.to_ring_hom = (integralClosure R _).toSubring.Subtype :=
    by
    ext
    conv_rhs => rw [← algeq.symm_apply_apply x]
    rfl
  have H :=
    (mem_lifts _).1
      (mem_lifts_of_monic_of_dvd_map K hf (monic_mul_leading_coeff_inv g_ne_0) g_mul_dvd)
  refine' ⟨map algeq.to_alg_hom.to_ring_hom _, _⟩
  use Classical.choose H
  rw [map_map, this]
  exact Classical.choose_spec H
#align is_integrally_closed.eq_map_mul_C_of_dvd IsIntegrallyClosed.eq_map_mul_c_of_dvd

end IsIntegrallyClosed

