/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module ring_theory.polynomial.gauss_lemma
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Int.Basic
import Mathbin.FieldTheory.SplittingField
import Mathbin.RingTheory.Localization.Integral
import Mathbin.RingTheory.IntegrallyClosed

/-!
# Gauss's Lemma

Gauss's Lemma is one of a few results pertaining to irreducibility of primitive polynomials.

## Main Results
 - `polynomial.monic.irreducible_iff_irreducible_map_fraction_map`:
  A monic polynomial over an integrally closed domain is irreducible iff it is irreducible in a
    fraction field
 - `is_integrally_closed_iff'`:
   Integrally closed domains are precisely the domains for in which Gauss's lemma holds
    for monic polynomials
 - `polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map`:
  A primitive polynomial over a GCD domain is irreducible iff it is irreducible in a fraction field
 - `polynomial.is_primitive.int.irreducible_iff_irreducible_map_cast`:
  A primitive polynomial over `ℤ` is irreducible iff it is irreducible over `ℚ`.
 - `polynomial.is_primitive.dvd_iff_fraction_map_dvd_fraction_map`:
  Two primitive polynomials over a GCD domain divide each other iff they do in a fraction field.
 - `polynomial.is_primitive.int.dvd_iff_map_cast_dvd_map_cast`:
  Two primitive polynomials over `ℤ` divide each other if they do in `ℚ`.

-/


open nonZeroDivisors Polynomial

variable {R : Type _} [CommRing R]

namespace Polynomial

section

variable {S : Type _} [CommRing S] [IsDomain S]

variable {φ : R →+* S} (hinj : Function.Injective φ) {f : R[X]} (hf : f.IsPrimitive)

include hinj hf

theorem IsPrimitive.isUnit_iff_isUnit_map_of_injective : IsUnit f ↔ IsUnit (map φ f) :=
  by
  refine' ⟨(map_ring_hom φ).isUnit_map, fun h => _⟩
  rcases is_unit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  have hdeg := degree_C u.ne_zero
  rw [hu, degree_map_eq_of_injective hinj] at hdeg
  rw [eq_C_of_degree_eq_zero hdeg] at hf⊢
  exact is_unit_C.mpr (is_primitive_iff_is_unit_of_C_dvd.mp hf (f.coeff 0) dvd_rfl)
#align polynomial.is_primitive.is_unit_iff_is_unit_map_of_injective Polynomial.IsPrimitive.isUnit_iff_isUnit_map_of_injective

theorem IsPrimitive.irreducible_of_irreducible_map_of_injective (h_irr : Irreducible (map φ f)) :
    Irreducible f :=
  by
  refine'
    ⟨fun h => h_irr.not_unit (IsUnit.map (map_ring_hom φ) h), fun a b h =>
      (h_irr.is_unit_or_is_unit <| by rw [h, Polynomial.map_mul]).imp _ _⟩
  all_goals apply ((is_primitive_of_dvd hf _).isUnit_iff_isUnit_map_of_injective hinj).mpr
  exacts[Dvd.intro _ h.symm, Dvd.intro_left _ h.symm]
#align polynomial.is_primitive.irreducible_of_irreducible_map_of_injective Polynomial.IsPrimitive.irreducible_of_irreducible_map_of_injective

end

section FractionMap

variable {K : Type _} [Field K] [Algebra R K] [IsFractionRing R K]

theorem IsPrimitive.isUnit_iff_isUnit_map {p : R[X]} (hp : p.IsPrimitive) :
    IsUnit p ↔ IsUnit (p.map (algebraMap R K)) :=
  hp.isUnit_iff_isUnit_map_of_injective (IsFractionRing.injective _ _)
#align polynomial.is_primitive.is_unit_iff_is_unit_map Polynomial.IsPrimitive.isUnit_iff_isUnit_map

variable [IsDomain R]

section IsIntegrallyClosed

open IsIntegrallyClosed

/-- **Gauss's Lemma** for integrally closed domains states that a monic polynomial is irreducible
  iff it is irreducible in the fraction field. -/
theorem Monic.irreducible_iff_irreducible_map_fraction_map [IsIntegrallyClosed R] {p : R[X]}
    (h : p.Monic) : Irreducible p ↔ Irreducible (p.map <| algebraMap R K) :=
  by
  /- The ← direction follows from `is_primitive.irreducible_of_irreducible_map_of_injective`.
       For the → direction, it is enought to show that if `(p.map $ algebra_map R K) = a * b` and
       `a` is not a unit then `b` is a unit -/
  refine'
    ⟨fun hp =>
      irreducible_iff.mpr
        ⟨hp.not_unit.imp h.is_primitive.is_unit_iff_is_unit_map.mpr, fun a b H =>
          or_iff_not_imp_left.mpr fun hₐ => _⟩,
      fun hp =>
      h.is_primitive.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective R K) hp⟩
  obtain ⟨a', ha⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_right_eq b H.symm)
  obtain ⟨b', hb⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_left_eq a H.symm)
  have : a.leading_coeff * b.leading_coeff = 1 := by
    rw [← leading_coeff_mul, ← H, monic.leading_coeff (h.map <| algebraMap R K)]
  rw [← ha, ← hb, mul_comm _ (C b.leading_coeff), mul_assoc, ← mul_assoc (C a.leading_coeff), ←
    C_mul, this, C_1, one_mul, ← Polynomial.map_mul] at H
  rw [← hb, ← Polynomial.coe_mapRingHom]
  refine'
    IsUnit.mul (IsUnit.map _ (Or.resolve_left (hp.is_unit_or_is_unit _) (show ¬IsUnit a' from _)))
      (is_unit_iff_exists_inv'.mpr
        (Exists.intro (C a.leading_coeff) <| by rwa [← C_mul, this, C_1]))
  · exact Polynomial.map_injective _ (IsFractionRing.injective R K) H
  · by_contra h_contra
    refine' hₐ _
    rw [← ha, ← Polynomial.coe_mapRingHom]
    exact
      IsUnit.mul (IsUnit.map _ h_contra)
        (is_unit_iff_exists_inv.mpr
          (Exists.intro (C b.leading_coeff) <| by rwa [← C_mul, this, C_1]))
#align polynomial.monic.irreducible_iff_irreducible_map_fraction_map Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map

/-- Integrally closed domains are precisely the domains for in which Gauss's lemma holds
    for monic polynomials -/
theorem isIntegrallyClosed_iff' :
    IsIntegrallyClosed R ↔
      ∀ p : R[X], p.Monic → (Irreducible p ↔ Irreducible (p.map <| algebraMap R K)) :=
  by
  constructor
  · intro hR p hp
    letI := hR
    exact monic.irreducible_iff_irreducible_map_fraction_map hp
  · intro H
    refine'
      (isIntegrallyClosed_iff K).mpr fun x hx =>
        ring_hom.mem_range.mp <| minpoly.mem_range_of_degree_eq_one R x _
    rw [← monic.degree_map (minpoly.monic hx) (algebraMap R K)]
    apply
      degree_eq_one_of_irreducible_of_root ((H _ <| minpoly.monic hx).mp (minpoly.irreducible hx))
    rw [is_root, eval_map, ← aeval_def, minpoly.aeval R x]
#align polynomial.is_integrally_closed_iff' Polynomial.isIntegrallyClosed_iff'

theorem Monic.dvd_of_fraction_map_dvd_fraction_map [IsIntegrallyClosed R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic) (h : q.map (algebraMap R K) ∣ p.map (algebraMap R K)) : q ∣ p :=
  by
  obtain ⟨r, hr⟩ := h
  obtain ⟨d', hr'⟩ := IsIntegrallyClosed.eq_map_mul_c_of_dvd K hp (dvd_of_mul_left_eq _ hr.symm)
  rw [monic.leading_coeff, C_1, mul_one] at hr'
  rw [← hr', ← Polynomial.map_mul] at hr
  exact dvd_of_mul_right_eq _ (Polynomial.map_injective _ (IsFractionRing.injective R K) hr.symm)
  · exact monic.of_mul_monic_left (hq.map (algebraMap R K)) (by simpa [← hr] using hp.map _)
#align polynomial.monic.dvd_of_fraction_map_dvd_fraction_map Polynomial.Monic.dvd_of_fraction_map_dvd_fraction_map

theorem Monic.dvd_iff_fraction_map_dvd_fraction_map [IsIntegrallyClosed R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic) : q.map (algebraMap R K) ∣ p.map (algebraMap R K) ↔ q ∣ p :=
  ⟨fun h => hp.dvd_of_fraction_map_dvd_fraction_map hq h, fun ⟨a, b⟩ =>
    ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩⟩
#align polynomial.monic.dvd_iff_fraction_map_dvd_fraction_map Polynomial.Monic.dvd_iff_fraction_map_dvd_fraction_map

end IsIntegrallyClosed

open IsLocalization

section NormalizedGCDMonoid

variable [NormalizedGCDMonoid R]

theorem isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart {p : K[X]} (h0 : p ≠ 0)
    (h : IsUnit (integerNormalization R⁰ p).primPart) : IsUnit p :=
  by
  rcases is_unit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  obtain ⟨⟨c, c0⟩, hc⟩ := integer_normalization_map_to_map R⁰ p
  rw [Subtype.coe_mk, Algebra.smul_def, algebra_map_apply] at hc
  apply isUnit_of_mul_isUnit_right
  rw [← hc, (integer_normalization R⁰ p).eq_c_content_mul_primPart, ← hu, ← RingHom.map_mul,
    is_unit_iff]
  refine'
    ⟨algebraMap R K ((integer_normalization R⁰ p).content * ↑u), isUnit_iff_ne_zero.2 fun con => _,
      by simp⟩
  replace con := (injective_iff_map_eq_zero (algebraMap R K)).1 (IsFractionRing.injective _ _) _ Con
  rw [mul_eq_zero, content_eq_zero_iff, IsFractionRing.integerNormalization_eq_zero_iff] at con
  rcases Con with (con | con)
  · apply h0 Con
  · apply Units.ne_zero _ Con
#align polynomial.is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart

/-- **Gauss's Lemma** for GCD domains states that a primitive polynomial is irreducible iff it is
  irreducible in the fraction field. -/
theorem IsPrimitive.irreducible_iff_irreducible_map_fraction_map {p : R[X]} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (algebraMap R K)) :=
  by
  refine'
    ⟨fun hi => ⟨fun h => hi.not_unit (hp.is_unit_iff_is_unit_map.2 h), fun a b hab => _⟩,
      hp.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective _ _)⟩
  obtain ⟨⟨c, c0⟩, hc⟩ := integer_normalization_map_to_map R⁰ a
  obtain ⟨⟨d, d0⟩, hd⟩ := integer_normalization_map_to_map R⁰ b
  rw [Algebra.smul_def, algebra_map_apply, Subtype.coe_mk] at hc hd
  rw [mem_nonZeroDivisors_iff_ne_zero] at c0 d0
  have hcd0 : c * d ≠ 0 := mul_ne_zero c0 d0
  rw [Ne.def, ← C_eq_zero] at hcd0
  have h1 : C c * C d * p = integer_normalization R⁰ a * integer_normalization R⁰ b :=
    by
    apply map_injective (algebraMap R K) (IsFractionRing.injective _ _) _
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, hc, hd, map_C, map_C, hab]
    ring
  obtain ⟨u, hu⟩ :
    Associated (c * d)
      (content (integer_normalization R⁰ a) * content (integer_normalization R⁰ b)) :=
    by
    rw [← dvd_dvd_iff_associated, ← normalize_eq_normalize_iff, normalize.map_mul,
      normalize.map_mul, normalize_content, normalize_content, ←
      mul_one (normalize c * normalize d), ← hp.content_eq_one, ← content_C, ← content_C, ←
      content_mul, ← content_mul, ← content_mul, h1]
  rw [← RingHom.map_mul, eq_comm, (integer_normalization R⁰ a).eq_c_content_mul_primPart,
    (integer_normalization R⁰ b).eq_c_content_mul_primPart, mul_assoc, mul_comm _ (C _ * _), ←
    mul_assoc, ← mul_assoc, ← RingHom.map_mul, ← hu, RingHom.map_mul, mul_assoc, mul_assoc, ←
    mul_assoc (C ↑u)] at h1
  have h0 : a ≠ 0 ∧ b ≠ 0 := by
    classical
      rw [Ne.def, Ne.def, ← Decidable.not_or_iff_and_not, ← mul_eq_zero, ← hab]
      intro con
      apply hp.ne_zero (map_injective (algebraMap R K) (IsFractionRing.injective _ _) _)
      simp [Con]
  rcases hi.is_unit_or_is_unit (mul_left_cancel₀ hcd0 h1).symm with (h | h)
  · right
    apply
      is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part h0.2
        (isUnit_of_mul_isUnit_right h)
  · left
    apply is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part h0.1 h
#align polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map

theorem IsPrimitive.dvd_of_fraction_map_dvd_fraction_map {p q : R[X]} (hp : p.IsPrimitive)
    (hq : q.IsPrimitive) (h_dvd : p.map (algebraMap R K) ∣ q.map (algebraMap R K)) : p ∣ q :=
  by
  rcases h_dvd with ⟨r, hr⟩
  obtain ⟨⟨s, s0⟩, hs⟩ := integer_normalization_map_to_map R⁰ r
  rw [Subtype.coe_mk, Algebra.smul_def, algebra_map_apply] at hs
  have h : p ∣ q * C s := by
    use integer_normalization R⁰ r
    apply map_injective (algebraMap R K) (IsFractionRing.injective _ _)
    rw [Polynomial.map_mul, Polynomial.map_mul, hs, hr, mul_assoc, mul_comm r]
    simp
  rw [← hp.dvd_prim_part_iff_dvd, prim_part_mul, hq.prim_part_eq, Associated.dvd_iff_dvd_right] at h
  · exact h
  · symm
    rcases is_unit_prim_part_C s with ⟨u, hu⟩
    use u
    rw [hu]
  iterate 2 
    apply mul_ne_zero hq.ne_zero
    rw [Ne.def, C_eq_zero]
    contrapose! s0
    simp [s0, mem_nonZeroDivisors_iff_ne_zero]
#align polynomial.is_primitive.dvd_of_fraction_map_dvd_fraction_map Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map

variable (K)

theorem IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map {p q : R[X]} (hp : p.IsPrimitive)
    (hq : q.IsPrimitive) : p ∣ q ↔ p.map (algebraMap R K) ∣ q.map (algebraMap R K) :=
  ⟨fun ⟨a, b⟩ => ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩, fun h =>
    hp.dvd_of_fraction_map_dvd_fraction_map hq h⟩
#align polynomial.is_primitive.dvd_iff_fraction_map_dvd_fraction_map Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map

end NormalizedGCDMonoid

end FractionMap

/-- **Gauss's Lemma** for `ℤ` states that a primitive integer polynomial is irreducible iff it is
  irreducible over `ℚ`. -/
theorem IsPrimitive.Int.irreducible_iff_irreducible_map_cast {p : ℤ[X]} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (Int.castRingHom ℚ)) :=
  hp.irreducible_iff_irreducible_map_fraction_map
#align polynomial.is_primitive.int.irreducible_iff_irreducible_map_cast Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast

theorem IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast (p q : ℤ[X]) (hp : p.IsPrimitive)
    (hq : q.IsPrimitive) : p ∣ q ↔ p.map (Int.castRingHom ℚ) ∣ q.map (Int.castRingHom ℚ) :=
  hp.dvd_iff_fraction_map_dvd_fraction_map ℚ hq
#align polynomial.is_primitive.int.dvd_iff_map_cast_dvd_map_cast Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast

end Polynomial

