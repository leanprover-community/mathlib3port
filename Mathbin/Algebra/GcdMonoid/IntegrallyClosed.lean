/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebra.gcd_monoid.integrally_closed
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GcdMonoid.Basic
import Mathbin.RingTheory.IntegrallyClosed
import Mathbin.RingTheory.Polynomial.Eisenstein

/-!

# GCD domains are integrally closed

-/


open BigOperators Polynomial

variable {R A : Type _} [CommRing R] [IsDomain R] [GcdMonoid R] [CommRing A] [Algebra R A]

theorem IsLocalization.surj_of_gcd_domain (M : Submonoid R) [IsLocalization M A] (z : A) :
    ∃ a b : R, IsUnit (gcd a b) ∧ z * algebraMap R A b = algebraMap R A a :=
  by
  obtain ⟨x, ⟨y, hy⟩, rfl⟩ := IsLocalization.mk'_surjective M z
  obtain ⟨x', y', hx', hy', hu⟩ := extract_gcd x y
  use x', y', hu
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul]
  convert IsLocalization.mk'_mul_cancel_left _ _ using 2
  · rw [Subtype.coe_mk, hy', ← mul_comm y', mul_assoc]
    conv_lhs => rw [hx']
  · infer_instance
#align is_localization.surj_of_gcd_domain IsLocalization.surj_of_gcd_domain

instance (priority := 100) GcdMonoid.toIsIntegrallyClosed : IsIntegrallyClosed R :=
  ⟨fun X ⟨p, hp₁, hp₂⟩ =>
    by
    obtain ⟨x, y, hg, he⟩ := IsLocalization.surj_of_gcd_domain (nonZeroDivisors R) X
    have :=
      Polynomial.dvd_pow_nat_degree_of_eval₂_eq_zero (IsFractionRing.injective R <| FractionRing R)
        hp₁ y x _ hp₂ (by rw [mul_comm, he])
    have : IsUnit y := by
      rw [isUnit_iff_dvd_one, ← one_pow]
      exact
        (dvd_gcd this <| dvd_refl y).trans
          (gcd_pow_left_dvd_pow_gcd.trans <| pow_dvd_pow_of_dvd (isUnit_iff_dvd_one.1 hg) _)
    use x * (this.unit⁻¹ : _)
    erw [map_mul, ← Units.coe_map_inv, eq_comm, Units.eq_mul_inv_iff_mul_eq]
    exact he⟩
#align gcd_monoid.to_is_integrally_closed GcdMonoid.toIsIntegrallyClosed

