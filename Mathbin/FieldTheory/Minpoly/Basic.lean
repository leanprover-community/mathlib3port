/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johan Commelin

! This file was ported from Lean 3 source module field_theory.minpoly.basic
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.FieldDivision
import Mathbin.RingTheory.IntegralClosure
import Mathbin.RingTheory.Polynomial.GaussLemma

/-!
# Minimal polynomials

This file defines the minimal polynomial of an element `x` of an `A`-algebra `B`,
under the assumption that x is integral over `A`, and derives some basic properties
such as ireducibility under the assumption `B` is a domain.

-/


open Classical Polynomial

open Polynomial Set Function

variable {A B : Type _}

section MinPolyDef

variable (A) [CommRing A] [Ring B] [Algebra A B]

/-- Suppose `x : B`, where `B` is an `A`-algebra.

The minimal polynomial `minpoly A x` of `x`
is a monic polynomial with coefficients in `A` of smallest degree that has `x` as its root,
if such exists (`is_integral A x`) or zero otherwise.

For example, if `V` is a `𝕜`-vector space for some field `𝕜` and `f : V →ₗ[𝕜] V` then
the minimal polynomial of `f` is `minpoly 𝕜 f`.
-/
noncomputable def minpoly (x : B) : A[X] :=
  if hx : IsIntegral A x then WellFounded.min degree_lt_wf _ hx else 0
#align minpoly minpoly

end MinPolyDef

namespace minpoly

section Ring

variable [CommRing A] [Ring B] [Algebra A B]

variable {x : B}

/-- A minimal polynomial is monic. -/
theorem monic (hx : IsIntegral A x) : Monic (minpoly A x) :=
  by
  delta minpoly
  rw [dif_pos hx]
  exact (WellFounded.min_mem degree_lt_wf _ hx).1
#align minpoly.monic minpoly.monic

/-- A minimal polynomial is nonzero. -/
theorem ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly A x ≠ 0 :=
  (monic hx).NeZero
#align minpoly.ne_zero minpoly.ne_zero

theorem eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0 :=
  dif_neg hx
#align minpoly.eq_zero minpoly.eq_zero

variable (A x)

/-- An element is a root of its minimal polynomial. -/
@[simp]
theorem aeval : aeval x (minpoly A x) = 0 :=
  by
  delta minpoly; split_ifs with hx
  · exact (WellFounded.min_mem degree_lt_wf _ hx).2
  · exact aeval_zero _
#align minpoly.aeval minpoly.aeval

/-- A minimal polynomial is not `1`. -/
theorem ne_one [Nontrivial B] : minpoly A x ≠ 1 :=
  by
  intro h
  refine' (one_ne_zero : (1 : B) ≠ 0) _
  simpa using congr_arg (Polynomial.aeval x) h
#align minpoly.ne_one minpoly.ne_one

theorem map_ne_one [Nontrivial B] {R : Type _} [Semiring R] [Nontrivial R] (f : A →+* R) :
    (minpoly A x).map f ≠ 1 := by
  by_cases hx : IsIntegral A x
  · exact mt ((monic hx).eq_one_of_map_eq_one f) (ne_one A x)
  · rw [eq_zero hx, Polynomial.map_zero]
    exact zero_ne_one
#align minpoly.map_ne_one minpoly.map_ne_one

/-- A minimal polynomial is not a unit. -/
theorem not_is_unit [Nontrivial B] : ¬IsUnit (minpoly A x) :=
  by
  haveI : Nontrivial A := (algebraMap A B).domain_nontrivial
  by_cases hx : IsIntegral A x
  · exact mt (monic hx).eq_one_of_is_unit (ne_one A x)
  · rw [eq_zero hx]
    exact not_isUnit_zero
#align minpoly.not_is_unit minpoly.not_is_unit

theorem mem_range_of_degree_eq_one (hx : (minpoly A x).degree = 1) : x ∈ (algebraMap A B).range :=
  by
  have h : IsIntegral A x := by
    by_contra h
    rw [eq_zero h, degree_zero, ← WithBot.coe_one] at hx
    exact ne_of_lt (show ⊥ < ↑1 from WithBot.bot_lt_coe 1) hx
  have key := minpoly.aeval A x
  rw [eq_X_add_C_of_degree_eq_one hx, (minpoly.monic h).leadingCoeff, C_1, one_mul, aeval_add,
    aeval_C, aeval_X, ← eq_neg_iff_add_eq_zero, ← RingHom.map_neg] at key
  exact ⟨-(minpoly A x).coeff 0, key.symm⟩
#align minpoly.mem_range_of_degree_eq_one minpoly.mem_range_of_degree_eq_one

/-- The defining property of the minimal polynomial of an element `x`:
it is the monic polynomial with smallest degree that has `x` as its root. -/
theorem min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0) :
    degree (minpoly A x) ≤ degree p := by
  delta minpoly; split_ifs with hx
  · exact le_of_not_lt (WellFounded.not_lt_min degree_lt_wf _ hx ⟨pmonic, hp⟩)
  · simp only [degree_zero, bot_le]
#align minpoly.min minpoly.min

@[nontriviality]
theorem subsingleton [Subsingleton B] : minpoly A x = 1 :=
  by
  nontriviality A
  have := minpoly.min A x monic_one (Subsingleton.elim _ _)
  rw [degree_one] at this
  cases' le_or_lt (minpoly A x).degree 0 with h h
  · rwa [(monic ⟨1, monic_one, by simp⟩ : (minpoly A x).Monic).degree_le_zero_iff_eq_one] at h
  · exact (this.not_lt h).elim
#align minpoly.subsingleton minpoly.subsingleton

end Ring

section CommRing

variable [CommRing A]

section Ring

variable [Ring B] [Algebra A B] [Nontrivial B]

variable {x : B}

/-- The degree of a minimal polynomial, as a natural number, is positive. -/
theorem nat_degree_pos (hx : IsIntegral A x) : 0 < natDegree (minpoly A x) :=
  by
  rw [pos_iff_ne_zero]
  intro ndeg_eq_zero
  have eq_one : minpoly A x = 1 :=
    by
    rw [eq_C_of_nat_degree_eq_zero ndeg_eq_zero]
    convert C_1
    simpa only [ndeg_eq_zero.symm] using (monic hx).leadingCoeff
  simpa only [eq_one, AlgHom.map_one, one_ne_zero] using aeval A x
#align minpoly.nat_degree_pos minpoly.nat_degree_pos

/-- The degree of a minimal polynomial is positive. -/
theorem degree_pos (hx : IsIntegral A x) : 0 < degree (minpoly A x) :=
  nat_degree_pos_iff_degree_pos.mp (nat_degree_pos hx)
#align minpoly.degree_pos minpoly.degree_pos

/-- If `B/A` is an injective ring extension, and `a` is an element of `A`,
then the minimal polynomial of `algebra_map A B a` is `X - C a`. -/
theorem eq_X_sub_C_of_algebra_map_inj (a : A) (hf : Function.Injective (algebraMap A B)) :
    minpoly A (algebraMap A B a) = X - c a :=
  by
  nontriviality A
  have hdegle : (minpoly A (algebraMap A B a)).natDegree ≤ 1 :=
    by
    apply WithBot.coe_le_coe.1
    rw [← degree_eq_nat_degree (NeZero (@is_integral_algebra_map A B _ _ _ a)), WithTop.coe_one, ←
      degree_X_sub_C a]
    refine' min A (algebraMap A B a) (monic_X_sub_C a) _
    simp only [aeval_C, aeval_X, AlgHom.map_sub, sub_self]
  have hdeg : (minpoly A (algebraMap A B a)).degree = 1 :=
    by
    apply (degree_eq_iff_nat_degree_eq (NeZero (@is_integral_algebra_map A B _ _ _ a))).2
    apply le_antisymm hdegle (nat_degree_pos (@is_integral_algebra_map A B _ _ _ a))
  have hrw := eq_X_add_C_of_degree_eq_one hdeg
  simp only [monic (@is_integral_algebra_map A B _ _ _ a), one_mul, monic.leading_coeff,
    RingHom.map_one] at hrw
  have h0 : (minpoly A (algebraMap A B a)).coeff 0 = -a :=
    by
    have hroot := aeval A (algebraMap A B a)
    rw [hrw, add_comm] at hroot
    simp only [aeval_C, aeval_X, aeval_add] at hroot
    replace hroot := eq_neg_of_add_eq_zero_left hroot
    rw [← RingHom.map_neg _ a] at hroot
    exact hf hroot
  rw [hrw]
  simp only [h0, RingHom.map_neg, sub_eq_add_neg]
#align minpoly.eq_X_sub_C_of_algebra_map_inj minpoly.eq_X_sub_C_of_algebra_map_inj

end Ring

section IsDomain

variable [IsDomain A] [Ring B] [Algebra A B]

variable {x : B}

/-- If `a` strictly divides the minimal polynomial of `x`, then `x` cannot be a root for `a`. -/
theorem aeval_ne_zero_of_dvd_not_unit_minpoly {a : A[X]} (hx : IsIntegral A x) (hamonic : a.Monic)
    (hdvd : DvdNotUnit a (minpoly A x)) : Polynomial.aeval x a ≠ 0 :=
  by
  intro ha
  refine' not_lt_of_ge (minpoly.min A x hamonic ha) _
  obtain ⟨hzeroa, b, hb_nunit, prod⟩ := hdvd
  have hbmonic : b.monic := by
    rw [monic.def]
    have := monic hx
    rwa [monic.def, Prod, leading_coeff_mul, monic.def.mp hamonic, one_mul] at this
  have hzerob : b ≠ 0 := hbmonic.ne_zero
  have degbzero : 0 < b.nat_degree := by
    apply Nat.pos_of_ne_zero
    intro h
    have h₁ := eq_C_of_nat_degree_eq_zero h
    rw [← h, ← leading_coeff, monic.def.1 hbmonic, C_1] at h₁
    rw [h₁] at hb_nunit
    have := isUnit_one
    contradiction
  rw [Prod, degree_mul, degree_eq_nat_degree hzeroa, degree_eq_nat_degree hzerob]
  exact_mod_cast lt_add_of_pos_right _ degbzero
#align minpoly.aeval_ne_zero_of_dvd_not_unit_minpoly minpoly.aeval_ne_zero_of_dvd_not_unit_minpoly

variable [IsDomain B]

/-- A minimal polynomial is irreducible. -/
theorem irreducible (hx : IsIntegral A x) : Irreducible (minpoly A x) :=
  by
  cases' irreducible_or_factor (minpoly A x) (not_is_unit A x) with hirr hred
  · exact hirr
  exfalso
  obtain ⟨a, b, ha_nunit, hb_nunit, hab_eq⟩ := hred
  have coeff_prod : a.leading_coeff * b.leading_coeff = 1 :=
    by
    rw [← monic.def.1 (monic hx), ← hab_eq]
    simp only [leading_coeff_mul]
  have hamonic : (a * C b.leading_coeff).Monic :=
    by
    rw [monic.def]
    simp only [coeff_prod, leading_coeff_mul, leading_coeff_C]
  have hbmonic : (b * C a.leading_coeff).Monic :=
    by
    rw [monic.def, mul_comm]
    simp only [coeff_prod, leading_coeff_mul, leading_coeff_C]
  have prod : minpoly A x = a * C b.leading_coeff * (b * C a.leading_coeff) :=
    by
    symm
    calc
      a * C b.leading_coeff * (b * C a.leading_coeff) =
          a * b * (C a.leading_coeff * C b.leading_coeff) :=
        by ring
      _ = a * b * C (a.leading_coeff * b.leading_coeff) := by simp only [RingHom.map_mul]
      _ = a * b := by rw [coeff_prod, C_1, mul_one]
      _ = minpoly A x := hab_eq
      
  have hzero := aeval A x
  rw [Prod, aeval_mul, mul_eq_zero] at hzero
  cases hzero
  · refine' aeval_ne_zero_of_dvd_not_unit_minpoly hx hamonic _ hzero
    exact ⟨hamonic.ne_zero, _, mt isUnit_of_mul_isUnit_left hb_nunit, Prod⟩
  · refine' aeval_ne_zero_of_dvd_not_unit_minpoly hx hbmonic _ hzero
    rw [mul_comm] at prod
    exact ⟨hbmonic.ne_zero, _, mt isUnit_of_mul_isUnit_left ha_nunit, Prod⟩
#align minpoly.irreducible minpoly.irreducible

end IsDomain

end CommRing

end minpoly

