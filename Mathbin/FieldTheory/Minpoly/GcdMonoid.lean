/-
Copyright (c) 2019 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module field_theory.minpoly.gcd_monoid
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.FieldDivision
import Mathbin.RingTheory.IntegralClosure
import Mathbin.RingTheory.Polynomial.GaussLemma
import Mathbin.FieldTheory.Minpoly.Field

/-!
# Minimal polynomials over a GCD monoid

This file specializes the theory of minpoly to the case of an algebra over a GCD monoid.

## Main results

 * `gcd_domain_eq_field_fractions`: For GCD domains, the minimal polynomial over the ring is the
    same as the minimal polynomial over the fraction field.

 * `gcd_domain_dvd` : For GCD domains, the minimal polynomial divides any primitive polynomial
    that has the integral element as root.

 * `gcd_domain_unique` : The minimal polynomial of an element `x` is uniquely characterized by
    its defining property: if there is another monic polynomial of minimal degree that has `x` as a
    root, then this polynomial is equal to the minimal polynomial of `x`.
-/


open Classical Polynomial

open Polynomial Set Function minpoly

namespace minpoly

section GcdDomain

variable {R S : Type _} (K L : Type _) [CommRing R] [IsDomain R] [NormalizedGCDMonoid R] [Field K]
  [CommRing S] [IsDomain S] [Algebra R K] [IsFractionRing R K] [Algebra R S] [Field L] [Algebra S L]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] {s : S}
  (hs : IsIntegral R s)

include hs

/-- For GCD domains, the minimal polynomial over the ring is the same as the minimal polynomial
over the fraction field. See `minpoly.gcd_domain_eq_field_fractions'` if `S` is already a
`K`-algebra. -/
theorem gcd_domain_eq_field_fractions :
    minpoly K (algebraMap S L s) = (minpoly R s).map (algebraMap R K) :=
  by
  refine' (eq_of_irreducible_of_monic _ _ _).symm
  ·
    exact
      (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map
            (Polynomial.Monic.is_primitive (monic hs))).1
        (Irreducible hs)
  · rw [aeval_map_algebra_map, aeval_algebra_map_apply, aeval, map_zero]
  · exact (monic hs).map _
#align minpoly.gcd_domain_eq_field_fractions minpoly.gcd_domain_eq_field_fractions

/-- For GCD domains, the minimal polynomial over the ring is the same as the minimal polynomial
over the fraction field. Compared to `minpoly.gcd_domain_eq_field_fractions`, this version is useful
if the element is in a ring that is already a `K`-algebra. -/
theorem gcd_domain_eq_field_fractions' [Algebra K S] [IsScalarTower R K S] :
    minpoly K s = (minpoly R s).map (algebraMap R K) :=
  by
  let L := FractionRing S
  rw [← gcd_domain_eq_field_fractions K L hs]
  refine'
    minpoly.eq_of_algebra_map_eq (IsFractionRing.injective S L) (is_integral_of_is_scalar_tower hs)
      rfl
#align minpoly.gcd_domain_eq_field_fractions' minpoly.gcd_domain_eq_field_fractions'

variable [NoZeroSMulDivisors R S]

/-- For GCD domains, the minimal polynomial divides any primitive polynomial that has the integral
element as root. See also `minpoly.dvd` which relaxes the assumptions on `S` in exchange for
stronger assumptions on `R`. -/
theorem gcd_domain_dvd {P : R[X]} (hP : P ≠ 0) (hroot : Polynomial.aeval s P = 0) :
    minpoly R s ∣ P := by
  let K := FractionRing R
  let L := FractionRing S
  let P₁ := P.prim_part
  suffices minpoly R s ∣ P₁ by exact dvd_trans this (prim_part_dvd _)
  apply
    (is_primitive.dvd_iff_fraction_map_dvd_fraction_map K (monic hs).IsPrimitive
        P.is_primitive_prim_part).2
  let y := algebraMap S L s
  have hy : IsIntegral R y := hs.algebra_map
  rw [← gcd_domain_eq_field_fractions K L hs]
  refine' dvd _ _ _
  rw [aeval_map_algebra_map, aeval_algebra_map_apply, aeval_prim_part_eq_zero hP hroot, map_zero]
#align minpoly.gcd_domain_dvd minpoly.gcd_domain_dvd

/-- If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` is at least the
degree of the minimal polynomial of `x`. See also `minpoly.degree_le_of_ne_zero` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
theorem gcd_domain_degree_le_of_ne_zero {p : R[X]} (hp0 : p ≠ 0) (hp : Polynomial.aeval s p = 0) :
    degree (minpoly R s) ≤ degree p :=
  by
  rw [degree_eq_nat_degree (minpoly.ne_zero hs), degree_eq_nat_degree hp0]
  norm_cast
  exact nat_degree_le_of_dvd (gcd_domain_dvd hs hp0 hp) hp0
#align minpoly.gcd_domain_degree_le_of_ne_zero minpoly.gcd_domain_degree_le_of_ne_zero

omit hs

/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root, then this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.unique` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
theorem gcd_domain_unique {P : R[X]} (hmo : P.Monic) (hP : Polynomial.aeval s P = 0)
    (Pmin : ∀ Q : R[X], Q.Monic → Polynomial.aeval s Q = 0 → degree P ≤ degree Q) :
    P = minpoly R s := by
  have hs : IsIntegral R s := ⟨P, hmo, hP⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
  have := gcd_domain_degree_le_of_ne_zero hs hnz (by simp [hP])
  contrapose! this
  refine' degree_sub_lt _ (NeZero hs) _
  · exact le_antisymm (min R s hmo hP) (Pmin (minpoly R s) (monic hs) (aeval R s))
  · rw [(monic hs).leadingCoeff, hmo.leading_coeff]
#align minpoly.gcd_domain_unique minpoly.gcd_domain_unique

end GcdDomain

end minpoly

