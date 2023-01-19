/-
Copyright (c) 2019 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module field_theory.minpoly.gcd_monoid
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.FieldDivision
import Mathbin.RingTheory.AdjoinRoot
import Mathbin.FieldTheory.Minpoly.Field
import Mathbin.RingTheory.Polynomial.GaussLemma

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

 * `is_integrally_closed_eq_field_fractions`: For integrally closed domains, the minimal polynomial
    over the ring is the same as the minimal polynomial over the fraction field.

## Todo

 * Remove all results that are now special cases (e.g. we no longer need `gcd_monoid_dvd` since we
    have `is_integrally_closed_dvd`).
-/


open Classical Polynomial

open Polynomial Set Function minpoly

namespace minpoly

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]

section

variable (K L : Type _) [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra R L]
  [Algebra S L] [Algebra K L] [IsScalarTower R K L] [IsScalarTower R S L]

section GcdDomain

variable [NormalizedGCDMonoid R]

/-- For GCD domains, the minimal polynomial over the ring is the same as the minimal polynomial
over the fraction field. See `minpoly.gcd_domain_eq_field_fractions'` if `S` is already a
`K`-algebra. -/
theorem gcd_domain_eq_field_fractions [IsDomain S] {s : S} (hs : IsIntegral R s) :
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
theorem gcd_domain_eq_field_fractions' [IsDomain S] [Algebra K S] [IsScalarTower R K S] {s : S}
    (hs : IsIntegral R s) : minpoly K s = (minpoly R s).map (algebraMap R K) :=
  by
  let L := FractionRing S
  rw [← gcd_domain_eq_field_fractions K L hs]
  refine'
    minpoly.eq_of_algebra_map_eq (IsFractionRing.injective S L) (is_integral_of_is_scalar_tower hs)
      rfl
#align minpoly.gcd_domain_eq_field_fractions' minpoly.gcd_domain_eq_field_fractions'

end GcdDomain

variable [IsIntegrallyClosed R]

/-- For integrally closed domains, the minimal polynomial over the ring is the same as the minimal
polynomial over the fraction field. See `minpoly.is_integrally_closed_eq_field_fractions'` if
`S` is already a `K`-algebra. -/
theorem is_integrally_closed_eq_field_fractions [IsDomain S] {s : S} (hs : IsIntegral R s) :
    minpoly K (algebraMap S L s) = (minpoly R s).map (algebraMap R K) :=
  by
  refine' (eq_of_irreducible_of_monic _ _ _).symm
  ·
    exact
      (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (monic hs)).1 (Irreducible hs)
  · rw [aeval_map_algebra_map, aeval_algebra_map_apply, aeval, map_zero]
  · exact (monic hs).map _
#align minpoly.is_integrally_closed_eq_field_fractions minpoly.is_integrally_closed_eq_field_fractions

/-- For integrally closed domains, the minimal polynomial over the ring is the same as the minimal
polynomial over the fraction field. Compared to `minpoly.is_integrally_closed_eq_field_fractions`,
this version is useful if the element is in a ring that is already a `K`-algebra. -/
theorem is_integrally_closed_eq_field_fractions' [IsDomain S] [Algebra K S] [IsScalarTower R K S]
    {s : S} (hs : IsIntegral R s) : minpoly K s = (minpoly R s).map (algebraMap R K) :=
  by
  let L := FractionRing S
  rw [← is_integrally_closed_eq_field_fractions K L hs]
  refine'
    minpoly.eq_of_algebra_map_eq (IsFractionRing.injective S L) (is_integral_of_is_scalar_tower hs)
      rfl
#align minpoly.is_integrally_closed_eq_field_fractions' minpoly.is_integrally_closed_eq_field_fractions'

/-- For GCD domains, the minimal polynomial over the ring is the same as the minimal polynomial
over the fraction field. Compared to `minpoly.is_integrally_closed_eq_field_fractions`, this
version is useful if the element is in a ring that is not a domain -/
theorem is_integrally_closed_eq_field_fractions'' [NoZeroSMulDivisors S L] {s : S}
    (hs : IsIntegral R s) : minpoly K (algebraMap S L s) = map (algebraMap R K) (minpoly R s) :=
  by
  --the idea of the proof is the following: since the minpoly of `a` over `Frac(R)` divides the
  --minpoly of `a` over `R`, it is itself in `R`. Hence its degree is greater or equal to that of
  --the minpoly of `a` over `R`. But the minpoly of `a` over `Frac(R)` divides the minpoly of a
  --over `R` in `R[X]` so we are done.
  --a few "trivial" preliminary results to set up the proof
  have lem0 : minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (minpoly R s) :=
    dvd_map_of_is_scalar_tower' R K L s
  have lem1 : IsIntegral K (algebraMap S L s) :=
    by
    refine' is_integral_map_of_comp_eq_of_is_integral (algebraMap R K) _ _ hs
    rw [← IsScalarTower.algebra_map_eq, ← IsScalarTower.algebra_map_eq]
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (minpoly.monic hs) lem0
  rw [(minpoly.monic lem1).leadingCoeff, C_1, mul_one] at hg
  have lem2 : Polynomial.aeval s g = 0 :=
    by
    have := minpoly.aeval K (algebraMap S L s)
    rw [← hg, ← map_aeval_eq_aeval_map, ← map_zero (algebraMap S L)] at this
    · exact NoZeroSMulDivisors.algebra_map_injective S L this
    · rw [← IsScalarTower.algebra_map_eq, ← IsScalarTower.algebra_map_eq]
  have lem3 : g.monic := by
    simpa only [Function.Injective.monic_map_iff (IsFractionRing.injective R K), hg] using
      minpoly.monic lem1
  rw [← hg]
  refine'
    congr_arg _
      (Eq.symm (Polynomial.eq_of_monic_of_dvd_of_nat_degree_le lem3 (minpoly.monic hs) _ _))
  · rwa [← map_dvd_map _ (IsFractionRing.injective R K) lem3, hg]
  · exact nat_degree_le_nat_degree (minpoly.min R s lem3 lem2)
#align minpoly.is_integrally_closed_eq_field_fractions'' minpoly.is_integrally_closed_eq_field_fractions''

end

variable [IsDomain S] [NoZeroSMulDivisors R S]

theorem gcd_domain_dvd [NormalizedGCDMonoid R] {s : S} (hs : IsIntegral R s) {P : R[X]} (hP : P ≠ 0)
    (hroot : Polynomial.aeval s P = 0) : minpoly R s ∣ P :=
  by
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

variable [IsIntegrallyClosed R]

/-- For integrally closed rings, the minimal polynomial divides any polynomial that has the
  integral element as root. See also `minpoly.dvd` which relaxes the assumptions on `S`
  in exchange for stronger assumptions on `R`. -/
theorem is_integrally_closed_dvd [Nontrivial R] (p : R[X]) {s : S} (hs : IsIntegral R s) :
    Polynomial.aeval s p = 0 ↔ minpoly R s ∣ p :=
  by
  refine' ⟨fun hp => _, fun hp => _⟩
  · let K := FractionRing R
    let L := FractionRing S
    have : minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (p %ₘ minpoly R s) :=
      by
      rw [map_mod_by_monic _ (minpoly.monic hs), mod_by_monic_eq_sub_mul_div]
      refine' dvd_sub (minpoly.dvd K (algebraMap S L s) _) _
      rw [← map_aeval_eq_aeval_map, hp, map_zero]
      rw [← IsScalarTower.algebra_map_eq, ← IsScalarTower.algebra_map_eq]
      apply dvd_mul_of_dvd_left
      rw [is_integrally_closed_eq_field_fractions'' K L hs]
      exact monic.map _ (minpoly.monic hs)
    rw [is_integrally_closed_eq_field_fractions'' _ _ hs,
      map_dvd_map (algebraMap R K) (IsFractionRing.injective R K) (minpoly.monic hs)] at this
    rw [← dvd_iff_mod_by_monic_eq_zero (minpoly.monic hs)]
    refine'
      Polynomial.eq_zero_of_dvd_of_degree_lt this (degree_mod_by_monic_lt p <| minpoly.monic hs)
    all_goals infer_instance
  ·
    simpa only [RingHom.mem_ker, RingHom.coe_comp, coe_eval_ring_hom, coe_map_ring_hom,
      Function.comp_apply, eval_map, ← aeval_def] using
      aeval_eq_zero_of_dvd_aeval_eq_zero hp (minpoly.aeval R s)
#align minpoly.is_integrally_closed_dvd minpoly.is_integrally_closed_dvd

theorem ker_eval {s : S} (hs : IsIntegral R s) :
    ((Polynomial.aeval s).toRingHom : R[X] →+* S).ker = Ideal.span ({minpoly R s} : Set R[X]) :=
  by
  apply le_antisymm <;> intro p hp
  ·
    rwa [RingHom.mem_ker, AlgHom.to_ring_hom_eq_coe, AlgHom.coe_to_ring_hom,
      is_integrally_closed_dvd p hs, ← Ideal.mem_span_singleton] at hp
  ·
    rwa [RingHom.mem_ker, AlgHom.to_ring_hom_eq_coe, AlgHom.coe_to_ring_hom,
      is_integrally_closed_dvd p hs, ← Ideal.mem_span_singleton]
#align minpoly.ker_eval minpoly.ker_eval

/-- If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` is at least the
degree of the minimal polynomial of `x`. See also `minpoly.degree_le_of_ne_zero` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
theorem IsIntegrallyClosed.degree_le_of_ne_zero {s : S} (hs : IsIntegral R s) {p : R[X]}
    (hp0 : p ≠ 0) (hp : Polynomial.aeval s p = 0) : degree (minpoly R s) ≤ degree p :=
  by
  rw [degree_eq_nat_degree (minpoly.ne_zero hs), degree_eq_nat_degree hp0]
  norm_cast
  exact nat_degree_le_of_dvd ((is_integrally_closed_dvd _ hs).mp hp) hp0
#align minpoly.is_integrally_closed.degree_le_of_ne_zero minpoly.IsIntegrallyClosed.degree_le_of_ne_zero

/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root, then this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.unique` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
theorem IsIntegrallyClosed.Minpoly.unique {s : S} {P : R[X]} (hmo : P.Monic)
    (hP : Polynomial.aeval s P = 0)
    (Pmin : ∀ Q : R[X], Q.Monic → Polynomial.aeval s Q = 0 → degree P ≤ degree Q) :
    P = minpoly R s := by
  have hs : IsIntegral R s := ⟨P, hmo, hP⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
  have := is_integrally_closed.degree_le_of_ne_zero hs hnz (by simp [hP])
  contrapose! this
  refine' degree_sub_lt _ (NeZero hs) _
  · exact le_antisymm (min R s hmo hP) (Pmin (minpoly R s) (monic hs) (aeval R s))
  · rw [(monic hs).leadingCoeff, hmo.leading_coeff]
#align minpoly.is_integrally_closed.minpoly.unique minpoly.IsIntegrallyClosed.Minpoly.unique

section AdjoinRoot

noncomputable section

open Algebra Polynomial AdjoinRoot

variable {R} {x : S}

theorem ToAdjoin.injective (hx : IsIntegral R x) : Function.Injective (Minpoly.toAdjoin R x) :=
  by
  refine' (injective_iff_map_eq_zero _).2 fun P₁ hP₁ => _
  obtain ⟨P, hP⟩ := mk_surjective (minpoly.monic hx) P₁
  by_cases hPzero : P = 0
  · simpa [hPzero] using hP.symm
  rw [← hP, minpoly.to_adjoin_apply', lift_hom_mk, ← Subalgebra.coe_eq_zero, aeval_subalgebra_coe,
    [anonymous], is_integrally_closed_dvd _ hx] at hP₁
  obtain ⟨Q, hQ⟩ := hP₁
  rw [← hP, hQ, RingHom.map_mul, mk_self, zero_mul]
#align minpoly.to_adjoin.injective minpoly.ToAdjoin.injective

/-- The algebra isomorphism `adjoin_root (minpoly R x) ≃ₐ[R] adjoin R x` -/
@[simps]
def equivAdjoin (hx : IsIntegral R x) : AdjoinRoot (minpoly R x) ≃ₐ[R] adjoin R ({x} : Set S) :=
  AlgEquiv.ofBijective (Minpoly.toAdjoin R x)
    ⟨minpoly.ToAdjoin.injective hx, Minpoly.toAdjoin.surjective R x⟩
#align minpoly.equiv_adjoin minpoly.equivAdjoin

/-- The `power_basis` of `adjoin R {x}` given by `x`. See `algebra.adjoin.power_basis` for a version
over a field. -/
@[simps]
def Algebra.adjoin.powerBasis' (hx : IsIntegral R x) :
    PowerBasis R (Algebra.adjoin R ({x} : Set S)) :=
  PowerBasis.map (AdjoinRoot.powerBasis' (minpoly.monic hx)) (minpoly.equivAdjoin hx)
#align algebra.adjoin.power_basis' Algebra.adjoin.powerBasis'

/-- The power basis given by `x` if `B.gen ∈ adjoin R {x}`. -/
@[simps]
noncomputable def PowerBasis.ofGenMemAdjoin' (B : PowerBasis R S) (hint : IsIntegral R x)
    (hx : B.gen ∈ adjoin R ({x} : Set S)) : PowerBasis R S :=
  (Algebra.adjoin.powerBasis' hint).map <|
    (Subalgebra.equivOfEq _ _ <| PowerBasis.adjoin_eq_top_of_gen_mem_adjoin hx).trans
      Subalgebra.topEquiv
#align power_basis.of_gen_mem_adjoin' PowerBasis.ofGenMemAdjoin'

end AdjoinRoot

end minpoly

