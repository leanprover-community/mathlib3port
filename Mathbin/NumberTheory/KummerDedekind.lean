/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/
import Mathbin.RingTheory.AdjoinRoot
import Mathbin.RingTheory.DedekindDomain.Ideal
import Mathbin.RingTheory.AlgebraTower

/-!
# Kummer-Dedekind theorem

This file proves the monogenic version of the Kummer-Dedekind theorem on the splitting of prime
ideals in an extension of the ring of integers. This states that if `I` is a prime ideal of
Dedekind domain `R` and `S = R[α]` for some `α` that is integral over `R` with minimal polynomial
`f`, then the prime factorisations of `I * S` and `f mod I` have the same shape, i.e. they have the
same number of prime factors, and each prime factors of `I * S` can be paired with a prime factor
of `f mod I` in a way that ensures multiplicities match (in fact, this pairing can be made explicit
with a formula).

## Main definitions

 * `normalized_factors_map_equiv_normalized_factors_min_poly_mk` : The bijection in the
    Kummer-Dedekind theorem. This is the pairing between the prime factors of `I * S` and the prime
    factors of `f mod I`.

## Main results

 * `normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map` : The Kummer-Dedekind
    theorem.
 * `ideal.irreducible_map_of_irreducible_minpoly` : `I.map (algebra_map R S)` is irreducible if
    `(map I^.quotient.mk (minpoly R pb.gen))` is irreducible, where `pb` is a power basis of `S`
    over `R`.

## TODO

 * Define the conductor ideal and prove the Kummer-Dedekind theorem in full generality.

 * Prove the converse of `ideal.irreducible_map_of_irreducible_minpoly`.

 * Prove that `normalized_factors_map_equiv_normalized_factors_min_poly_mk` can be expressed as
    `normalized_factors_map_equiv_normalized_factors_min_poly_mk g = ⟨I, G(α)⟩` for `g` a prime
    factor of `f mod I` and `G` a lift of `g` to `R[X]`.

## References

 * [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

kummer, dedekind, kummer dedekind, dedekind-kummer, dedekind kummer
-/


namespace KummerDedekind

open BigOperators Polynomial Classical

open Ideal Polynomial DoubleQuot UniqueFactorizationMonoid

variable {R : Type _} [CommRingₓ R]

variable {S : Type _} [CommRingₓ S] [IsDomain S] [IsDedekindDomain S] [Algebra R S]

variable (pb : PowerBasis R S) {I : Ideal R}

attribute [local instance] Ideal.Quotient.field

variable [IsDomain R]

/-- The first half of the **Kummer-Dedekind Theorem** in the monogenic case, stating that the prime
    factors of `I*S` are in bijection with those of the minimal polynomial of the generator of `S`
    over `R`, taken `mod I`.-/
noncomputable def normalizedFactorsMapEquivNormalizedFactorsMinPolyMk (hI : IsMaximal I) (hI' : I ≠ ⊥) :
    { J : Ideal S | J ∈ normalizedFactors (I.map (algebraMap R S)) } ≃
      { d : (R ⧸ I)[X] | d ∈ normalizedFactors (map I (minpoly R pb.gen)) } :=
  (--show that `I * S` ≠ ⊥
        --show that the ideal spanned by `(minpoly R pb.gen) mod I` is non-zero
        normalizedFactorsEquivOfQuotEquiv
        (↑(pb.quotientEquivQuotientMinpolyMap I))
        (show I.map (algebraMap R S) ≠ ⊥ by
          rwa [Ne.def, map_eq_bot_iff_of_injective pb.basis.algebra_map_injective, ← Ne.def])
        (by
          by_contra
          exact
            (show map I (minpoly R pb.gen) ≠ 0 from Polynomial.map_monic_ne_zero (minpoly.monic pb.is_integral_gen))
              (span_singleton_eq_bot.mp h))).trans
    (normalizedFactorsEquivSpanNormalizedFactors
        (show map I (minpoly R pb.gen) ≠ 0 from Polynomial.map_monic_ne_zero (minpoly.monic pb.is_integral_gen))).symm

/-- The second half of the **Kummer-Dedekind Theorem** in the monogenic case, stating that the
    bijection `factors_equiv'` defined in the first half preserves multiplicities. -/
theorem multiplicity_factors_map_eq_multiplicity (hI : IsMaximal I) (hI' : I ≠ ⊥) {J : Ideal S}
    (hJ : J ∈ normalizedFactors (I.map (algebraMap R S))) :
    multiplicity J (I.map (algebraMap R S)) =
      multiplicity (↑(normalizedFactorsMapEquivNormalizedFactorsMinPolyMk pb hI hI' ⟨J, hJ⟩))
        (map I (minpoly R pb.gen)) :=
  by
  rw [normalized_factors_map_equiv_normalized_factors_min_poly_mk, Equivₓ.coe_trans, Function.comp_app,
    multiplicity_normalized_factors_equiv_span_normalized_factors_symm_eq_multiplicity,
    normalized_factors_equiv_of_quot_equiv_multiplicity_eq_multiplicity]

/-- The **Kummer-Dedekind Theorem**. -/
theorem normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map (hI : IsMaximal I) (hI' : I ≠ ⊥) :
    normalizedFactors (I.map (algebraMap R S)) =
      Multiset.map (fun f => ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk pb hI hI').symm f : Ideal S))
        (normalizedFactors (Polynomial.map I (minpoly R pb.gen))).attach :=
  by
  ext J
  -- WLOG, assume J is a normalized factor
  by_cases hJ:J ∈ normalized_factors (I.map (algebraMap R S))
  swap
  · rw [multiset.count_eq_zero.mpr hJ, eq_comm, Multiset.count_eq_zero, Multiset.mem_map]
    simp only [Multiset.mem_attach, true_andₓ, not_exists]
    rintro J' rfl
    exact hJ ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm J').Prop
    
  -- Then we just have to compare the multiplicities, which we already proved are equal.
  have := multiplicity_factors_map_eq_multiplicity pb hI hI' hJ
  rw [multiplicity_eq_count_normalized_factors, multiplicity_eq_count_normalized_factors,
    UniqueFactorizationMonoid.normalize_normalized_factor _ hJ, UniqueFactorizationMonoid.normalize_normalized_factor,
    PartEnat.coe_inj] at this
  refine' this.trans _
  -- Get rid of the `map` by applying the equiv to both sides.
  generalize hJ' : (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI') ⟨J, hJ⟩ = J'
  have : ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm J' : Ideal S) = J := by
    rw [← hJ', Equivₓ.symm_apply_apply _ _, Subtype.coe_mk]
  subst this
  -- Get rid of the `attach` by applying the subtype `coe` to both sides.
  rw [Multiset.count_map_eq_count' fun f =>
      ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm f : Ideal S),
    Multiset.attach_count_eq_count_coe]
  · exact subtype.coe_injective.comp (Equivₓ.injective _)
    
  · exact (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' _).Prop
    
  · exact
      irreducible_of_normalized_factor _ (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' _).Prop
    
  · exact Polynomial.map_monic_ne_zero (minpoly.monic pb.is_integral_gen)
    
  · exact irreducible_of_normalized_factor _ hJ
    
  · rwa [← bot_eq_zero, Ne.def, map_eq_bot_iff_of_injective pb.basis.algebra_map_injective]
    

theorem Ideal.irreducible_map_of_irreducible_minpoly (hI : IsMaximal I) (hI' : I ≠ ⊥)
    (hf : Irreducible (map I (minpoly R pb.gen))) : Irreducible (I.map (algebraMap R S)) := by
  have mem_norm_factors : normalize (map I (minpoly R pb.gen)) ∈ normalized_factors (map I (minpoly R pb.gen)) := by
    simp [normalized_factors_irreducible hf]
  suffices ∃ x, normalized_factors (I.map (algebraMap R S)) = {x} by
    obtain ⟨x, hx⟩ := this
    have h :=
      normalized_factors_prod
        (show I.map (algebraMap R S) ≠ 0 by
          rwa [← bot_eq_zero, Ne.def, map_eq_bot_iff_of_injective pb.basis.algebra_map_injective])
    rw [associated_iff_eq, hx, Multiset.prod_singleton] at h
    rw [← h]
    exact irreducible_of_normalized_factor x (show x ∈ normalized_factors (I.map (algebraMap R S)) by simp [hx])
  rw [normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map pb hI hI']
  use
    ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm
      ⟨normalize (map I (minpoly R pb.gen)), mem_norm_factors⟩ :
      Ideal S)
  rw [Multiset.map_eq_singleton]
  use ⟨normalize (map I (minpoly R pb.gen)), mem_norm_factors⟩
  refine' ⟨_, rfl⟩
  apply Multiset.map_injective Subtype.coe_injective
  rw [Multiset.attach_map_coe, Multiset.map_singleton, Subtype.coe_mk]
  exact normalized_factors_irreducible hf

end KummerDedekind

