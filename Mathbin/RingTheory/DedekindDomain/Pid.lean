/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import RingTheory.DedekindDomain.Dvr
import RingTheory.DedekindDomain.Ideal

#align_import ring_theory.dedekind_domain.pid from "leanprover-community/mathlib"@"6b31d1eebd64eab86d5bd9936bfaada6ca8b5842"

/-!
# Proving a Dedekind domain is a PID

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some results that we can use to show all ideals in a Dedekind domain are
principal.

## Main results

 * `ideal.is_principal.of_finite_maximals_of_is_unit`: an invertible ideal in a commutative ring
   with finitely many maximal ideals, is a principal ideal.
 * `is_principal_ideal_ring.of_finite_primes`: if a Dedekind domain has finitely many prime ideals,
   it is a principal ideal domain.
-/


variable {R : Type _} [CommRing R]

open Ideal

open UniqueFactorizationMonoid

open scoped BigOperators

open scoped nonZeroDivisors

open UniqueFactorizationMonoid

#print Ideal.eq_span_singleton_of_mem_of_not_mem_sq_of_not_mem_prime_ne /-
/-- Let `P` be a prime ideal, `x ∈ P \ P²` and `x ∉ Q` for all prime ideals `Q ≠ P`.
Then `P` is generated by `x`. -/
theorem Ideal.eq_span_singleton_of_mem_of_not_mem_sq_of_not_mem_prime_ne {P : Ideal R}
    (hP : P.IsPrime) [IsDomain R] [IsDedekindDomain R] {x : R} (x_mem : x ∈ P) (hxP2 : x ∉ P ^ 2)
    (hxQ : ∀ Q : Ideal R, IsPrime Q → Q ≠ P → x ∉ Q) : P = Ideal.span {x} :=
  by
  letI := Classical.decEq (Ideal R)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxP2 (zero_mem _)
  by_cases hP0 : P = ⊥
  · subst hP0
    simpa using hxP2
  have hspan0 : span ({x} : Set R) ≠ ⊥ := mt ideal.span_singleton_eq_bot.mp hx0
  have span_le := (Ideal.span_singleton_le_iff_mem _).mpr x_mem
  refine'
    associated_iff_eq.mp
      ((associated_iff_normalized_factors_eq_normalized_factors hP0 hspan0).mpr
        (le_antisymm ((dvd_iff_normalized_factors_le_normalized_factors hP0 hspan0).mp _) _))
  · rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  simp only [normalized_factors_irreducible (Ideal.prime_of_isPrime hP0 hP).Irreducible,
    normalize_eq, Multiset.le_iff_count, Multiset.count_singleton]
  intro Q
  split_ifs with hQ
  · subst hQ
    refine' (Ideal.count_normalizedFactors_eq _ _).le <;>
        simp only [Ideal.span_singleton_le_iff_mem, pow_one] <;>
      assumption
  by_cases hQp : is_prime Q
  · skip
    refine' (Ideal.count_normalizedFactors_eq _ _).le <;>
      simp only [Ideal.span_singleton_le_iff_mem, pow_one, pow_zero, one_eq_top, Submodule.mem_top]
    exact hxQ _ hQp hQ
  ·
    exact
      (multiset.count_eq_zero.mpr fun hQi =>
          hQp
            (is_prime_of_prime
              (irreducible_iff_prime.mp (irreducible_of_normalized_factor _ hQi)))).le
#align ideal.eq_span_singleton_of_mem_of_not_mem_sq_of_not_mem_prime_ne Ideal.eq_span_singleton_of_mem_of_not_mem_sq_of_not_mem_prime_ne
-/

#print FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top /-
theorem FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top {R A : Type _}
    [CommRing R] [CommRing A] [Algebra R A] {S : Submonoid R} [IsLocalization S A]
    (I : (FractionalIdeal S A)ˣ) {v : A} (hv : v ∈ (↑I⁻¹ : FractionalIdeal S A))
    (h : Submodule.comap (Algebra.linearMap R A) (I * Submodule.span R {v}) = ⊤) :
    Submodule.IsPrincipal (I : Submodule R A) :=
  by
  have hinv := I.mul_inv
  set J := Submodule.comap (Algebra.linearMap R A) (I * Submodule.span R {v})
  have hJ : IsLocalization.coeSubmodule A J = I * Submodule.span R {v} :=
    by
    rw [Subtype.ext_iff, FractionalIdeal.coe_mul, FractionalIdeal.coe_one] at hinv
    apply Submodule.map_comap_eq_self
    rw [← Submodule.one_eq_range, ← hinv]
    exact Submodule.mul_le_mul_right ((Submodule.span_singleton_le_iff_mem _ _).2 hv)
  have : (1 : A) ∈ ↑I * Submodule.span R {v} :=
    by
    rw [← hJ, h, IsLocalization.coeSubmodule_top, Submodule.mem_one]
    exact ⟨1, (algebraMap R _).map_one⟩
  obtain ⟨w, hw, hvw⟩ := Submodule.mem_mul_span_singleton.1 this
  refine' ⟨⟨w, _⟩⟩
  rw [← FractionalIdeal.coe_spanSingleton S, ← inv_inv I, eq_comm, coe_coe]
  refine' congr_arg coe (Units.eq_inv_of_mul_eq_one_left (le_antisymm _ _))
  · infer_instance
  · conv_rhs => rw [← hinv, mul_comm]
    apply FractionalIdeal.mul_le_mul_left (fractional_ideal.span_singleton_le_iff_mem.mpr hw)
  · rw [FractionalIdeal.one_le, ← hvw, mul_comm]
    exact FractionalIdeal.mul_mem_mul hv (FractionalIdeal.mem_spanSingleton_self _ _)
#align fractional_ideal.is_principal_of_unit_of_comap_mul_span_singleton_eq_top FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top
-/

#print FractionalIdeal.isPrincipal.of_finite_maximals_of_inv /-
/--
An invertible fractional ideal of a commutative ring with finitely many maximal ideals is principal.

https://math.stackexchange.com/a/95857 -/
theorem FractionalIdeal.isPrincipal.of_finite_maximals_of_inv {A : Type _} [CommRing A]
    [Algebra R A] {S : Submonoid R} [IsLocalization S A] (hS : S ≤ R⁰)
    (hf : {I : Ideal R | I.IsMaximal}.Finite) (I I' : FractionalIdeal S A) (hinv : I * I' = 1) :
    Submodule.IsPrincipal (I : Submodule R A) :=
  by
  have hinv' := hinv
  rw [Subtype.ext_iff, FractionalIdeal.coe_mul] at hinv
  let s := hf.to_finset
  haveI := Classical.decEq (Ideal R)
  have coprime : ∀ M ∈ s, ∀ M' ∈ s.erase M, M ⊔ M' = ⊤ :=
    by
    simp_rw [Finset.mem_erase, hf.mem_to_finset]
    rintro M hM M' ⟨hne, hM'⟩
    exact Ideal.IsMaximal.coprime_of_ne hM hM' hne.symm
  have nle : ∀ M ∈ s, ¬(⨅ M' ∈ s.erase M, M') ≤ M := fun M hM =>
    left_lt_sup.1
      ((hf.mem_to_finset.1 hM).ne_top.lt_top.trans_eq (Ideal.sup_iInf_eq_top <| coprime M hM).symm)
  have : ∀ M ∈ s, ∃ a ∈ I, ∃ b ∈ I', a * b ∉ IsLocalization.coeSubmodule A M :=
    by
    intro M hM; by_contra! h
    obtain ⟨x, hx, hxM⟩ :=
      SetLike.exists_of_lt
        ((IsLocalization.coeSubmodule_strictMono hS (hf.mem_to_finset.1 hM).ne_top.lt_top).trans_eq
          hinv.symm)
    refine' hxM (Submodule.map₂_le.2 _ hx); exact h
  choose! a ha b hb hm using this
  choose! u hu hum using fun M hM => SetLike.not_le_iff_exists.1 (nle M hM)
  let v := ∑ M in s, u M • b M
  have hv : v ∈ I' := Submodule.sum_mem _ fun M hM => Submodule.smul_mem _ _ <| hb M hM
  refine'
    FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top
      (Units.mkOfMulEqOne I I' hinv') hv (of_not_not fun h => _)
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ h
  replace hM := hf.mem_to_finset.2 hM
  have : ∀ a ∈ I, ∀ b ∈ I', ∃ c, algebraMap R _ c = a * b :=
    by
    intro a ha b hb; have hi := hinv.le
    obtain ⟨c, -, hc⟩ := hi (Submodule.mul_mem_mul ha hb)
    exact ⟨c, hc⟩
  have hmem : a M * v ∈ IsLocalization.coeSubmodule A M :=
    by
    obtain ⟨c, hc⟩ := this _ (ha M hM) v hv
    refine' IsLocalization.coeSubmodule_mono _ hJM ⟨c, _, hc⟩
    have := Submodule.mul_mem_mul (ha M hM) (Submodule.mem_span_singleton_self v)
    rwa [← hc] at this
  simp_rw [Finset.mul_sum, mul_smul_comm] at hmem
  rw [← s.add_sum_erase _ hM, Submodule.add_mem_iff_left] at hmem
  · refine' hm M hM _
    obtain ⟨c, hc : algebraMap R A c = a M * b M⟩ := this _ (ha M hM) _ (hb M hM)
    rw [← hc] at hmem ⊢
    rw [Algebra.smul_def, ← _root_.map_mul] at hmem
    obtain ⟨d, hdM, he⟩ := hmem
    rw [IsLocalization.injective _ hS he] at hdM
    exact
      Submodule.mem_map_of_mem
        (((hf.mem_to_finset.1 hM).IsPrime.mem_or_mem hdM).resolve_left <| hum M hM)
  · refine' Submodule.sum_mem _ fun M' hM' => _
    rw [Finset.mem_erase] at hM'
    obtain ⟨c, hc⟩ := this _ (ha M hM) _ (hb M' hM'.2)
    rw [← hc, Algebra.smul_def, ← _root_.map_mul]
    specialize hu M' hM'.2
    simp_rw [Ideal.mem_iInf, Finset.mem_erase] at hu
    exact Submodule.mem_map_of_mem (M.mul_mem_right _ <| hu M ⟨hM'.1.symm, hM⟩)
#align fractional_ideal.is_principal.of_finite_maximals_of_inv FractionalIdeal.isPrincipal.of_finite_maximals_of_inv
-/

#print Ideal.IsPrincipal.of_finite_maximals_of_isUnit /-
/-- An invertible ideal in a commutative ring with finitely many maximal ideals is principal.

https://math.stackexchange.com/a/95857 -/
theorem Ideal.IsPrincipal.of_finite_maximals_of_isUnit (hf : {I : Ideal R | I.IsMaximal}.Finite)
    {I : Ideal R} (hI : IsUnit (I : FractionalIdeal R⁰ (FractionRing R))) : I.IsPrincipal :=
  (IsLocalization.coeSubmodule_isPrincipal _ le_rfl).mp
    (FractionalIdeal.isPrincipal.of_finite_maximals_of_inv le_rfl hf I
      (↑hI.Unit⁻¹ : FractionalIdeal R⁰ (FractionRing R)) hI.Unit.mul_inv)
#align ideal.is_principal.of_finite_maximals_of_is_unit Ideal.IsPrincipal.of_finite_maximals_of_isUnit
-/

#print IsPrincipalIdealRing.of_finite_primes /-
/-- A Dedekind domain is a PID if its set of primes is finite. -/
theorem IsPrincipalIdealRing.of_finite_primes [IsDomain R] [IsDedekindDomain R]
    (h : {I : Ideal R | I.IsPrime}.Finite) : IsPrincipalIdealRing R :=
  ⟨fun I => by
    obtain rfl | hI := eq_or_ne I ⊥
    · exact bot_isPrincipal
    apply Ideal.IsPrincipal.of_finite_maximals_of_isUnit
    · apply h.subset; exact @Ideal.IsMaximal.isPrime _ _
    · exact isUnit_of_mul_eq_one _ _ (FractionalIdeal.coe_ideal_mul_inv I hI)⟩
#align is_principal_ideal_ring.of_finite_primes IsPrincipalIdealRing.of_finite_primes
-/

variable [IsDomain R] [IsDedekindDomain R]

variable (S : Type _) [CommRing S] [IsDomain S]

variable [Algebra R S] [Module.Free R S] [Module.Finite R S]

variable (p : Ideal R) (hp0 : p ≠ ⊥) [IsPrime p]

variable {Sₚ : Type _} [CommRing Sₚ] [Algebra S Sₚ]

variable [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]

variable [Algebra R Sₚ] [IsScalarTower R S Sₚ]

/- The first hypothesis below follows from properties of the localization but is needed for the
second, so we leave it to the user to provide (automatically). -/
variable [IsDomain Sₚ] [IsDedekindDomain Sₚ]

#print IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime /-
/-- If `p` is a prime in the Dedekind domain `R`, `S` an extension of `R` and `Sₚ` the localization
of `S` at `p`, then all primes in `Sₚ` are factors of the image of `p` in `Sₚ`. -/
theorem IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime [DecidableEq (Ideal Sₚ)]
    {P : Ideal Sₚ} (hP : IsPrime P) (hP0 : P ≠ ⊥) :
    P ∈ normalizedFactors (Ideal.map (algebraMap R Sₚ) p) :=
  by
  have non_zero_div : Algebra.algebraMapSubmonoid S p.prime_compl ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (NoZeroSMulDivisors.algebraMap_injective _ _)
      p.prime_compl_le_non_zero_divisors
  letI : Algebra (Localization.AtPrime p) Sₚ := localizationAlgebra p.prime_compl S
  haveI : IsScalarTower R (Localization.AtPrime p) Sₚ :=
    IsScalarTower.of_algebraMap_eq fun x => by
      erw [IsLocalization.map_eq, IsScalarTower.algebraMap_apply R S]
  obtain ⟨pid, p', ⟨hp'0, hp'p⟩, hpu⟩ :=
    (DiscreteValuationRing.iff_pid_with_one_nonzero_prime (Localization.AtPrime p)).mp
      (IsLocalization.AtPrime.discreteValuationRing_of_dedekind_domain R hp0 _)
  have : LocalRing.maximalIdeal (Localization.AtPrime p) ≠ ⊥ :=
    by
    rw [Submodule.ne_bot_iff] at hp0 ⊢
    obtain ⟨x, x_mem, x_ne⟩ := hp0
    exact
      ⟨algebraMap _ _ x, (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _).mpr x_mem,
        IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ p.prime_compl_le_non_zero_divisors
          (mem_nonZeroDivisors_of_ne_zero x_ne)⟩
  rw [← Multiset.singleton_le, ← normalize_eq P, ←
    normalized_factors_irreducible (Ideal.prime_of_isPrime hP0 hP).Irreducible, ←
    dvd_iff_normalized_factors_le_normalized_factors hP0, dvd_iff_le,
    IsScalarTower.algebraMap_eq R (Localization.AtPrime p) Sₚ, ← Ideal.map_map,
    Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap,
    hpu (LocalRing.maximalIdeal _) ⟨this, _⟩, hpu (comap _ _) ⟨_, _⟩]
  · exact le_rfl
  · have hRS : Algebra.IsIntegral R S :=
      isIntegral_of_noetherian (isNoetherian_of_isNoetherianRing_of_finite Module.Finite.out)
    exact mt (Ideal.eq_bot_of_comap_eq_bot (isIntegral_localization hRS)) hP0
  · exact Ideal.comap_isPrime (algebraMap (Localization.AtPrime p) Sₚ) P
  · exact (LocalRing.maximalIdeal.isMaximal _).IsPrime
  · rw [Ne.def, zero_eq_bot, Ideal.map_eq_bot_iff_of_injective]
    · assumption
    rw [IsScalarTower.algebraMap_eq R S Sₚ]
    exact
      (IsLocalization.injective Sₚ non_zero_div).comp (NoZeroSMulDivisors.algebraMap_injective _ _)
#align is_localization.over_prime.mem_normalized_factors_of_is_prime IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime
-/

#print IsDedekindDomain.isPrincipalIdealRing_localization_over_prime /-
/-- Let `p` be a prime in the Dedekind domain `R` and `S` be an integral extension of `R`,
then the localization `Sₚ` of `S` at `p` is a PID. -/
theorem IsDedekindDomain.isPrincipalIdealRing_localization_over_prime : IsPrincipalIdealRing Sₚ :=
  by
  letI := Classical.decEq (Ideal Sₚ)
  letI := Classical.decPred fun P : Ideal Sₚ => P.IsPrime
  refine'
    IsPrincipalIdealRing.of_finite_primes
      (Set.Finite.ofFinset
        (Finset.filter (fun P => P.IsPrime)
          ({⊥} ∪ (normalized_factors (Ideal.map (algebraMap R Sₚ) p)).toFinset))
        fun P => _)
  rw [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, Set.mem_setOf,
    Multiset.mem_toFinset]
  exact
    and_iff_right_of_imp fun hP =>
      or_iff_not_imp_left.mpr (IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime S p hp0 hP)
#align is_dedekind_domain.is_principal_ideal_ring_localization_over_prime IsDedekindDomain.isPrincipalIdealRing_localization_over_prime
-/

