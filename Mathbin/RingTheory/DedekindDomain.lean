import Mathbin.RingTheory.DiscreteValuationRing
import Mathbin.RingTheory.FractionalIdeal
import Mathbin.RingTheory.Ideal.Over
import Mathbin.RingTheory.IntegrallyClosed
import Mathbin.RingTheory.Polynomial.RationalRoot
import Mathbin.RingTheory.Trace
import Mathbin.Algebra.Associated
import Mathbin.AlgebraicGeometry.PrimeSpectrum.Noetherian

/-!
# Dedekind domains

This file defines the notion of a Dedekind domain (or Dedekind ring),
giving three equivalent definitions (TODO: and shows that they are equivalent).

## Main definitions

 - `is_dedekind_domain` defines a Dedekind domain as a commutative ring that is
   Noetherian, integrally closed in its field of fractions and has Krull dimension at most one.
   `is_dedekind_domain_iff` shows that this does not depend on the choice of field of fractions.
 - `is_dedekind_domain_dvr` alternatively defines a Dedekind domain as an integral domain that
   is Noetherian, and the localization at every nonzero prime ideal is a DVR.
 - `is_dedekind_domain_inv` alternatively defines a Dedekind domain as an integral domain where
   every nonzero fractional ideal is invertible.
 - `is_dedekind_domain_inv_iff` shows that this does note depend on the choice of field of
   fractions.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ is_field A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/


variable (R A K : Type _) [CommRingₓ R] [CommRingₓ A] [Field K]

open_locale nonZeroDivisors

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (p «expr ≠ » («expr⊥»() : ideal R))
/--  A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
def Ringₓ.DimensionLeOne : Prop :=
  ∀ p _ : p ≠ (⊥ : Ideal R), p.is_prime → p.is_maximal

open Ideal Ringₓ

namespace Ringₓ

theorem dimension_le_one.principal_ideal_ring [IsDomain A] [IsPrincipalIdealRing A] : dimension_le_one A :=
  fun p nonzero prime => by
  have := Prime
  exact IsPrime.to_maximal_ideal nonzero

theorem dimension_le_one.is_integral_closure (B : Type _) [CommRingₓ B] [IsDomain B] [Nontrivial R] [Algebra R A]
    [Algebra R B] [Algebra B A] [IsScalarTower R B A] [IsIntegralClosure B R A] (h : dimension_le_one R) :
    dimension_le_one B := fun p ne_bot prime => by
  exact
    is_integral_closure.is_maximal_of_is_maximal_comap A p
      (h _ (is_integral_closure.comap_ne_bot A ne_bot) inferInstance)

theorem dimension_le_one.integral_closure [Nontrivial R] [IsDomain A] [Algebra R A] (h : dimension_le_one R) :
    dimension_le_one (integralClosure R A) :=
  h.is_integral_closure R A (integralClosure R A)

end Ringₓ

variable [IsDomain A]

/-- 
A Dedekind domain is an integral domain that is Noetherian, integrally closed, and
has Krull dimension at most one.

This is definition 3.2 of [Neukirch1992].

The integral closure condition is independent of the choice of field of fractions:
use `is_dedekind_domain_iff` to prove `is_dedekind_domain` for a given `fraction_map`.

This is the default implementation, but there are equivalent definitions,
`is_dedekind_domain_dvr` and `is_dedekind_domain_inv`.
TODO: Prove that these are actually equivalent definitions.
-/
class IsDedekindDomain : Prop where
  IsNoetherianRing : IsNoetherianRing A
  DimensionLeOne : dimension_le_one A
  IsIntegrallyClosed : IsIntegrallyClosed A

attribute [instance] IsDedekindDomain.is_noetherian_ring IsDedekindDomain.is_integrally_closed

/--  An integral domain is a Dedekind domain iff and only if it is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
theorem is_dedekind_domain_iff (K : Type _) [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomain A ↔
      IsNoetherianRing A ∧ dimension_le_one A ∧ ∀ {x : K}, IsIntegral A x → ∃ y, algebraMap A K y = x :=
  ⟨fun ⟨hr, hd, hi⟩ => ⟨hr, hd, fun x => (is_integrally_closed_iff K).mp hi⟩, fun ⟨hr, hd, hi⟩ =>
    ⟨hr, hd, (is_integrally_closed_iff K).mpr @hi⟩⟩

instance (priority := 100) IsPrincipalIdealRing.is_dedekind_domain [IsPrincipalIdealRing A] : IsDedekindDomain A :=
  ⟨PrincipalIdealRing.is_noetherian_ring, Ringₓ.DimensionLeOne.principal_ideal_ring A,
    UniqueFactorizationMonoid.is_integrally_closed⟩

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (P «expr ≠ » («expr⊥»() : ideal A))
/-- 
A Dedekind domain is an integral domain that is Noetherian, and the
localization at every nonzero prime is a discrete valuation ring.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure IsDedekindDomainDvr : Prop where
  IsNoetherianRing : IsNoetherianRing A
  is_dvr_at_nonzero_prime : ∀ P _ : P ≠ (⊥ : Ideal A), P.is_prime → DiscreteValuationRing (Localization.AtPrime P)

section Inverse

namespace FractionalIdeal

variable {R₁ : Type _} [CommRingₓ R₁] [IsDomain R₁] [Algebra R₁ K] [IsFractionRing R₁ K]

variable {I J : FractionalIdeal R₁⁰ K}

noncomputable instance : HasInv (FractionalIdeal R₁⁰ K) :=
  ⟨fun I => 1 / I⟩

theorem inv_eq : I⁻¹ = 1 / I :=
  rfl

theorem inv_zero' : (0 : FractionalIdeal R₁⁰ K)⁻¹ = 0 :=
  FractionalIdeal.div_zero

theorem inv_nonzero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    J⁻¹ = ⟨(1 : FractionalIdeal R₁⁰ K) / J, FractionalIdeal.fractional_div_of_nonzero h⟩ :=
  FractionalIdeal.div_nonzero _

theorem coe_inv_of_nonzero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    (↑J⁻¹ : Submodule R₁ K) = IsLocalization.coeSubmodule K ⊤ / J := by
  rwa [inv_nonzero _]
  rfl
  assumption

variable {K}

theorem mem_inv_iff (hI : I ≠ 0) {x : K} : x ∈ I⁻¹ ↔ ∀, ∀ y ∈ I, ∀, (x*y) ∈ (1 : FractionalIdeal R₁⁰ K) :=
  FractionalIdeal.mem_div_iff_of_nonzero hI

theorem inv_anti_mono (hI : I ≠ 0) (hJ : J ≠ 0) (hIJ : I ≤ J) : J⁻¹ ≤ I⁻¹ := fun x => by
  simp only [mem_inv_iff hI, mem_inv_iff hJ]
  exact fun h y hy => h y (hIJ hy)

theorem le_self_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I ≤ (1 : FractionalIdeal R₁⁰ K)) : I ≤ I*I⁻¹ :=
  FractionalIdeal.le_self_mul_one_div hI

variable (K)

theorem coe_ideal_le_self_mul_inv (I : Ideal R₁) : (I : FractionalIdeal R₁⁰ K) ≤ I*I⁻¹ :=
  le_self_mul_inv FractionalIdeal.coe_ideal_le_one

/--  `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (I J : FractionalIdeal R₁⁰ K) (h : (I*J) = 1) : J = I⁻¹ := by
  have hI : I ≠ 0 := FractionalIdeal.ne_zero_of_mul_eq_one I J h
  suffices h' : (I*1 / I) = 1
  ·
    exact congr_argₓ Units.inv $ @Units.ext _ _ (Units.mkOfMulEqOne _ _ h) (Units.mkOfMulEqOne _ _ h') rfl
  apply le_antisymmₓ
  ·
    apply fractional_ideal.mul_le.mpr _
    intro x hx y hy
    rw [mul_commₓ]
    exact (FractionalIdeal.mem_div_iff_of_nonzero hI).mp hy x hx
  rw [← h]
  apply FractionalIdeal.mul_left_mono I
  apply (FractionalIdeal.le_div_iff_of_nonzero hI).mpr _
  intro y hy x hx
  rw [mul_commₓ]
  exact FractionalIdeal.mul_mem_mul hx hy

theorem mul_inv_cancel_iff {I : FractionalIdeal R₁⁰ K} : (I*I⁻¹) = 1 ↔ ∃ J, (I*J) = 1 :=
  ⟨fun h => ⟨I⁻¹, h⟩, fun ⟨J, hJ⟩ => by
    rwa [← right_inverse_eq K I J hJ]⟩

theorem mul_inv_cancel_iff_is_unit {I : FractionalIdeal R₁⁰ K} : (I*I⁻¹) = 1 ↔ IsUnit I :=
  (mul_inv_cancel_iff K).trans is_unit_iff_exists_inv.symm

variable {K' : Type _} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

@[simp]
theorem map_inv (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') : I⁻¹.map (h : K →ₐ[R₁] K') = I.map h⁻¹ := by
  rw [inv_eq, FractionalIdeal.map_div, FractionalIdeal.map_one, inv_eq]

open Submodule Submodule.IsPrincipal

@[simp]
theorem span_singleton_inv (x : K) : FractionalIdeal.spanSingleton R₁⁰ x⁻¹ = FractionalIdeal.spanSingleton _ (x⁻¹) :=
  FractionalIdeal.one_div_span_singleton x

theorem mul_generator_self_inv {R₁ : Type _} [CommRingₓ R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K]
    (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
    (I*FractionalIdeal.spanSingleton _ (generator (I : Submodule R₁ K)⁻¹)) = 1 := by
  conv_lhs => congr rw [FractionalIdeal.eq_span_singleton_of_principal I]
  rw [FractionalIdeal.span_singleton_mul_span_singleton, mul_inv_cancel, FractionalIdeal.span_singleton_one]
  intro generator_I_eq_zero
  apply h
  rw [FractionalIdeal.eq_span_singleton_of_principal I, generator_I_eq_zero, FractionalIdeal.span_singleton_zero]

theorem invertible_of_principal (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
    (I*I⁻¹) = 1 :=
  FractionalIdeal.mul_div_self_cancel_iff.mpr
    ⟨FractionalIdeal.spanSingleton _ (generator (I : Submodule R₁ K)⁻¹), mul_generator_self_inv _ I h⟩

theorem invertible_iff_generator_nonzero (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] :
    (I*I⁻¹) = 1 ↔ generator (I : Submodule R₁ K) ≠ 0 := by
  constructor
  ·
    intro hI hg
    apply FractionalIdeal.ne_zero_of_mul_eq_one _ _ hI
    rw [FractionalIdeal.eq_span_singleton_of_principal I, hg, FractionalIdeal.span_singleton_zero]
  ·
    intro hg
    apply invertible_of_principal
    rw [FractionalIdeal.eq_span_singleton_of_principal I]
    intro hI
    have := FractionalIdeal.mem_span_singleton_self _ (generator (I : Submodule R₁ K))
    rw [hI, FractionalIdeal.mem_zero_iff] at this
    contradiction

theorem is_principal_inv (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
    Submodule.IsPrincipal I⁻¹.1 := by
  rw [FractionalIdeal.val_eq_coe, FractionalIdeal.is_principal_iff]
  use generator (I : Submodule R₁ K)⁻¹
  have hI : (I*FractionalIdeal.spanSingleton _ (generator (I : Submodule R₁ K)⁻¹)) = 1
  apply mul_generator_self_inv _ I h
  exact (right_inverse_eq _ I (FractionalIdeal.spanSingleton _ (generator (I : Submodule R₁ K)⁻¹)) hI).symm

@[simp]
theorem one_inv : (1⁻¹ : FractionalIdeal R₁⁰ K) = 1 :=
  FractionalIdeal.div_one

end FractionalIdeal

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (I «expr ≠ » («expr⊥»() : fractional_ideal «expr ⁰»(A) (fraction_ring A)))
/-- 
A Dedekind domain is an integral domain such that every fractional ideal has an inverse.

This is equivalent to `is_dedekind_domain`.
In particular we provide a `fractional_ideal.comm_group_with_zero` instance,
assuming `is_dedekind_domain A`, which implies `is_dedekind_domain_inv`. For **integral** ideals,
`is_dedekind_domain`(`_inv`) implies only `ideal.cancel_comm_monoid_with_zero`.
-/
def IsDedekindDomainInv : Prop :=
  ∀ I _ : I ≠ (⊥ : FractionalIdeal A⁰ (FractionRing A)), (I*I⁻¹) = 1

open FractionalIdeal

variable {R A K}

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (I «expr ≠ » («expr⊥»() : fractional_ideal «expr ⁰»(A) K))
theorem is_dedekind_domain_inv_iff [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomainInv A ↔ ∀ I _ : I ≠ (⊥ : FractionalIdeal A⁰ K), (I*I⁻¹) = 1 := by
  set h := FractionRing.algEquiv A K
  constructor <;> rintro hi I hI
  ·
    refine' FractionalIdeal.map_injective h.symm.to_alg_hom h.symm.injective _
    rw [AlgEquiv.to_alg_hom_eq_coe, inv_eq, FractionalIdeal.map_mul, FractionalIdeal.map_one_div,
      FractionalIdeal.map_one, ← inv_eq, hi]
    exact FractionalIdeal.map_ne_zero _ hI
  ·
    refine' FractionalIdeal.map_injective h.to_alg_hom h.injective _
    rw [AlgEquiv.to_alg_hom_eq_coe, inv_eq, FractionalIdeal.map_mul, FractionalIdeal.map_one_div,
      FractionalIdeal.map_one, ← inv_eq, hi]
    exact FractionalIdeal.map_ne_zero _ hI

theorem FractionalIdeal.adjoin_integral_eq_one_of_is_unit [Algebra A K] [IsFractionRing A K] (x : K)
    (hx : IsIntegral A x) (hI : IsUnit (adjoin_integral A⁰ x hx)) : adjoin_integral A⁰ x hx = 1 := by
  set I := adjoin_integral A⁰ x hx
  have mul_self : (I*I) = I := by
    apply FractionalIdeal.coe_to_submodule_injective
    simp
  convert congr_argₓ (·*I⁻¹) mul_self <;> simp only [(mul_inv_cancel_iff_is_unit K).mpr hI, mul_assocₓ, mul_oneₓ]

namespace IsDedekindDomainInv

variable [Algebra A K] [IsFractionRing A K] (h : IsDedekindDomainInv A)

include h

theorem mul_inv_eq_one {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : (I*I⁻¹) = 1 :=
  is_dedekind_domain_inv_iff.mp h I hI

theorem inv_mul_eq_one {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : (I⁻¹*I) = 1 :=
  (mul_commₓ _ _).trans (h.mul_inv_eq_one hI)

protected theorem IsUnit {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : IsUnit I :=
  is_unit_of_mul_eq_one _ _ (h.mul_inv_eq_one hI)

theorem IsNoetherianRing : IsNoetherianRing A := by
  refine' is_noetherian_ring_iff.mpr ⟨fun I : Ideal A => _⟩
  by_cases' hI : I = ⊥
  ·
    rw [hI]
    apply Submodule.fg_bot
  have hI : (I : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 :=
    (coe_to_fractional_ideal_ne_zero (le_reflₓ (nonZeroDivisors A))).mpr hI
  exact I.fg_of_is_unit (IsFractionRing.injective A (FractionRing A)) (h.is_unit hI)

theorem integrally_closed : IsIntegrallyClosed A := by
  refine' ⟨fun x hx => _⟩
  rw [← Set.mem_range, ← Algebra.mem_bot, ← Subalgebra.mem_to_submodule, Algebra.to_submodule_bot, ←
    coe_span_singleton A⁰ (1 : FractionRing A), FractionalIdeal.span_singleton_one, ←
    FractionalIdeal.adjoin_integral_eq_one_of_is_unit x hx (h.is_unit _)]
  ·
    exact mem_adjoin_integral_self A⁰ x hx
  ·
    exact fun h => one_ne_zero (eq_zero_iff.mp h 1 (Subalgebra.one_mem _))

theorem dimension_le_one : dimension_le_one A := by
  rintro P P_ne hP
  refine' ideal.is_maximal_def.mpr ⟨hP.ne_top, fun M hM => _⟩
  have P'_ne : (P : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 :=
    (coe_to_fractional_ideal_ne_zero (le_reflₓ (nonZeroDivisors A))).mpr P_ne
  have M'_ne : (M : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 :=
    (coe_to_fractional_ideal_ne_zero (le_reflₓ (nonZeroDivisors A))).mpr (lt_of_le_of_ltₓ bot_le hM).ne'
  suffices (M⁻¹*P : FractionalIdeal A⁰ (FractionRing A)) ≤ P by
    rw [eq_top_iff, ← coe_ideal_le_coe_ideal (FractionRing A), FractionalIdeal.coe_ideal_top]
    calc (1 : FractionalIdeal A⁰ (FractionRing A)) = (_*_)*_ := _ _ ≤ _*_ :=
      mul_right_mono (P⁻¹*M : FractionalIdeal A⁰ (FractionRing A)) this _ = M := _
    ·
      rw [mul_assocₓ, ← mul_assocₓ (↑P), h.mul_inv_eq_one P'_ne, one_mulₓ, h.inv_mul_eq_one M'_ne]
    ·
      rw [← mul_assocₓ (↑P), h.mul_inv_eq_one P'_ne, one_mulₓ]
    ·
      infer_instance
  intro x hx
  have le_one : (M⁻¹*P : FractionalIdeal A⁰ (FractionRing A)) ≤ 1 := by
    rw [← h.inv_mul_eq_one M'_ne]
    exact FractionalIdeal.mul_left_mono _ ((coe_ideal_le_coe_ideal (FractionRing A)).mpr hM.le)
  obtain ⟨y, hy, rfl⟩ := (mem_coe_ideal _).mp (le_one hx)
  obtain ⟨z, hzM, hzp⟩ := SetLike.exists_of_lt hM
  have zy_mem := FractionalIdeal.mul_mem_mul (mem_coe_ideal_of_mem A⁰ hzM) hx
  rw [← RingHom.map_mul, ← mul_assocₓ, h.mul_inv_eq_one M'_ne, one_mulₓ] at zy_mem
  obtain ⟨zy, hzy, zy_eq⟩ := (mem_coe_ideal A⁰).mp zy_mem
  rw [IsFractionRing.injective A (FractionRing A) zy_eq] at hzy
  exact mem_coe_ideal_of_mem A⁰ (Or.resolve_left (hP.mem_or_mem hzy) hzp)

/--  Showing one side of the equivalence between the definitions
`is_dedekind_domain_inv` and `is_dedekind_domain` of Dedekind domains. -/
theorem IsDedekindDomain : IsDedekindDomain A :=
  ⟨h.is_noetherian_ring, h.dimension_le_one, h.integrally_closed⟩

end IsDedekindDomainInv

variable [Algebra A K] [IsFractionRing A K]

/--  Specialization of `exists_prime_spectrum_prod_le_and_ne_bot_of_domain` to Dedekind domains:
Let `I : ideal A` be a nonzero ideal, where `A` is a Dedekind domain that is not a field.
Then `exists_prime_spectrum_prod_le_and_ne_bot_of_domain` states we can find a product of prime
ideals that is contained within `I`. This lemma extends that result by making the product minimal:
let `M` be a maximal ideal that contains `I`, then the product including `M` is contained within `I`
and the product excluding `M` is not contained within `I`. -/
theorem exists_multiset_prod_cons_le_and_prod_not_le [IsDedekindDomain A] (hNF : ¬IsField A) {I M : Ideal A}
    (hI0 : I ≠ ⊥) (hIM : I ≤ M) [hM : M.is_maximal] :
    ∃ Z : Multiset (PrimeSpectrum A),
      (M ::ₘ Z.map PrimeSpectrum.asIdeal).Prod ≤ I ∧ ¬Multiset.prod (Z.map PrimeSpectrum.asIdeal) ≤ I :=
  by
  obtain ⟨Z₀, hZ₀⟩ := PrimeSpectrum.exists_prime_spectrum_prod_le_and_ne_bot_of_domain hNF hI0
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ :=
    multiset.well_founded_lt.has_min
      (fun Z => (Z.map PrimeSpectrum.asIdeal).Prod ≤ I ∧ (Z.map PrimeSpectrum.asIdeal).Prod ≠ ⊥) ⟨Z₀, hZ₀⟩
  have hZM : Multiset.prod (Z.map PrimeSpectrum.asIdeal) ≤ M := le_transₓ hZI hIM
  have hZ0 : Z ≠ 0 := by
    rintro rfl
    simpa [hM.ne_top] using hZM
  obtain ⟨_, hPZ', hPM⟩ := (hM.is_prime.multiset_prod_le (mt multiset.map_eq_zero.mp hZ0)).mp hZM
  obtain ⟨P, hPZ, rfl⟩ := multiset.mem_map.mp hPZ'
  let this' := Classical.decEq (Ideal A)
  have := Multiset.map_erase PrimeSpectrum.asIdeal Subtype.coe_injective P Z
  obtain ⟨hP0, hZP0⟩ : P.as_ideal ≠ ⊥ ∧ ((Z.erase P).map PrimeSpectrum.asIdeal).Prod ≠ ⊥
  ·
    rwa [Ne.def, ← Multiset.cons_erase hPZ', Multiset.prod_cons, Ideal.mul_eq_bot, not_or_distrib, ← this] at hprodZ
  have hPM' := (IsDedekindDomain.dimension_le_one _ hP0 P.is_prime).eq_of_le hM.ne_top hPM
  run_tac
    tactic.unfreeze_local_instances
  subst hPM'
  refine' ⟨Z.erase P, _, _⟩
  ·
    convert hZI
    rw [this, Multiset.cons_erase hPZ']
  ·
    refine' fun h => h_eraseZ (Z.erase P) ⟨h, _⟩ (multiset.erase_lt.mpr hPZ)
    exact hZP0

namespace FractionalIdeal

theorem exists_not_mem_one_of_ne_bot [IsDedekindDomain A] (hNF : ¬IsField A) {I : Ideal A} (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    ∃ x : K, x ∈ (I⁻¹ : FractionalIdeal A⁰ K) ∧ x ∉ (1 : FractionalIdeal A⁰ K) := by
  suffices
    ∀ {M : Ideal A} hM : M.is_maximal, ∃ x : K, x ∈ (M⁻¹ : FractionalIdeal A⁰ K) ∧ x ∉ (1 : FractionalIdeal A⁰ K)by
    obtain ⟨M, hM, hIM⟩ : ∃ M : Ideal A, is_maximal M ∧ I ≤ M := Ideal.exists_le_maximal I hI1
    skip
    have hM0 := (M.bot_lt_of_maximal hNF).ne'
    obtain ⟨x, hxM, hx1⟩ := this hM
    refine' ⟨x, inv_anti_mono _ _ ((coe_ideal_le_coe_ideal _).mpr hIM) hxM, hx1⟩ <;>
      apply FractionalIdeal.coe_ideal_ne_zero <;> assumption
  intro M hM
  skip
  obtain ⟨⟨a, haM⟩, ha0⟩ := Submodule.nonzero_mem_of_bot_lt (M.bot_lt_of_maximal hNF)
  replace ha0 : a ≠ 0 := subtype.coe_injective.ne ha0
  let J : Ideal A := Ideal.span {a}
  have hJ0 : J ≠ ⊥ := mt ideal.span_singleton_eq_bot.mp ha0
  have hJM : J ≤ M := ideal.span_le.mpr (set.singleton_subset_iff.mpr haM)
  have hM0 : ⊥ < M := M.bot_lt_of_maximal hNF
  obtain ⟨Z, hle, hnle⟩ := exists_multiset_prod_cons_le_and_prod_not_le hNF hJ0 hJM
  obtain ⟨b, hbZ, hbJ⟩ := set_like.not_le_iff_exists.mp hnle
  have hnz_fa : algebraMap A K a ≠ 0 := mt ((RingHom.injective_iff _).mp (IsFractionRing.injective A K) a) ha0
  have hb0 : algebraMap A K b ≠ 0 :=
    mt ((RingHom.injective_iff _).mp (IsFractionRing.injective A K) b) fun h => hbJ $ h.symm ▸ J.zero_mem
  refine' ⟨algebraMap A K b*algebraMap A K a⁻¹, (mem_inv_iff _).mpr _, _⟩
  ·
    exact (FractionalIdeal.coe_to_fractional_ideal_ne_zero (le_reflₓ _)).mpr hM0.ne'
  ·
    rintro y₀ hy₀
    obtain ⟨y, h_Iy, rfl⟩ := (FractionalIdeal.mem_coe_ideal _).mp hy₀
    rw [mul_commₓ, ← mul_assocₓ, ← RingHom.map_mul]
    have h_yb : (y*b) ∈ J := by
      apply hle
      rw [Multiset.prod_cons]
      exact Submodule.smul_mem_smul h_Iy hbZ
    rw [Ideal.mem_span_singleton'] at h_yb
    rcases h_yb with ⟨c, hc⟩
    rw [← hc, RingHom.map_mul, mul_assocₓ, mul_inv_cancel hnz_fa, mul_oneₓ]
    apply FractionalIdeal.coe_mem_one
  ·
    refine' mt (FractionalIdeal.mem_one_iff _).mp _
    rintro ⟨x', h₂_abs⟩
    rw [← div_eq_mul_inv, eq_div_iff_mul_eq hnz_fa, ← RingHom.map_mul] at h₂_abs
    have := ideal.mem_span_singleton'.mpr ⟨x', IsFractionRing.injective A K h₂_abs⟩
    contradiction

theorem one_mem_inv_coe_ideal {I : Ideal A} (hI : I ≠ ⊥) : (1 : K) ∈ (I : FractionalIdeal A⁰ K)⁻¹ := by
  rw [mem_inv_iff (FractionalIdeal.coe_ideal_ne_zero hI)]
  intro y hy
  rw [one_mulₓ]
  exact coe_ideal_le_one hy
  assumption

theorem mul_inv_cancel_of_le_one [h : IsDedekindDomain A] {I : Ideal A} (hI0 : I ≠ ⊥)
    (hI : ((I*I⁻¹)⁻¹ : FractionalIdeal A⁰ K) ≤ 1) : (I*I⁻¹ : FractionalIdeal A⁰ K) = 1 := by
  by_cases' hI1 : I = ⊤
  ·
    rw [hI1, coe_ideal_top, one_mulₓ, FractionalIdeal.one_inv]
  by_cases' hNF : IsField A
  ·
    let this' := hNF.to_field A
    rcases hI1 (I.eq_bot_or_top.resolve_left hI0) with ⟨⟩
  obtain ⟨J, hJ⟩ : ∃ J : Ideal A, (J : FractionalIdeal A⁰ K) = I*I⁻¹ :=
    le_one_iff_exists_coe_ideal.mp mul_one_div_le_one
  by_cases' hJ0 : J = ⊥
  ·
    subst hJ0
    refine' absurd _ hI0
    rw [eq_bot_iff, ← coe_ideal_le_coe_ideal K, hJ]
    exact coe_ideal_le_self_mul_inv K I
    infer_instance
  by_cases' hJ1 : J = ⊤
  ·
    rw [← hJ, hJ1, coe_ideal_top]
  obtain ⟨x, hx, hx1⟩ : ∃ x : K, x ∈ (J : FractionalIdeal A⁰ K)⁻¹ ∧ x ∉ (1 : FractionalIdeal A⁰ K) :=
    exists_not_mem_one_of_ne_bot hNF hJ0 hJ1
  contrapose! hx1 with h_abs
  rw [hJ] at hx
  exact hI hx

/--  Nonzero integral ideals in a Dedekind domain are invertible.

We will use this to show that nonzero fractional ideals are invertible,
and finally conclude that fractional ideals in a Dedekind domain form a group with zero.
-/
theorem coe_ideal_mul_inv [h : IsDedekindDomain A] (I : Ideal A) (hI0 : I ≠ ⊥) : (I*I⁻¹ : FractionalIdeal A⁰ K) = 1 :=
  by
  apply mul_inv_cancel_of_le_one hI0
  by_cases' hJ0 : (I*I⁻¹ : FractionalIdeal A⁰ K) = 0
  ·
    rw [hJ0, inv_zero']
    exact FractionalIdeal.zero_le _
  intro x hx
  suffices x ∈ integralClosure A K by
    rwa [IsIntegrallyClosed.integral_closure_eq_bot, Algebra.mem_bot, Set.mem_range, ← FractionalIdeal.mem_one_iff] at
        this <;>
      assumption
  rw [mem_integral_closure_iff_mem_fg]
  have x_mul_mem : ∀, ∀ b ∈ (I⁻¹ : FractionalIdeal A⁰ K), ∀, (x*b) ∈ (I⁻¹ : FractionalIdeal A⁰ K) := by
    intro b hb
    rw [mem_inv_iff] at hx⊢
    swap
    ·
      exact FractionalIdeal.coe_ideal_ne_zero hI0
    swap
    ·
      exact hJ0
    simp only [mul_assocₓ, mul_commₓ b] at hx⊢
    intro y hy
    exact hx _ (FractionalIdeal.mul_mem_mul hy hb)
  refine'
    ⟨AlgHom.range (Polynomial.aeval x : Polynomial A →ₐ[A] K),
      is_noetherian_submodule.mp (FractionalIdeal.is_noetherian (I⁻¹)) _ fun y hy => _,
      ⟨Polynomial.x, Polynomial.aeval_X x⟩⟩
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hy
  rw [Polynomial.aeval_eq_sum_range]
  refine' Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ _
  clear hi
  induction' i with i ih
  ·
    rw [pow_zeroₓ]
    exact one_mem_inv_coe_ideal hI0
  ·
    show (x^i.succ) ∈ (I⁻¹ : FractionalIdeal A⁰ K)
    rw [pow_succₓ]
    exact x_mul_mem _ ih

/--  Nonzero fractional ideals in a Dedekind domain are units.

This is also available as `_root_.mul_inv_cancel`, using the
`comm_group_with_zero` instance defined below.
-/
protected theorem mul_inv_cancel [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hne : I ≠ 0) : (I*I⁻¹) = 1 := by
  obtain ⟨a, J, ha, hJ⟩ : ∃ (a : A)(aI : Ideal A), a ≠ 0 ∧ I = span_singleton A⁰ (algebraMap _ _ a⁻¹)*aI :=
    exists_eq_span_singleton_mul I
  suffices h₂ : (I*span_singleton A⁰ (algebraMap _ _ a)*J⁻¹) = 1
  ·
    rw [mul_inv_cancel_iff]
    exact ⟨span_singleton A⁰ (algebraMap _ _ a)*J⁻¹, h₂⟩
  subst hJ
  rw [mul_assocₓ, mul_left_commₓ (J : FractionalIdeal A⁰ K), coe_ideal_mul_inv, mul_oneₓ,
    FractionalIdeal.span_singleton_mul_span_singleton, inv_mul_cancel, FractionalIdeal.span_singleton_one]
  ·
    exact mt ((algebraMap A K).injective_iff.mp (IsFractionRing.injective A K) _) ha
  ·
    exact fractional_ideal.coe_ideal_ne_zero_iff.mp (right_ne_zero_of_mul hne)

theorem mul_right_le_iff [IsDedekindDomain A] {J : FractionalIdeal A⁰ K} (hJ : J ≠ 0) :
    ∀ {I I'}, ((I*J) ≤ I'*J) ↔ I ≤ I' := by
  intro I I'
  constructor
  ·
    intro h
    convert mul_right_mono (J⁻¹) h <;> rw [mul_assocₓ, FractionalIdeal.mul_inv_cancel hJ, mul_oneₓ]
  ·
    exact fun h => mul_right_mono J h

theorem mul_left_le_iff [IsDedekindDomain A] {J : FractionalIdeal A⁰ K} (hJ : J ≠ 0) {I I'} : ((J*I) ≤ J*I') ↔ I ≤ I' :=
  by
  convert FractionalIdeal.mul_right_le_iff hJ using 1 <;> simp only [mul_commₓ]

theorem mul_right_strict_mono [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : StrictMono (·*I) :=
  strict_mono_of_le_iff_le fun _ _ => (mul_right_le_iff hI).symm

theorem mul_left_strict_mono [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : StrictMono ((·*·) I) :=
  strict_mono_of_le_iff_le fun _ _ => (mul_left_le_iff hI).symm

/-- 
This is also available as `_root_.div_eq_mul_inv`, using the
`comm_group_with_zero` instance defined below.
-/
protected theorem div_eq_mul_inv [IsDedekindDomain A] (I J : FractionalIdeal A⁰ K) : I / J = I*J⁻¹ := by
  by_cases' hJ : J = 0
  ·
    rw [hJ, div_zero, inv_zero', mul_zero]
  refine' le_antisymmₓ ((mul_right_le_iff hJ).mp _) ((le_div_iff_mul_le hJ).mpr _)
  ·
    rw [mul_assocₓ, mul_commₓ (J⁻¹), FractionalIdeal.mul_inv_cancel hJ, mul_oneₓ, mul_le]
    intro x hx y hy
    rw [mem_div_iff_of_nonzero hJ] at hx
    exact hx y hy
  rw [mul_assocₓ, mul_commₓ (J⁻¹), FractionalIdeal.mul_inv_cancel hJ, mul_oneₓ]
  exact le_reflₓ I

end FractionalIdeal

/--  `is_dedekind_domain` and `is_dedekind_domain_inv` are equivalent ways
to express that an integral domain is a Dedekind domain. -/
theorem is_dedekind_domain_iff_is_dedekind_domain_inv : IsDedekindDomain A ↔ IsDedekindDomainInv A :=
  ⟨fun h I hI => by
    exact FractionalIdeal.mul_inv_cancel hI, fun h => h.is_dedekind_domain⟩

end Inverse

section IsDedekindDomain

variable {R A} [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal

noncomputable instance FractionalIdeal.commGroupWithZero : CommGroupWithZero (FractionalIdeal A⁰ K) :=
  { FractionalIdeal.commSemiring with inv := fun I => I⁻¹, inv_zero := inv_zero' _, div := · / ·,
    div_eq_mul_inv := FractionalIdeal.div_eq_mul_inv,
    exists_pair_ne :=
      ⟨0, 1,
        (coe_to_fractional_ideal_injective (le_reflₓ _)).Ne
          (by
            simpa using @zero_ne_one (Ideal A) _ _)⟩,
    mul_inv_cancel := fun I => FractionalIdeal.mul_inv_cancel }

noncomputable instance Ideal.cancelCommMonoidWithZero : CancelCommMonoidWithZero (Ideal A) :=
  Function.Injective.cancelCommMonoidWithZero (coe_ideal_hom A⁰ (FractionRing A)) coe_ideal_injective
    (RingHom.map_zero _) (RingHom.map_one _) (RingHom.map_mul _)

/--  For ideals in a Dedekind domain, to divide is to contain. -/
theorem Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J ≤ I :=
  ⟨Ideal.le_of_dvd, fun h => by
    by_cases' hI : I = ⊥
    ·
      have hJ : J = ⊥ := by
        rwa [hI, ← eq_bot_iff] at h
      rw [hI, hJ]
    have hI' : (I : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 :=
      (FractionalIdeal.coe_to_fractional_ideal_ne_zero (le_reflₓ (nonZeroDivisors A))).mpr hI
    have : ((I : FractionalIdeal A⁰ (FractionRing A))⁻¹*J) ≤ 1 :=
      le_transₓ (FractionalIdeal.mul_left_mono ((↑I)⁻¹) ((coe_ideal_le_coe_ideal _).mpr h))
        (le_of_eqₓ (inv_mul_cancel hI'))
    obtain ⟨H, hH⟩ := fractional_ideal.le_one_iff_exists_coe_ideal.mp this
    use H
    refine'
      coe_to_fractional_ideal_injective (le_reflₓ (nonZeroDivisors A))
        (show (J : FractionalIdeal A⁰ (FractionRing A)) = _ from _)
    rw [FractionalIdeal.coe_ideal_mul, hH, ← mul_assocₓ, mul_inv_cancel hI', one_mulₓ]⟩

theorem Ideal.dvd_not_unit_iff_lt {I J : Ideal A} : DvdNotUnit I J ↔ J < I :=
  ⟨fun ⟨hI, H, hunit, hmul⟩ =>
    lt_of_le_of_neₓ (Ideal.dvd_iff_le.mp ⟨H, hmul⟩)
      (mt
        (fun h =>
          have : H = 1 :=
            mul_left_cancel₀ hI
              (by
                rw [← hmul, h, mul_oneₓ])
          show IsUnit H from this.symm ▸ is_unit_one)
        hunit),
    fun h =>
    dvd_not_unit_of_dvd_of_not_dvd (Ideal.dvd_iff_le.mpr (le_of_ltₓ h)) (mt Ideal.dvd_iff_le.mp (not_le_of_lt h))⟩

instance : WfDvdMonoid (Ideal A) where
  well_founded_dvd_not_unit :=
    have : WellFounded (· > · : Ideal A → Ideal A → Prop) :=
      is_noetherian_iff_well_founded.mp (is_noetherian_ring_iff.mp IsDedekindDomain.is_noetherian_ring)
    by
    convert this
    ext
    rw [Ideal.dvd_not_unit_iff_lt]

instance Ideal.unique_factorization_monoid : UniqueFactorizationMonoid (Ideal A) :=
  { Ideal.wf_dvd_monoid with
    irreducible_iff_prime := fun P =>
      ⟨fun hirr =>
        ⟨hirr.ne_zero, hirr.not_unit, fun I J => by
          have : P.is_maximal := by
            refine' ⟨⟨mt ideal.is_unit_iff.mpr hirr.not_unit, _⟩⟩
            intro J hJ
            obtain ⟨J_ne, H, hunit, P_eq⟩ := ideal.dvd_not_unit_iff_lt.mpr hJ
            exact ideal.is_unit_iff.mp ((hirr.is_unit_or_is_unit P_eq).resolve_right hunit)
          rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.dvd_iff_le, SetLike.le_def, SetLike.le_def, SetLike.le_def]
          contrapose!
          rintro ⟨⟨x, x_mem, x_not_mem⟩, ⟨y, y_mem, y_not_mem⟩⟩
          exact ⟨x*y, Ideal.mul_mem_mul x_mem y_mem, mt this.is_prime.mem_or_mem (not_orₓ x_not_mem y_not_mem)⟩⟩,
        Prime.irreducible⟩ }

noncomputable instance Ideal.normalizationMonoid : NormalizationMonoid (Ideal A) :=
  normalizationMonoidOfUniqueUnits

@[simp]
theorem Ideal.dvd_span_singleton {I : Ideal A} {x : A} : I ∣ Ideal.span {x} ↔ x ∈ I :=
  Ideal.dvd_iff_le.trans (Ideal.span_le.trans Set.singleton_subset_iff)

theorem Ideal.is_prime_of_prime {P : Ideal A} (h : Prime P) : is_prime P := by
  refine' ⟨_, fun x y hxy => _⟩
  ·
    (
      rintro rfl)
    rw [← Ideal.one_eq_top] at h
    exact h.not_unit is_unit_one
  ·
    simp only [← Ideal.dvd_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at hxy⊢
    exact h.dvd_or_dvd hxy

theorem Ideal.prime_of_is_prime {P : Ideal A} (hP : P ≠ ⊥) (h : is_prime P) : Prime P := by
  refine' ⟨hP, mt ideal.is_unit_iff.mp h.ne_top, fun I J hIJ => _⟩
  simpa only [Ideal.dvd_iff_le] using h.mul_le.mp (Ideal.le_of_dvd hIJ)

/--  In a Dedekind domain, the (nonzero) prime elements of the monoid with zero `ideal A`
are exactly the prime ideals. -/
theorem Ideal.prime_iff_is_prime {P : Ideal A} (hP : P ≠ ⊥) : Prime P ↔ is_prime P :=
  ⟨Ideal.is_prime_of_prime, Ideal.prime_of_is_prime hP⟩

end IsDedekindDomain

section IsIntegralClosure

/-! ### `is_integral_closure` section

We show that an integral closure of a Dedekind domain in a finite separable
field extension is again a Dedekind domain. This implies the ring of integers
of a number field is a Dedekind domain. -/


open Algebra

open_locale BigOperators

variable {A K} [Algebra A K] [IsFractionRing A K]

variable {L : Type _} [Field L] (C : Type _) [CommRingₓ C]

variable [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L]

variable [Algebra C L] [IsIntegralClosure C A L] [Algebra A C] [IsScalarTower A C L]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `IsIntegralClosure.range_le_span_dual_basis [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `IsSeparable [`K `L]) "]")
    (Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.instBinder "[" [] (Term.app `Fintype [`ι]) "]")
    (Term.instBinder "[" [] (Term.app `DecidableEq [`ι]) "]")
    (Term.explicitBinder "(" [`b] [":" (Term.app `Basis [`ι `K `L])] [] ")")
    (Term.explicitBinder
     "("
     [`hb_int]
     [":" (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `IsIntegral [`A (Term.app `b [`i])]))]
     []
     ")")
    (Term.instBinder "[" [] (Term.app `IsIntegrallyClosed [`A]) "]")]
   (Term.typeSpec
    ":"
    («term_≤_»
     (Term.proj (Term.app (Term.proj (Term.app `Algebra.linearMap [`C `L]) "." `restrictScalars) [`A]) "." `range)
     "≤"
     (Term.app
      `Submodule.span
      [`A
       («term_$__»
        `Set.Range
        "$"
        (Term.app
         (Term.proj (Term.app `trace_form [`K `L]) "." `dualBasis)
         [(Term.app `trace_form_nondegenerate [`K `L]) `b]))]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `db
           []
           ":="
           (Term.app
            (Term.proj (Term.app `trace_form [`K `L]) "." `dualBasis)
            [(Term.app `trace_form_nondegenerate [`K `L]) `b]))))
        [])
       (group
        (Tactic.rintro
         "rintro"
         [(Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
          (Tactic.rintroPat.one
           (Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
            "⟩"))]
         [])
        [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `LinearMap.coe_restrict_scalars_eq_coe)
           ","
           (Tactic.simpLemma [] [] `Algebra.linear_map_apply)]
          "]"]
         [])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hx []]
           [(Term.typeSpec ":" (Term.app `IsIntegral [`A (Term.app `algebraMap [`C `L `x])]))]
           ":="
           (Term.proj (Term.app `IsIntegralClosure.is_integral [`A `L `x]) "." `algebraMap))))
        [])
       (group
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          («term∃_,_»
           "∃"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] [":" (Term.arrow `ι "→" `A)]))
           ","
           («term_=_»
            (Term.app `algebraMap [`C `L `x])
            "="
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             ", "
             (Algebra.Group.Defs.«term_•_» (Term.app `c [`i]) " • " (Term.app `db [`i])))))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.obtain
                "obtain"
                [(Tactic.rcasesPatMed
                  [(Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x_eq)]) [])]
                    "⟩")])]
                []
                [":=" [`this]])
               [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `x_eq)] "]") []) [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `Submodule.sum_mem
                 [(Term.hole "_")
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`i (Term.hole "_")] [])]
                    "=>"
                    (Term.app
                     `Submodule.smul_mem
                     [(Term.hole "_") (Term.hole "_") (Term.app `Submodule.subset_span [(Term.hole "_")])])))]))
               [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_range)] "]") []) [])
              (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")) [])])))))
        [])
       (group
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          («term∃_,_»
           "∃"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] [":" (Term.arrow `ι "→" `K)]))
           ","
           («term_∧_»
            (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `IsIntegral [`A (Term.app `c [`i])]))
            "∧"
            («term_=_»
             (Term.app `algebraMap [`C `L `x])
             "="
             (Algebra.BigOperators.Basic.«term∑_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              ", "
              (Algebra.Group.Defs.«term_•_» (Term.app `c [`i]) " • " (Term.app `db [`i]))))))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.obtain
                "obtain"
                [(Tactic.rcasesPatMed
                  [(Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hc)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                    "⟩")])]
                []
                [":=" [`this]])
               [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hc' []]
                  [(Term.typeSpec
                    ":"
                    (Term.forall
                     "∀"
                     [(Term.simpleBinder [`i] [])]
                     ","
                     (Term.app `IsLocalization.IsInteger [`A (Term.app `c [`i])])))]
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`i] [])]
                    "=>"
                    (Term.app `is_integrally_closed.is_integral_iff.mp [(Term.app `hc [`i])]))))))
               [])
              (group
               (Tactic.use
                "use"
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`i] [])]
                   "=>"
                   (Term.app `Classical.some [(Term.app `hc' [`i])])))])
               [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `hx.trans
                 [(Term.app
                   `Finset.sum_congr
                   [`rfl
                    (Term.fun
                     "fun"
                     (Term.basicFun [(Term.simpleBinder [`i (Term.hole "_")] [])] "=>" (Term.hole "_")))])]))
               [])
              (group
               (Mathlib.Tactic.Conv.convLHS
                "conv_lhs"
                []
                []
                "=>"
                (Tactic.Conv.convSeq
                 (Tactic.Conv.convSeq1Indented
                  [(group
                    (Tactic.Conv.convRw__
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule ["←"] (Term.app `Classical.some_spec [(Term.app `hc' [`i])]))]
                      "]"))
                    [])])))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   ["←"]
                   (Term.app
                    `IsScalarTower.algebra_map_smul
                    [`K (Term.app `Classical.some [(Term.app `hc' [`i])]) (Term.app `db [`i])]))]
                 "]")
                [])
               [])])))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`i] [])]
             "=>"
             (Term.app `db.repr [(Term.app `algebraMap [`C `L `x]) `i])))
           ","
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Term.hole "_")))
           ","
           (Term.proj (Term.app `db.sum_repr [(Term.hole "_")]) "." `symm)]
          "⟩"))
        [])
       (group
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `BilinForm.dual_basis_repr_apply)] "]") [])
        [])
       (group
        (Tactic.exact "exact" (Term.app `is_integral_trace [(Term.app `is_integral_mul [`hx (Term.app `hb_int [`i])])]))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `db
          []
          ":="
          (Term.app
           (Term.proj (Term.app `trace_form [`K `L]) "." `dualBasis)
           [(Term.app `trace_form_nondegenerate [`K `L]) `b]))))
       [])
      (group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
         (Tactic.rintroPat.one
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
           "⟩"))]
        [])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `LinearMap.coe_restrict_scalars_eq_coe)
          ","
          (Tactic.simpLemma [] [] `Algebra.linear_map_apply)]
         "]"]
        [])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hx []]
          [(Term.typeSpec ":" (Term.app `IsIntegral [`A (Term.app `algebraMap [`C `L `x])]))]
          ":="
          (Term.proj (Term.app `IsIntegralClosure.is_integral [`A `L `x]) "." `algebraMap))))
       [])
      (group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         («term∃_,_»
          "∃"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] [":" (Term.arrow `ι "→" `A)]))
          ","
          («term_=_»
           (Term.app `algebraMap [`C `L `x])
           "="
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            ", "
            (Algebra.Group.Defs.«term_•_» (Term.app `c [`i]) " • " (Term.app `db [`i])))))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.obtain
               "obtain"
               [(Tactic.rcasesPatMed
                 [(Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x_eq)]) [])]
                   "⟩")])]
               []
               [":=" [`this]])
              [])
             (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `x_eq)] "]") []) [])
             (group
              (Tactic.refine'
               "refine'"
               (Term.app
                `Submodule.sum_mem
                [(Term.hole "_")
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`i (Term.hole "_")] [])]
                   "=>"
                   (Term.app
                    `Submodule.smul_mem
                    [(Term.hole "_") (Term.hole "_") (Term.app `Submodule.subset_span [(Term.hole "_")])])))]))
              [])
             (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_range)] "]") []) [])
             (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`i "," `rfl] "⟩")) [])])))))
       [])
      (group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         («term∃_,_»
          "∃"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] [":" (Term.arrow `ι "→" `K)]))
          ","
          («term_∧_»
           (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `IsIntegral [`A (Term.app `c [`i])]))
           "∧"
           («term_=_»
            (Term.app `algebraMap [`C `L `x])
            "="
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             ", "
             (Algebra.Group.Defs.«term_•_» (Term.app `c [`i]) " • " (Term.app `db [`i]))))))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.obtain
               "obtain"
               [(Tactic.rcasesPatMed
                 [(Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hc)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                   "⟩")])]
               []
               [":=" [`this]])
              [])
             (group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hc' []]
                 [(Term.typeSpec
                   ":"
                   (Term.forall
                    "∀"
                    [(Term.simpleBinder [`i] [])]
                    ","
                    (Term.app `IsLocalization.IsInteger [`A (Term.app `c [`i])])))]
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`i] [])]
                   "=>"
                   (Term.app `is_integrally_closed.is_integral_iff.mp [(Term.app `hc [`i])]))))))
              [])
             (group
              (Tactic.use
               "use"
               [(Term.fun
                 "fun"
                 (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Term.app `Classical.some [(Term.app `hc' [`i])])))])
              [])
             (group
              (Tactic.refine'
               "refine'"
               (Term.app
                `hx.trans
                [(Term.app
                  `Finset.sum_congr
                  [`rfl
                   (Term.fun
                    "fun"
                    (Term.basicFun [(Term.simpleBinder [`i (Term.hole "_")] [])] "=>" (Term.hole "_")))])]))
              [])
             (group
              (Mathlib.Tactic.Conv.convLHS
               "conv_lhs"
               []
               []
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(group
                   (Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] (Term.app `Classical.some_spec [(Term.app `hc' [`i])]))]
                     "]"))
                   [])])))
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  ["←"]
                  (Term.app
                   `IsScalarTower.algebra_map_smul
                   [`K (Term.app `Classical.some [(Term.app `hc' [`i])]) (Term.app `db [`i])]))]
                "]")
               [])
              [])])))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`i] [])]
            "=>"
            (Term.app `db.repr [(Term.app `algebraMap [`C `L `x]) `i])))
          ","
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Term.hole "_")))
          ","
          (Term.proj (Term.app `db.sum_repr [(Term.hole "_")]) "." `symm)]
         "⟩"))
       [])
      (group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `BilinForm.dual_basis_repr_apply)] "]") [])
       [])
      (group
       (Tactic.exact "exact" (Term.app `is_integral_trace [(Term.app `is_integral_mul [`hx (Term.app `hb_int [`i])])]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `is_integral_trace [(Term.app `is_integral_mul [`hx (Term.app `hb_int [`i])])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `is_integral_trace [(Term.app `is_integral_mul [`hx (Term.app `hb_int [`i])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `is_integral_mul [`hx (Term.app `hb_int [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hb_int [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hb_int
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hb_int [`i]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `is_integral_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `is_integral_mul [`hx (Term.paren "(" [(Term.app `hb_int [`i]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `is_integral_trace
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `BilinForm.dual_basis_repr_apply)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `BilinForm.dual_basis_repr_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [(Term.fun
      "fun"
      (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Term.app `db.repr [(Term.app `algebraMap [`C `L `x]) `i])))
     ","
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Term.hole "_")))
     ","
     (Term.proj (Term.app `db.sum_repr [(Term.hole "_")]) "." `symm)]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Term.app `db.repr [(Term.app `algebraMap [`C `L `x]) `i])))
    ","
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Term.hole "_")))
    ","
    (Term.proj (Term.app `db.sum_repr [(Term.hole "_")]) "." `symm)]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `db.sum_repr [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `db.sum_repr [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `db.sum_repr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `db.sum_repr [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Term.app `db.repr [(Term.app `algebraMap [`C `L `x]) `i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `db.repr [(Term.app `algebraMap [`C `L `x]) `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `algebraMap [`C `L `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `L
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `algebraMap
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `algebraMap [`C `L `x]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `db.repr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticSuffices_
   "suffices"
   (Term.sufficesDecl
    []
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] [":" (Term.arrow `ι "→" `K)]))
     ","
     («term_∧_»
      (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `IsIntegral [`A (Term.app `c [`i])]))
      "∧"
      («term_=_»
       (Term.app `algebraMap [`C `L `x])
       "="
       (Algebra.BigOperators.Basic.«term∑_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        ", "
        (Algebra.Group.Defs.«term_•_» (Term.app `c [`i]) " • " (Term.app `db [`i]))))))
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.obtain
          "obtain"
          [(Tactic.rcasesPatMed
            [(Tactic.rcasesPat.tuple
              "⟨"
              [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
               ","
               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hc)]) [])
               ","
               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
              "⟩")])]
          []
          [":=" [`this]])
         [])
        (group
         (Tactic.tacticHave_
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            [`hc' []]
            [(Term.typeSpec
              ":"
              (Term.forall
               "∀"
               [(Term.simpleBinder [`i] [])]
               ","
               (Term.app `IsLocalization.IsInteger [`A (Term.app `c [`i])])))]
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`i] [])]
              "=>"
              (Term.app `is_integrally_closed.is_integral_iff.mp [(Term.app `hc [`i])]))))))
         [])
        (group
         (Tactic.use
          "use"
          [(Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Term.app `Classical.some [(Term.app `hc' [`i])])))])
         [])
        (group
         (Tactic.refine'
          "refine'"
          (Term.app
           `hx.trans
           [(Term.app
             `Finset.sum_congr
             [`rfl
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i (Term.hole "_")] [])] "=>" (Term.hole "_")))])]))
         [])
        (group
         (Mathlib.Tactic.Conv.convLHS
          "conv_lhs"
          []
          []
          "=>"
          (Tactic.Conv.convSeq
           (Tactic.Conv.convSeq1Indented
            [(group
              (Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] (Term.app `Classical.some_spec [(Term.app `hc' [`i])]))]
                "]"))
              [])])))
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule
             ["←"]
             (Term.app
              `IsScalarTower.algebra_map_smul
              [`K (Term.app `Classical.some [(Term.app `hc' [`i])]) (Term.app `db [`i])]))]
           "]")
          [])
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSuffices_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.sufficesDecl', expected 'Lean.Parser.Term.sufficesDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      ["←"]
      (Term.app
       `IsScalarTower.algebra_map_smul
       [`K (Term.app `Classical.some [(Term.app `hc' [`i])]) (Term.app `db [`i])]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IsScalarTower.algebra_map_smul [`K (Term.app `Classical.some [(Term.app `hc' [`i])]) (Term.app `db [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `db [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `db
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `db [`i]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Classical.some [(Term.app `hc' [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hc' [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hc'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hc' [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Classical.some
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `Classical.some [(Term.paren "(" [(Term.app `hc' [`i]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IsScalarTower.algebra_map_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Conv.convLHS
   "conv_lhs"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.convRw__
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `Classical.some_spec [(Term.app `hc' [`i])]))] "]"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convLHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Classical.some_spec [(Term.app `hc' [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hc' [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hc'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hc' [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Classical.some_spec
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `hx.trans
    [(Term.app
      `Finset.sum_congr
      [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i (Term.hole "_")] [])] "=>" (Term.hole "_")))])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `hx.trans
   [(Term.app
     `Finset.sum_congr
     [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i (Term.hole "_")] [])] "=>" (Term.hole "_")))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Finset.sum_congr
   [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i (Term.hole "_")] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i (Term.hole "_")] [])] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `Finset.sum_congr
   [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i (Term.hole "_")] [])] "=>" (Term.hole "_")))])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hx.trans
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.use
   "use"
   [(Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Term.app `Classical.some [(Term.app `hc' [`i])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.use', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Term.app `Classical.some [(Term.app `hc' [`i])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Classical.some [(Term.app `hc' [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hc' [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hc'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hc' [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Classical.some
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hc' []]
     [(Term.typeSpec
       ":"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`i] [])]
        ","
        (Term.app `IsLocalization.IsInteger [`A (Term.app `c [`i])])))]
     ":="
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`i] [])]
       "=>"
       (Term.app `is_integrally_closed.is_integral_iff.mp [(Term.app `hc [`i])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [])]
    "=>"
    (Term.app `is_integrally_closed.is_integral_iff.mp [(Term.app `hc [`i])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `is_integrally_closed.is_integral_iff.mp [(Term.app `hc [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hc [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hc [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `is_integrally_closed.is_integral_iff.mp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `IsLocalization.IsInteger [`A (Term.app `c [`i])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IsLocalization.IsInteger [`A (Term.app `c [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `c [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `c [`i]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `A
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IsLocalization.IsInteger
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.obtain
   "obtain"
   [(Tactic.rcasesPatMed
     [(Tactic.rcasesPat.tuple
       "⟨"
       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
        ","
        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hc)]) [])
        ","
        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
       "⟩")])]
   []
   [":=" [`this]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.obtain', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatMed', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, [anonymous]))
  («term∃_,_»
   "∃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] [":" (Term.arrow `ι "→" `K)]))
   ","
   («term_∧_»
    (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `IsIntegral [`A (Term.app `c [`i])]))
    "∧"
    («term_=_»
     (Term.app `algebraMap [`C `L `x])
     "="
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      ", "
      (Algebra.Group.Defs.«term_•_» (Term.app `c [`i]) " • " (Term.app `db [`i]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_»
   (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `IsIntegral [`A (Term.app `c [`i])]))
   "∧"
   («term_=_»
    (Term.app `algebraMap [`C `L `x])
    "="
    (Algebra.BigOperators.Basic.«term∑_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     ", "
     (Algebra.Group.Defs.«term_•_» (Term.app `c [`i]) " • " (Term.app `db [`i])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app `algebraMap [`C `L `x])
   "="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    ", "
    (Algebra.Group.Defs.«term_•_» (Term.app `c [`i]) " • " (Term.app `db [`i]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   ", "
   (Algebra.Group.Defs.«term_•_» (Term.app `c [`i]) " • " (Term.app `db [`i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_» (Term.app `c [`i]) " • " (Term.app `db [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `db [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `db
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.app `c [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  IsIntegralClosure.range_le_span_dual_basis
  [ IsSeparable K L ]
      { ι : Type _ }
      [ Fintype ι ]
      [ DecidableEq ι ]
      ( b : Basis ι K L )
      ( hb_int : ∀ i , IsIntegral A b i )
      [ IsIntegrallyClosed A ]
    :
      Algebra.linearMap C L . restrictScalars A . range
        ≤
        Submodule.span A Set.Range $ trace_form K L . dualBasis trace_form_nondegenerate K L b
  :=
    by
      let db := trace_form K L . dualBasis trace_form_nondegenerate K L b
        rintro _ ⟨ x , rfl ⟩
        simp only [ LinearMap.coe_restrict_scalars_eq_coe , Algebra.linear_map_apply ]
        have hx : IsIntegral A algebraMap C L x := IsIntegralClosure.is_integral A L x . algebraMap
        suffices
          ∃ c : ι → A , algebraMap C L x = ∑ i , c i • db i
            by
              obtain ⟨ c , x_eq ⟩ := this
                rw [ x_eq ]
                refine' Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ Submodule.subset_span _
                rw [ Set.mem_range ]
                exact ⟨ i , rfl ⟩
        suffices
          ∃ c : ι → K , ∀ i , IsIntegral A c i ∧ algebraMap C L x = ∑ i , c i • db i
            by
              obtain ⟨ c , hc , hx ⟩ := this
                have hc' : ∀ i , IsLocalization.IsInteger A c i := fun i => is_integrally_closed.is_integral_iff.mp hc i
                use fun i => Classical.some hc' i
                refine' hx.trans Finset.sum_congr rfl fun i _ => _
                conv_lhs => rw [ ← Classical.some_spec hc' i ]
                rw [ ← IsScalarTower.algebra_map_smul K Classical.some hc' i db i ]
        refine' ⟨ fun i => db.repr algebraMap C L x i , fun i => _ , db.sum_repr _ . symm ⟩
        rw [ BilinForm.dual_basis_repr_apply ]
        exact is_integral_trace is_integral_mul hx hb_int i

theorem integral_closure_le_span_dual_basis [IsSeparable K L] {ι : Type _} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
    (hb_int : ∀ i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
    (integralClosure A L).toSubmodule ≤
      Submodule.span A (Set.Range $ (trace_form K L).dualBasis (trace_form_nondegenerate K L) b) :=
  by
  refine' le_transₓ _ (IsIntegralClosure.range_le_span_dual_basis (integralClosure A L) b hb_int)
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

variable (A) (K)

include K

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (y «expr ≠ » (0 : A))
/--  Send a set of `x`'es in a finite extension `L` of the fraction field of `R`
to `(y : R) • x ∈ integral_closure R L`. -/
theorem exists_integral_multiples (s : Finset L) : ∃ (y : _)(_ : y ≠ (0 : A)), ∀, ∀ x ∈ s, ∀, IsIntegral A (y • x) := by
  have := Classical.decEq L
  refine' s.induction _ _
  ·
    use 1, one_ne_zero
    rintro x ⟨⟩
  ·
    rintro x s hx ⟨y, hy, hs⟩
    obtain ⟨x', y', hy', hx'⟩ :=
      exists_integral_multiple ((IsFractionRing.is_algebraic_iff A K).mpr (Algebra.is_algebraic_of_finite x))
        ((algebraMap A L).injective_iff.mp _)
    refine' ⟨y*y', mul_ne_zero hy hy', fun x'' hx'' => _⟩
    rcases finset.mem_insert.mp hx'' with (rfl | hx'')
    ·
      rw [mul_smul, Algebra.smul_def, Algebra.smul_def, mul_commₓ _ x'', hx']
      exact is_integral_mul is_integral_algebra_map x'.2
    ·
      rw [mul_commₓ, mul_smul, Algebra.smul_def]
      exact is_integral_mul is_integral_algebra_map (hs _ hx'')
    ·
      rw [IsScalarTower.algebra_map_eq A K L]
      apply (algebraMap K L).Injective.comp
      exact IsFractionRing.injective _ _

variable (L)

/--  If `L` is a finite extension of `K = Frac(A)`,
then `L` has a basis over `A` consisting of integral elements. -/
theorem FiniteDimensional.exists_is_basis_integral : ∃ (s : Finset L)(b : Basis s K L), ∀ x, IsIntegral A (b x) := by
  let this' := Classical.decEq L
  let this' : IsNoetherian K L := IsNoetherian.iff_fg.2 inferInstance
  let s' := IsNoetherian.finsetBasisIndex K L
  let bs' := IsNoetherian.finsetBasis K L
  obtain ⟨y, hy, his'⟩ := exists_integral_multiples A K (finset.univ.image bs')
  have hy' : algebraMap A L y ≠ 0 := by
    refine' mt ((algebraMap A L).injective_iff.mp _ _) hy
    rw [IsScalarTower.algebra_map_eq A K L]
    exact (algebraMap K L).Injective.comp (IsFractionRing.injective A K)
  refine'
    ⟨s',
      bs'.map
        { Algebra.lmul _ _ (algebraMap A L y) with toFun := fun x => algebraMap A L y*x,
          invFun := fun x => algebraMap A L y⁻¹*x, left_inv := _, right_inv := _ },
      _⟩
  ·
    intro x
    simp only [inv_mul_cancel_left₀ hy']
  ·
    intro x
    simp only [mul_inv_cancel_left₀ hy']
  ·
    rintro ⟨x', hx'⟩
    simp only [Algebra.smul_def, Finset.mem_image, exists_prop, Finset.mem_univ, true_andₓ] at his'
    simp only [Basis.map_apply, LinearEquiv.coe_mk]
    exact his' _ ⟨_, rfl⟩

variable (A K L) [IsSeparable K L]

include L

theorem IsIntegralClosure.is_noetherian_ring [IsIntegrallyClosed A] [IsNoetherianRing A] : IsNoetherianRing C := by
  have := Classical.decEq L
  obtain ⟨s, b, hb_int⟩ := FiniteDimensional.exists_is_basis_integral A K L
  rw [is_noetherian_ring_iff]
  let b' := (trace_form K L).dualBasis (trace_form_nondegenerate K L) b
  let this' := is_noetherian_span_of_finite A (Set.finite_range b')
  let f : C →ₗ[A] Submodule.span A (Set.Range b') :=
    (Submodule.ofLe (IsIntegralClosure.range_le_span_dual_basis C b hb_int)).comp
      ((Algebra.linearMap C L).restrictScalars A).range_restrict
  refine' is_noetherian_of_tower A (is_noetherian_of_ker_bot f _)
  rw [LinearMap.ker_comp, Submodule.ker_of_le, Submodule.comap_bot, LinearMap.ker_cod_restrict]
  exact LinearMap.ker_eq_bot_of_injective (IsIntegralClosure.algebra_map_injective C A L)

variable {A K}

theorem integralClosure.is_noetherian_ring [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherianRing (integralClosure A L) :=
  IsIntegralClosure.is_noetherian_ring A K L (integralClosure A L)

variable (A K) [IsDomain C]

theorem IsIntegralClosure.is_dedekind_domain [h : IsDedekindDomain A] : IsDedekindDomain C := by
  have : IsFractionRing C L := IsIntegralClosure.is_fraction_ring_of_finite_extension A K L C
  exact
    ⟨IsIntegralClosure.is_noetherian_ring A K L C, h.dimension_le_one.is_integral_closure _ L _,
      (is_integrally_closed_iff L).mpr fun x hx =>
        ⟨IsIntegralClosure.mk' C x (is_integral_trans (IsIntegralClosure.is_integral_algebra A L) _ hx),
          IsIntegralClosure.algebra_map_mk' _ _ _⟩⟩

theorem integralClosure.is_dedekind_domain [h : IsDedekindDomain A] : IsDedekindDomain (integralClosure A L) :=
  IsIntegralClosure.is_dedekind_domain A K L (integralClosure A L)

omit K

variable [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]

variable [FiniteDimensional (FractionRing A) L] [IsSeparable (FractionRing A) L]

instance integralClosure.is_dedekind_domain_fraction_ring [IsDedekindDomain A] :
    IsDedekindDomain (integralClosure A L) :=
  integralClosure.is_dedekind_domain A (FractionRing A) L

end IsIntegralClosure

section IsDedekindDomain

variable {T : Type _} [CommRingₓ T] [IsDomain T] [IsDedekindDomain T] (I J : Ideal T)

open_locale Classical

open Multiset UniqueFactorizationMonoid Ideal

theorem prod_normalized_factors_eq_self {I : Ideal T} (hI : I ≠ ⊥) : (normalized_factors I).Prod = I :=
  associated_iff_eq.1 (normalized_factors_prod hI)

theorem normalized_factors_prod {α : Multiset (Ideal T)} (h : ∀, ∀ p ∈ α, ∀, Prime p) : normalized_factors α.prod = α :=
  by
  simp_rw [← Multiset.rel_eq, ← associated_eq_eq]
  exact prime_factors_unique prime_of_normalized_factor h (normalized_factors_prod (α.prod_ne_zero_of_prime h))

theorem count_le_of_ideal_ge {I J : Ideal T} (h : I ≤ J) (hI : I ≠ ⊥) (K : Ideal T) :
    count K (normalized_factors J) ≤ count K (normalized_factors I) :=
  le_iff_count.1 ((dvd_iff_normalized_factors_le_normalized_factors (ne_bot_of_le_ne_bot hI h) hI).1 (dvd_iff_le.2 h)) _

theorem sup_eq_prod_inf_factors (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : I⊔J = (normalized_factors I ∩ normalized_factors J).Prod :=
  by
  have H :
    normalized_factors (normalized_factors I ∩ normalized_factors J).Prod =
      normalized_factors I ∩ normalized_factors J :=
    by
    apply _root_.normalized_factors_prod
    intro p hp
    rw [mem_inter] at hp
    exact prime_of_normalized_factor p hp.left
  have :=
    Multiset.prod_ne_zero_of_prime (normalized_factors I ∩ normalized_factors J) fun _ h =>
      prime_of_normalized_factor _ (Multiset.mem_inter.1 h).1
  apply le_antisymmₓ
  ·
    rw [sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
    constructor
    ·
      rw [dvd_iff_normalized_factors_le_normalized_factors this hI, H]
      exact inf_le_left
    ·
      rw [dvd_iff_normalized_factors_le_normalized_factors this hJ, H]
      exact inf_le_right
  ·
    rw [← dvd_iff_le, dvd_iff_normalized_factors_le_normalized_factors, _root_.normalized_factors_prod, le_iff_count]
    ·
      intro a
      rw [Multiset.count_inter]
      exact le_minₓ (count_le_of_ideal_ge le_sup_left hI a) (count_le_of_ideal_ge le_sup_right hJ a)
    ·
      intro p hp
      rw [mem_inter] at hp
      exact prime_of_normalized_factor p hp.left
    ·
      exact ne_bot_of_le_ne_bot hI le_sup_left
    ·
      exact this

end IsDedekindDomain

