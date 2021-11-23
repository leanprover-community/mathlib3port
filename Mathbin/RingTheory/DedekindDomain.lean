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


variable(R A K : Type _)[CommRingₓ R][CommRingₓ A][Field K]

open_locale nonZeroDivisors

/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
def Ringₓ.DimensionLeOne : Prop :=
  ∀ p _ : p ≠ (⊥ : Ideal R), p.is_prime → p.is_maximal

open Ideal Ringₓ

namespace Ringₓ

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dimension_le_one.principal_ideal_ring [is_domain A] [is_principal_ideal_ring A] : dimension_le_one A :=
λ p nonzero prime, by { haveI [] [] [":=", expr prime],
  exact [expr is_prime.to_maximal_ideal nonzero] }

theorem dimension_le_one.is_integral_closure (B : Type _) [CommRingₓ B] [IsDomain B] [Nontrivial R] [Algebra R A]
  [Algebra R B] [Algebra B A] [IsScalarTower R B A] [IsIntegralClosure B R A] (h : dimension_le_one R) :
  dimension_le_one B :=
  fun p ne_bot prime =>
    by 
      exact
        is_integral_closure.is_maximal_of_is_maximal_comap A p
          (h _ (is_integral_closure.comap_ne_bot A ne_bot) inferInstance)

theorem dimension_le_one.integral_closure [Nontrivial R] [IsDomain A] [Algebra R A] (h : dimension_le_one R) :
  dimension_le_one (integralClosure R A) :=
  h.is_integral_closure R A (integralClosure R A)

end Ringₓ

variable[IsDomain A]

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

/-- An integral domain is a Dedekind domain iff and only if it is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
theorem is_dedekind_domain_iff (K : Type _) [Field K] [Algebra A K] [IsFractionRing A K] :
  IsDedekindDomain A ↔
    IsNoetherianRing A ∧ dimension_le_one A ∧ ∀ {x : K}, IsIntegral A x → ∃ y, algebraMap A K y = x :=
  ⟨fun ⟨hr, hd, hi⟩ => ⟨hr, hd, fun x => (is_integrally_closed_iff K).mp hi⟩,
    fun ⟨hr, hd, hi⟩ => ⟨hr, hd, (is_integrally_closed_iff K).mpr @hi⟩⟩

instance (priority := 100)IsPrincipalIdealRing.is_dedekind_domain [IsPrincipalIdealRing A] : IsDedekindDomain A :=
  ⟨PrincipalIdealRing.is_noetherian_ring, Ringₓ.DimensionLeOne.principal_ideal_ring A,
    UniqueFactorizationMonoid.is_integrally_closed⟩

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

variable{R₁ : Type _}[CommRingₓ R₁][IsDomain R₁][Algebra R₁ K][IsFractionRing R₁ K]

variable{I J : FractionalIdeal R₁⁰ K}

noncomputable instance  : HasInv (FractionalIdeal R₁⁰ K) :=
  ⟨fun I => 1 / I⟩

theorem inv_eq : I⁻¹ = 1 / I :=
  rfl

theorem inv_zero' : (0 : FractionalIdeal R₁⁰ K)⁻¹ = 0 :=
  FractionalIdeal.div_zero

theorem inv_nonzero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
  J⁻¹ = ⟨(1 : FractionalIdeal R₁⁰ K) / J, FractionalIdeal.fractional_div_of_nonzero h⟩ :=
  FractionalIdeal.div_nonzero _

theorem coe_inv_of_nonzero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
  («expr↑ » (J⁻¹) : Submodule R₁ K) = IsLocalization.coeSubmodule K ⊤ / J :=
  by 
    rwa [inv_nonzero _]
    rfl 
    assumption

variable{K}

theorem mem_inv_iff (hI : I ≠ 0) {x : K} : x ∈ I⁻¹ ↔ ∀ y _ : y ∈ I, (x*y) ∈ (1 : FractionalIdeal R₁⁰ K) :=
  FractionalIdeal.mem_div_iff_of_nonzero hI

theorem inv_anti_mono (hI : I ≠ 0) (hJ : J ≠ 0) (hIJ : I ≤ J) : J⁻¹ ≤ I⁻¹ :=
  fun x =>
    by 
      simp only [mem_inv_iff hI, mem_inv_iff hJ]
      exact fun h y hy => h y (hIJ hy)

theorem le_self_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I ≤ (1 : FractionalIdeal R₁⁰ K)) : I ≤ I*I⁻¹ :=
  FractionalIdeal.le_self_mul_one_div hI

variable(K)

theorem coe_ideal_le_self_mul_inv (I : Ideal R₁) : (I : FractionalIdeal R₁⁰ K) ≤ I*I⁻¹ :=
  le_self_mul_inv FractionalIdeal.coe_ideal_le_one

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq
(I J : fractional_ideal «expr ⁰»(R₁) K)
(h : «expr = »(«expr * »(I, J), 1)) : «expr = »(J, «expr ⁻¹»(I)) :=
begin
  have [ident hI] [":", expr «expr ≠ »(I, 0)] [":=", expr fractional_ideal.ne_zero_of_mul_eq_one I J h],
  suffices [ident h'] [":", expr «expr = »(«expr * »(I, «expr / »(1, I)), 1)],
  { exact [expr «expr $ »(congr_arg units.inv, @units.ext _ _ (units.mk_of_mul_eq_one _ _ h) (units.mk_of_mul_eq_one _ _ h') rfl)] },
  apply [expr le_antisymm],
  { apply [expr fractional_ideal.mul_le.mpr _],
    intros [ident x, ident hx, ident y, ident hy],
    rw [expr mul_comm] [],
    exact [expr (fractional_ideal.mem_div_iff_of_nonzero hI).mp hy x hx] },
  rw ["<-", expr h] [],
  apply [expr fractional_ideal.mul_left_mono I],
  apply [expr (fractional_ideal.le_div_iff_of_nonzero hI).mpr _],
  intros [ident y, ident hy, ident x, ident hx],
  rw [expr mul_comm] [],
  exact [expr fractional_ideal.mul_mem_mul hx hy]
end

theorem mul_inv_cancel_iff {I : FractionalIdeal R₁⁰ K} : (I*I⁻¹) = 1 ↔ ∃ J, (I*J) = 1 :=
  ⟨fun h => ⟨I⁻¹, h⟩,
    fun ⟨J, hJ⟩ =>
      by 
        rwa [←right_inverse_eq K I J hJ]⟩

theorem mul_inv_cancel_iff_is_unit {I : FractionalIdeal R₁⁰ K} : (I*I⁻¹) = 1 ↔ IsUnit I :=
  (mul_inv_cancel_iff K).trans is_unit_iff_exists_inv.symm

variable{K' : Type _}[Field K'][Algebra R₁ K'][IsFractionRing R₁ K']

@[simp]
theorem map_inv (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') : I⁻¹.map (h : K →ₐ[R₁] K') = I.map h⁻¹ :=
  by 
    rw [inv_eq, FractionalIdeal.map_div, FractionalIdeal.map_one, inv_eq]

open Submodule Submodule.IsPrincipal

@[simp]
theorem span_singleton_inv (x : K) : FractionalIdeal.spanSingleton R₁⁰ x⁻¹ = FractionalIdeal.spanSingleton _ (x⁻¹) :=
  FractionalIdeal.one_div_span_singleton x

theorem mul_generator_self_inv {R₁ : Type _} [CommRingₓ R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K]
  (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
  (I*FractionalIdeal.spanSingleton _ (generator (I : Submodule R₁ K)⁻¹)) = 1 :=
  by 
    convLHS => congr rw [FractionalIdeal.eq_span_singleton_of_principal I]
    rw [FractionalIdeal.span_singleton_mul_span_singleton, mul_inv_cancel, FractionalIdeal.span_singleton_one]
    intro generator_I_eq_zero 
    apply h 
    rw [FractionalIdeal.eq_span_singleton_of_principal I, generator_I_eq_zero, FractionalIdeal.span_singleton_zero]

theorem invertible_of_principal (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
  (I*I⁻¹) = 1 :=
  FractionalIdeal.mul_div_self_cancel_iff.mpr
    ⟨FractionalIdeal.spanSingleton _ (generator (I : Submodule R₁ K)⁻¹), mul_generator_self_inv _ I h⟩

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem invertible_iff_generator_nonzero
(I : fractional_ideal «expr ⁰»(R₁) K)
[submodule.is_principal (I : submodule R₁ K)] : «expr ↔ »(«expr = »(«expr * »(I, «expr ⁻¹»(I)), 1), «expr ≠ »(generator (I : submodule R₁ K), 0)) :=
begin
  split,
  { intros [ident hI, ident hg],
    apply [expr fractional_ideal.ne_zero_of_mul_eq_one _ _ hI],
    rw ["[", expr fractional_ideal.eq_span_singleton_of_principal I, ",", expr hg, ",", expr fractional_ideal.span_singleton_zero, "]"] [] },
  { intro [ident hg],
    apply [expr invertible_of_principal],
    rw ["[", expr fractional_ideal.eq_span_singleton_of_principal I, "]"] [],
    intro [ident hI],
    have [] [] [":=", expr fractional_ideal.mem_span_singleton_self _ (generator (I : submodule R₁ K))],
    rw ["[", expr hI, ",", expr fractional_ideal.mem_zero_iff, "]"] ["at", ident this],
    contradiction }
end

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_principal_inv
(I : fractional_ideal «expr ⁰»(R₁) K)
[submodule.is_principal (I : submodule R₁ K)]
(h : «expr ≠ »(I, 0)) : submodule.is_principal «expr ⁻¹»(I).1 :=
begin
  rw ["[", expr fractional_ideal.val_eq_coe, ",", expr fractional_ideal.is_principal_iff, "]"] [],
  use [expr «expr ⁻¹»(generator (I : submodule R₁ K))],
  have [ident hI] [":", expr «expr = »(«expr * »(I, fractional_ideal.span_singleton _ «expr ⁻¹»(generator (I : submodule R₁ K))), 1)] [],
  apply [expr mul_generator_self_inv _ I h],
  exact [expr (right_inverse_eq _ I (fractional_ideal.span_singleton _ «expr ⁻¹»(generator (I : submodule R₁ K))) hI).symm]
end

@[simp]
theorem FractionalIdeal.one_inv : (1⁻¹ : FractionalIdeal R₁⁰ K) = 1 :=
  FractionalIdeal.div_one

/--
A Dedekind domain is an integral domain such that every fractional ideal has an inverse.

This is equivalent to `is_dedekind_domain`.
In particular we provide a `fractional_ideal.comm_group_with_zero` instance,
assuming `is_dedekind_domain A`, which implies `is_dedekind_domain_inv`. For **integral** ideals,
`is_dedekind_domain`(`_inv`) implies only `ideal.comm_cancel_monoid_with_zero`.
-/
def IsDedekindDomainInv : Prop :=
  ∀ I _ : I ≠ (⊥ : FractionalIdeal A⁰ (FractionRing A)), (I*I⁻¹) = 1

open FractionalIdeal

variable{R A K}

theorem is_dedekind_domain_inv_iff [Algebra A K] [IsFractionRing A K] :
  IsDedekindDomainInv A ↔ ∀ I _ : I ≠ (⊥ : FractionalIdeal A⁰ K), (I*I⁻¹) = 1 :=
  by 
    set h := FractionRing.algEquiv A K 
    split  <;> rintro hi I hI
    ·
      refine' FractionalIdeal.map_injective h.symm.to_alg_hom h.symm.injective _ 
      rw [AlgEquiv.to_alg_hom_eq_coe, inv_eq, FractionalIdeal.map_mul, FractionalIdeal.map_one_div,
        FractionalIdeal.map_one, ←inv_eq, hi]
      exact FractionalIdeal.map_ne_zero _ hI
    ·
      refine' FractionalIdeal.map_injective h.to_alg_hom h.injective _ 
      rw [AlgEquiv.to_alg_hom_eq_coe, inv_eq, FractionalIdeal.map_mul, FractionalIdeal.map_one_div,
        FractionalIdeal.map_one, ←inv_eq, hi]
      exact FractionalIdeal.map_ne_zero _ hI

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fractional_ideal.adjoin_integral_eq_one_of_is_unit
[algebra A K]
[is_fraction_ring A K]
(x : K)
(hx : is_integral A x)
(hI : is_unit (adjoin_integral «expr ⁰»(A) x hx)) : «expr = »(adjoin_integral «expr ⁰»(A) x hx, 1) :=
begin
  set [] [ident I] [] [":="] [expr adjoin_integral «expr ⁰»(A) x hx] [],
  have [ident mul_self] [":", expr «expr = »(«expr * »(I, I), I)] [],
  { apply [expr fractional_ideal.coe_to_submodule_injective],
    simp [] [] [] [] [] [] },
  convert [] [expr congr_arg ((«expr * » «expr ⁻¹»(I))) mul_self] []; simp [] [] ["only"] ["[", expr (mul_inv_cancel_iff_is_unit K).mpr hI, ",", expr mul_assoc, ",", expr mul_one, "]"] [] []
end

namespace IsDedekindDomainInv

variable[Algebra A K][IsFractionRing A K](h : IsDedekindDomainInv A)

include h

theorem mul_inv_eq_one {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : (I*I⁻¹) = 1 :=
  is_dedekind_domain_inv_iff.mp h I hI

theorem inv_mul_eq_one {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : (I⁻¹*I) = 1 :=
  (mul_commₓ _ _).trans (h.mul_inv_eq_one hI)

protected theorem IsUnit {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) : IsUnit I :=
  is_unit_of_mul_eq_one _ _ (h.mul_inv_eq_one hI)

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_noetherian_ring : is_noetherian_ring A :=
begin
  refine [expr is_noetherian_ring_iff.mpr ⟨λ I : ideal A, _⟩],
  by_cases [expr hI, ":", expr «expr = »(I, «expr⊥»())],
  { rw [expr hI] [],
    apply [expr submodule.fg_bot] },
  have [ident hI] [":", expr «expr ≠ »((I : fractional_ideal «expr ⁰»(A) (fraction_ring A)), 0)] [":=", expr (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr hI],
  exact [expr I.fg_of_is_unit (is_fraction_ring.injective A (fraction_ring A)) (h.is_unit hI)]
end

theorem integrally_closed : IsIntegrallyClosed A :=
  by 
    refine' ⟨fun x hx => _⟩
    rw [←Set.mem_range, ←Algebra.mem_bot, ←Subalgebra.mem_to_submodule, Algebra.to_submodule_bot,
      ←coe_span_singleton A⁰ (1 : FractionRing A), FractionalIdeal.span_singleton_one,
      ←FractionalIdeal.adjoin_integral_eq_one_of_is_unit x hx (h.is_unit _)]
    ·
      exact mem_adjoin_integral_self A⁰ x hx
    ·
      exact fun h => one_ne_zero (eq_zero_iff.mp h 1 (Subalgebra.one_mem _))

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dimension_le_one : dimension_le_one A :=
begin
  rintros [ident P, ident P_ne, ident hP],
  refine [expr ideal.is_maximal_def.mpr ⟨hP.ne_top, λ M hM, _⟩],
  have [ident P'_ne] [":", expr «expr ≠ »((P : fractional_ideal «expr ⁰»(A) (fraction_ring A)), 0)] [":=", expr (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr P_ne],
  have [ident M'_ne] [":", expr «expr ≠ »((M : fractional_ideal «expr ⁰»(A) (fraction_ring A)), 0)] [":=", expr (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr (lt_of_le_of_lt bot_le hM).ne'],
  suffices [] [":", expr «expr ≤ »((«expr * »(«expr ⁻¹»(M), P) : fractional_ideal «expr ⁰»(A) (fraction_ring A)), P)],
  { rw ["[", expr eq_top_iff, ",", "<-", expr coe_ideal_le_coe_ideal (fraction_ring A), ",", expr fractional_ideal.coe_ideal_top, "]"] [],
    calc
      «expr = »((1 : fractional_ideal «expr ⁰»(A) (fraction_ring A)), «expr * »(«expr * »(_, _), _)) : _
      «expr ≤ »(..., «expr * »(_, _)) : mul_right_mono («expr * »(«expr ⁻¹»(P), M) : fractional_ideal «expr ⁰»(A) (fraction_ring A)) this
      «expr = »(..., M) : _,
    { rw ["[", expr mul_assoc, ",", "<-", expr mul_assoc «expr↑ »(P), ",", expr h.mul_inv_eq_one P'_ne, ",", expr one_mul, ",", expr h.inv_mul_eq_one M'_ne, "]"] [] },
    { rw ["[", "<-", expr mul_assoc «expr↑ »(P), ",", expr h.mul_inv_eq_one P'_ne, ",", expr one_mul, "]"] [] },
    { apply_instance } },
  intros [ident x, ident hx],
  have [ident le_one] [":", expr «expr ≤ »((«expr * »(«expr ⁻¹»(M), P) : fractional_ideal «expr ⁰»(A) (fraction_ring A)), 1)] [],
  { rw ["[", "<-", expr h.inv_mul_eq_one M'_ne, "]"] [],
    exact [expr fractional_ideal.mul_left_mono _ ((coe_ideal_le_coe_ideal (fraction_ring A)).mpr hM.le)] },
  obtain ["⟨", ident y, ",", ident hy, ",", ident rfl, "⟩", ":=", expr (mem_coe_ideal _).mp (le_one hx)],
  obtain ["⟨", ident z, ",", ident hzM, ",", ident hzp, "⟩", ":=", expr set_like.exists_of_lt hM],
  have [ident zy_mem] [] [":=", expr fractional_ideal.mul_mem_mul (mem_coe_ideal_of_mem «expr ⁰»(A) hzM) hx],
  rw ["[", "<-", expr ring_hom.map_mul, ",", "<-", expr mul_assoc, ",", expr h.mul_inv_eq_one M'_ne, ",", expr one_mul, "]"] ["at", ident zy_mem],
  obtain ["⟨", ident zy, ",", ident hzy, ",", ident zy_eq, "⟩", ":=", expr (mem_coe_ideal «expr ⁰»(A)).mp zy_mem],
  rw [expr is_fraction_ring.injective A (fraction_ring A) zy_eq] ["at", ident hzy],
  exact [expr mem_coe_ideal_of_mem «expr ⁰»(A) (or.resolve_left (hP.mem_or_mem hzy) hzp)]
end

/-- Showing one side of the equivalence between the definitions
`is_dedekind_domain_inv` and `is_dedekind_domain` of Dedekind domains. -/
theorem IsDedekindDomain : IsDedekindDomain A :=
  ⟨h.is_noetherian_ring, h.dimension_le_one, h.integrally_closed⟩

end IsDedekindDomainInv

variable[Algebra A K][IsFractionRing A K]

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Specialization of `exists_prime_spectrum_prod_le_and_ne_bot_of_domain` to Dedekind domains:
Let `I : ideal A` be a nonzero ideal, where `A` is a Dedekind domain that is not a field.
Then `exists_prime_spectrum_prod_le_and_ne_bot_of_domain` states we can find a product of prime
ideals that is contained within `I`. This lemma extends that result by making the product minimal:
let `M` be a maximal ideal that contains `I`, then the product including `M` is contained within `I`
and the product excluding `M` is not contained within `I`. -/
theorem exists_multiset_prod_cons_le_and_prod_not_le
[is_dedekind_domain A]
(hNF : «expr¬ »(is_field A))
{I M : ideal A}
(hI0 : «expr ≠ »(I, «expr⊥»()))
(hIM : «expr ≤ »(I, M))
[hM : M.is_maximal] : «expr∃ , »((Z : multiset (prime_spectrum A)), «expr ∧ »(«expr ≤ »(«expr ::ₘ »(M, Z.map prime_spectrum.as_ideal).prod, I), «expr¬ »(«expr ≤ »(multiset.prod (Z.map prime_spectrum.as_ideal), I)))) :=
begin
  obtain ["⟨", ident Z₀, ",", ident hZ₀, "⟩", ":=", expr prime_spectrum.exists_prime_spectrum_prod_le_and_ne_bot_of_domain hNF hI0],
  obtain ["⟨", ident Z, ",", "⟨", ident hZI, ",", ident hprodZ, "⟩", ",", ident h_eraseZ, "⟩", ":=", expr multiset.well_founded_lt.has_min (λ
    Z, «expr ∧ »(«expr ≤ »((Z.map prime_spectrum.as_ideal).prod, I), «expr ≠ »((Z.map prime_spectrum.as_ideal).prod, «expr⊥»()))) ⟨Z₀, hZ₀⟩],
  have [ident hZM] [":", expr «expr ≤ »(multiset.prod (Z.map prime_spectrum.as_ideal), M)] [":=", expr le_trans hZI hIM],
  have [ident hZ0] [":", expr «expr ≠ »(Z, 0)] [],
  { rintro [ident rfl],
    simpa [] [] [] ["[", expr hM.ne_top, "]"] [] ["using", expr hZM] },
  obtain ["⟨", "_", ",", ident hPZ', ",", ident hPM, "⟩", ":=", expr (hM.is_prime.multiset_prod_le (mt multiset.map_eq_zero.mp hZ0)).mp hZM],
  obtain ["⟨", ident P, ",", ident hPZ, ",", ident rfl, "⟩", ":=", expr multiset.mem_map.mp hPZ'],
  letI [] [] [":=", expr classical.dec_eq (ideal A)],
  have [] [] [":=", expr multiset.map_erase prime_spectrum.as_ideal subtype.coe_injective P Z],
  obtain ["⟨", ident hP0, ",", ident hZP0, "⟩", ":", expr «expr ∧ »(«expr ≠ »(P.as_ideal, «expr⊥»()), «expr ≠ »(((Z.erase P).map prime_spectrum.as_ideal).prod, «expr⊥»()))],
  { rwa ["[", expr ne.def, ",", "<-", expr multiset.cons_erase hPZ', ",", expr multiset.prod_cons, ",", expr ideal.mul_eq_bot, ",", expr not_or_distrib, ",", "<-", expr this, "]"] ["at", ident hprodZ] },
  have [ident hPM'] [] [":=", expr (is_dedekind_domain.dimension_le_one _ hP0 P.is_prime).eq_of_le hM.ne_top hPM],
  tactic.unfreeze_local_instances,
  subst [expr hPM'],
  refine [expr ⟨Z.erase P, _, _⟩],
  { convert [] [expr hZI] [],
    rw ["[", expr this, ",", expr multiset.cons_erase hPZ', "]"] [] },
  { refine [expr λ h, h_eraseZ (Z.erase P) ⟨h, _⟩ (multiset.erase_lt.mpr hPZ)],
    exact [expr hZP0] }
end

namespace FractionalIdeal

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_not_mem_one_of_ne_bot
[is_dedekind_domain A]
(hNF : «expr¬ »(is_field A))
{I : ideal A}
(hI0 : «expr ≠ »(I, «expr⊥»()))
(hI1 : «expr ≠ »(I, «expr⊤»())) : «expr∃ , »((x : K), «expr ∧ »(«expr ∈ »(x, («expr ⁻¹»(I) : fractional_ideal «expr ⁰»(A) K)), «expr ∉ »(x, (1 : fractional_ideal «expr ⁰»(A) K)))) :=
begin
  suffices [] [":", expr ∀
   {M : ideal A}
   (hM : M.is_maximal), «expr∃ , »((x : K), «expr ∧ »(«expr ∈ »(x, («expr ⁻¹»(M) : fractional_ideal «expr ⁰»(A) K)), «expr ∉ »(x, (1 : fractional_ideal «expr ⁰»(A) K))))],
  { obtain ["⟨", ident M, ",", ident hM, ",", ident hIM, "⟩", ":", expr «expr∃ , »((M : ideal A), «expr ∧ »(is_maximal M, «expr ≤ »(I, M))), ":=", expr ideal.exists_le_maximal I hI1],
    resetI,
    have [ident hM0] [] [":=", expr (M.bot_lt_of_maximal hNF).ne'],
    obtain ["⟨", ident x, ",", ident hxM, ",", ident hx1, "⟩", ":=", expr this hM],
    refine [expr ⟨x, inv_anti_mono _ _ ((coe_ideal_le_coe_ideal _).mpr hIM) hxM, hx1⟩]; apply [expr fractional_ideal.coe_ideal_ne_zero]; assumption },
  intros [ident M, ident hM],
  resetI,
  obtain ["⟨", "⟨", ident a, ",", ident haM, "⟩", ",", ident ha0, "⟩", ":=", expr submodule.nonzero_mem_of_bot_lt (M.bot_lt_of_maximal hNF)],
  replace [ident ha0] [":", expr «expr ≠ »(a, 0)] [":=", expr subtype.coe_injective.ne ha0],
  let [ident J] [":", expr ideal A] [":=", expr ideal.span {a}],
  have [ident hJ0] [":", expr «expr ≠ »(J, «expr⊥»())] [":=", expr mt ideal.span_singleton_eq_bot.mp ha0],
  have [ident hJM] [":", expr «expr ≤ »(J, M)] [":=", expr ideal.span_le.mpr (set.singleton_subset_iff.mpr haM)],
  have [ident hM0] [":", expr «expr < »(«expr⊥»(), M)] [":=", expr M.bot_lt_of_maximal hNF],
  obtain ["⟨", ident Z, ",", ident hle, ",", ident hnle, "⟩", ":=", expr exists_multiset_prod_cons_le_and_prod_not_le hNF hJ0 hJM],
  obtain ["⟨", ident b, ",", ident hbZ, ",", ident hbJ, "⟩", ":=", expr set_like.not_le_iff_exists.mp hnle],
  have [ident hnz_fa] [":", expr «expr ≠ »(algebra_map A K a, 0)] [":=", expr mt ((ring_hom.injective_iff _).mp (is_fraction_ring.injective A K) a) ha0],
  have [ident hb0] [":", expr «expr ≠ »(algebra_map A K b, 0)] [":=", expr mt ((ring_hom.injective_iff _).mp (is_fraction_ring.injective A K) b) (λ
    h, «expr $ »(hbJ, «expr ▸ »(h.symm, J.zero_mem)))],
  refine [expr ⟨«expr * »(algebra_map A K b, «expr ⁻¹»(algebra_map A K a)), (mem_inv_iff _).mpr _, _⟩],
  { exact [expr (fractional_ideal.coe_to_fractional_ideal_ne_zero (le_refl _)).mpr hM0.ne'] },
  { rintro [ident y₀, ident hy₀],
    obtain ["⟨", ident y, ",", ident h_Iy, ",", ident rfl, "⟩", ":=", expr (fractional_ideal.mem_coe_ideal _).mp hy₀],
    rw ["[", expr mul_comm, ",", "<-", expr mul_assoc, ",", "<-", expr ring_hom.map_mul, "]"] [],
    have [ident h_yb] [":", expr «expr ∈ »(«expr * »(y, b), J)] [],
    { apply [expr hle],
      rw [expr multiset.prod_cons] [],
      exact [expr submodule.smul_mem_smul h_Iy hbZ] },
    rw [expr ideal.mem_span_singleton'] ["at", ident h_yb],
    rcases [expr h_yb, "with", "⟨", ident c, ",", ident hc, "⟩"],
    rw ["[", "<-", expr hc, ",", expr ring_hom.map_mul, ",", expr mul_assoc, ",", expr mul_inv_cancel hnz_fa, ",", expr mul_one, "]"] [],
    apply [expr fractional_ideal.coe_mem_one] },
  { refine [expr mt (fractional_ideal.mem_one_iff _).mp _],
    rintros ["⟨", ident x', ",", ident h₂_abs, "⟩"],
    rw ["[", "<-", expr div_eq_mul_inv, ",", expr eq_div_iff_mul_eq hnz_fa, ",", "<-", expr ring_hom.map_mul, "]"] ["at", ident h₂_abs],
    have [] [] [":=", expr ideal.mem_span_singleton'.mpr ⟨x', is_fraction_ring.injective A K h₂_abs⟩],
    contradiction }
end

theorem one_mem_inv_coe_ideal {I : Ideal A} (hI : I ≠ ⊥) : (1 : K) ∈ (I : FractionalIdeal A⁰ K)⁻¹ :=
  by 
    rw [mem_inv_iff (FractionalIdeal.coe_ideal_ne_zero hI)]
    intro y hy 
    rw [one_mulₓ]
    exact coe_ideal_le_one hy 
    assumption

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_inv_cancel_of_le_one
[h : is_dedekind_domain A]
{I : ideal A}
(hI0 : «expr ≠ »(I, «expr⊥»()))
(hI : «expr ≤ »((«expr ⁻¹»(«expr * »(I, «expr ⁻¹»(I))) : fractional_ideal «expr ⁰»(A) K), 1)) : «expr = »((«expr * »(I, «expr ⁻¹»(I)) : fractional_ideal «expr ⁰»(A) K), 1) :=
begin
  by_cases [expr hI1, ":", expr «expr = »(I, «expr⊤»())],
  { rw ["[", expr hI1, ",", expr coe_ideal_top, ",", expr one_mul, ",", expr fractional_ideal.one_inv, "]"] [] },
  by_cases [expr hNF, ":", expr is_field A],
  { letI [] [] [":=", expr hNF.to_field A],
    rcases [expr hI1 (I.eq_bot_or_top.resolve_left hI0)] },
  obtain ["⟨", ident J, ",", ident hJ, "⟩", ":", expr «expr∃ , »((J : ideal A), «expr = »((J : fractional_ideal «expr ⁰»(A) K), «expr * »(I, «expr ⁻¹»(I)))), ":=", expr le_one_iff_exists_coe_ideal.mp mul_one_div_le_one],
  by_cases [expr hJ0, ":", expr «expr = »(J, «expr⊥»())],
  { subst [expr hJ0],
    refine [expr absurd _ hI0],
    rw ["[", expr eq_bot_iff, ",", "<-", expr coe_ideal_le_coe_ideal K, ",", expr hJ, "]"] [],
    exact [expr coe_ideal_le_self_mul_inv K I],
    apply_instance },
  by_cases [expr hJ1, ":", expr «expr = »(J, «expr⊤»())],
  { rw ["[", "<-", expr hJ, ",", expr hJ1, ",", expr coe_ideal_top, "]"] [] },
  obtain ["⟨", ident x, ",", ident hx, ",", ident hx1, "⟩", ":", expr «expr∃ , »((x : K), «expr ∧ »(«expr ∈ »(x, «expr ⁻¹»((J : fractional_ideal «expr ⁰»(A) K))), «expr ∉ »(x, (1 : fractional_ideal «expr ⁰»(A) K)))), ":=", expr exists_not_mem_one_of_ne_bot hNF hJ0 hJ1],
  contrapose ["!"] [ident hx1, "with", ident h_abs],
  rw [expr hJ] ["at", ident hx],
  exact [expr hI hx]
end

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Nonzero integral ideals in a Dedekind domain are invertible.

We will use this to show that nonzero fractional ideals are invertible,
and finally conclude that fractional ideals in a Dedekind domain form a group with zero.
-/
theorem coe_ideal_mul_inv
[h : is_dedekind_domain A]
(I : ideal A)
(hI0 : «expr ≠ »(I, «expr⊥»())) : «expr = »((«expr * »(I, «expr ⁻¹»(I)) : fractional_ideal «expr ⁰»(A) K), 1) :=
begin
  apply [expr mul_inv_cancel_of_le_one hI0],
  by_cases [expr hJ0, ":", expr «expr = »((«expr * »(I, «expr ⁻¹»(I)) : fractional_ideal «expr ⁰»(A) K), 0)],
  { rw ["[", expr hJ0, ",", expr inv_zero', "]"] [],
    exact [expr fractional_ideal.zero_le _] },
  intros [ident x, ident hx],
  suffices [] [":", expr «expr ∈ »(x, integral_closure A K)],
  { rwa ["[", expr is_integrally_closed.integral_closure_eq_bot, ",", expr algebra.mem_bot, ",", expr set.mem_range, ",", "<-", expr fractional_ideal.mem_one_iff, "]"] ["at", ident this]; assumption },
  rw [expr mem_integral_closure_iff_mem_fg] [],
  have [ident x_mul_mem] [":", expr ∀
   b «expr ∈ » («expr ⁻¹»(I) : fractional_ideal «expr ⁰»(A) K), «expr ∈ »(«expr * »(x, b), («expr ⁻¹»(I) : fractional_ideal «expr ⁰»(A) K))] [],
  { intros [ident b, ident hb],
    rw [expr mem_inv_iff] ["at", "⊢", ident hx],
    swap,
    { exact [expr fractional_ideal.coe_ideal_ne_zero hI0] },
    swap,
    { exact [expr hJ0] },
    simp [] [] ["only"] ["[", expr mul_assoc, ",", expr mul_comm b, "]"] [] ["at", "⊢", ident hx],
    intros [ident y, ident hy],
    exact [expr hx _ (fractional_ideal.mul_mem_mul hy hb)] },
  refine [expr ⟨alg_hom.range (polynomial.aeval x : «expr →ₐ[ ] »(polynomial A, A, K)), is_noetherian_submodule.mp (fractional_ideal.is_noetherian «expr ⁻¹»(I)) _ (λ
     y hy, _), ⟨polynomial.X, polynomial.aeval_X x⟩⟩],
  obtain ["⟨", ident p, ",", ident rfl, "⟩", ":=", expr (alg_hom.mem_range _).mp hy],
  rw [expr polynomial.aeval_eq_sum_range] [],
  refine [expr submodule.sum_mem _ (λ i hi, submodule.smul_mem _ _ _)],
  clear [ident hi],
  induction [expr i] [] ["with", ident i, ident ih] [],
  { rw [expr pow_zero] [],
    exact [expr one_mem_inv_coe_ideal hI0] },
  { show [expr «expr ∈ »(«expr ^ »(x, i.succ), («expr ⁻¹»(I) : fractional_ideal «expr ⁰»(A) K))],
    rw [expr pow_succ] [],
    exact [expr x_mul_mem _ ih] }
end

/-- Nonzero fractional ideals in a Dedekind domain are units.

This is also available as `_root_.mul_inv_cancel`, using the
`comm_group_with_zero` instance defined below.
-/
protected theorem mul_inv_cancel [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hne : I ≠ 0) : (I*I⁻¹) = 1 :=
  by 
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
  ∀ {I I'}, ((I*J) ≤ I'*J) ↔ I ≤ I' :=
  by 
    intro I I' 
    split 
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
protected theorem div_eq_mul_inv [IsDedekindDomain A] (I J : FractionalIdeal A⁰ K) : I / J = I*J⁻¹ :=
  by 
    byCases' hJ : J = 0
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

/-- `is_dedekind_domain` and `is_dedekind_domain_inv` are equivalent ways
to express that an integral domain is a Dedekind domain. -/
theorem is_dedekind_domain_iff_is_dedekind_domain_inv : IsDedekindDomain A ↔ IsDedekindDomainInv A :=
  ⟨fun h I hI =>
      by 
        exact FractionalIdeal.mul_inv_cancel hI,
    fun h => h.is_dedekind_domain⟩

end Inverse

section IsDedekindDomain

variable{R A}[IsDedekindDomain A][Algebra A K][IsFractionRing A K]

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

noncomputable instance Ideal.commCancelMonoidWithZero : CommCancelMonoidWithZero (Ideal A) :=
  Function.Injective.commCancelMonoidWithZero (coe_ideal_hom A⁰ (FractionRing A)) coe_ideal_injective
    (RingHom.map_zero _) (RingHom.map_one _) (RingHom.map_mul _)

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For ideals in a Dedekind domain, to divide is to contain. -/
theorem ideal.dvd_iff_le {I J : ideal A} : «expr ↔ »(«expr ∣ »(I, J), «expr ≤ »(J, I)) :=
⟨ideal.le_of_dvd, λ h, begin
   by_cases [expr hI, ":", expr «expr = »(I, «expr⊥»())],
   { have [ident hJ] [":", expr «expr = »(J, «expr⊥»())] [],
     { rwa ["[", expr hI, ",", "<-", expr eq_bot_iff, "]"] ["at", ident h] },
     rw ["[", expr hI, ",", expr hJ, "]"] [] },
   have [ident hI'] [":", expr «expr ≠ »((I : fractional_ideal «expr ⁰»(A) (fraction_ring A)), 0)] [":=", expr (fractional_ideal.coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr hI],
   have [] [":", expr «expr ≤ »(«expr * »(«expr ⁻¹»((I : fractional_ideal «expr ⁰»(A) (fraction_ring A))), J), 1)] [":=", expr le_trans (fractional_ideal.mul_left_mono «expr ⁻¹»(«expr↑ »(I)) ((coe_ideal_le_coe_ideal _).mpr h)) (le_of_eq (inv_mul_cancel hI'))],
   obtain ["⟨", ident H, ",", ident hH, "⟩", ":=", expr fractional_ideal.le_one_iff_exists_coe_ideal.mp this],
   use [expr H],
   refine [expr coe_to_fractional_ideal_injective (le_refl (non_zero_divisors A)) (show «expr = »((J : fractional_ideal «expr ⁰»(A) (fraction_ring A)), _), from _)],
   rw ["[", expr fractional_ideal.coe_ideal_mul, ",", expr hH, ",", "<-", expr mul_assoc, ",", expr mul_inv_cancel hI', ",", expr one_mul, "]"] []
 end⟩

theorem Ideal.dvd_not_unit_iff_lt {I J : Ideal A} : DvdNotUnit I J ↔ J < I :=
  ⟨fun ⟨hI, H, hunit, hmul⟩ =>
      lt_of_le_of_neₓ (Ideal.dvd_iff_le.mp ⟨H, hmul⟩)
        (mt
          (fun h =>
            have  : H = 1 :=
              mul_left_cancel₀ hI
                (by 
                  rw [←hmul, h, mul_oneₓ])
            show IsUnit H from this.symm ▸ is_unit_one)
          hunit),
    fun h =>
      dvd_not_unit_of_dvd_of_not_dvd (Ideal.dvd_iff_le.mpr (le_of_ltₓ h)) (mt Ideal.dvd_iff_le.mp (not_le_of_lt h))⟩

instance  : WfDvdMonoid (Ideal A) :=
  { well_founded_dvd_not_unit :=
      have  : WellFounded (· > · : Ideal A → Ideal A → Prop) :=
        is_noetherian_iff_well_founded.mp (is_noetherian_ring_iff.mp IsDedekindDomain.is_noetherian_ring)
      by 
        convert this 
        ext 
        rw [Ideal.dvd_not_unit_iff_lt] }

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance ideal.unique_factorization_monoid : unique_factorization_monoid (ideal A) :=
{ irreducible_iff_prime := λ
  P, ⟨λ
   hirr, ⟨hirr.ne_zero, hirr.not_unit, λ I J, begin
      have [] [":", expr P.is_maximal] [],
      { refine [expr ⟨⟨mt ideal.is_unit_iff.mpr hirr.not_unit, _⟩⟩],
        intros [ident J, ident hJ],
        obtain ["⟨", ident J_ne, ",", ident H, ",", ident hunit, ",", ident P_eq, "⟩", ":=", expr ideal.dvd_not_unit_iff_lt.mpr hJ],
        exact [expr ideal.is_unit_iff.mp ((hirr.is_unit_or_is_unit P_eq).resolve_right hunit)] },
      rw ["[", expr ideal.dvd_iff_le, ",", expr ideal.dvd_iff_le, ",", expr ideal.dvd_iff_le, ",", expr set_like.le_def, ",", expr set_like.le_def, ",", expr set_like.le_def, "]"] [],
      contrapose ["!"] [],
      rintros ["⟨", "⟨", ident x, ",", ident x_mem, ",", ident x_not_mem, "⟩", ",", "⟨", ident y, ",", ident y_mem, ",", ident y_not_mem, "⟩", "⟩"],
      exact [expr ⟨«expr * »(x, y), ideal.mul_mem_mul x_mem y_mem, mt this.is_prime.mem_or_mem (not_or x_not_mem y_not_mem)⟩]
    end⟩, prime.irreducible⟩,
  ..ideal.wf_dvd_monoid }

noncomputable instance Ideal.normalizationMonoid : NormalizationMonoid (Ideal A) :=
  normalizationMonoidOfUniqueUnits

@[simp]
theorem Ideal.dvd_span_singleton {I : Ideal A} {x : A} : I ∣ Ideal.span {x} ↔ x ∈ I :=
  Ideal.dvd_iff_le.trans (Ideal.span_le.trans Set.singleton_subset_iff)

theorem Ideal.is_prime_of_prime {P : Ideal A} (h : Prime P) : is_prime P :=
  by 
    refine' ⟨_, fun x y hxy => _⟩
    ·
      (
        rintro rfl)
      rw [←Ideal.one_eq_top] at h 
      exact h.not_unit is_unit_one
    ·
      simp only [←Ideal.dvd_span_singleton, ←Ideal.span_singleton_mul_span_singleton] at hxy⊢
      exact h.dvd_or_dvd hxy

theorem Ideal.prime_of_is_prime {P : Ideal A} (hP : P ≠ ⊥) (h : is_prime P) : Prime P :=
  by 
    refine' ⟨hP, mt ideal.is_unit_iff.mp h.ne_top, fun I J hIJ => _⟩
    simpa only [Ideal.dvd_iff_le] using h.mul_le.mp (Ideal.le_of_dvd hIJ)

/-- In a Dedekind domain, the (nonzero) prime elements of the monoid with zero `ideal A`
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

variable{A K}[Algebra A K][IsFractionRing A K]

variable{L : Type _}[Field L](C : Type _)[CommRingₓ C]

variable[Algebra K L][FiniteDimensional K L][Algebra A L][IsScalarTower A K L]

variable[Algebra C L][IsIntegralClosure C A L][Algebra A C][IsScalarTower A C L]

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_integral_closure.range_le_span_dual_basis
[is_separable K L]
{ι : Type*}
[fintype ι]
[decidable_eq ι]
(b : basis ι K L)
(hb_int : ∀ i, is_integral A (b i))
[is_integrally_closed A] : «expr ≤ »(((algebra.linear_map C L).restrict_scalars A).range, submodule.span A «expr $ »(set.range, (trace_form K L).dual_basis (trace_form_nondegenerate K L) b)) :=
begin
  let [ident db] [] [":=", expr (trace_form K L).dual_basis (trace_form_nondegenerate K L) b],
  rintros ["_", "⟨", ident x, ",", ident rfl, "⟩"],
  simp [] [] ["only"] ["[", expr linear_map.coe_restrict_scalars_eq_coe, ",", expr algebra.linear_map_apply, "]"] [] [],
  have [ident hx] [":", expr is_integral A (algebra_map C L x)] [":=", expr (is_integral_closure.is_integral A L x).algebra_map],
  suffices [] [":", expr «expr∃ , »((c : ι → A), «expr = »(algebra_map C L x, «expr∑ , »((i), «expr • »(c i, db i))))],
  { obtain ["⟨", ident c, ",", ident x_eq, "⟩", ":=", expr this],
    rw [expr x_eq] [],
    refine [expr submodule.sum_mem _ (λ i _, submodule.smul_mem _ _ (submodule.subset_span _))],
    rw [expr set.mem_range] [],
    exact [expr ⟨i, rfl⟩] },
  suffices [] [":", expr «expr∃ , »((c : ι → K), «expr ∧ »(∀
     i, is_integral A (c i), «expr = »(algebra_map C L x, «expr∑ , »((i), «expr • »(c i, db i)))))],
  { obtain ["⟨", ident c, ",", ident hc, ",", ident hx, "⟩", ":=", expr this],
    have [ident hc'] [":", expr ∀
     i, is_localization.is_integer A (c i)] [":=", expr λ i, is_integrally_closed.is_integral_iff.mp (hc i)],
    use [expr λ i, classical.some (hc' i)],
    refine [expr hx.trans (finset.sum_congr rfl (λ i _, _))],
    conv_lhs [] [] { rw ["[", "<-", expr classical.some_spec (hc' i), "]"] },
    rw ["[", "<-", expr is_scalar_tower.algebra_map_smul K (classical.some (hc' i)) (db i), "]"] [] },
  refine [expr ⟨λ i, db.repr (algebra_map C L x) i, λ i, _, (db.sum_repr _).symm⟩],
  rw [expr bilin_form.dual_basis_repr_apply] [],
  exact [expr is_integral_trace (is_integral_mul hx (hb_int i))]
end

theorem integral_closure_le_span_dual_basis [IsSeparable K L] {ι : Type _} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
  (hb_int : ∀ i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
  (integralClosure A L).toSubmodule ≤
    Submodule.span A (Set.Range$ (trace_form K L).dualBasis (trace_form_nondegenerate K L) b) :=
  by 
    refine' le_transₓ _ (IsIntegralClosure.range_le_span_dual_basis (integralClosure A L) b hb_int)
    intro x hx 
    exact ⟨⟨x, hx⟩, rfl⟩

variable(A)(K)

include K

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Send a set of `x`'es in a finite extension `L` of the fraction field of `R`
to `(y : R) • x ∈ integral_closure R L`. -/
theorem exists_integral_multiples
(s : finset L) : «expr∃ , »((y «expr ≠ » (0 : A)), ∀ x «expr ∈ » s, is_integral A «expr • »(y, x)) :=
begin
  haveI [] [] [":=", expr classical.dec_eq L],
  refine [expr s.induction _ _],
  { use ["[", expr 1, ",", expr one_ne_zero, "]"],
    rintros [ident x, "⟨", "⟩"] },
  { rintros [ident x, ident s, ident hx, "⟨", ident y, ",", ident hy, ",", ident hs, "⟩"],
    obtain ["⟨", ident x', ",", ident y', ",", ident hy', ",", ident hx', "⟩", ":=", expr exists_integral_multiple ((is_fraction_ring.is_algebraic_iff A K).mpr (algebra.is_algebraic_of_finite x)) ((algebra_map A L).injective_iff.mp _)],
    refine [expr ⟨«expr * »(y, y'), mul_ne_zero hy hy', λ x'' hx'', _⟩],
    rcases [expr finset.mem_insert.mp hx'', "with", "(", ident rfl, "|", ident hx'', ")"],
    { rw ["[", expr mul_smul, ",", expr algebra.smul_def, ",", expr algebra.smul_def, ",", expr mul_comm _ x'', ",", expr hx', "]"] [],
      exact [expr is_integral_mul is_integral_algebra_map x'.2] },
    { rw ["[", expr mul_comm, ",", expr mul_smul, ",", expr algebra.smul_def, "]"] [],
      exact [expr is_integral_mul is_integral_algebra_map (hs _ hx'')] },
    { rw [expr is_scalar_tower.algebra_map_eq A K L] [],
      apply [expr (algebra_map K L).injective.comp],
      exact [expr is_fraction_ring.injective _ _] } }
end

variable(L)

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `L` is a finite extension of `K = Frac(A)`,
then `L` has a basis over `A` consisting of integral elements. -/
theorem finite_dimensional.exists_is_basis_integral : «expr∃ , »((s : finset L)
 (b : basis s K L), ∀ x, is_integral A (b x)) :=
begin
  letI [] [] [":=", expr classical.dec_eq L],
  letI [] [":", expr is_noetherian K L] [":=", expr is_noetherian.iff_fg.2 infer_instance],
  let [ident s'] [] [":=", expr is_noetherian.finset_basis_index K L],
  let [ident bs'] [] [":=", expr is_noetherian.finset_basis K L],
  obtain ["⟨", ident y, ",", ident hy, ",", ident his', "⟩", ":=", expr exists_integral_multiples A K (finset.univ.image bs')],
  have [ident hy'] [":", expr «expr ≠ »(algebra_map A L y, 0)] [],
  { refine [expr mt ((algebra_map A L).injective_iff.mp _ _) hy],
    rw [expr is_scalar_tower.algebra_map_eq A K L] [],
    exact [expr (algebra_map K L).injective.comp (is_fraction_ring.injective A K)] },
  refine [expr ⟨s', bs'.map { to_fun := λ x, «expr * »(algebra_map A L y, x),
      inv_fun := λ x, «expr * »(«expr ⁻¹»(algebra_map A L y), x),
      left_inv := _,
      right_inv := _,
      ..algebra.lmul _ _ (algebra_map A L y) }, _⟩],
  { intros [ident x],
    simp [] [] ["only"] ["[", expr inv_mul_cancel_left₀ hy', "]"] [] [] },
  { intros [ident x],
    simp [] [] ["only"] ["[", expr mul_inv_cancel_left₀ hy', "]"] [] [] },
  { rintros ["⟨", ident x', ",", ident hx', "⟩"],
    simp [] [] ["only"] ["[", expr algebra.smul_def, ",", expr finset.mem_image, ",", expr exists_prop, ",", expr finset.mem_univ, ",", expr true_and, "]"] [] ["at", ident his'],
    simp [] [] ["only"] ["[", expr basis.map_apply, ",", expr linear_equiv.coe_mk, "]"] [] [],
    exact [expr his' _ ⟨_, rfl⟩] }
end

variable(A K L)[IsSeparable K L]

include L

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_integral_closure.is_noetherian_ring [is_integrally_closed A] [is_noetherian_ring A] : is_noetherian_ring C :=
begin
  haveI [] [] [":=", expr classical.dec_eq L],
  obtain ["⟨", ident s, ",", ident b, ",", ident hb_int, "⟩", ":=", expr finite_dimensional.exists_is_basis_integral A K L],
  rw [expr is_noetherian_ring_iff] [],
  let [ident b'] [] [":=", expr (trace_form K L).dual_basis (trace_form_nondegenerate K L) b],
  letI [] [] [":=", expr is_noetherian_span_of_finite A (set.finite_range b')],
  let [ident f] [":", expr «expr →ₗ[ ] »(C, A, submodule.span A (set.range b'))] [":=", expr (submodule.of_le (is_integral_closure.range_le_span_dual_basis C b hb_int)).comp ((algebra.linear_map C L).restrict_scalars A).range_restrict],
  refine [expr is_noetherian_of_tower A (is_noetherian_of_ker_bot f _)],
  rw ["[", expr linear_map.ker_comp, ",", expr submodule.ker_of_le, ",", expr submodule.comap_bot, ",", expr linear_map.ker_cod_restrict, "]"] [],
  exact [expr linear_map.ker_eq_bot_of_injective (is_integral_closure.algebra_map_injective C A L)]
end

variable{A K}

theorem integralClosure.is_noetherian_ring [IsIntegrallyClosed A] [IsNoetherianRing A] :
  IsNoetherianRing (integralClosure A L) :=
  IsIntegralClosure.is_noetherian_ring A K L (integralClosure A L)

variable(A K)[IsDomain C]

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_integral_closure.is_dedekind_domain [h : is_dedekind_domain A] : is_dedekind_domain C :=
begin
  haveI [] [":", expr is_fraction_ring C L] [":=", expr is_integral_closure.is_fraction_ring_of_finite_extension A K L C],
  exact [expr ⟨is_integral_closure.is_noetherian_ring A K L C, h.dimension_le_one.is_integral_closure _ L _, (is_integrally_closed_iff L).mpr (λ
     x
     hx, ⟨is_integral_closure.mk' C x (is_integral_trans (is_integral_closure.is_integral_algebra A L) _ hx), is_integral_closure.algebra_map_mk' _ _ _⟩)⟩]
end

theorem integralClosure.is_dedekind_domain [h : IsDedekindDomain A] : IsDedekindDomain (integralClosure A L) :=
  IsIntegralClosure.is_dedekind_domain A K L (integralClosure A L)

omit K

variable[Algebra (FractionRing A) L][IsScalarTower A (FractionRing A) L]

variable[FiniteDimensional (FractionRing A) L][IsSeparable (FractionRing A) L]

instance integralClosure.is_dedekind_domain_fraction_ring [IsDedekindDomain A] :
  IsDedekindDomain (integralClosure A L) :=
  integralClosure.is_dedekind_domain A (FractionRing A) L

end IsIntegralClosure

section IsDedekindDomain

variable{T : Type _}[CommRingₓ T][IsDomain T][IsDedekindDomain T](I J : Ideal T)

open_locale Classical

open Multiset UniqueFactorizationMonoid Ideal

theorem prod_normalized_factors_eq_self {I : Ideal T} (hI : I ≠ ⊥) : (normalized_factors I).Prod = I :=
  associated_iff_eq.1 (normalized_factors_prod hI)

theorem normalized_factors_prod {α : Multiset (Ideal T)} (h : ∀ p _ : p ∈ α, Prime p) : normalized_factors α.prod = α :=
  by 
    simpRw [←Multiset.rel_eq, ←associated_eq_eq]
    exact prime_factors_unique prime_of_normalized_factor h (normalized_factors_prod (α.prod_ne_zero_of_prime h))

theorem count_le_of_ideal_ge {I J : Ideal T} (h : I ≤ J) (hI : I ≠ ⊥) (K : Ideal T) :
  count K (normalized_factors J) ≤ count K (normalized_factors I) :=
  le_iff_count.1 ((dvd_iff_normalized_factors_le_normalized_factors (ne_bot_of_le_ne_bot hI h) hI).1 (dvd_iff_le.2 h)) _

-- error in RingTheory.DedekindDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sup_eq_prod_inf_factors
(hI : «expr ≠ »(I, «expr⊥»()))
(hJ : «expr ≠ »(J, «expr⊥»())) : «expr = »(«expr ⊔ »(I, J), «expr ∩ »(normalized_factors I, normalized_factors J).prod) :=
begin
  have [ident H] [":", expr «expr = »(normalized_factors «expr ∩ »(normalized_factors I, normalized_factors J).prod, «expr ∩ »(normalized_factors I, normalized_factors J))] [],
  { apply [expr _root_.normalized_factors_prod],
    intros [ident p, ident hp],
    rw [expr mem_inter] ["at", ident hp],
    exact [expr prime_of_normalized_factor p hp.left] },
  have [] [] [":=", expr multiset.prod_ne_zero_of_prime «expr ∩ »(normalized_factors I, normalized_factors J) (λ
    _ h, prime_of_normalized_factor _ (multiset.mem_inter.1 h).1)],
  apply [expr le_antisymm],
  { rw ["[", expr sup_le_iff, ",", "<-", expr dvd_iff_le, ",", "<-", expr dvd_iff_le, "]"] [],
    split,
    { rw ["[", expr dvd_iff_normalized_factors_le_normalized_factors this hI, ",", expr H, "]"] [],
      exact [expr inf_le_left] },
    { rw ["[", expr dvd_iff_normalized_factors_le_normalized_factors this hJ, ",", expr H, "]"] [],
      exact [expr inf_le_right] } },
  { rw ["[", "<-", expr dvd_iff_le, ",", expr dvd_iff_normalized_factors_le_normalized_factors, ",", expr _root_.normalized_factors_prod, ",", expr le_iff_count, "]"] [],
    { intro [ident a],
      rw [expr multiset.count_inter] [],
      exact [expr le_min (count_le_of_ideal_ge le_sup_left hI a) (count_le_of_ideal_ge le_sup_right hJ a)] },
    { intros [ident p, ident hp],
      rw [expr mem_inter] ["at", ident hp],
      exact [expr prime_of_normalized_factor p hp.left] },
    { exact [expr ne_bot_of_le_ne_bot hI le_sup_left] },
    { exact [expr this] } }
end

end IsDedekindDomain

