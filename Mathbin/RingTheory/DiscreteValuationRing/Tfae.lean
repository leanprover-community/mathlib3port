/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import RingTheory.Ideal.Cotangent
import RingTheory.DedekindDomain.Basic
import RingTheory.Valuation.ValuationRing
import RingTheory.Nakayama

#align_import ring_theory.discrete_valuation_ring.tfae from "leanprover-community/mathlib"@"6b31d1eebd64eab86d5bd9936bfaada6ca8b5842"

/-!

# Equivalent conditions for DVR

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In `discrete_valuation_ring.tfae`, we show that the following are equivalent for a
noetherian local domain `(R, m, k)`:
- `R` is a discrete valuation ring
- `R` is a valuation ring
- `R` is a dedekind domain
- `R` is integrally closed with a unique prime ideal
- `m` is principal
- `dimₖ m/m² = 1`
- Every nonzero ideal is a power of `m`.

-/


variable (R : Type _) [CommRing R] (K : Type _) [Field K] [Algebra R K] [IsFractionRing R K]

open scoped DiscreteValuation

open LocalRing

open scoped BigOperators

#print exists_maximalIdeal_pow_eq_of_principal /-
theorem exists_maximalIdeal_pow_eq_of_principal [IsNoetherianRing R] [LocalRing R] [IsDomain R]
    (h : ¬IsField R) (h' : (maximalIdeal R).IsPrincipal) (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = maximalIdeal R ^ n := by classical
#align exists_maximal_ideal_pow_eq_of_principal exists_maximalIdeal_pow_eq_of_principal
-/

#print maximalIdeal_isPrincipal_of_isDedekindDomain /-
theorem maximalIdeal_isPrincipal_of_isDedekindDomain [LocalRing R] [IsDomain R]
    [IsDedekindDomain R] : (maximalIdeal R).IsPrincipal := by classical
#align maximal_ideal_is_principal_of_is_dedekind_domain maximalIdeal_isPrincipal_of_isDedekindDomain
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (I «expr ≠ » «expr⊥»()) -/
#print DiscreteValuationRing.TFAE /-
theorem DiscreteValuationRing.TFAE [IsNoetherianRing R] [LocalRing R] [IsDomain R]
    (h : ¬IsField R) :
    TFAE
      [DiscreteValuationRing R, ValuationRing R, IsDedekindDomain R,
        IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime, (maximalIdeal R).IsPrincipal,
        FiniteDimensional.finrank (ResidueField R) (CotangentSpace R) = 1,
        ∀ (I) (_ : I ≠ ⊥), ∃ n : ℕ, I = maximalIdeal R ^ n] :=
  by
  have ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField (maximal_ideal.is_maximal R) h
  classical
#align discrete_valuation_ring.tfae DiscreteValuationRing.TFAE
-/

