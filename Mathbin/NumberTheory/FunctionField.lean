/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/
import Mathbin.FieldTheory.Ratfunc
import Mathbin.RingTheory.Algebraic
import Mathbin.RingTheory.DedekindDomain.IntegralClosure
import Mathbin.RingTheory.IntegrallyClosed

/-!
# Function fields

This file defines a function field and the ring of integers corresponding to it.

## Main definitions
 - `function_field Fq F` states that `F` is a function field over the (finite) field `Fq`,
   i.e. it is a finite extension of the field of rational functions in one variable over `Fq`.
 - `function_field.ring_of_integers` defines the ring of integers corresponding to a function field
    as the integral closure of `polynomial Fq` in the function field.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. We also omit assumptions like `finite Fq` or
`is_scalar_tower Fq[X] (fraction_ring Fq[X]) F` in definitions,
adding them back in lemmas when they are needed.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags
function field, ring of integers
-/


noncomputable section

open_locale nonZeroDivisors Polynomial

variable (Fq F : Type) [Field Fq] [Field F]

/-- `F` is a function field over the finite field `Fq` if it is a finite
extension of the field of rational functions in one variable over `Fq`.

Note that `F` can be a function field over multiple, non-isomorphic, `Fq`.
-/
abbrev FunctionField [Algebra (Ratfunc Fq) F] : Prop :=
  FiniteDimensional (Ratfunc Fq) F

/-- `F` is a function field over `Fq` iff it is a finite extension of `Fq(t)`. -/
protected theorem function_field_iff (Fqt : Type _) [Field Fqt] [Algebra Fq[X] Fqt] [IsFractionRing Fq[X] Fqt]
    [Algebra (Ratfunc Fq) F] [Algebra Fqt F] [Algebra Fq[X] F] [IsScalarTower Fq[X] Fqt F]
    [IsScalarTower Fq[X] (Ratfunc Fq) F] : FunctionField Fq F ↔ FiniteDimensional Fqt F := by
  let e := IsLocalization.algEquiv Fq[X]⁰ (Ratfunc Fq) Fqt
  have : ∀ c x : F, e c • x = c • x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def]
    congr
    refine' congr_funₓ _ c
    refine' IsLocalization.ext (nonZeroDivisors Fq[X]) _ _ _ _ _ _ _ <;>
      intros <;>
        simp only [AlgEquiv.map_one, RingHom.map_one, AlgEquiv.map_mul, RingHom.map_mul, AlgEquiv.commutes, ←
          IsScalarTower.algebra_map_apply]
  constructor <;> intro h <;> skip
  · let b := FiniteDimensional.finBasis (Ratfunc Fq) F
    exact FiniteDimensional.of_fintype_basis (b.map_coeffs e this)
    
  · let b := FiniteDimensional.finBasis Fqt F
    refine' FiniteDimensional.of_fintype_basis (b.map_coeffs e.symm _)
    intro c x
    convert (this (e.symm c) x).symm
    simp only [e.apply_symm_apply]
    

namespace FunctionField

/-- The function field analogue of `number_field.ring_of_integers`:
`function_field.ring_of_integers Fq Fqt F` is the integral closure of `Fq[t]` in `F`.

We don't actually assume `F` is a function field over `Fq` in the definition,
only when proving its properties.
-/
def ringOfIntegers [Algebra Fq[X] F] :=
  integralClosure Fq[X] F

namespace RingOfIntegers

variable [Algebra Fq[X] F]

instance : IsDomain (ringOfIntegers Fq F) :=
  (ringOfIntegers Fq F).IsDomain

instance : IsIntegralClosure (ringOfIntegers Fq F) Fq[X] F :=
  integralClosure.is_integral_closure _ _

variable [Algebra (Ratfunc Fq) F] [FunctionField Fq F]

variable [IsScalarTower Fq[X] (Ratfunc Fq) F]

instance : IsFractionRing (ringOfIntegers Fq F) F :=
  integralClosure.is_fraction_ring_of_finite_extension (Ratfunc Fq) F

instance : IsIntegrallyClosed (ringOfIntegers Fq F) :=
  integralClosure.is_integrally_closed_of_finite_extension (Ratfunc Fq)

instance [IsSeparable (Ratfunc Fq) F] : IsDedekindDomain (ringOfIntegers Fq F) :=
  IsIntegralClosure.is_dedekind_domain Fq[X] (Ratfunc Fq) F _

end RingOfIntegers

end FunctionField

