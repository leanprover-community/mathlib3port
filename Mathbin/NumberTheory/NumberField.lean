import Mathbin.Algebra.Field.Basic 
import Mathbin.Data.Rat.Basic 
import Mathbin.RingTheory.Algebraic 
import Mathbin.RingTheory.DedekindDomain 
import Mathbin.RingTheory.IntegralClosure 
import Mathbin.RingTheory.Polynomial.RationalRoot

/-!
# Number fields
This file defines a number field and the ring of integers corresponding to it.

## Main definitions
 - `number_field` defines a number field as a field which has characteristic zero and is finite
    dimensional over ℚ.
 - `ring_of_integers` defines the ring of integers (or number ring) corresponding to a number field
    as the integral closure of ℤ in the number field.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags
number field, ring of integers
-/


/-- A number field is a field which has characteristic zero and is finite
dimensional over ℚ. -/
class NumberField(K : Type _)[Field K] : Prop where 
  [to_char_zero : CharZero K]
  [to_finite_dimensional : FiniteDimensional ℚ K]

open Function

open_locale Classical BigOperators

namespace NumberField

variable(K : Type _)[Field K][nf : NumberField K]

include nf

attribute [instance] NumberField.to_char_zero NumberField.to_finite_dimensional

protected theorem IsAlgebraic : Algebra.IsAlgebraic ℚ K :=
  Algebra.is_algebraic_of_finite

omit nf

/-- The ring of integers (or number ring) corresponding to a number field
is the integral closure of ℤ in the number field. -/
def ring_of_integers :=
  integralClosure ℤ K

namespace RingOfIntegers

variable{K}

instance  [NumberField K] : IsFractionRing (ring_of_integers K) K :=
  integralClosure.is_fraction_ring_of_finite_extension ℚ _

instance  : IsIntegralClosure (ring_of_integers K) ℤ K :=
  integralClosure.is_integral_closure _ _

instance  [NumberField K] : IsIntegrallyClosed (ring_of_integers K) :=
  integralClosure.is_integrally_closed_of_finite_extension ℚ

theorem is_integral_coe (x : ring_of_integers K) : IsIntegral ℤ (x : K) :=
  x.2

/-- The ring of integers of `K` are equivalent to any integral closure of `ℤ` in `K` -/
protected noncomputable def Equiv (R : Type _) [CommRingₓ R] [Algebra R K] [IsIntegralClosure R ℤ K] :
  ring_of_integers K ≃+* R :=
  (IsIntegralClosure.equiv ℤ R K _).symm.toRingEquiv

variable(K)

instance  [NumberField K] : CharZero (ring_of_integers K) :=
  CharZero.of_algebra K

instance  [NumberField K] : IsDedekindDomain (ring_of_integers K) :=
  IsIntegralClosure.is_dedekind_domain ℤ ℚ K _

end RingOfIntegers

end NumberField

namespace Rat

open NumberField

instance rat.number_field : NumberField ℚ :=
  { to_char_zero := inferInstance,
    to_finite_dimensional :=
      by 
        convert (inferInstance : FiniteDimensional ℚ ℚ)
        ext 
        simp [Algebra.smul_def] }

/-- The ring of integers of `ℚ` as a number field is just `ℤ`. -/
noncomputable def ring_of_integers_equiv : ring_of_integers ℚ ≃+* ℤ :=
  ring_of_integers.equiv ℤ

end Rat

