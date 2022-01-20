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
class NumberField (K : Type _) [Field K] : Prop where
  [to_char_zero : CharZero K]
  [to_finite_dimensional : FiniteDimensional ℚ K]

open Function

open_locale Classical BigOperators

namespace NumberField

variable (K L : Type _) [Field K] [Field L] [nf : NumberField K]

include nf

attribute [instance] NumberField.to_char_zero NumberField.to_finite_dimensional

protected theorem IsAlgebraic : Algebra.IsAlgebraic ℚ K :=
  Algebra.is_algebraic_of_finite

omit nf

/-- The ring of integers (or number ring) corresponding to a number field
is the integral closure of ℤ in the number field. -/
def ring_of_integers :=
  integralClosure ℤ K

localized [NumberField] notation "𝓞" => NumberField.ringOfIntegers

theorem mem_ring_of_integers (x : K) : x ∈ 𝓞 K ↔ IsIntegral ℤ x :=
  Iff.rfl

instance ring_of_integers_algebra [Algebra K L] : Algebra (𝓞 K) (𝓞 L) :=
  RingHom.toAlgebra
    { toFun := fun k => ⟨algebraMap K L k, IsIntegral.algebra_map k.2⟩,
      map_zero' :=
        Subtype.ext $ by
          simp only [Subtype.coe_mk, Subalgebra.coe_zero, map_zero],
      map_one' :=
        Subtype.ext $ by
          simp only [Subtype.coe_mk, Subalgebra.coe_one, map_one],
      map_add' := fun x y =>
        Subtype.ext $ by
          simp only [map_add, Subalgebra.coe_add, Subtype.coe_mk],
      map_mul' := fun x y =>
        Subtype.ext $ by
          simp only [Subalgebra.coe_mul, map_mul, Subtype.coe_mk] }

namespace RingOfIntegers

variable {K}

instance [NumberField K] : IsFractionRing (𝓞 K) K :=
  integralClosure.is_fraction_ring_of_finite_extension ℚ _

instance : IsIntegralClosure (𝓞 K) ℤ K :=
  integralClosure.is_integral_closure _ _

instance [NumberField K] : IsIntegrallyClosed (𝓞 K) :=
  integralClosure.is_integrally_closed_of_finite_extension ℚ

theorem is_integral_coe (x : 𝓞 K) : IsIntegral ℤ (x : K) :=
  x.2

/-- The ring of integers of `K` are equivalent to any integral closure of `ℤ` in `K` -/
protected noncomputable def Equivₓ (R : Type _) [CommRingₓ R] [Algebra R K] [IsIntegralClosure R ℤ K] : 𝓞 K ≃+* R :=
  (IsIntegralClosure.equiv ℤ R K _).symm.toRingEquiv

variable (K)

instance [NumberField K] : CharZero (𝓞 K) :=
  CharZero.of_module _ K

instance [NumberField K] : IsDedekindDomain (𝓞 K) :=
  IsIntegralClosure.is_dedekind_domain ℤ ℚ K _

end RingOfIntegers

end NumberField

namespace Rat

open NumberField

instance rat.number_field : NumberField ℚ where
  to_char_zero := inferInstance
  to_finite_dimensional := by
    convert (inferInstance : FiniteDimensional ℚ ℚ)
    ext1
    simp [Algebra.smul_def]

/-- The ring of integers of `ℚ` as a number field is just `ℤ`. -/
noncomputable def ring_of_integers_equiv : ring_of_integers ℚ ≃+* ℤ :=
  ring_of_integers.equiv ℤ

end Rat

