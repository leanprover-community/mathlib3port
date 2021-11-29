import Mathbin.NumberTheory.ClassNumber.AdmissibleCardPowDegree 
import Mathbin.NumberTheory.ClassNumber.Finite 
import Mathbin.NumberTheory.FunctionField

/-!
# Class numbers of function fields

This file defines the class number of a function field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
- `function_field.class_number`: the class number of a function field is the (finite)
cardinality of the class group of its ring of integers
-/


namespace FunctionField

variable (Fq F : Type) [Field Fq] [Fintype Fq] [Field F]

variable [Algebra (Polynomial Fq) F] [Algebra (Ratfunc Fq) F]

variable [IsScalarTower (Polynomial Fq) (Ratfunc Fq) F]

variable [FunctionField Fq F] [IsSeparable (Ratfunc Fq) F]

open_locale Classical

namespace RingOfIntegers

open FunctionField

noncomputable instance : Fintype (ClassGroup (ring_of_integers Fq F) F) :=
  ClassGroup.fintypeOfAdmissibleOfFinite (Ratfunc Fq) F
    (Polynomial.cardPowDegreeIsAdmissible :
    AbsoluteValue.IsAdmissible (Polynomial.cardPowDegree : AbsoluteValue (Polynomial Fq) ℤ))

end RingOfIntegers

/-- The class number in a function field is the (finite) cardinality of the class group. -/
noncomputable def class_number : ℕ :=
  Fintype.card (ClassGroup (ring_of_integers Fq F) F)

/-- The class number of a function field is `1` iff the ring of integers is a PID. -/
theorem class_number_eq_one_iff : class_number Fq F = 1 ↔ IsPrincipalIdealRing (ring_of_integers Fq F) :=
  card_class_group_eq_one_iff

end FunctionField

