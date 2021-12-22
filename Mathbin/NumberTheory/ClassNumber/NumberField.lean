import Mathbin.NumberTheory.ClassNumber.AdmissibleAbs
import Mathbin.NumberTheory.ClassNumber.Finite
import Mathbin.NumberTheory.NumberField

/-!
# Class numbers of number fields

This file defines the class number of a number field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
- `number_field.class_number`: the class number of a number field is the (finite)
cardinality of the class group of its ring of integers
-/


namespace NumberField

variable (K : Type _) [Field K] [NumberField K]

namespace RingOfIntegers

noncomputable instance : Fintype (ClassGroup (ring_of_integers K) K) :=
  ClassGroup.fintypeOfAdmissibleOfFinite ℚ _ AbsoluteValue.absIsAdmissible

end RingOfIntegers

/--  The class number of a number field is the (finite) cardinality of the class group. -/
noncomputable def class_number : ℕ :=
  Fintype.card (ClassGroup (ring_of_integers K) K)

variable {K}

/--  The class number of a number field is `1` iff the ring of integers is a PID. -/
theorem class_number_eq_one_iff : class_number K = 1 ↔ IsPrincipalIdealRing (ring_of_integers K) :=
  card_class_group_eq_one_iff

end NumberField

namespace Rat

open NumberField

theorem class_number_eq : NumberField.classNumber ℚ = 1 :=
  class_number_eq_one_iff.mpr $ by
    convert
      IsPrincipalIdealRing.of_surjective (rat.ring_of_integers_equiv.symm : ℤ →+* ring_of_integers ℚ)
        rat.ring_of_integers_equiv.symm.surjective

end Rat

