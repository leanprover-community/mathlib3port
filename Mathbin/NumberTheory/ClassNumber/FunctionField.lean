/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import NumberTheory.ClassNumber.AdmissibleCardPowDegree
import NumberTheory.ClassNumber.Finite
import NumberTheory.FunctionField

#align_import number_theory.class_number.function_field from "leanprover-community/mathlib"@"30faa0c3618ce1472bf6305ae0e3fa56affa3f95"

/-!
# Class numbers of function fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the class number of a function field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
- `function_field.class_number`: the class number of a function field is the (finite)
cardinality of the class group of its ring of integers
-/


namespace FunctionField

open scoped Polynomial

variable (Fq F : Type) [Field Fq] [Fintype Fq] [Field F]

variable [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]

variable [IsScalarTower Fq[X] (RatFunc Fq) F]

variable [FunctionField Fq F] [IsSeparable (RatFunc Fq) F]

open scoped Classical

namespace RingOfIntegers

open FunctionField

noncomputable instance : Fintype (ClassGroup (ringOfIntegers Fq F)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite (RatFunc Fq) F
    (Polynomial.cardPowDegreeIsAdmissible :
      AbsoluteValue.IsAdmissible (Polynomial.cardPowDegree : AbsoluteValue Fq[X] ℤ))

end RingOfIntegers

#print FunctionField.classNumber /-
/-- The class number in a function field is the (finite) cardinality of the class group. -/
noncomputable def classNumber : ℕ :=
  Fintype.card (ClassGroup (ringOfIntegers Fq F))
#align function_field.class_number FunctionField.classNumber
-/

#print FunctionField.classNumber_eq_one_iff /-
/-- The class number of a function field is `1` iff the ring of integers is a PID. -/
theorem classNumber_eq_one_iff :
    classNumber Fq F = 1 ↔ IsPrincipalIdealRing (ringOfIntegers Fq F) :=
  card_classGroup_eq_one_iff
#align function_field.class_number_eq_one_iff FunctionField.classNumber_eq_one_iff
-/

end FunctionField

