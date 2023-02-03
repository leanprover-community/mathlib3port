/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module number_theory.class_number.function_field
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
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

open Polynomial

variable (Fq F : Type) [Field Fq] [Fintype Fq] [Field F]

variable [Algebra Fq[X] F] [Algebra (Ratfunc Fq) F]

variable [IsScalarTower Fq[X] (Ratfunc Fq) F]

variable [FunctionField Fq F] [IsSeparable (Ratfunc Fq) F]

open Classical

namespace RingOfIntegers

open FunctionField

noncomputable instance : Fintype (ClassGroup (ringOfIntegers Fq F)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite (Ratfunc Fq) F
    (Polynomial.cardPowDegreeIsAdmissible :
      AbsoluteValue.IsAdmissible (Polynomial.cardPowDegree : AbsoluteValue Fq[X] ℤ))

end RingOfIntegers

/-- The class number in a function field is the (finite) cardinality of the class group. -/
noncomputable def classNumber : ℕ :=
  Fintype.card (ClassGroup (ringOfIntegers Fq F))
#align function_field.class_number FunctionField.classNumber

/-- The class number of a function field is `1` iff the ring of integers is a PID. -/
theorem classNumber_eq_one_iff :
    classNumber Fq F = 1 ↔ IsPrincipalIdealRing (ringOfIntegers Fq F) :=
  card_classGroup_eq_one_iff
#align function_field.class_number_eq_one_iff FunctionField.classNumber_eq_one_iff

end FunctionField

