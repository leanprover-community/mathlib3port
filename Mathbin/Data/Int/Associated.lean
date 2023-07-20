/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Algebra.Associated
import Mathbin.Data.Int.Units

#align_import data.int.associated from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Associated elements and the integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some results on equality up to units in the integers.

## Main results

 * `int.nat_abs_eq_iff_associated`: the absolute value is equal iff integers are associated
-/


#print Int.natAbs_eq_iff_associated /-
theorem Int.natAbs_eq_iff_associated {a b : ℤ} : a.natAbs = b.natAbs ↔ Associated a b :=
  by
  refine' int.nat_abs_eq_nat_abs_iff.trans _
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact ⟨-1, by simp⟩
  · rintro ⟨u, rfl⟩
    obtain rfl | rfl := Int.units_eq_one_or u
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
#align int.nat_abs_eq_iff_associated Int.natAbs_eq_iff_associated
-/

