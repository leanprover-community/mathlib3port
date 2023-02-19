/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module data.int.associated
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Associated
import Mathbin.Data.Int.Units

/-!
# Associated elements and the integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some results on equality up to units in the integers.

## Main results

 * `int.nat_abs_eq_iff_associated`: the absolute value is equal iff integers are associated
-/


/- warning: int.nat_abs_eq_iff_associated -> Int.natAbs_eq_iff_associated is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, Iff (Eq.{1} Nat (Int.natAbs a) (Int.natAbs b)) (Associated.{0} Int Int.monoid a b)
but is expected to have type
  forall {a : Int} {b : Int}, Iff (Eq.{1} Nat (Int.natAbs a) (Int.natAbs b)) (Associated.{0} Int Int.instMonoidInt a b)
Case conversion may be inaccurate. Consider using '#align int.nat_abs_eq_iff_associated Int.natAbs_eq_iff_associatedₓ'. -/
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

