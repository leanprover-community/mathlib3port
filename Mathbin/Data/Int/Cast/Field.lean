/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.Data.Int.Cast.Lemmas
import Mathbin.Algebra.Field.Defs
import Mathbin.Algebra.GroupWithZero.Units.Lemmas

#align_import data.int.cast.field from "leanprover-community/mathlib"@"acee671f47b8e7972a1eb6f4eed74b4b3abce829"

/-!
# Cast of integers into fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file concerns the canonical homomorphism `ℤ → F`, where `F` is a field.

## Main results

 * `int.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
-/


namespace Int

open Nat

variable {α : Type _}

#print Int.cast_neg_natCast /-
/-- Auxiliary lemma for norm_cast to move the cast `-↑n` upwards to `↑-↑n`.

(The restriction to `division_ring` is necessary, otherwise this would also apply in the case where
`R = ℤ` and cause nontermination.)
-/
@[norm_cast]
theorem cast_neg_natCast {R} [DivisionRing R] (n : ℕ) : ((-n : ℤ) : R) = -n := by simp
#align int.cast_neg_nat_cast Int.cast_neg_natCast
-/

#print Int.cast_div /-
@[simp]
theorem cast_div [DivisionRing α] {m n : ℤ} (n_dvd : n ∣ m) (n_nonzero : (n : α) ≠ 0) :
    ((m / n : ℤ) : α) = m / n := by
  rcases n_dvd with ⟨k, rfl⟩
  have : n ≠ 0 := by rintro rfl; simpa using n_nonzero
  rw [Int.mul_ediv_cancel_left _ this, mul_comm n k, Int.cast_mul, mul_div_cancel _ n_nonzero]
#align int.cast_div Int.cast_div
-/

end Int

