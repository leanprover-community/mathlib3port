/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Algebra.Order.Ring.Rat
import Data.Rat.Lemmas
import Data.Int.Sqrt

#align_import data.rat.sqrt from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Square root on rational numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the square root function on rational numbers `rat.sqrt`
and proves several theorems about it.

-/


namespace Rat

#print Rat.sqrt /-
/-- Square root function on rational numbers, defined by taking the (integer) square root of the
numerator and the square root (on natural numbers) of the denominator. -/
@[pp_nodot]
def sqrt (q : ℚ) : ℚ :=
  Rat.mk (Int.sqrt q.num) (Nat.sqrt q.den)
#align rat.sqrt Rat.sqrt
-/

#print Rat.sqrt_eq /-
theorem sqrt_eq (q : ℚ) : Rat.sqrt (q * q) = |q| := by
  rw [sqrt, mul_self_num, mul_self_denom, Int.sqrt_eq, Nat.sqrt_eq, abs_def]
#align rat.sqrt_eq Rat.sqrt_eq
-/

#print Rat.exists_mul_self /-
theorem exists_mul_self (x : ℚ) : (∃ q, q * q = x) ↔ Rat.sqrt x * Rat.sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, abs_mul_abs_self], fun h => ⟨Rat.sqrt x, h⟩⟩
#align rat.exists_mul_self Rat.exists_mul_self
-/

#print Rat.sqrt_nonneg /-
theorem sqrt_nonneg (q : ℚ) : 0 ≤ Rat.sqrt q :=
  nonneg_iff_zero_le.1 <|
    (divInt_nonneg_iff_of_pos_right _ <|
          Int.natCast_pos.2 <|
            Nat.pos_of_ne_zero fun H => pos_iff_ne_zero.1 q.Pos <| Nat.sqrt_eq_zero.1 H).2 <|
      Int.natCast_nonneg _
#align rat.sqrt_nonneg Rat.sqrt_nonneg
-/

end Rat

