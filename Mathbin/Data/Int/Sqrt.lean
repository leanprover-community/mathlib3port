/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Data.Nat.Sqrt

/-!
# Square root of integers

This file defines the square root function on integers. `int.sqrt z` is the greatest integer `r`
such that `r * r ≤ z`. If `z ≤ 0`, then `int.sqrt z = 0`.
-/


namespace Int

/-- `sqrt z` is the square root of an integer `z`. If `z` is positive, it returns the largest
integer `r` such that `r * r ≤ n`. If it is negative, it returns `0`. For example, `sqrt (-1) = 0`,
`sqrt 1 = 1`, `sqrt 2 = 1` -/
@[pp_nodot]
def sqrt (z : ℤ) : ℤ :=
  Nat.sqrt <| Int.toNat z

theorem sqrt_eq (n : ℤ) : sqrt (n * n) = n.natAbs := by
  rw [sqrt, ← nat_abs_mul_self, to_nat_coe_nat, Nat.sqrt_eq]

theorem exists_mul_self (x : ℤ) : (∃ n, n * n = x) ↔ sqrt x * sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by
    rw [← hn, sqrt_eq, ← Int.coe_nat_mul, nat_abs_mul_self], fun h => ⟨sqrt x, h⟩⟩

theorem sqrt_nonneg (n : ℤ) : 0 ≤ sqrt n :=
  coe_nat_nonneg _

end Int

