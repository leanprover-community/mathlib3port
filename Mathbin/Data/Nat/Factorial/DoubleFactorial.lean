/-
Copyright (c) 2023 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson

! This file was ported from Lean 3 source module data.nat.factorial.double_factorial
! leanprover-community/mathlib commit 33c67ae661dd8988516ff7f247b0be3018cdd952
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Factorial.Basic
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Tactic.Ring

/-!
# Double factorials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the double factorial,
  `n‼ := n * (n - 2) * (n - 4) * ...`.

## Main declarations

* `nat.double_factorial`: The double factorial.
-/


open scoped Nat

namespace Nat

#print Nat.doubleFactorial /-
/-- `nat.double_factorial n` is the double factorial of `n`. -/
@[simp]
def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | k + 2 => (k + 2) * double_factorial k
#align nat.double_factorial Nat.doubleFactorial
-/

-- mathport name: nat.double_factorial
-- This notation is `\!!` not two !'s
scoped notation:10000 n "‼" => Nat.doubleFactorial n

#print Nat.doubleFactorial_add_two /-
theorem doubleFactorial_add_two (n : ℕ) : (n + 2)‼ = (n + 2) * n‼ :=
  rfl
#align nat.double_factorial_add_two Nat.doubleFactorial_add_two
-/

#print Nat.doubleFactorial_add_one /-
theorem doubleFactorial_add_one (n : ℕ) : (n + 1)‼ = (n + 1) * (n - 1)‼ := by cases n <;> rfl
#align nat.double_factorial_add_one Nat.doubleFactorial_add_one
-/

#print Nat.factorial_eq_mul_doubleFactorial /-
theorem factorial_eq_mul_doubleFactorial : ∀ n : ℕ, (n + 1)! = (n + 1)‼ * n‼
  | 0 => rfl
  | k + 1 => by
    rw [double_factorial_add_two, factorial, factorial_eq_mul_double_factorial, mul_comm _ k‼,
      mul_assoc]
#align nat.factorial_eq_mul_double_factorial Nat.factorial_eq_mul_doubleFactorial
-/

#print Nat.doubleFactorial_two_mul /-
theorem doubleFactorial_two_mul : ∀ n : ℕ, (2 * n)‼ = 2 ^ n * n !
  | 0 => rfl
  | n + 1 =>
    by
    rw [mul_add, mul_one, double_factorial_add_two, factorial, pow_succ, double_factorial_two_mul,
      succ_eq_add_one]
    ring
#align nat.double_factorial_two_mul Nat.doubleFactorial_two_mul
-/

open scoped BigOperators

#print Nat.doubleFactorial_eq_prod_even /-
theorem doubleFactorial_eq_prod_even : ∀ n : ℕ, (2 * n)‼ = ∏ i in Finset.range n, 2 * (i + 1)
  | 0 => rfl
  | n + 1 =>
    by
    rw [Finset.prod_range_succ, ← double_factorial_eq_prod_even, mul_comm (2 * n)‼,
      (by ring : 2 * (n + 1) = 2 * n + 2)]
    rfl
#align nat.double_factorial_eq_prod_even Nat.doubleFactorial_eq_prod_even
-/

#print Nat.doubleFactorial_eq_prod_odd /-
theorem doubleFactorial_eq_prod_odd : ∀ n : ℕ, (2 * n + 1)‼ = ∏ i in Finset.range n, 2 * (i + 1) + 1
  | 0 => rfl
  | n + 1 =>
    by
    rw [Finset.prod_range_succ, ← double_factorial_eq_prod_odd, mul_comm (2 * n + 1)‼,
      (by ring : 2 * (n + 1) + 1 = 2 * n + 1 + 2)]
    rfl
#align nat.double_factorial_eq_prod_odd Nat.doubleFactorial_eq_prod_odd
-/

end Nat

