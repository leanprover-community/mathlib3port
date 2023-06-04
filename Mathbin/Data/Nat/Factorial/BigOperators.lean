/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte

! This file was ported from Lean 3 source module data.nat.factorial.big_operators
! leanprover-community/mathlib commit 327c3c0d9232d80e250dc8f65e7835b82b266ea5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Factorial.Basic
import Mathbin.Algebra.BigOperators.Order

/-!
# Factorial with big operators

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some lemmas on factorials in combination with big operators.

While in terms of semantics they could be in the `basic.lean` file, importing 
`algebra.big_operators.basic` leads to a cyclic import.

-/


open scoped Nat BigOperators

namespace Nat

variable {α : Type _} (s : Finset α) (f : α → ℕ)

#print Nat.prod_factorial_pos /-
theorem prod_factorial_pos : 0 < ∏ i in s, (f i)! :=
  Finset.prod_pos fun i _ => factorial_pos (f i)
#align nat.prod_factorial_pos Nat.prod_factorial_pos
-/

#print Nat.prod_factorial_dvd_factorial_sum /-
theorem prod_factorial_dvd_factorial_sum : (∏ i in s, (f i)!) ∣ (∑ i in s, f i)! := by
  classical
  induction' s using Finset.induction with a' s' has ih
  · simp only [Finset.sum_empty, Finset.prod_empty, factorial]
  · simp only [Finset.prod_insert has, Finset.sum_insert has]
    refine' dvd_trans (mul_dvd_mul_left (f a')! ih) _
    apply Nat.factorial_mul_factorial_dvd_factorial_add
#align nat.prod_factorial_dvd_factorial_sum Nat.prod_factorial_dvd_factorial_sum
-/

end Nat

