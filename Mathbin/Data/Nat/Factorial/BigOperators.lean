/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
import Mathbin.Data.Nat.Factorial.Basic
import Mathbin.Algebra.BigOperators.Order

/-!
# Factorial with big operators

This file contains some lemmas on factorials in combination with big operators.

While in terms of semantics they could be in the `basic.lean` file, importing 
`algebra.big_operators.basic` leads to a cyclic import.

-/


open Nat BigOperators

namespace Nat

variable {α : Type _} (s : Finsetₓ α) (f : α → ℕ)

theorem prod_factorial_pos : 0 < ∏ i in s, (f i)! :=
  Finsetₓ.prod_pos fun i _ => factorial_pos (f i)

theorem prod_factorial_dvd_factorial_sum : (∏ i in s, (f i)!) ∣ (∑ i in s, f i)! := by
  classical
  induction' s using Finsetₓ.induction with a' s' has ih
  · simp only [Finsetₓ.sum_empty, Finsetₓ.prod_empty, factorial]
    
  · simp only [Finsetₓ.prod_insert has, Finsetₓ.sum_insert has]
    refine' dvd_trans (mul_dvd_mul_left (f a')! ih) _
    apply Nat.factorial_mul_factorial_dvd_factorial_add
    

end Nat

