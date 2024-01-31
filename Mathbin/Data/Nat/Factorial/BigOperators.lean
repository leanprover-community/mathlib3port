/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
import Data.Nat.Factorial.Basic
import Algebra.BigOperators.Order

#align_import data.nat.factorial.big_operators from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

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
theorem prod_factorial_dvd_factorial_sum : ∏ i in s, (f i)! ∣ (∑ i in s, f i)! := by classical
#align nat.prod_factorial_dvd_factorial_sum Nat.prod_factorial_dvd_factorial_sum
-/

end Nat

