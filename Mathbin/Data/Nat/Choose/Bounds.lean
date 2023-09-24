/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Rodriguez
-/
import Algebra.GroupPower.Lemmas
import Algebra.Order.Field.Basic
import Data.Nat.Choose.Basic

#align_import data.nat.choose.bounds from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Inequalities for binomial coefficients

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves exponential bounds on binomial coefficients. We might want to add here the
bounds `n^r/r^r ≤ n.choose r ≤ e^r n^r/r^r` in the future.

## Main declarations

* `nat.choose_le_pow`: `n.choose r ≤ n^r / r!`
* `nat.pow_le_choose`: `(n + 1 - r)^r / r! ≤ n.choose r`. Beware of the fishy ℕ-subtraction.
-/


open scoped Nat

variable {α : Type _} [LinearOrderedSemifield α]

namespace Nat

#print Nat.choose_le_pow /-
theorem choose_le_pow (r n : ℕ) : (n.choose r : α) ≤ n ^ r / r ! :=
  by
  rw [le_div_iff']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.desc_factorial_le_pow r
  exact_mod_cast r.factorial_pos
#align nat.choose_le_pow Nat.choose_le_pow
-/

#print Nat.pow_le_choose /-
-- horrific casting is due to ℕ-subtraction
theorem pow_le_choose (r n : ℕ) : ((n + 1 - r : ℕ) ^ r : α) / r ! ≤ n.choose r :=
  by
  rw [div_le_iff']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.pow_sub_le_desc_factorial r
  exact_mod_cast r.factorial_pos
#align nat.pow_le_choose Nat.pow_le_choose
-/

end Nat

