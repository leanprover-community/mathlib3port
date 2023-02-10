/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module order.filter.modeq
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Parity
import Mathbin.Order.Filter.AtTopBot

/-!
# Numbers are frequently modeq to fixed numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that `m ≡ d [MOD n]` frequently as `m → ∞`.
-/


open Filter

namespace Nat

#print Nat.frequently_modEq /-
/-- Infinitely many natural numbers are equal to `d` mod `n`. -/
theorem frequently_modEq {n : ℕ} (h : n ≠ 0) (d : ℕ) : ∃ᶠ m in atTop, m ≡ d [MOD n] :=
  ((tendsto_add_atTop_nat d).comp (tendsto_id.nsmul_atTop h.bot_lt)).Frequently <|
    frequently_of_forall fun m => by simp [Nat.modEq_iff_dvd, ← sub_sub]
#align nat.frequently_modeq Nat.frequently_modEq
-/

#print Nat.frequently_mod_eq /-
theorem frequently_mod_eq {d n : ℕ} (h : d < n) : ∃ᶠ m in atTop, m % n = d := by
  simpa only [Nat.ModEq, mod_eq_of_lt h] using frequently_modeq h.ne_bot d
#align nat.frequently_mod_eq Nat.frequently_mod_eq
-/

#print Nat.frequently_even /-
theorem frequently_even : ∃ᶠ m : ℕ in atTop, Even m := by
  simpa only [even_iff] using frequently_mod_eq zero_lt_two
#align nat.frequently_even Nat.frequently_even
-/

#print Nat.frequently_odd /-
theorem frequently_odd : ∃ᶠ m : ℕ in atTop, Odd m := by
  simpa only [odd_iff] using frequently_mod_eq one_lt_two
#align nat.frequently_odd Nat.frequently_odd
-/

end Nat

