/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module data.zmod.parity
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Parity
import Mathbin.Data.Zmod.Basic

/-!
# Relating parity to natural numbers mod 2

This module provides lemmas relating `zmod 2` to `even` and `odd`.

## Tags

parity, zmod, even, odd
-/


namespace Zmod

theorem eq_zero_iff_even {n : ℕ} : (n : Zmod 2) = 0 ↔ Even n :=
  (CharP.cast_eq_zero_iff (Zmod 2) 2 n).trans even_iff_two_dvd.symm
#align zmod.eq_zero_iff_even Zmod.eq_zero_iff_even

theorem eq_one_iff_odd {n : ℕ} : (n : Zmod 2) = 1 ↔ Odd n := by
  rw [← @Nat.cast_one (Zmod 2), Zmod.eq_iff_modeq_nat, Nat.odd_iff, Nat.Modeq]
  norm_num
#align zmod.eq_one_iff_odd Zmod.eq_one_iff_odd

theorem ne_zero_iff_odd {n : ℕ} : (n : Zmod 2) ≠ 0 ↔ Odd n := by
  constructor <;>
    · contrapose
      simp [eq_zero_iff_even]
#align zmod.ne_zero_iff_odd Zmod.ne_zero_iff_odd

end Zmod

