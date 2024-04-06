/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Data.Nat.Parity
import Data.ZMod.Basic

#align_import data.zmod.parity from "leanprover-community/mathlib"@"290a7ba01fbcab1b64757bdaa270d28f4dcede35"

/-!
# Relating parity to natural numbers mod 2

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module provides lemmas relating `zmod 2` to `even` and `odd`.

## Tags

parity, zmod, even, odd
-/


namespace ZMod

#print ZMod.eq_zero_iff_even /-
theorem eq_zero_iff_even {n : ℕ} : (n : ZMod 2) = 0 ↔ Even n :=
  (CharP.cast_eq_zero_iff (ZMod 2) 2 n).trans even_iff_two_dvd.symm
#align zmod.eq_zero_iff_even ZMod.eq_zero_iff_even
-/

#print ZMod.eq_one_iff_odd /-
theorem eq_one_iff_odd {n : ℕ} : (n : ZMod 2) = 1 ↔ Odd n := by
  rw [← @Nat.cast_one (ZMod 2), ZMod.eq_iff_modEq_nat, Nat.odd_iff, Nat.ModEq]; norm_num
#align zmod.eq_one_iff_odd ZMod.eq_one_iff_odd
-/

#print ZMod.ne_zero_iff_odd /-
theorem ne_zero_iff_odd {n : ℕ} : (n : ZMod 2) ≠ 0 ↔ Odd n := by
  constructor <;> · contrapose; simp [eq_zero_iff_even]
#align zmod.ne_zero_iff_odd ZMod.ne_zero_iff_odd
-/

end ZMod

