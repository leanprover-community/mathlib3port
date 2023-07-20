/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Algebra.Invertible
import Mathbin.Algebra.CharP.Basic

#align_import algebra.char_p.invertible from "leanprover-community/mathlib"@"10bf4f825ad729c5653adc039dafa3622e7f93c9"

/-!
# Invertibility of elements given a characteristic

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file includes some instances of `invertible` for specific numbers in
characteristic zero. Some more cases are given as a `def`, to be included only
when needed. To construct instances for concrete numbers,
`invertible_of_nonzero` is a useful definition.
-/


variable {K : Type _}

section Field

variable [Field K]

#print invertibleOfRingCharNotDvd /-
/-- A natural number `t` is invertible in a field `K` if the charactistic of `K` does not divide
`t`. -/
def invertibleOfRingCharNotDvd {t : ℕ} (not_dvd : ¬ringChar K ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((ringChar.spec K t).mp h)
#align invertible_of_ring_char_not_dvd invertibleOfRingCharNotDvd
-/

#print not_ringChar_dvd_of_invertible /-
theorem not_ringChar_dvd_of_invertible {t : ℕ} [Invertible (t : K)] : ¬ringChar K ∣ t :=
  by
  rw [← ringChar.spec, ← Ne.def]
  exact nonzero_of_invertible (t : K)
#align not_ring_char_dvd_of_invertible not_ringChar_dvd_of_invertible
-/

#print invertibleOfCharPNotDvd /-
/-- A natural number `t` is invertible in a field `K` of charactistic `p` if `p` does not divide
`t`. -/
def invertibleOfCharPNotDvd {p : ℕ} [CharP K p] {t : ℕ} (not_dvd : ¬p ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((CharP.cast_eq_zero_iff K p t).mp h)
#align invertible_of_char_p_not_dvd invertibleOfCharPNotDvd
-/

#print invertibleOfPos /-
-- warning: this could potentially loop with `ne_zero.invertible` - if there is weird type-class
-- loops, watch out for that.
instance invertibleOfPos [CharZero K] (n : ℕ) [NeZero n] : Invertible (n : K) :=
  invertibleOfNonzero <| NeZero.out
#align invertible_of_pos invertibleOfPos
-/

end Field

section DivisionRing

variable [DivisionRing K] [CharZero K]

#print invertibleSucc /-
instance invertibleSucc (n : ℕ) : Invertible (n.succ : K) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
#align invertible_succ invertibleSucc
-/

/-!
A few `invertible n` instances for small numerals `n`. Feel free to add your own
number when you need its inverse.
-/


#print invertibleTwo /-
instance invertibleTwo : Invertible (2 : K) :=
  invertibleOfNonzero (by exact_mod_cast (by decide : 2 ≠ 0))
#align invertible_two invertibleTwo
-/

#print invertibleThree /-
instance invertibleThree : Invertible (3 : K) :=
  invertibleOfNonzero (by exact_mod_cast (by decide : 3 ≠ 0))
#align invertible_three invertibleThree
-/

end DivisionRing

