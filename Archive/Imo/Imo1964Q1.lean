/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Tactic.IntervalCases
import Data.Nat.ModEq

#align_import imo.imo1964_q1 from "leanprover-community/mathlib"@"08b081ea92d80e3a41f899eea36ef6d56e0f1db0"

/-!
# IMO 1964 Q1

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

(a) Find all positive integers $n$ for which $2^n-1$ is divisible by $7$.

(b) Prove that there is no positive integer $n$ for which $2^n+1$ is divisible by $7$.

We define a predicate for the solutions in (a), and prove that it is the set of positive
integers which are a multiple of 3.
-/


/-!
## Intermediate lemmas
-/


open Nat

namespace Imo1964Q1

theorem two_pow_three_hMul_mod_seven (m : ℕ) : 2 ^ (3 * m) ≡ 1 [MOD 7] :=
  by
  rw [pow_mul]
  have h : 8 ≡ 1 [MOD 7] := modeq_of_dvd (by use-1; norm_num)
  convert h.pow _
  simp
#align imo1964_q1.two_pow_three_mul_mod_seven Imo1964Q1.two_pow_three_hMul_mod_seven

theorem two_pow_three_hMul_add_one_mod_seven (m : ℕ) : 2 ^ (3 * m + 1) ≡ 2 [MOD 7] :=
  by
  rw [pow_add]
  exact (two_pow_three_mul_mod_seven m).mulRight _
#align imo1964_q1.two_pow_three_mul_add_one_mod_seven Imo1964Q1.two_pow_three_hMul_add_one_mod_seven

theorem two_pow_three_hMul_add_two_mod_seven (m : ℕ) : 2 ^ (3 * m + 2) ≡ 4 [MOD 7] :=
  by
  rw [pow_add]
  exact (two_pow_three_mul_mod_seven m).mulRight _
#align imo1964_q1.two_pow_three_mul_add_two_mod_seven Imo1964Q1.two_pow_three_hMul_add_two_mod_seven

/-!
## The question
-/


def ProblemPredicate (n : ℕ) : Prop :=
  7 ∣ 2 ^ n - 1
#align imo1964_q1.problem_predicate Imo1964Q1.ProblemPredicate

theorem aux (n : ℕ) : ProblemPredicate n ↔ 2 ^ n ≡ 1 [MOD 7] :=
  by
  rw [Nat.ModEq.comm]
  apply (modeq_iff_dvd' _).symm
  apply Nat.one_le_pow'
#align imo1964_q1.aux Imo1964Q1.aux

theorem imo1964_q1a (n : ℕ) (hn : 0 < n) : ProblemPredicate n ↔ 3 ∣ n :=
  by
  rw [aux]
  constructor
  · intro h
    let t := n % 3
    rw [show n = 3 * (n / 3) + t from (Nat.div_add_mod n 3).symm] at h
    have ht : t < 3 := Nat.mod_lt _ (by decide)
    interval_cases hr : t <;> rw [hr] at h
    · exact Nat.dvd_of_mod_eq_zero hr
    · exfalso
      have nonsense := (two_pow_three_mul_add_one_mod_seven _).symm.trans h
      rw [modeq_iff_dvd] at nonsense
      norm_num at nonsense
    · exfalso
      have nonsense := (two_pow_three_mul_add_two_mod_seven _).symm.trans h
      rw [modeq_iff_dvd] at nonsense
      norm_num at nonsense
  · rintro ⟨m, rfl⟩
    apply two_pow_three_mul_mod_seven
#align imo1964_q1.imo1964_q1a Imo1964Q1.imo1964_q1a

end Imo1964Q1

open Imo1964Q1

theorem imo1964_q1b (n : ℕ) : ¬7 ∣ 2 ^ n + 1 :=
  by
  let t := n % 3
  rw [← modeq_zero_iff_dvd, show n = 3 * (n / 3) + t from (Nat.div_add_mod n 3).symm]
  have ht : t < 3 := Nat.mod_lt _ (by decide)
  interval_cases hr : t <;> rw [hr]
  · rw [add_zero]
    intro h
    have := h.symm.trans ((two_pow_three_mul_mod_seven _).addRight _)
    rw [modeq_iff_dvd] at this
    norm_num at this
  · intro h
    have := h.symm.trans ((two_pow_three_mul_add_one_mod_seven _).addRight _)
    rw [modeq_iff_dvd] at this
    norm_num at this
  · intro h
    have := h.symm.trans ((two_pow_three_mul_add_two_mod_seven _).addRight _)
    rw [modeq_iff_dvd] at this
    norm_num at this
#align imo1964_q1b imo1964_q1b

