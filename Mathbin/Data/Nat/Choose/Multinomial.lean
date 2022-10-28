/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
import Mathbin.Algebra.BigOperators.Fin
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Data.Nat.Choose.Basic
import Mathbin.Data.Nat.Factorial.BigOperators
import Mathbin.Data.Fin.VecNotation
import Mathbin.Tactic.Linarith.Default

/-!
# Multinomial

This file defines the multinomial coefficient and several small lemma's for manipulating it.

## Main declarations

- `nat.multinomial`: the multinomial coefficient

-/


open BigOperators Nat

namespace Nat

variable {α : Type _} (s : Finset α) (f : α → ℕ)

variable {a b : α}

/-- The multinomial coefficient. Gives the number of strings consisting of symbols
from `s`, where `c ∈ s` appears with multiplicity `f c`.

Defined as `(∑ i in s, f i)! / ∏ i in s, (f i)!`.
-/
def multinomial : ℕ :=
  (∑ i in s, f i)! / ∏ i in s, (f i)!

theorem multinomial_pos : 0 < multinomial s f :=
  Nat.div_pos (le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s f)) (prod_factorial_pos s f)

theorem multinomial_spec : (∏ i in s, (f i)!) * multinomial s f = (∑ i in s, f i)! :=
  Nat.mul_div_cancel' (prod_factorial_dvd_factorial_sum s f)

@[simp]
theorem multinomial_nil : multinomial ∅ f = 1 :=
  rfl

@[simp]
theorem multinomial_singleton : multinomial {a} f = 1 := by simp [multinomial, Nat.div_self (factorial_pos (f a))]

@[simp]
theorem multinomial_insert_one [DecidableEq α] (h : a ∉ s) (h₁ : f a = 1) :
    multinomial (insert a s) f = (s.Sum f).succ * multinomial s f := by
  simp only [multinomial, one_mul, factorial]
  rw [Finset.sum_insert h, Finset.prod_insert h, h₁, add_comm, ← succ_eq_add_one, factorial_succ]
  simp only [factorial_one, one_mul, Function.comp_app, factorial]
  rw [Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _)]

theorem multinomial_insert [DecidableEq α] (h : a ∉ s) :
    multinomial (insert a s) f = (f a + s.Sum f).choose (f a) * multinomial s f := by
  rw [choose_eq_factorial_div_factorial (le.intro rfl)]
  simp only [multinomial, Nat.add_sub_cancel_left, Finset.sum_insert h, Finset.prod_insert h, Function.comp_app]
  rw [div_mul_div_comm ((f a).factorial_mul_factorial_dvd_factorial_add (s.sum f))
      (prod_factorial_dvd_factorial_sum _ _),
    mul_comm (f a)! (s.sum f)!, mul_assoc, mul_comm _ (s.sum f)!, Nat.mul_div_mul _ _ (factorial_pos _)]

/-! ### Connection to binomial coefficients -/


theorem binomial_eq [DecidableEq α] (h : a ≠ b) : multinomial {a, b} f = (f a + f b)! / ((f a)! * (f b)!) := by
  simp [multinomial, Finset.sum_pair h, Finset.prod_pair h]

theorem binomial_eq_choose [DecidableEq α] (h : a ≠ b) : multinomial {a, b} f = (f a + f b).choose (f a) := by
  simp [binomial_eq _ h, choose_eq_factorial_div_factorial (Nat.le_add_right _ _)]

theorem binomial_spec [DecidableEq α] (hab : a ≠ b) : (f a)! * (f b)! * multinomial {a, b} f = (f a + f b)! := by
  simpa [Finset.sum_pair hab, Finset.prod_pair hab] using multinomial_spec {a, b} f

@[simp]
theorem binomial_one [DecidableEq α] (h : a ≠ b) (h₁ : f a = 1) : multinomial {a, b} f = (f b).succ := by
  simp [multinomial_insert_one {b} f (finset.not_mem_singleton.mpr h) h₁]

theorem binomial_succ_succ [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} (Function.update (Function.update f a (f a).succ) b (f b).succ) =
      multinomial {a, b} (Function.update f a (f a).succ) + multinomial {a, b} (Function.update f b (f b).succ) :=
  by
  simp only [binomial_eq_choose, Function.update_apply, Function.update_noteq, succ_add, add_succ, choose_succ_succ, h,
    Ne.def, not_false_iff, Function.update_same]
  rw [if_neg h.symm]
  ring

theorem succ_mul_binomial [DecidableEq α] (h : a ≠ b) :
    (f a + f b).succ * multinomial {a, b} f = (f a).succ * multinomial {a, b} (Function.update f a (f a).succ) := by
  rw [binomial_eq_choose _ h, binomial_eq_choose _ h, mul_comm (f a).succ, Function.update_same,
    Function.update_noteq (ne_comm.mp h)]
  convert succ_mul_choose_eq (f a + f b) (f a)
  exact succ_add (f a) (f b)

/-! ### Simple cases -/


theorem multinomial_univ_two (a b : ℕ) : multinomial Finset.univ ![a, b] = (a + b)! / (a ! * b !) := by
  simp [multinomial, Fin.sum_univ_two, Fin.prod_univ_two]

theorem multinomial_univ_three (a b c : ℕ) : multinomial Finset.univ ![a, b, c] = (a + b + c)! / (a ! * b ! * c !) := by
  simp [multinomial, Fin.sum_univ_three, Fin.prod_univ_three]

end Nat

