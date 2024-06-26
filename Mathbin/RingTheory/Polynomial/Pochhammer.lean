/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Tactic.Abel
import Algebra.Polynomial.Eval

#align_import ring_theory.polynomial.pochhammer from "leanprover-community/mathlib"@"69c6a5a12d8a2b159f20933e60115a4f2de62b58"

/-!
# The Pochhammer polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define and prove some basic relations about
`pochhammer S n : S[X] := X * (X + 1) * ... * (X + n - 1)`
which is also known as the rising factorial. A version of this definition
that is focused on `nat` can be found in `data.nat.factorial` as `nat.asc_factorial`.

## Implementation

As with many other families of polynomials, even though the coefficients are always in `ℕ`,
we define the polynomial with coefficients in any `[semiring S]`.

## TODO

There is lots more in this direction:
* q-factorials, q-binomials, q-Pochhammer.
-/


universe u v

open Polynomial

open scoped Polynomial

section Semiring

variable (S : Type u) [Semiring S]

#print ascPochhammer /-
/-- `pochhammer S n` is the polynomial `X * (X+1) * ... * (X + n - 1)`,
with coefficients in the semiring `S`.
-/
noncomputable def ascPochhammer : ℕ → S[X]
  | 0 => 1
  | n + 1 => X * (ascPochhammer n).comp (X + 1)
#align pochhammer ascPochhammer
-/

#print ascPochhammer_zero /-
@[simp]
theorem ascPochhammer_zero : ascPochhammer S 0 = 1 :=
  rfl
#align pochhammer_zero ascPochhammer_zero
-/

#print ascPochhammer_one /-
@[simp]
theorem ascPochhammer_one : ascPochhammer S 1 = X := by simp [ascPochhammer]
#align pochhammer_one ascPochhammer_one
-/

#print ascPochhammer_succ_left /-
theorem ascPochhammer_succ_left (n : ℕ) :
    ascPochhammer S (n + 1) = X * (ascPochhammer S n).comp (X + 1) := by rw [ascPochhammer]
#align pochhammer_succ_left ascPochhammer_succ_left
-/

section

variable {S} {T : Type v} [Semiring T]

#print ascPochhammer_map /-
@[simp]
theorem ascPochhammer_map (f : S →+* T) (n : ℕ) : (ascPochhammer S n).map f = ascPochhammer T n :=
  by
  induction' n with n ih
  · simp
  · simp [ih, ascPochhammer_succ_left, map_comp]
#align pochhammer_map ascPochhammer_map
-/

end

#print ascPochhammer_eval_cast /-
@[simp, norm_cast]
theorem ascPochhammer_eval_cast (n k : ℕ) :
    ((ascPochhammer ℕ n).eval k : S) = (ascPochhammer S n).eval k := by
  rw [← ascPochhammer_map (algebraMap ℕ S), eval_map, ← eq_natCast (algebraMap ℕ S),
    eval₂_at_nat_cast, Nat.cast_id, eq_natCast]
#align pochhammer_eval_cast ascPochhammer_eval_cast
-/

#print ascPochhammer_eval_zero /-
theorem ascPochhammer_eval_zero {n : ℕ} : (ascPochhammer S n).eval 0 = if n = 0 then 1 else 0 :=
  by
  cases n
  · simp
  · simp [X_mul, Nat.succ_ne_zero, ascPochhammer_succ_left]
#align pochhammer_eval_zero ascPochhammer_eval_zero
-/

#print ascPochhammer_zero_eval_zero /-
theorem ascPochhammer_zero_eval_zero : (ascPochhammer S 0).eval 0 = 1 := by simp
#align pochhammer_zero_eval_zero ascPochhammer_zero_eval_zero
-/

#print ascPochhammer_ne_zero_eval_zero /-
@[simp]
theorem ascPochhammer_ne_zero_eval_zero {n : ℕ} (h : n ≠ 0) : (ascPochhammer S n).eval 0 = 0 := by
  simp [ascPochhammer_eval_zero, h]
#align pochhammer_ne_zero_eval_zero ascPochhammer_ne_zero_eval_zero
-/

#print ascPochhammer_succ_right /-
theorem ascPochhammer_succ_right (n : ℕ) : ascPochhammer S (n + 1) = ascPochhammer S n * (X + n) :=
  by
  suffices h : ascPochhammer ℕ (n + 1) = ascPochhammer ℕ n * (X + n)
  · apply_fun Polynomial.map (algebraMap ℕ S) at h
    simpa only [ascPochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_natCast] using h
  induction' n with n ih
  · simp
  ·
    conv_lhs =>
      rw [ascPochhammer_succ_left, ih, mul_comp, ← mul_assoc, ← ascPochhammer_succ_left, add_comp,
        X_comp, nat_cast_comp, add_assoc, add_comm (1 : ℕ[X]), ← Nat.cast_succ]
#align pochhammer_succ_right ascPochhammer_succ_right
-/

#print ascPochhammer_succ_eval /-
theorem ascPochhammer_succ_eval {S : Type _} [Semiring S] (n : ℕ) (k : S) :
    (ascPochhammer S (n + 1)).eval k = (ascPochhammer S n).eval k * (k + n) := by
  rw [ascPochhammer_succ_right, mul_add, eval_add, eval_mul_X, ← Nat.cast_comm, ← C_eq_nat_cast,
    eval_C_mul, Nat.cast_comm, ← mul_add]
#align pochhammer_succ_eval ascPochhammer_succ_eval
-/

#print ascPochhammer_succ_comp_X_add_one /-
theorem ascPochhammer_succ_comp_X_add_one (n : ℕ) :
    (ascPochhammer S (n + 1)).comp (X + 1) =
      ascPochhammer S (n + 1) + (n + 1) • (ascPochhammer S n).comp (X + 1) :=
  by
  suffices
    (ascPochhammer ℕ (n + 1)).comp (X + 1) =
      ascPochhammer ℕ (n + 1) + (n + 1) * (ascPochhammer ℕ n).comp (X + 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Nat.castRingHom S)) this
  nth_rw 2 [ascPochhammer_succ_left]
  rw [← add_mul, ascPochhammer_succ_right ℕ n, mul_comp, mul_comm, add_comp, X_comp, nat_cast_comp,
    add_comm ↑n, ← add_assoc]
#align pochhammer_succ_comp_X_add_one ascPochhammer_succ_comp_X_add_one
-/

#print Polynomial.mul_X_add_natCast_comp /-
theorem Polynomial.mul_X_add_natCast_comp {p q : S[X]} {n : ℕ} :
    (p * (X + n)).comp q = p.comp q * (q + n) := by
  rw [mul_add, add_comp, mul_X_comp, ← Nat.cast_comm, nat_cast_mul_comp, Nat.cast_comm, mul_add]
#align polynomial.mul_X_add_nat_cast_comp Polynomial.mul_X_add_natCast_comp
-/

#print ascPochhammer_mul /-
theorem ascPochhammer_mul (n m : ℕ) :
    ascPochhammer S n * (ascPochhammer S m).comp (X + n) = ascPochhammer S (n + m) :=
  by
  induction' m with m ih
  · simp
  ·
    rw [ascPochhammer_succ_right, Polynomial.mul_X_add_natCast_comp, ← mul_assoc, ih,
      Nat.succ_eq_add_one, ← add_assoc, ascPochhammer_succ_right, Nat.cast_add, add_assoc]
#align pochhammer_mul ascPochhammer_mul
-/

#print ascPochhammer_nat_eq_ascFactorial /-
theorem ascPochhammer_nat_eq_ascFactorial (n : ℕ) :
    ∀ k, (ascPochhammer ℕ k).eval (n + 1) = n.ascFactorial k
  | 0 => by erw [eval_one] <;> rfl
  | t + 1 =>
    by
    rw [ascPochhammer_succ_right, eval_mul, ascPochhammer_nat_eq_ascFactorial t]
    suffices n.asc_factorial t * (n + 1 + t) = n.asc_factorial (t + 1) by simpa
    rw [Nat.ascFactorial_succ, add_right_comm, mul_comm]
#align pochhammer_nat_eq_asc_factorial ascPochhammer_nat_eq_ascFactorial
-/

#print ascPochhammer_nat_eq_descFactorial /-
theorem ascPochhammer_nat_eq_descFactorial (a b : ℕ) :
    (ascPochhammer ℕ b).eval a = (a + b - 1).descFactorial b :=
  by
  cases b
  · rw [Nat.descFactorial_zero, ascPochhammer_zero, Polynomial.eval_one]
  rw [Nat.add_succ, Nat.succ_sub_succ, tsub_zero]
  cases a
  ·
    rw [ascPochhammer_ne_zero_eval_zero _ b.succ_ne_zero, zero_add,
      Nat.descFactorial_of_lt b.lt_succ_self]
  ·
    rw [Nat.succ_add, ← Nat.add_succ, Nat.add_descFactorial_eq_ascFactorial,
      ascPochhammer_nat_eq_ascFactorial]
#align pochhammer_nat_eq_desc_factorial ascPochhammer_nat_eq_descFactorial
-/

end Semiring

section StrictOrderedSemiring

variable {S : Type _} [StrictOrderedSemiring S]

#print ascPochhammer_pos /-
theorem ascPochhammer_pos (n : ℕ) (s : S) (h : 0 < s) : 0 < (ascPochhammer S n).eval s :=
  by
  induction' n with n ih
  · simp only [Nat.zero_eq, ascPochhammer_zero, eval_one]; exact zero_lt_one
  · rw [ascPochhammer_succ_right, mul_add, eval_add, ← Nat.cast_comm, eval_nat_cast_mul, eval_mul_X,
      Nat.cast_comm, ← mul_add]
    exact mul_pos ih (lt_of_lt_of_le h ((le_add_iff_nonneg_right _).mpr (Nat.cast_nonneg n)))
#align pochhammer_pos ascPochhammer_pos
-/

end StrictOrderedSemiring

section Factorial

open scoped Nat

variable (S : Type _) [Semiring S] (r n : ℕ)

#print ascPochhammer_eval_one /-
@[simp]
theorem ascPochhammer_eval_one (S : Type _) [Semiring S] (n : ℕ) :
    (ascPochhammer S n).eval (1 : S) = (n ! : S) := by
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.zero_ascFactorial]
#align pochhammer_eval_one ascPochhammer_eval_one
-/

#print factorial_mul_ascPochhammer /-
theorem factorial_mul_ascPochhammer (S : Type _) [Semiring S] (r n : ℕ) :
    (r ! : S) * (ascPochhammer S n).eval (r + 1) = (r + n)! := by
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.factorial_mul_ascFactorial]
#align factorial_mul_pochhammer factorial_mul_ascPochhammer
-/

#print ascPochhammer_nat_eval_succ /-
theorem ascPochhammer_nat_eval_succ (r : ℕ) :
    ∀ n : ℕ, n * (ascPochhammer ℕ r).eval (n + 1) = (n + r) * (ascPochhammer ℕ r).eval n
  | 0 => by
    by_cases h : r = 0
    · simp only [h, MulZeroClass.zero_mul, zero_add]
    · simp only [ascPochhammer_eval_zero, MulZeroClass.zero_mul, if_neg h, MulZeroClass.mul_zero]
  | k + 1 => by simp only [ascPochhammer_nat_eq_ascFactorial, Nat.succ_ascFactorial, add_right_comm]
#align pochhammer_nat_eval_succ ascPochhammer_nat_eval_succ
-/

#print ascPochhammer_eval_succ /-
theorem ascPochhammer_eval_succ (r n : ℕ) :
    (n : S) * (ascPochhammer S r).eval (n + 1 : S) = (n + r) * (ascPochhammer S r).eval n := by
  exact_mod_cast congr_arg Nat.cast (ascPochhammer_nat_eval_succ r n)
#align pochhammer_eval_succ ascPochhammer_eval_succ
-/

end Factorial

