/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Algebra.Polynomial.Coeff
import Data.Nat.Choose.Basic

#align_import data.nat.choose.vandermonde from "leanprover-community/mathlib"@"69c6a5a12d8a2b159f20933e60115a4f2de62b58"

/-!

# Vandermonde's identity

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove Vandermonde's identity (`nat.add_choose_eq`):
`(m + n).choose k = ∑ (ij : ℕ × ℕ) in antidiagonal k, m.choose ij.1 * n.choose ij.2`

We follow the algebraic proof from
https://en.wikipedia.org/wiki/Vandermonde%27s_identity#Algebraic_proof .

-/


open scoped BigOperators

open Polynomial Finset.Nat

#print Nat.add_choose_eq /-
/-- Vandermonde's identity -/
theorem Nat.add_choose_eq (m n k : ℕ) :
    (m + n).choose k = ∑ ij : ℕ × ℕ in antidiagonal k, m.choose ij.1 * n.choose ij.2 :=
  by
  calc
    (m + n).choose k = ((X + 1) ^ (m + n)).coeff k := _
    _ = ((X + 1) ^ m * (X + 1) ^ n).coeff k := by rw [pow_add]
    _ = ∑ ij : ℕ × ℕ in antidiagonal k, m.choose ij.1 * n.choose ij.2 := _
  · rw [coeff_X_add_one_pow, Nat.cast_id]
  · rw [coeff_mul, Finset.sum_congr rfl]
    simp only [coeff_X_add_one_pow, Nat.cast_id, eq_self_iff_true, imp_true_iff]
#align nat.add_choose_eq Nat.add_choose_eq
-/

