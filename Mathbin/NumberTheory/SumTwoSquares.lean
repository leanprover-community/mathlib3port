/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module number_theory.sum_two_squares
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.NumberTheory.Zsqrtd.GaussianInt

/-!
# Sums of two squares

Proof of Fermat's theorem on the sum of two squares. Every prime congruent to 1 mod 4 is the sum
of two squares.

# Todo

Fully characterize the natural numbers that are the sum of two squares: those such that for every
prime p congruent to 3 mod 4, the largest power of p dividing them is even.
-/


open GaussianInt

/-- **Fermat's theorem on the sum of two squares**. Every prime congruent to 1 mod 4 is the sum
of two squares. Also known as **Fermat's Christmas theorem**. -/
theorem Nat.Prime.sq_add_sq {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  by
  apply sq_add_sq_of_nat_prime_of_not_irreducible p
  rw [PrincipalIdealRing.irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime p, hp]
  norm_num
#align nat.prime.sq_add_sq Nat.Prime.sq_add_sq

