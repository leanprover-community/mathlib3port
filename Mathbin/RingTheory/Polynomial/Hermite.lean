/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle

! This file was ported from Lean 3 source module ring_theory.polynomial.hermite
! leanprover-community/mathlib commit c6275ef4bef8a44472109311361a0eacae160e1e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Derivative

/-!
# Hermite polynomials

This file defines `polynomial.hermite n`, the nth probabilist's Hermite polynomial.

## Main definitions

* `polynomial.hermite n`: the `n`th probabilist's Hermite polynomial,
  defined recursively as a `polynomial ℤ`

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/


noncomputable section

open Polynomial

namespace Polynomial

/-- the nth probabilist's Hermite polynomial -/
noncomputable def hermite : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => X * hermite n - (hermite n).derivative
#align polynomial.hermite Polynomial.hermite

@[simp]
theorem hermite_succ (n : ℕ) : hermite (n + 1) = X * hermite n - (hermite n).derivative := by
  rw [hermite]
#align polynomial.hermite_succ Polynomial.hermite_succ

theorem hermite_eq_iterate (n : ℕ) : hermite n = ((fun p => X * p - p.derivative)^[n]) 1 :=
  by
  induction' n with n ih
  · rfl
  · rw [Function.iterate_succ_apply', ← ih, hermite_succ]
#align polynomial.hermite_eq_iterate Polynomial.hermite_eq_iterate

@[simp]
theorem hermite_zero : hermite 0 = C 1 :=
  rfl
#align polynomial.hermite_zero Polynomial.hermite_zero

@[simp]
theorem hermite_one : hermite 1 = X :=
  by
  rw [hermite_succ, hermite_zero]
  simp only [map_one, mul_one, derivative_one, sub_zero]
#align polynomial.hermite_one Polynomial.hermite_one

end Polynomial

