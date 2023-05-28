/-
Copyright (c) 2020 Johan Commelin, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis

! This file was ported from Lean 3 source module data.mv_polynomial.invertible
! leanprover-community/mathlib commit 1dac236edca9b4b6f5f00b1ad831e35f89472837
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.MvPolynomial.Basic
import Mathbin.RingTheory.AlgebraTower

/-!
# Invertible polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is a stub containing some basic facts about
invertible elements in the ring of polynomials.
-/


open MvPolynomial

noncomputable instance MvPolynomial.invertibleC (σ : Type _) {R : Type _} [CommSemiring R] (r : R)
    [Invertible r] : Invertible (C r : MvPolynomial σ R) :=
  Invertible.map (C : R →+* MvPolynomial σ R) _
#align mv_polynomial.invertible_C MvPolynomial.invertibleC

/-- A natural number that is invertible when coerced to a commutative semiring `R`
is also invertible when coerced to any polynomial ring with rational coefficients.

Short-cut for typeclass resolution. -/
noncomputable instance MvPolynomial.invertibleCoeNat (σ R : Type _) (p : ℕ) [CommSemiring R]
    [Invertible (p : R)] : Invertible (p : MvPolynomial σ R) :=
  IsScalarTower.invertibleAlgebraCoeNat R _ _
#align mv_polynomial.invertible_coe_nat MvPolynomial.invertibleCoeNat

