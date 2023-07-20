/-
Copyright (c) 2020 Johan Commelin, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathbin.Data.MvPolynomial.Basic
import Mathbin.RingTheory.AlgebraTower

#align_import data.mv_polynomial.invertible from "leanprover-community/mathlib"@"1dac236edca9b4b6f5f00b1ad831e35f89472837"

/-!
# Invertible polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is a stub containing some basic facts about
invertible elements in the ring of polynomials.
-/


open MvPolynomial

#print MvPolynomial.invertibleC /-
noncomputable instance MvPolynomial.invertibleC (σ : Type _) {R : Type _} [CommSemiring R] (r : R)
    [Invertible r] : Invertible (C r : MvPolynomial σ R) :=
  Invertible.map (C : R →+* MvPolynomial σ R) _
#align mv_polynomial.invertible_C MvPolynomial.invertibleC
-/

#print MvPolynomial.invertibleCoeNat /-
/-- A natural number that is invertible when coerced to a commutative semiring `R`
is also invertible when coerced to any polynomial ring with rational coefficients.

Short-cut for typeclass resolution. -/
noncomputable instance MvPolynomial.invertibleCoeNat (σ R : Type _) (p : ℕ) [CommSemiring R]
    [Invertible (p : R)] : Invertible (p : MvPolynomial σ R) :=
  IsScalarTower.invertibleAlgebraCoeNat R _ _
#align mv_polynomial.invertible_coe_nat MvPolynomial.invertibleCoeNat
-/

