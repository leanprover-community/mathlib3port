/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module linear_algebra.matrix.invariant_basis_number
! leanprover-community/mathlib commit 09597669f02422ed388036273d8848119699c22f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.LinearAlgebra.InvariantBasisNumber

/-!
# Invertible matrices over a ring with invariant basis number are square.
-/


variable {n m : Type _} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

variable {R : Type _} [Semiring R] [InvariantBasisNumber R]

open Matrix

theorem Matrix.square_of_invertible (M : Matrix n m R) (N : Matrix m n R) (h : M ⬝ N = 1)
    (h' : N ⬝ M = 1) : Fintype.card n = Fintype.card m :=
  card_eq_of_lequiv R (Matrix.toLinearEquivRight'OfInv h' h)
#align matrix.square_of_invertible Matrix.square_of_invertible

