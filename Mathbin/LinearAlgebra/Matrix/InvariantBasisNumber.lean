/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LinearAlgebra.Matrix.ToLin
import LinearAlgebra.InvariantBasisNumber

#align_import linear_algebra.matrix.invariant_basis_number from "leanprover-community/mathlib"@"f2b757fc5c341d88741b9c4630b1e8ba973c5726"

/-!
# Invertible matrices over a ring with invariant basis number are square.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {n m : Type _} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

variable {R : Type _} [Semiring R] [InvariantBasisNumber R]

open scoped Matrix

#print Matrix.square_of_invertible /-
theorem Matrix.square_of_invertible (M : Matrix n m R) (N : Matrix m n R) (h : M ⬝ N = 1)
    (h' : N ⬝ M = 1) : Fintype.card n = Fintype.card m :=
  card_eq_of_linearEquiv R (Matrix.toLinearEquivRight'OfInv h' h)
#align matrix.square_of_invertible Matrix.square_of_invertible
-/

