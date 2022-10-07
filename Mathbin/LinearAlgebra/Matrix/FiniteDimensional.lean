/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.LinearAlgebra.FiniteDimensional

/-!
# The finite-dimensional space of matrices

This file shows that `m` by `n` matrices form a finite-dimensional space,
and proves the `finrank` of that space is equal to `card m * card n`.

## Main definitions

 * `matrix.finite_dimensional`: matrices form a finite dimensional vector space over a field `K`
 * `matrix.finrank_matrix`: the `finrank` of `matrix m n R` is `card m * card n`

## Tags

matrix, finite dimensional, findim, finrank

-/


universe u v

namespace Matrix

section FiniteDimensional

variable {m n : Type _} {R : Type v} [Field R]

instance [Finite m] [Finite n] : FiniteDimensional R (Matrix m n R) :=
  LinearEquiv.finite_dimensional (LinearEquiv.curry R m n)

/-- The dimension of the space of finite dimensional matrices
is the product of the number of rows and columns.
-/
@[simp]
theorem finrank_matrix [Fintypeₓ m] [Fintypeₓ n] :
    FiniteDimensional.finrank R (Matrix m n R) = Fintypeₓ.card m * Fintypeₓ.card n := by
  rw [@LinearEquiv.finrank_eq R (Matrix m n R) _ _ _ _ _ _ (LinearEquiv.curry R m n).symm,
    FiniteDimensional.finrank_fintype_fun_eq_card, Fintypeₓ.card_prod]

end FiniteDimensional

end Matrix

