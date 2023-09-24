/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Algebra.DualNumber
import Data.Matrix.Basic

#align_import data.matrix.dual_number from "leanprover-community/mathlib"@"d64d67d000b974f0d86a2be7918cf800be6271c8"

/-!
# Matrices of dual numbers are isomorphic to dual numbers over matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Showing this for the more general case of `triv_sq_zero_ext R M` would require an action between
`matrix n n R` and `matrix n n M`, which would risk causing diamonds.
-/


variable {R n : Type} [CommSemiring R] [Fintype n] [DecidableEq n]

open Matrix TrivSqZeroExt

#print Matrix.dualNumberEquiv /-
/-- Matrices over dual numbers and dual numbers over matrices are isomorphic. -/
@[simps]
def Matrix.dualNumberEquiv : Matrix n n (DualNumber R) ≃ₐ[R] DualNumber (Matrix n n R)
    where
  toFun A := ⟨of fun i j => (A i j).fst, of fun i j => (A i j).snd⟩
  invFun d := of fun i j => (d.fst i j, d.snd i j)
  left_inv A := Matrix.ext fun i j => TrivSqZeroExt.ext rfl rfl
  right_inv d := TrivSqZeroExt.ext (Matrix.ext fun i j => rfl) (Matrix.ext fun i j => rfl)
  map_mul' A B := by
    ext <;> dsimp [mul_apply]
    · simp_rw [fst_sum, fst_mul]
    · simp_rw [snd_sum, snd_mul, smul_eq_mul, op_smul_eq_mul, Finset.sum_add_distrib]
  map_add' A B := TrivSqZeroExt.ext rfl rfl
  commutes' r :=
    by
    simp_rw [algebra_map_eq_inl', algebra_map_eq_diagonal, Pi.algebraMap_def,
      Algebra.id.map_eq_self, algebra_map_eq_inl, ← diagonal_map (inl_zero R), map_apply, fst_inl,
      snd_inl]
    rfl
#align matrix.dual_number_equiv Matrix.dualNumberEquiv
-/

