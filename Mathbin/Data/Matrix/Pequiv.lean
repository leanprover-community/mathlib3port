/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.matrix.pequiv
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.Data.Pequiv

/-!
# partial equivalences for matrices

Using partial equivalences to represent matrices.
This file introduces the function `pequiv.to_matrix`, which returns a matrix containing ones and
zeros. For any partial equivalence `f`, `f.to_matrix i j = 1 ↔ f i = some j`.

The following important properties of this function are proved
`to_matrix_trans : (f.trans g).to_matrix = f.to_matrix ⬝ g.to_matrix`
`to_matrix_symm  : f.symm.to_matrix = f.to_matrixᵀ`
`to_matrix_refl : (pequiv.refl n).to_matrix = 1`
`to_matrix_bot : ⊥.to_matrix = 0`

This theory gives the matrix representation of projection linear maps, and their right inverses.
For example, the matrix `(single (0 : fin 1) (i : fin n)).to_matrix` corresponds to the ith
projection map from R^n to R.

Any injective function `fin m → fin n` gives rise to a `pequiv`, whose matrix is the projection
map from R^m → R^n represented by the same function. The transpose of this matrix is the right
inverse of this map, sending anything not in the image to zero.

## notations

This file uses the notation ` ⬝ ` for `matrix.mul` and `ᵀ` for `matrix.transpose`.
-/


namespace PEquiv

open Matrix

universe u v

variable {k l m n : Type _}

variable {α : Type v}

open Matrix

/- warning: pequiv.to_matrix -> PEquiv.toMatrix is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α], (PEquiv.{u2, u3} m n) -> (Matrix.{u2, u3, u1} m n α)
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u3} α] [_inst_3 : One.{u3} α], (PEquiv.{u1, u2} m n) -> (Matrix.{u1, u2, u3} m n α)
Case conversion may be inaccurate. Consider using '#align pequiv.to_matrix PEquiv.toMatrixₓ'. -/
/-- `to_matrix` returns a matrix containing ones and zeros. `f.to_matrix i j` is `1` if
  `f i = some j` and `0` otherwise -/
def toMatrix [DecidableEq n] [Zero α] [One α] (f : m ≃. n) : Matrix m n α
  | i, j => if j ∈ f i then 1 else 0
#align pequiv.to_matrix PEquiv.toMatrix

theorem mul_matrix_apply [Fintype m] [DecidableEq m] [Semiring α] (f : l ≃. m) (M : Matrix m n α)
    (i j) : (f.toMatrix ⬝ M) i j = Option.casesOn (f i) 0 fun fi => M fi j :=
  by
  dsimp [to_matrix, Matrix.mul_apply]
  cases' h : f i with fi
  · simp [h]
  · rw [Finset.sum_eq_single fi] <;> simp (config := { contextual := true }) [h, eq_comm]
#align pequiv.mul_matrix_apply PEquiv.mul_matrix_apply

theorem toMatrix_symm [DecidableEq m] [DecidableEq n] [Zero α] [One α] (f : m ≃. n) :
    (f.symm.toMatrix : Matrix n m α) = f.toMatrixᵀ := by
  ext <;> simp only [transpose, mem_iff_mem f, to_matrix] <;> congr
#align pequiv.to_matrix_symm PEquiv.toMatrix_symm

@[simp]
theorem toMatrix_refl [DecidableEq n] [Zero α] [One α] :
    ((PEquiv.refl n).toMatrix : Matrix n n α) = 1 := by
  ext <;> simp [to_matrix, one_apply] <;> congr
#align pequiv.to_matrix_refl PEquiv.toMatrix_refl

theorem matrix_mul_apply [Fintype m] [Semiring α] [DecidableEq n] (M : Matrix l m α) (f : m ≃. n)
    (i j) : (M ⬝ f.toMatrix) i j = Option.casesOn (f.symm j) 0 fun fj => M i fj :=
  by
  dsimp [to_matrix, Matrix.mul_apply]
  cases' h : f.symm j with fj
  · simp [h, ← f.eq_some_iff]
  · rw [Finset.sum_eq_single fj]
    · simp [h, ← f.eq_some_iff]
    · intro b H n
      simp [h, ← f.eq_some_iff, n.symm]
    · simp
#align pequiv.matrix_mul_apply PEquiv.matrix_mul_apply

theorem toPEquiv_mul_matrix [Fintype m] [DecidableEq m] [Semiring α] (f : m ≃ m)
    (M : Matrix m n α) : f.toPequiv.toMatrix ⬝ M = fun i => M (f i) :=
  by
  ext (i j)
  rw [mul_matrix_apply, Equiv.toPEquiv_apply]
#align pequiv.to_pequiv_mul_matrix PEquiv.toPEquiv_mul_matrix

theorem mul_toPEquiv_toMatrix {m n α : Type _} [Fintype n] [DecidableEq n] [Semiring α] (f : n ≃ n)
    (M : Matrix m n α) : M ⬝ f.toPequiv.toMatrix = M.submatrix id f.symm :=
  Matrix.ext fun i j => by
    rw [PEquiv.matrix_mul_apply, ← Equiv.toPEquiv_symm, Equiv.toPEquiv_apply,
      Matrix.submatrix_apply, id.def]
#align pequiv.mul_to_pequiv_to_matrix PEquiv.mul_toPEquiv_toMatrix

theorem toMatrix_trans [Fintype m] [DecidableEq m] [DecidableEq n] [Semiring α] (f : l ≃. m)
    (g : m ≃. n) : ((f.trans g).toMatrix : Matrix l n α) = f.toMatrix ⬝ g.toMatrix :=
  by
  ext (i j)
  rw [mul_matrix_apply]
  dsimp [to_matrix, PEquiv.trans]
  cases f i <;> simp
#align pequiv.to_matrix_trans PEquiv.toMatrix_trans

@[simp]
theorem toMatrix_bot [DecidableEq n] [Zero α] [One α] :
    ((⊥ : PEquiv m n).toMatrix : Matrix m n α) = 0 :=
  rfl
#align pequiv.to_matrix_bot PEquiv.toMatrix_bot

theorem toMatrix_injective [DecidableEq n] [MonoidWithZero α] [Nontrivial α] :
    Function.Injective (@toMatrix m n α _ _ _) := by
  classical
    intro f g
    refine' not_imp_not.1 _
    simp only [matrix.ext_iff.symm, to_matrix, PEquiv.ext_iff, not_forall, exists_imp]
    intro i hi
    use i
    cases' hf : f i with fi
    · cases' hg : g i with gi
      · cc
      · use gi
        simp
    · use fi
      simp [hf.symm, Ne.symm hi]
#align pequiv.to_matrix_injective PEquiv.toMatrix_injective

theorem toMatrix_swap [DecidableEq n] [Ring α] (i j : n) :
    (Equiv.swap i j).toPequiv.toMatrix =
      (1 : Matrix n n α) - (single i i).toMatrix - (single j j).toMatrix + (single i j).toMatrix +
        (single j i).toMatrix :=
  by
  ext
  dsimp [to_matrix, single, Equiv.swap_apply_def, Equiv.toPEquiv, one_apply]
  split_ifs <;>
    first
      |· simp_all|·
        exfalso
        assumption
#align pequiv.to_matrix_swap PEquiv.toMatrix_swap

@[simp]
theorem single_mul_single [Fintype n] [DecidableEq k] [DecidableEq m] [DecidableEq n] [Semiring α]
    (a : m) (b : n) (c : k) :
    ((single a b).toMatrix : Matrix _ _ α) ⬝ (single b c).toMatrix = (single a c).toMatrix := by
  rw [← to_matrix_trans, single_trans_single]
#align pequiv.single_mul_single PEquiv.single_mul_single

theorem single_mul_single_of_ne [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m]
    [Semiring α] {b₁ b₂ : n} (hb : b₁ ≠ b₂) (a : m) (c : k) :
    ((single a b₁).toMatrix : Matrix _ _ α) ⬝ (single b₂ c).toMatrix = 0 := by
  rw [← to_matrix_trans, single_trans_single_of_ne hb, to_matrix_bot]
#align pequiv.single_mul_single_of_ne PEquiv.single_mul_single_of_ne

/-- Restatement of `single_mul_single`, which will simplify expressions in `simp` normal form,
  when associativity may otherwise need to be carefully applied. -/
@[simp]
theorem single_mul_single_right [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
    [DecidableEq m] [Semiring α] (a : m) (b : n) (c : k) (M : Matrix k l α) :
    (single a b).toMatrix ⬝ ((single b c).toMatrix ⬝ M) = (single a c).toMatrix ⬝ M := by
  rw [← Matrix.mul_assoc, single_mul_single]
#align pequiv.single_mul_single_right PEquiv.single_mul_single_right

/-- We can also define permutation matrices by permuting the rows of the identity matrix. -/
theorem equiv_toPEquiv_toMatrix [DecidableEq n] [Zero α] [One α] (σ : Equiv n n) (i j : n) :
    σ.toPequiv.toMatrix i j = (1 : Matrix n n α) (σ i) j :=
  if_congr Option.some_inj rfl rfl
#align pequiv.equiv_to_pequiv_to_matrix PEquiv.equiv_toPEquiv_toMatrix

end PEquiv

