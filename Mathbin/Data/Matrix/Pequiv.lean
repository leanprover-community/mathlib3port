/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.matrix.pequiv
! leanprover-community/mathlib commit 19cb3751e5e9b3d97adb51023949c50c13b5fdfd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.Data.Pequiv

/-!
# partial equivalences for matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print PEquiv.toMatrix /-
/-- `to_matrix` returns a matrix containing ones and zeros. `f.to_matrix i j` is `1` if
  `f i = some j` and `0` otherwise -/
def toMatrix [DecidableEq n] [Zero α] [One α] (f : m ≃. n) : Matrix m n α :=
  of fun i j => if j ∈ f i then (1 : α) else 0
#align pequiv.to_matrix PEquiv.toMatrix
-/

/- warning: pequiv.to_matrix_apply -> PEquiv.toMatrix_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α] (f : PEquiv.{u2, u3} m n) (i : m) (j : n), Eq.{succ u1} α (PEquiv.toMatrix.{u1, u2, u3} m n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3 f i j) (ite.{succ u1} α (Membership.Mem.{u3, u3} n (Option.{u3} n) (Option.hasMem.{u3} n) j (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (PEquiv.{u2, u3} m n) (fun (_x : PEquiv.{u2, u3} m n) => m -> (Option.{u3} n)) (FunLike.hasCoeToFun.{max (succ u2) (succ u3), succ u2, succ u3} (PEquiv.{u2, u3} m n) m (fun (_x : m) => Option.{u3} n) (PEquiv.funLike.{u2, u3} m n)) f i)) (Option.decidableEq.{u3} n (fun (a : n) (b : n) => _inst_1 a b) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (PEquiv.{u2, u3} m n) (fun (_x : PEquiv.{u2, u3} m n) => m -> (Option.{u3} n)) (FunLike.hasCoeToFun.{max (succ u2) (succ u3), succ u2, succ u3} (PEquiv.{u2, u3} m n) m (fun (_x : m) => Option.{u3} n) (PEquiv.funLike.{u2, u3} m n)) f i) (Option.some.{u3} n j)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_3))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_2))))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u3} α] [_inst_3 : One.{u3} α] (f : PEquiv.{u1, u2} m n) (i : m) (j : n), Eq.{succ u3} α (PEquiv.toMatrix.{u3, u1, u2} m n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3 f i j) (ite.{succ u3} α (Membership.mem.{u2, u2} n ((fun (x._@.Mathlib.Data.PEquiv._hyg.659 : m) => Option.{u2} n) i) (Option.instMembershipOption.{u2} n) j (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (PEquiv.{u1, u2} m n) m (fun (_x : m) => (fun (x._@.Mathlib.Data.PEquiv._hyg.659 : m) => Option.{u2} n) _x) (PEquiv.instFunLikePEquivOption.{u1, u2} m n) f i)) (PEquiv.instDecidableMemOptionInstMembershipOption.{u2} n (fun (a : n) (b : n) => _inst_1 a b) j (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (PEquiv.{u1, u2} m n) m (fun (a : m) => (fun (x._@.Mathlib.Data.PEquiv._hyg.659 : m) => Option.{u2} n) a) (PEquiv.instFunLikePEquivOption.{u1, u2} m n) f i)) (OfNat.ofNat.{u3} α 1 (One.toOfNat1.{u3} α _inst_3)) (OfNat.ofNat.{u3} α 0 (Zero.toOfNat0.{u3} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align pequiv.to_matrix_apply PEquiv.toMatrix_applyₓ'. -/
-- TODO: set as an equation lemma for `to_matrix`, see mathlib4#3024
@[simp]
theorem toMatrix_apply [DecidableEq n] [Zero α] [One α] (f : m ≃. n) (i j) :
    toMatrix f i j = if j ∈ f i then (1 : α) else 0 :=
  rfl
#align pequiv.to_matrix_apply PEquiv.toMatrix_apply

/- warning: pequiv.mul_matrix_apply -> PEquiv.mul_matrix_apply is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : Semiring.{u1} α] (f : PEquiv.{u2, u3} l m) (M : Matrix.{u3, u4, u1} m n α) (i : l) (j : n), Eq.{succ u1} α (Matrix.mul.{u1, u2, u3, u4} l m n α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (PEquiv.toMatrix.{u1, u2, u3} l m α (fun (a : m) (b : m) => _inst_2 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) f) M i j) (Option.casesOn.{succ u1, u3} m (fun (_x : Option.{u3} m) => α) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (PEquiv.{u2, u3} l m) (fun (_x : PEquiv.{u2, u3} l m) => l -> (Option.{u3} m)) (FunLike.hasCoeToFun.{max (succ u2) (succ u3), succ u2, succ u3} (PEquiv.{u2, u3} l m) l (fun (_x : l) => Option.{u3} m) (PEquiv.funLike.{u2, u3} l m)) f i) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))))))) (fun (fi : m) => M fi j))
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u1}} {α : Type.{u4}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : Semiring.{u4} α] (f : PEquiv.{u2, u3} l m) (M : Matrix.{u3, u1, u4} m n α) (i : l) (j : n), Eq.{succ u4} α (Matrix.mul.{u4, u2, u3, u1} l m n α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_3))) (PEquiv.toMatrix.{u4, u2, u3} l m α (fun (a : m) (b : m) => _inst_2 a b) (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_3)) (Semiring.toOne.{u4} α _inst_3) f) M i j) (Option.casesOn.{succ u4, u3} m (fun (_x : (fun (x._@.Mathlib.Data.PEquiv._hyg.659 : l) => Option.{u3} m) i) => α) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (PEquiv.{u2, u3} l m) l (fun (_x : l) => (fun (x._@.Mathlib.Data.PEquiv._hyg.659 : l) => Option.{u3} m) _x) (PEquiv.instFunLikePEquivOption.{u2, u3} l m) f i) (OfNat.ofNat.{u4} α 0 (Zero.toOfNat0.{u4} α (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_3)))) (fun (fi : m) => M fi j))
Case conversion may be inaccurate. Consider using '#align pequiv.mul_matrix_apply PEquiv.mul_matrix_applyₓ'. -/
theorem mul_matrix_apply [Fintype m] [DecidableEq m] [Semiring α] (f : l ≃. m) (M : Matrix m n α)
    (i j) : (f.toMatrix ⬝ M) i j = Option.casesOn (f i) 0 fun fi => M fi j :=
  by
  dsimp [to_matrix, Matrix.mul_apply]
  cases' h : f i with fi
  · simp [h]
  · rw [Finset.sum_eq_single fi] <;> simp (config := { contextual := true }) [h, eq_comm]
#align pequiv.mul_matrix_apply PEquiv.mul_matrix_apply

/- warning: pequiv.to_matrix_symm -> PEquiv.toMatrix_symm is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} m] [_inst_2 : DecidableEq.{succ u3} n] [_inst_3 : Zero.{u1} α] [_inst_4 : One.{u1} α] (f : PEquiv.{u2, u3} m n), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (PEquiv.toMatrix.{u1, u3, u2} n m α (fun (a : m) (b : m) => _inst_1 a b) _inst_3 _inst_4 (PEquiv.symm.{u2, u3} m n f)) (Matrix.transpose.{u1, u2, u3} m n α (PEquiv.toMatrix.{u1, u2, u3} m n α (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_4 f))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} m] [_inst_2 : DecidableEq.{succ u1} n] [_inst_3 : Zero.{u3} α] [_inst_4 : One.{u3} α] (f : PEquiv.{u2, u1} m n), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (PEquiv.toMatrix.{u3, u1, u2} n m α (fun (a : m) (b : m) => _inst_1 a b) _inst_3 _inst_4 (PEquiv.symm.{u2, u1} m n f)) (Matrix.transpose.{u3, u2, u1} m n α (PEquiv.toMatrix.{u3, u2, u1} m n α (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_4 f))
Case conversion may be inaccurate. Consider using '#align pequiv.to_matrix_symm PEquiv.toMatrix_symmₓ'. -/
theorem toMatrix_symm [DecidableEq m] [DecidableEq n] [Zero α] [One α] (f : m ≃. n) :
    (f.symm.toMatrix : Matrix n m α) = f.toMatrixᵀ := by
  ext <;> simp only [transpose, mem_iff_mem f, to_matrix_apply] <;> congr
#align pequiv.to_matrix_symm PEquiv.toMatrix_symm

/- warning: pequiv.to_matrix_refl -> PEquiv.toMatrix_refl is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α], Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (PEquiv.toMatrix.{u1, u2, u2} n n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3 (PEquiv.refl.{u2} n)) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] [_inst_3 : One.{u2} α], Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (PEquiv.toMatrix.{u2, u1, u1} n n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3 (PEquiv.refl.{u1} n)) (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)))
Case conversion may be inaccurate. Consider using '#align pequiv.to_matrix_refl PEquiv.toMatrix_reflₓ'. -/
@[simp]
theorem toMatrix_refl [DecidableEq n] [Zero α] [One α] :
    ((PEquiv.refl n).toMatrix : Matrix n n α) = 1 := by
  ext <;> simp [to_matrix_apply, one_apply] <;> congr
#align pequiv.to_matrix_refl PEquiv.toMatrix_refl

/- warning: pequiv.matrix_mul_apply -> PEquiv.matrix_mul_apply is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} [_inst_1 : Fintype.{u3} m] [_inst_2 : Semiring.{u1} α] [_inst_3 : DecidableEq.{succ u4} n] (M : Matrix.{u2, u3, u1} l m α) (f : PEquiv.{u3, u4} m n) (i : l) (j : n), Eq.{succ u1} α (Matrix.mul.{u1, u2, u3, u4} l m n α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) M (PEquiv.toMatrix.{u1, u3, u4} m n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)))) f) i j) (Option.casesOn.{succ u1, u3} m (fun (_x : Option.{u3} m) => α) (coeFn.{max (succ u4) (succ u3), max (succ u4) (succ u3)} (PEquiv.{u4, u3} n m) (fun (_x : PEquiv.{u4, u3} n m) => n -> (Option.{u3} m)) (FunLike.hasCoeToFun.{max (succ u4) (succ u3), succ u4, succ u3} (PEquiv.{u4, u3} n m) n (fun (_x : n) => Option.{u3} m) (PEquiv.funLike.{u4, u3} n m)) (PEquiv.symm.{u3, u4} m n f) j) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))))))) (fun (fj : m) => M i fj))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u4}} [_inst_1 : Fintype.{u3} m] [_inst_2 : Semiring.{u4} α] [_inst_3 : DecidableEq.{succ u2} n] (M : Matrix.{u1, u3, u4} l m α) (f : PEquiv.{u3, u2} m n) (i : l) (j : n), Eq.{succ u4} α (Matrix.mul.{u4, u1, u3, u2} l m n α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_2))) M (PEquiv.toMatrix.{u4, u3, u2} m n α (fun (a : n) (b : n) => _inst_3 a b) (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_2)) (Semiring.toOne.{u4} α _inst_2) f) i j) (Option.casesOn.{succ u4, u3} m (fun (_x : (fun (x._@.Mathlib.Data.PEquiv._hyg.659 : n) => Option.{u3} m) j) => α) (FunLike.coe.{max (succ u3) (succ u2), succ u2, succ u3} (PEquiv.{u2, u3} n m) n (fun (_x : n) => (fun (x._@.Mathlib.Data.PEquiv._hyg.659 : n) => Option.{u3} m) _x) (PEquiv.instFunLikePEquivOption.{u2, u3} n m) (PEquiv.symm.{u3, u2} m n f) j) (OfNat.ofNat.{u4} α 0 (Zero.toOfNat0.{u4} α (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_2)))) (fun (fj : m) => M i fj))
Case conversion may be inaccurate. Consider using '#align pequiv.matrix_mul_apply PEquiv.matrix_mul_applyₓ'. -/
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

/- warning: pequiv.to_pequiv_mul_matrix -> PEquiv.toPEquiv_mul_matrix is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : Semiring.{u1} α] (f : Equiv.{succ u2, succ u2} m m) (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.mul.{u1, u2, u2, u3} m m n α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (PEquiv.toMatrix.{u1, u2, u2} m m α (fun (a : m) (b : m) => _inst_2 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (Equiv.toPEquiv.{u2, u2} m m f)) M) (fun (i : m) => M (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} m m) (fun (_x : Equiv.{succ u2, succ u2} m m) => m -> m) (Equiv.hasCoeToFun.{succ u2, succ u2} m m) f i))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Fintype.{u2} m] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : Semiring.{u3} α] (f : Equiv.{succ u2, succ u2} m m) (M : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.mul.{u3, u2, u2, u1} m m n α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_3))) (PEquiv.toMatrix.{u3, u2, u2} m m α (fun (a : m) (b : m) => _inst_2 a b) (MonoidWithZero.toZero.{u3} α (Semiring.toMonoidWithZero.{u3} α _inst_3)) (Semiring.toOne.{u3} α _inst_3) (Equiv.toPEquiv.{u2, u2} m m f)) M) (fun (i : m) => M (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} m m) m (fun (_x : m) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : m) => m) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} m m) f i))
Case conversion may be inaccurate. Consider using '#align pequiv.to_pequiv_mul_matrix PEquiv.toPEquiv_mul_matrixₓ'. -/
theorem toPEquiv_mul_matrix [Fintype m] [DecidableEq m] [Semiring α] (f : m ≃ m)
    (M : Matrix m n α) : f.toPEquiv.toMatrix ⬝ M = fun i => M (f i) :=
  by
  ext (i j)
  rw [mul_matrix_apply, Equiv.toPEquiv_apply]
#align pequiv.to_pequiv_mul_matrix PEquiv.toPEquiv_mul_matrix

/- warning: pequiv.mul_to_pequiv_to_matrix -> PEquiv.mul_toPEquiv_toMatrix is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : Fintype.{u2} n] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : Semiring.{u3} α] (f : Equiv.{succ u2, succ u2} n n) (M : Matrix.{u1, u2, u3} m n α), Eq.{succ (max u1 u2 u3)} (Matrix.{u1, u2, u3} m n α) (Matrix.mul.{u3, u1, u2, u2} m n n α _inst_1 (Distrib.toHasMul.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_3)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_3))) M (PEquiv.toMatrix.{u3, u2, u2} n n α (fun (a : n) (b : n) => _inst_2 a b) (MulZeroClass.toHasZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_3)))) (AddMonoidWithOne.toOne.{u3} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} α (NonAssocSemiring.toAddCommMonoidWithOne.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_3)))) (Equiv.toPEquiv.{u2, u2} n n f))) (Matrix.submatrix.{u3, u1, u1, u2, u2} m m n n α M (id.{succ u1} m) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} n n) (fun (_x : Equiv.{succ u2, succ u2} n n) => n -> n) (Equiv.hasCoeToFun.{succ u2, succ u2} n n) (Equiv.symm.{succ u2, succ u2} n n f)))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} n] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : Semiring.{u1} α] (f : Equiv.{succ u2, succ u2} n n) (M : Matrix.{u3, u2, u1} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u3, u2, u1} m n α) (Matrix.mul.{u1, u3, u2, u2} m n n α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) M (PEquiv.toMatrix.{u1, u2, u2} n n α (fun (a : n) (b : n) => _inst_2 a b) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_3)) (Semiring.toOne.{u1} α _inst_3) (Equiv.toPEquiv.{u2, u2} n n f))) (Matrix.submatrix.{u1, u3, u3, u2, u2} m m n n α M (id.{succ u3} m) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} n n) n (fun (_x : n) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : n) => n) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} n n) (Equiv.symm.{succ u2, succ u2} n n f)))
Case conversion may be inaccurate. Consider using '#align pequiv.mul_to_pequiv_to_matrix PEquiv.mul_toPEquiv_toMatrixₓ'. -/
theorem mul_toPEquiv_toMatrix {m n α : Type _} [Fintype n] [DecidableEq n] [Semiring α] (f : n ≃ n)
    (M : Matrix m n α) : M ⬝ f.toPEquiv.toMatrix = M.submatrix id f.symm :=
  Matrix.ext fun i j => by
    rw [PEquiv.matrix_mul_apply, ← Equiv.toPEquiv_symm, Equiv.toPEquiv_apply,
      Matrix.submatrix_apply, id.def]
#align pequiv.mul_to_pequiv_to_matrix PEquiv.mul_toPEquiv_toMatrix

/- warning: pequiv.to_matrix_trans -> PEquiv.toMatrix_trans is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : DecidableEq.{succ u4} n] [_inst_4 : Semiring.{u1} α] (f : PEquiv.{u2, u3} l m) (g : PEquiv.{u3, u4} m n), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} l n α) (PEquiv.toMatrix.{u1, u2, u4} l n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))) (PEquiv.trans.{u2, u3, u4} l m n f g)) (Matrix.mul.{u1, u2, u3, u4} l m n α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) (PEquiv.toMatrix.{u1, u2, u3} l m α (fun (a : m) (b : m) => _inst_2 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))) f) (PEquiv.toMatrix.{u1, u3, u4} m n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))) g))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u4}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u4} α] (f : PEquiv.{u1, u3} l m) (g : PEquiv.{u3, u2} m n), Eq.{max (max (succ u4) (succ u1)) (succ u2)} (Matrix.{u1, u2, u4} l n α) (PEquiv.toMatrix.{u4, u1, u2} l n α (fun (a : n) (b : n) => _inst_3 a b) (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_4)) (Semiring.toOne.{u4} α _inst_4) (PEquiv.trans.{u1, u3, u2} l m n f g)) (Matrix.mul.{u4, u1, u3, u2} l m n α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_4))) (PEquiv.toMatrix.{u4, u1, u3} l m α (fun (a : m) (b : m) => _inst_2 a b) (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_4)) (Semiring.toOne.{u4} α _inst_4) f) (PEquiv.toMatrix.{u4, u3, u2} m n α (fun (a : n) (b : n) => _inst_3 a b) (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_4)) (Semiring.toOne.{u4} α _inst_4) g))
Case conversion may be inaccurate. Consider using '#align pequiv.to_matrix_trans PEquiv.toMatrix_transₓ'. -/
theorem toMatrix_trans [Fintype m] [DecidableEq m] [DecidableEq n] [Semiring α] (f : l ≃. m)
    (g : m ≃. n) : ((f.trans g).toMatrix : Matrix l n α) = f.toMatrix ⬝ g.toMatrix :=
  by
  ext (i j)
  rw [mul_matrix_apply]
  dsimp [to_matrix, PEquiv.trans]
  cases f i <;> simp
#align pequiv.to_matrix_trans PEquiv.toMatrix_trans

/- warning: pequiv.to_matrix_bot -> PEquiv.toMatrix_bot is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α], Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (PEquiv.toMatrix.{u1, u2, u3} m n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3 (Bot.bot.{max u2 u3} (PEquiv.{u2, u3} m n) (PEquiv.hasBot.{u2, u3} m n))) (OfNat.ofNat.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (OfNat.mk.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (Zero.zero.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasZero.{u1, u2, u3} m n α _inst_2))))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u3} α] [_inst_3 : One.{u3} α], Eq.{max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u1, u2, u3} m n α) (PEquiv.toMatrix.{u3, u1, u2} m n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3 (Bot.bot.{max u1 u2} (PEquiv.{u1, u2} m n) (PEquiv.instBotPEquiv.{u1, u2} m n))) (OfNat.ofNat.{max (max u3 u1) u2} (Matrix.{u1, u2, u3} m n α) 0 (Zero.toOfNat0.{max (max u3 u1) u2} (Matrix.{u1, u2, u3} m n α) (Matrix.zero.{u3, u1, u2} m n α _inst_2)))
Case conversion may be inaccurate. Consider using '#align pequiv.to_matrix_bot PEquiv.toMatrix_botₓ'. -/
@[simp]
theorem toMatrix_bot [DecidableEq n] [Zero α] [One α] :
    ((⊥ : PEquiv m n).toMatrix : Matrix m n α) = 0 :=
  rfl
#align pequiv.to_matrix_bot PEquiv.toMatrix_bot

/- warning: pequiv.to_matrix_injective -> PEquiv.toMatrix_injective is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} n] [_inst_2 : MonoidWithZero.{u1} α] [_inst_3 : Nontrivial.{u1} α], Function.Injective.{max (succ u2) (succ u3), succ (max u2 u3 u1)} (PEquiv.{u2, u3} m n) (Matrix.{u2, u3, u1} m n α) (PEquiv.toMatrix.{u1, u2, u3} m n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_2))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_2))))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : MonoidWithZero.{u3} α] [_inst_3 : Nontrivial.{u3} α], Function.Injective.{max (succ u1) (succ u2), max (max (succ u3) (succ u1)) (succ u2)} (PEquiv.{u1, u2} m n) (Matrix.{u1, u2, u3} m n α) (PEquiv.toMatrix.{u3, u1, u2} m n α (fun (a : n) (b : n) => _inst_1 a b) (MonoidWithZero.toZero.{u3} α _inst_2) (Monoid.toOne.{u3} α (MonoidWithZero.toMonoid.{u3} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align pequiv.to_matrix_injective PEquiv.toMatrix_injectiveₓ'. -/
theorem toMatrix_injective [DecidableEq n] [MonoidWithZero α] [Nontrivial α] :
    Function.Injective (@toMatrix m n α _ _ _) := by
  classical
    intro f g
    refine' not_imp_not.1 _
    simp only [matrix.ext_iff.symm, to_matrix_apply, PEquiv.ext_iff, not_forall, exists_imp]
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

/- warning: pequiv.to_matrix_swap -> PEquiv.toMatrix_swap is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Ring.{u1} α] (i : n) (j : n), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (PEquiv.toMatrix.{u1, u2, u2} n n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))))) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_2)))) (Equiv.toPEquiv.{u2, u2} n n (Equiv.swap.{succ u2} n (fun (a : n) (b : n) => _inst_1 a b) i j))) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (instHAdd.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasAdd.{u1, u2, u2} n n α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_2)))) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (instHAdd.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasAdd.{u1, u2, u2} n n α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_2)))) (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (instHSub.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasSub.{u1, u2, u2} n n α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_2))))))) (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (instHSub.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasSub.{u1, u2, u2} n n α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_2))))))) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))))) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_2)))))))) (PEquiv.toMatrix.{u1, u2, u2} n n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))))) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_2)))) (PEquiv.single.{u2, u2} n n (fun (a : n) (b : n) => _inst_1 a b) (fun (a : n) (b : n) => _inst_1 a b) i i))) (PEquiv.toMatrix.{u1, u2, u2} n n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))))) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_2)))) (PEquiv.single.{u2, u2} n n (fun (a : n) (b : n) => _inst_1 a b) (fun (a : n) (b : n) => _inst_1 a b) j j))) (PEquiv.toMatrix.{u1, u2, u2} n n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))))) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_2)))) (PEquiv.single.{u2, u2} n n (fun (a : n) (b : n) => _inst_1 a b) (fun (a : n) (b : n) => _inst_1 a b) i j))) (PEquiv.toMatrix.{u1, u2, u2} n n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))))) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_2)))) (PEquiv.single.{u2, u2} n n (fun (a : n) (b : n) => _inst_1 a b) (fun (a : n) (b : n) => _inst_1 a b) j i)))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Ring.{u2} α] (i : n) (j : n), Eq.{max (succ u1) (succ u2)} (Matrix.{u1, u1, u2} n n α) (PEquiv.toMatrix.{u2, u1, u1} n n α (fun (a : n) (b : n) => _inst_1 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (Ring.toSemiring.{u2} α _inst_2))) (Semiring.toOne.{u2} α (Ring.toSemiring.{u2} α _inst_2)) (Equiv.toPEquiv.{u1, u1} n n (Equiv.swap.{succ u1} n (fun (a : n) (b : n) => _inst_1 a b) i j))) (HAdd.hAdd.{max u2 u1, max u1 u2, max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHAdd.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.add.{u2, u1, u1} n n α (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} α (NonAssocRing.toNonUnitalNonAssocRing.{u2} α (Ring.toNonAssocRing.{u2} α _inst_2))))))) (HAdd.hAdd.{max u2 u1, max u1 u2, max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHAdd.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.add.{u2, u1, u1} n n α (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} α (NonAssocRing.toNonUnitalNonAssocRing.{u2} α (Ring.toNonAssocRing.{u2} α _inst_2))))))) (HSub.hSub.{max u2 u1, max u1 u2, max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHSub.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.sub.{u2, u1, u1} n n α (Ring.toSub.{u2} α _inst_2))) (HSub.hSub.{max u2 u1, max u1 u2, max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHSub.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.sub.{u2, u1, u1} n n α (Ring.toSub.{u2} α _inst_2))) (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (Ring.toSemiring.{u2} α _inst_2))) (Semiring.toOne.{u2} α (Ring.toSemiring.{u2} α _inst_2))))) (PEquiv.toMatrix.{u2, u1, u1} n n α (fun (a : n) (b : n) => _inst_1 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (Ring.toSemiring.{u2} α _inst_2))) (Semiring.toOne.{u2} α (Ring.toSemiring.{u2} α _inst_2)) (PEquiv.single.{u1, u1} n n (fun (a : n) (b : n) => _inst_1 a b) (fun (a : n) (b : n) => _inst_1 a b) i i))) (PEquiv.toMatrix.{u2, u1, u1} n n α (fun (a : n) (b : n) => _inst_1 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (Ring.toSemiring.{u2} α _inst_2))) (Semiring.toOne.{u2} α (Ring.toSemiring.{u2} α _inst_2)) (PEquiv.single.{u1, u1} n n (fun (a : n) (b : n) => _inst_1 a b) (fun (a : n) (b : n) => _inst_1 a b) j j))) (PEquiv.toMatrix.{u2, u1, u1} n n α (fun (a : n) (b : n) => _inst_1 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (Ring.toSemiring.{u2} α _inst_2))) (Semiring.toOne.{u2} α (Ring.toSemiring.{u2} α _inst_2)) (PEquiv.single.{u1, u1} n n (fun (a : n) (b : n) => _inst_1 a b) (fun (a : n) (b : n) => _inst_1 a b) i j))) (PEquiv.toMatrix.{u2, u1, u1} n n α (fun (a : n) (b : n) => _inst_1 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (Ring.toSemiring.{u2} α _inst_2))) (Semiring.toOne.{u2} α (Ring.toSemiring.{u2} α _inst_2)) (PEquiv.single.{u1, u1} n n (fun (a : n) (b : n) => _inst_1 a b) (fun (a : n) (b : n) => _inst_1 a b) j i)))
Case conversion may be inaccurate. Consider using '#align pequiv.to_matrix_swap PEquiv.toMatrix_swapₓ'. -/
theorem toMatrix_swap [DecidableEq n] [Ring α] (i j : n) :
    (Equiv.swap i j).toPEquiv.toMatrix =
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

/- warning: pequiv.single_mul_single -> PEquiv.single_mul_single is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} [_inst_1 : Fintype.{u4} n] [_inst_2 : DecidableEq.{succ u2} k] [_inst_3 : DecidableEq.{succ u3} m] [_inst_4 : DecidableEq.{succ u4} n] [_inst_5 : Semiring.{u1} α] (a : m) (b : n) (c : k), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} m k α) (Matrix.mul.{u1, u3, u4, u2} m n k α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5))) (PEquiv.toMatrix.{u1, u3, u4} m n α (fun (a : n) (b : n) => _inst_4 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5)))) (PEquiv.single.{u3, u4} m n (fun (a : m) (b : m) => _inst_3 a b) (fun (a : n) (b : n) => _inst_4 a b) a b)) (PEquiv.toMatrix.{u1, u4, u2} n k α (fun (a : k) (b : k) => _inst_2 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5)))) (PEquiv.single.{u4, u2} n k (fun (a : n) (b : n) => _inst_4 a b) (fun (a : k) (b : k) => _inst_2 a b) b c))) (PEquiv.toMatrix.{u1, u3, u2} m k α (fun (a : k) (b : k) => _inst_2 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5)))) (PEquiv.single.{u3, u2} m k (fun (a : m) (b : m) => _inst_3 a b) (fun (a : k) (b : k) => _inst_2 a b) a c))
but is expected to have type
  forall {k : Type.{u2}} {m : Type.{u1}} {n : Type.{u3}} {α : Type.{u4}} [_inst_1 : Fintype.{u3} n] [_inst_2 : DecidableEq.{succ u2} k] [_inst_3 : DecidableEq.{succ u1} m] [_inst_4 : DecidableEq.{succ u3} n] [_inst_5 : Semiring.{u4} α] (a : m) (b : n) (c : k), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} m k α) (Matrix.mul.{u4, u1, u3, u2} m n k α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_5))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_5))) (PEquiv.toMatrix.{u4, u1, u3} m n α (fun (a : n) (b : n) => _inst_4 a b) (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_5)) (Semiring.toOne.{u4} α _inst_5) (PEquiv.single.{u1, u3} m n (fun (a : m) (b : m) => _inst_3 a b) (fun (a : n) (b : n) => _inst_4 a b) a b)) (PEquiv.toMatrix.{u4, u3, u2} n k α (fun (a : k) (b : k) => _inst_2 a b) (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_5)) (Semiring.toOne.{u4} α _inst_5) (PEquiv.single.{u3, u2} n k (fun (a : n) (b : n) => _inst_4 a b) (fun (a : k) (b : k) => _inst_2 a b) b c))) (PEquiv.toMatrix.{u4, u1, u2} m k α (fun (a : k) (b : k) => _inst_2 a b) (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_5)) (Semiring.toOne.{u4} α _inst_5) (PEquiv.single.{u1, u2} m k (fun (a : m) (b : m) => _inst_3 a b) (fun (a : k) (b : k) => _inst_2 a b) a c))
Case conversion may be inaccurate. Consider using '#align pequiv.single_mul_single PEquiv.single_mul_singleₓ'. -/
@[simp]
theorem single_mul_single [Fintype n] [DecidableEq k] [DecidableEq m] [DecidableEq n] [Semiring α]
    (a : m) (b : n) (c : k) :
    ((single a b).toMatrix : Matrix _ _ α) ⬝ (single b c).toMatrix = (single a c).toMatrix := by
  rw [← to_matrix_trans, single_trans_single]
#align pequiv.single_mul_single PEquiv.single_mul_single

/- warning: pequiv.single_mul_single_of_ne -> PEquiv.single_mul_single_of_ne is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} [_inst_1 : Fintype.{u4} n] [_inst_2 : DecidableEq.{succ u4} n] [_inst_3 : DecidableEq.{succ u2} k] [_inst_4 : DecidableEq.{succ u3} m] [_inst_5 : Semiring.{u1} α] {b₁ : n} {b₂ : n}, (Ne.{succ u4} n b₁ b₂) -> (forall (a : m) (c : k), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} m k α) (Matrix.mul.{u1, u3, u4, u2} m n k α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5))) (PEquiv.toMatrix.{u1, u3, u4} m n α (fun (a : n) (b : n) => _inst_2 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5)))) (PEquiv.single.{u3, u4} m n (fun (a : m) (b : m) => _inst_4 a b) (fun (a : n) (b : n) => _inst_2 a b) a b₁)) (PEquiv.toMatrix.{u1, u4, u2} n k α (fun (a : k) (b : k) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5)))) (PEquiv.single.{u4, u2} n k (fun (a : n) (b : n) => _inst_2 a b) (fun (a : k) (b : k) => _inst_3 a b) b₂ c))) (OfNat.ofNat.{max u3 u2 u1} (Matrix.{u3, u2, u1} m k α) 0 (OfNat.mk.{max u3 u2 u1} (Matrix.{u3, u2, u1} m k α) 0 (Zero.zero.{max u3 u2 u1} (Matrix.{u3, u2, u1} m k α) (Matrix.hasZero.{u1, u3, u2} m k α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_5)))))))))
but is expected to have type
  forall {k : Type.{u2}} {m : Type.{u1}} {n : Type.{u3}} {α : Type.{u4}} [_inst_1 : Fintype.{u3} n] [_inst_2 : DecidableEq.{succ u3} n] [_inst_3 : DecidableEq.{succ u2} k] [_inst_4 : DecidableEq.{succ u1} m] [_inst_5 : Semiring.{u4} α] {b₁ : n} {b₂ : n}, (Ne.{succ u3} n b₁ b₂) -> (forall (a : m) (c : k), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} m k α) (Matrix.mul.{u4, u1, u3, u2} m n k α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_5))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_5))) (PEquiv.toMatrix.{u4, u1, u3} m n α (fun (a : n) (b : n) => _inst_2 a b) (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_5)) (Semiring.toOne.{u4} α _inst_5) (PEquiv.single.{u1, u3} m n (fun (a : m) (b : m) => _inst_4 a b) (fun (a : n) (b : n) => _inst_2 a b) a b₁)) (PEquiv.toMatrix.{u4, u3, u2} n k α (fun (a : k) (b : k) => _inst_3 a b) (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_5)) (Semiring.toOne.{u4} α _inst_5) (PEquiv.single.{u3, u2} n k (fun (a : n) (b : n) => _inst_2 a b) (fun (a : k) (b : k) => _inst_3 a b) b₂ c))) (OfNat.ofNat.{max (max u4 u2) u1} (Matrix.{u1, u2, u4} m k α) 0 (Zero.toOfNat0.{max (max u4 u2) u1} (Matrix.{u1, u2, u4} m k α) (Matrix.zero.{u4, u1, u2} m k α (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_5))))))
Case conversion may be inaccurate. Consider using '#align pequiv.single_mul_single_of_ne PEquiv.single_mul_single_of_neₓ'. -/
theorem single_mul_single_of_ne [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m]
    [Semiring α] {b₁ b₂ : n} (hb : b₁ ≠ b₂) (a : m) (c : k) :
    ((single a b₁).toMatrix : Matrix _ _ α) ⬝ (single b₂ c).toMatrix = 0 := by
  rw [← to_matrix_trans, single_trans_single_of_ne hb, to_matrix_bot]
#align pequiv.single_mul_single_of_ne PEquiv.single_mul_single_of_ne

/- warning: pequiv.single_mul_single_right -> PEquiv.single_mul_single_right is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u2}} {l : Type.{u3}} {m : Type.{u4}} {n : Type.{u5}} {α : Type.{u1}} [_inst_1 : Fintype.{u5} n] [_inst_2 : Fintype.{u2} k] [_inst_3 : DecidableEq.{succ u5} n] [_inst_4 : DecidableEq.{succ u2} k] [_inst_5 : DecidableEq.{succ u4} m] [_inst_6 : Semiring.{u1} α] (a : m) (b : n) (c : k) (M : Matrix.{u2, u3, u1} k l α), Eq.{succ (max u4 u3 u1)} (Matrix.{u4, u3, u1} m l α) (Matrix.mul.{u1, u4, u5, u3} m n l α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_6)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_6))) (PEquiv.toMatrix.{u1, u4, u5} m n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_6)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_6)))) (PEquiv.single.{u4, u5} m n (fun (a : m) (b : m) => _inst_5 a b) (fun (a : n) (b : n) => _inst_3 a b) a b)) (Matrix.mul.{u1, u5, u2, u3} n k l α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_6)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_6))) (PEquiv.toMatrix.{u1, u5, u2} n k α (fun (a : k) (b : k) => _inst_4 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_6)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_6)))) (PEquiv.single.{u5, u2} n k (fun (a : n) (b : n) => _inst_3 a b) (fun (a : k) (b : k) => _inst_4 a b) b c)) M)) (Matrix.mul.{u1, u4, u2, u3} m k l α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_6)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_6))) (PEquiv.toMatrix.{u1, u4, u2} m k α (fun (a : k) (b : k) => _inst_4 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_6)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_6)))) (PEquiv.single.{u4, u2} m k (fun (a : m) (b : m) => _inst_5 a b) (fun (a : k) (b : k) => _inst_4 a b) a c)) M)
but is expected to have type
  forall {k : Type.{u3}} {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u4}} {α : Type.{u5}} [_inst_1 : Fintype.{u4} n] [_inst_2 : Fintype.{u3} k] [_inst_3 : DecidableEq.{succ u4} n] [_inst_4 : DecidableEq.{succ u3} k] [_inst_5 : DecidableEq.{succ u2} m] [_inst_6 : Semiring.{u5} α] (a : m) (b : n) (c : k) (M : Matrix.{u3, u1, u5} k l α), Eq.{max (max (succ u5) (succ u1)) (succ u2)} (Matrix.{u2, u1, u5} m l α) (Matrix.mul.{u5, u2, u4, u1} m n l α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u5} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} α (Semiring.toNonAssocSemiring.{u5} α _inst_6))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} α (Semiring.toNonAssocSemiring.{u5} α _inst_6))) (PEquiv.toMatrix.{u5, u2, u4} m n α (fun (a : n) (b : n) => _inst_3 a b) (MonoidWithZero.toZero.{u5} α (Semiring.toMonoidWithZero.{u5} α _inst_6)) (Semiring.toOne.{u5} α _inst_6) (PEquiv.single.{u2, u4} m n (fun (a : m) (b : m) => _inst_5 a b) (fun (a : n) (b : n) => _inst_3 a b) a b)) (Matrix.mul.{u5, u4, u3, u1} n k l α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u5} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} α (Semiring.toNonAssocSemiring.{u5} α _inst_6))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} α (Semiring.toNonAssocSemiring.{u5} α _inst_6))) (PEquiv.toMatrix.{u5, u4, u3} n k α (fun (a : k) (b : k) => _inst_4 a b) (MonoidWithZero.toZero.{u5} α (Semiring.toMonoidWithZero.{u5} α _inst_6)) (Semiring.toOne.{u5} α _inst_6) (PEquiv.single.{u4, u3} n k (fun (a : n) (b : n) => _inst_3 a b) (fun (a : k) (b : k) => _inst_4 a b) b c)) M)) (Matrix.mul.{u5, u2, u3, u1} m k l α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u5} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} α (Semiring.toNonAssocSemiring.{u5} α _inst_6))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} α (Semiring.toNonAssocSemiring.{u5} α _inst_6))) (PEquiv.toMatrix.{u5, u2, u3} m k α (fun (a : k) (b : k) => _inst_4 a b) (MonoidWithZero.toZero.{u5} α (Semiring.toMonoidWithZero.{u5} α _inst_6)) (Semiring.toOne.{u5} α _inst_6) (PEquiv.single.{u2, u3} m k (fun (a : m) (b : m) => _inst_5 a b) (fun (a : k) (b : k) => _inst_4 a b) a c)) M)
Case conversion may be inaccurate. Consider using '#align pequiv.single_mul_single_right PEquiv.single_mul_single_rightₓ'. -/
/-- Restatement of `single_mul_single`, which will simplify expressions in `simp` normal form,
  when associativity may otherwise need to be carefully applied. -/
@[simp]
theorem single_mul_single_right [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
    [DecidableEq m] [Semiring α] (a : m) (b : n) (c : k) (M : Matrix k l α) :
    (single a b).toMatrix ⬝ ((single b c).toMatrix ⬝ M) = (single a c).toMatrix ⬝ M := by
  rw [← Matrix.mul_assoc, single_mul_single]
#align pequiv.single_mul_single_right PEquiv.single_mul_single_right

/- warning: pequiv.equiv_to_pequiv_to_matrix -> PEquiv.equiv_toPEquiv_toMatrix is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α] (σ : Equiv.{succ u2, succ u2} n n) (i : n) (j : n), Eq.{succ u1} α (PEquiv.toMatrix.{u1, u2, u2} n n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3 (Equiv.toPEquiv.{u2, u2} n n σ) i j) (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} n n) (fun (_x : Equiv.{succ u2, succ u2} n n) => n -> n) (Equiv.hasCoeToFun.{succ u2, succ u2} n n) σ i) j)
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] [_inst_3 : One.{u2} α] (σ : Equiv.{succ u1, succ u1} n n) (i : n) (j : n), Eq.{succ u2} α (PEquiv.toMatrix.{u2, u1, u1} n n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3 (Equiv.toPEquiv.{u1, u1} n n σ) i j) (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} n n) n (fun (_x : n) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : n) => n) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} n n) σ i) j)
Case conversion may be inaccurate. Consider using '#align pequiv.equiv_to_pequiv_to_matrix PEquiv.equiv_toPEquiv_toMatrixₓ'. -/
/-- We can also define permutation matrices by permuting the rows of the identity matrix. -/
theorem equiv_toPEquiv_toMatrix [DecidableEq n] [Zero α] [One α] (σ : Equiv n n) (i j : n) :
    σ.toPEquiv.toMatrix i j = (1 : Matrix n n α) (σ i) j :=
  if_congr Option.some_inj rfl rfl
#align pequiv.equiv_to_pequiv_to_matrix PEquiv.equiv_toPEquiv_toMatrix

end PEquiv

