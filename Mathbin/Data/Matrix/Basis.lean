/-
Copyright (c) 2020 Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Scott Morrison, Eric Wieser, Oliver Nash

! This file was ported from Lean 3 source module data.matrix.basis
! leanprover-community/mathlib commit d64d67d000b974f0d86a2be7918cf800be6271c8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.LinearAlgebra.Matrix.Trace

/-!
# Matrices with a single non-zero element.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides `matrix.std_basis_matrix`. The matrix `matrix.std_basis_matrix i j c` has `c`
at position `(i, j)`, and zeroes elsewhere.
-/


variable {l m n : Type _}

variable {R α : Type _}

namespace Matrix

open Matrix

open BigOperators

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [Semiring α]

#print Matrix.stdBasisMatrix /-
/-- `std_basis_matrix i j a` is the matrix with `a` in the `i`-th row, `j`-th column,
and zeroes elsewhere.
-/
def stdBasisMatrix (i : m) (j : n) (a : α) : Matrix m n α := fun i' j' =>
  if i = i' ∧ j = j' then a else 0
#align matrix.std_basis_matrix Matrix.stdBasisMatrix
-/

/- warning: matrix.smul_std_basis_matrix -> Matrix.smul_stdBasisMatrix is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u3} α] (i : m) (j : n) (a : α) (b : α), Eq.{succ (max u1 u2 u3)} (Matrix.{u1, u2, u3} m n α) (SMul.smul.{u3, max u1 u2 u3} α (Matrix.{u1, u2, u3} m n α) (Matrix.hasSmul.{u3, u1, u2, u3} m n α α (Mul.toSMul.{u3} α (Distrib.toHasMul.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4)))))) b (Matrix.stdBasisMatrix.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j a)) (Matrix.stdBasisMatrix.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j (SMul.smul.{u3, u3} α α (Mul.toSMul.{u3} α (Distrib.toHasMul.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4))))) b a))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] (i : m) (j : n) (a : α) (b : α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u3, u2, u1} m n α) (HSMul.hSMul.{u1, max (max u1 u2) u3, max (max u3 u2) u1} α (Matrix.{u3, u2, u1} m n α) (Matrix.{u3, u2, u1} m n α) (instHSMul.{u1, max (max u3 u2) u1} α (Matrix.{u3, u2, u1} m n α) (Matrix.smul.{u1, u3, u2, u1} m n α α (SMulZeroClass.toSMul.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)) (SMulWithZero.toSMulZeroClass.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)) (MulZeroClass.toSMulWithZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))))))) b (Matrix.stdBasisMatrix.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j a)) (Matrix.stdBasisMatrix.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j (HSMul.hSMul.{u1, u1, u1} α α α (instHSMul.{u1, u1} α α (SMulZeroClass.toSMul.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)) (SMulWithZero.toSMulZeroClass.{u1, u1} α α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)) (MulZeroClass.toSMulWithZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))))))) b a))
Case conversion may be inaccurate. Consider using '#align matrix.smul_std_basis_matrix Matrix.smul_stdBasisMatrixₓ'. -/
@[simp]
theorem smul_stdBasisMatrix (i : m) (j : n) (a b : α) :
    b • stdBasisMatrix i j a = stdBasisMatrix i j (b • a) := by unfold std_basis_matrix; ext; simp
#align matrix.smul_std_basis_matrix Matrix.smul_stdBasisMatrix

/- warning: matrix.std_basis_matrix_zero -> Matrix.stdBasisMatrix_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u3} α] (i : m) (j : n), Eq.{succ (max u1 u2 u3)} (Matrix.{u1, u2, u3} m n α) (Matrix.stdBasisMatrix.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j (OfNat.ofNat.{u3} α 0 (OfNat.mk.{u3} α 0 (Zero.zero.{u3} α (MulZeroClass.toHasZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4)))))))) (OfNat.ofNat.{max u1 u2 u3} (Matrix.{u1, u2, u3} m n α) 0 (OfNat.mk.{max u1 u2 u3} (Matrix.{u1, u2, u3} m n α) 0 (Zero.zero.{max u1 u2 u3} (Matrix.{u1, u2, u3} m n α) (Matrix.hasZero.{u3, u1, u2} m n α (MulZeroClass.toHasZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4))))))))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] (i : m) (j : n), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u3, u2, u1} m n α) (Matrix.stdBasisMatrix.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4))))) (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{u3, u2, u1} m n α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (Matrix.{u3, u2, u1} m n α) (Matrix.zero.{u1, u3, u2} m n α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)))))
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix_zero Matrix.stdBasisMatrix_zeroₓ'. -/
@[simp]
theorem stdBasisMatrix_zero (i : m) (j : n) : stdBasisMatrix i j (0 : α) = 0 := by
  unfold std_basis_matrix; ext; simp
#align matrix.std_basis_matrix_zero Matrix.stdBasisMatrix_zero

/- warning: matrix.std_basis_matrix_add -> Matrix.stdBasisMatrix_add is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u3} α] (i : m) (j : n) (a : α) (b : α), Eq.{succ (max u1 u2 u3)} (Matrix.{u1, u2, u3} m n α) (Matrix.stdBasisMatrix.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j (HAdd.hAdd.{u3, u3, u3} α α α (instHAdd.{u3} α (Distrib.toHasAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4))))) a b)) (HAdd.hAdd.{max u1 u2 u3, max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n α) (Matrix.{u1, u2, u3} m n α) (Matrix.{u1, u2, u3} m n α) (instHAdd.{max u1 u2 u3} (Matrix.{u1, u2, u3} m n α) (Matrix.hasAdd.{u3, u1, u2} m n α (Distrib.toHasAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4)))))) (Matrix.stdBasisMatrix.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j a) (Matrix.stdBasisMatrix.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j b))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] (i : m) (j : n) (a : α) (b : α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u3, u2, u1} m n α) (Matrix.stdBasisMatrix.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))))) a b)) (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u3, u2, u1} m n α) (Matrix.{u3, u2, u1} m n α) (Matrix.{u3, u2, u1} m n α) (instHAdd.{max (max u3 u2) u1} (Matrix.{u3, u2, u1} m n α) (Matrix.add.{u1, u3, u2} m n α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))))) (Matrix.stdBasisMatrix.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j a) (Matrix.stdBasisMatrix.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j b))
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix_add Matrix.stdBasisMatrix_addₓ'. -/
theorem stdBasisMatrix_add (i : m) (j : n) (a b : α) :
    stdBasisMatrix i j (a + b) = stdBasisMatrix i j a + stdBasisMatrix i j b :=
  by
  unfold std_basis_matrix; ext
  split_ifs with h <;> simp [h]
#align matrix.std_basis_matrix_add Matrix.stdBasisMatrix_add

/- warning: matrix.matrix_eq_sum_std_basis -> Matrix.matrix_eq_sum_std_basis is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u3} α] [_inst_5 : Fintype.{u1} m] [_inst_6 : Fintype.{u2} n] (x : Matrix.{u1, u2, u3} m n α), Eq.{succ (max u1 u2 u3)} (Matrix.{u1, u2, u3} m n α) x (Finset.sum.{max u1 u2 u3, u1} (Matrix.{u1, u2, u3} m n α) m (Matrix.addCommMonoid.{u3, u1, u2} m n α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4)))) (Finset.univ.{u1} m _inst_5) (fun (i : m) => Finset.sum.{max u1 u2 u3, u2} (Matrix.{u1, u2, u3} m n α) n (Matrix.addCommMonoid.{u3, u1, u2} m n α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4)))) (Finset.univ.{u2} n _inst_6) (fun (j : n) => Matrix.stdBasisMatrix.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j (x i j))))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] [_inst_5 : Fintype.{u3} m] [_inst_6 : Fintype.{u2} n] (x : Matrix.{u3, u2, u1} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u3, u2, u1} m n α) x (Finset.sum.{max (max u1 u2) u3, u3} (Matrix.{u3, u2, u1} m n α) m (Matrix.addCommMonoid.{u1, u3, u2} m n α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))) (Finset.univ.{u3} m _inst_5) (fun (i : m) => Finset.sum.{max (max u1 u2) u3, u2} (Matrix.{u3, u2, u1} m n α) n (Matrix.addCommMonoid.{u1, u3, u2} m n α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))) (Finset.univ.{u2} n _inst_6) (fun (j : n) => Matrix.stdBasisMatrix.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j (x i j))))
Case conversion may be inaccurate. Consider using '#align matrix.matrix_eq_sum_std_basis Matrix.matrix_eq_sum_std_basisₓ'. -/
theorem matrix_eq_sum_std_basis [Fintype m] [Fintype n] (x : Matrix m n α) :
    x = ∑ (i : m) (j : n), stdBasisMatrix i j (x i j) :=
  by
  ext; symm
  iterate 2 rw [Finset.sum_apply]
  convert Fintype.sum_eq_single i _
  · simp [std_basis_matrix]
  · intro j hj
    simp [std_basis_matrix, hj]
#align matrix.matrix_eq_sum_std_basis Matrix.matrix_eq_sum_std_basis

/- warning: matrix.std_basis_eq_basis_mul_basis -> Matrix.std_basis_eq_basis_mul_basis is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : DecidableEq.{succ u2} n] (i : m) (j : n), Eq.{succ (max u1 u2)} (Matrix.{u1, u2, 0} m n Nat) (Matrix.stdBasisMatrix.{u1, u2, 0} m n Nat (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) Nat.semiring i j (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Matrix.vecMulVec.{0, u1, u2} m n Nat Nat.hasMul (fun (i' : m) => ite.{1} Nat (Eq.{succ u1} m i i') (_inst_2 i i') (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (j' : n) => ite.{1} Nat (Eq.{succ u2} n j j') (_inst_3 j j') (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : DecidableEq.{succ u1} n] (i : m) (j : n), Eq.{max (max (succ u2) (succ u1)) 1} (Matrix.{u2, u1, 0} m n Nat) (Matrix.stdBasisMatrix.{u2, u1, 0} m n Nat (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) Nat.semiring i j (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Matrix.vecMulVec.{0, u2, u1} m n Nat instMulNat (fun (i' : m) => ite.{1} Nat (Eq.{succ u2} m i i') (_inst_2 i i') (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (fun (j' : n) => ite.{1} Nat (Eq.{succ u1} n j j') (_inst_3 j j') (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_eq_basis_mul_basis Matrix.std_basis_eq_basis_mul_basisₓ'. -/
-- TODO: tie this up with the `basis` machinery of linear algebra
-- this is not completely trivial because we are indexing by two types, instead of one
-- TODO: add `std_basis_vec`
theorem std_basis_eq_basis_mul_basis (i : m) (j : n) :
    stdBasisMatrix i j 1 = vecMulVec (fun i' => ite (i = i') 1 0) fun j' => ite (j = j') 1 0 :=
  by
  ext
  norm_num [std_basis_matrix, vec_mul_vec]
  exact ite_and _ _ _ _
#align matrix.std_basis_eq_basis_mul_basis Matrix.std_basis_eq_basis_mul_basis

/- warning: matrix.induction_on' -> Matrix.induction_on' is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u3} α] [_inst_5 : Fintype.{u1} m] [_inst_6 : Fintype.{u2} n] {P : (Matrix.{u1, u2, u3} m n α) -> Prop} (M : Matrix.{u1, u2, u3} m n α), (P (OfNat.ofNat.{max u1 u2 u3} (Matrix.{u1, u2, u3} m n α) 0 (OfNat.mk.{max u1 u2 u3} (Matrix.{u1, u2, u3} m n α) 0 (Zero.zero.{max u1 u2 u3} (Matrix.{u1, u2, u3} m n α) (Matrix.hasZero.{u3, u1, u2} m n α (MulZeroClass.toHasZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4))))))))) -> (forall (p : Matrix.{u1, u2, u3} m n α) (q : Matrix.{u1, u2, u3} m n α), (P p) -> (P q) -> (P (HAdd.hAdd.{max u1 u2 u3, max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n α) (Matrix.{u1, u2, u3} m n α) (Matrix.{u1, u2, u3} m n α) (instHAdd.{max u1 u2 u3} (Matrix.{u1, u2, u3} m n α) (Matrix.hasAdd.{u3, u1, u2} m n α (Distrib.toHasAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4)))))) p q))) -> (forall (i : m) (j : n) (x : α), P (Matrix.stdBasisMatrix.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j x)) -> (P M)
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] [_inst_5 : Fintype.{u3} m] [_inst_6 : Fintype.{u2} n] {P : (Matrix.{u3, u2, u1} m n α) -> Prop} (M : Matrix.{u3, u2, u1} m n α), (P (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{u3, u2, u1} m n α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (Matrix.{u3, u2, u1} m n α) (Matrix.zero.{u1, u3, u2} m n α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)))))) -> (forall (p : Matrix.{u3, u2, u1} m n α) (q : Matrix.{u3, u2, u1} m n α), (P p) -> (P q) -> (P (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u3, u2, u1} m n α) (Matrix.{u3, u2, u1} m n α) (Matrix.{u3, u2, u1} m n α) (instHAdd.{max (max u3 u2) u1} (Matrix.{u3, u2, u1} m n α) (Matrix.add.{u1, u3, u2} m n α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))))) p q))) -> (forall (i : m) (j : n) (x : α), P (Matrix.stdBasisMatrix.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j x)) -> (P M)
Case conversion may be inaccurate. Consider using '#align matrix.induction_on' Matrix.induction_on'ₓ'. -/
-- todo: the old proof used fintypes, I don't know `finsupp` but this feels generalizable
@[elab_as_elim]
protected theorem induction_on' [Fintype m] [Fintype n] {P : Matrix m n α → Prop} (M : Matrix m n α)
    (h_zero : P 0) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ (i : m) (j : n) (x : α), P (stdBasisMatrix i j x)) : P M :=
  by
  rw [matrix_eq_sum_std_basis M, ← Finset.sum_product']
  apply Finset.sum_induction _ _ h_add h_zero
  · intros ; apply h_std_basis
#align matrix.induction_on' Matrix.induction_on'

/- warning: matrix.induction_on -> Matrix.induction_on is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u3} α] [_inst_5 : Fintype.{u1} m] [_inst_6 : Fintype.{u2} n] [_inst_7 : Nonempty.{succ u1} m] [_inst_8 : Nonempty.{succ u2} n] {P : (Matrix.{u1, u2, u3} m n α) -> Prop} (M : Matrix.{u1, u2, u3} m n α), (forall (p : Matrix.{u1, u2, u3} m n α) (q : Matrix.{u1, u2, u3} m n α), (P p) -> (P q) -> (P (HAdd.hAdd.{max u1 u2 u3, max u1 u2 u3, max u1 u2 u3} (Matrix.{u1, u2, u3} m n α) (Matrix.{u1, u2, u3} m n α) (Matrix.{u1, u2, u3} m n α) (instHAdd.{max u1 u2 u3} (Matrix.{u1, u2, u3} m n α) (Matrix.hasAdd.{u3, u1, u2} m n α (Distrib.toHasAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4)))))) p q))) -> (forall (i : m) (j : n) (x : α), P (Matrix.stdBasisMatrix.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j x)) -> (P M)
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] [_inst_5 : Fintype.{u3} m] [_inst_6 : Fintype.{u2} n] [_inst_7 : Nonempty.{succ u3} m] [_inst_8 : Nonempty.{succ u2} n] {P : (Matrix.{u3, u2, u1} m n α) -> Prop} (M : Matrix.{u3, u2, u1} m n α), (forall (p : Matrix.{u3, u2, u1} m n α) (q : Matrix.{u3, u2, u1} m n α), (P p) -> (P q) -> (P (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u3, u2, u1} m n α) (Matrix.{u3, u2, u1} m n α) (Matrix.{u3, u2, u1} m n α) (instHAdd.{max (max u3 u2) u1} (Matrix.{u3, u2, u1} m n α) (Matrix.add.{u1, u3, u2} m n α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))))) p q))) -> (forall (i : m) (j : n) (x : α), P (Matrix.stdBasisMatrix.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j x)) -> (P M)
Case conversion may be inaccurate. Consider using '#align matrix.induction_on Matrix.induction_onₓ'. -/
@[elab_as_elim]
protected theorem induction_on [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    {P : Matrix m n α → Prop} (M : Matrix m n α) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ i j x, P (stdBasisMatrix i j x)) : P M :=
  Matrix.induction_on' M
    (by
      inhabit m
      inhabit n
      simpa using h_std_basis default default 0)
    h_add h_std_basis
#align matrix.induction_on Matrix.induction_on

namespace StdBasisMatrix

section

variable (i : m) (j : n) (c : α) (i' : m) (j' : n)

/- warning: matrix.std_basis_matrix.apply_same -> Matrix.StdBasisMatrix.apply_same is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u3} α] (i : m) (j : n) (c : α), Eq.{succ u3} α (Matrix.stdBasisMatrix.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c i j) c
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : Semiring.{u3} α] (i : m) (j : n) (c : α), Eq.{succ u3} α (Matrix.stdBasisMatrix.{u2, u1, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c i j) c
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix.apply_same Matrix.StdBasisMatrix.apply_sameₓ'. -/
@[simp]
theorem apply_same : stdBasisMatrix i j c i j = c :=
  if_pos (And.intro rfl rfl)
#align matrix.std_basis_matrix.apply_same Matrix.StdBasisMatrix.apply_same

/- warning: matrix.std_basis_matrix.apply_of_ne -> Matrix.StdBasisMatrix.apply_of_ne is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u3} α] (i : m) (j : n) (c : α) (i' : m) (j' : n), (Not (And (Eq.{succ u1} m i i') (Eq.{succ u2} n j j'))) -> (Eq.{succ u3} α (Matrix.stdBasisMatrix.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c i' j') (OfNat.ofNat.{u3} α 0 (OfNat.mk.{u3} α 0 (Zero.zero.{u3} α (MulZeroClass.toHasZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4))))))))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] (i : m) (j : n) (c : α) (i' : m) (j' : n), (Not (And (Eq.{succ u3} m i i') (Eq.{succ u2} n j j'))) -> (Eq.{succ u1} α (Matrix.stdBasisMatrix.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c i' j') (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)))))
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix.apply_of_ne Matrix.StdBasisMatrix.apply_of_neₓ'. -/
@[simp]
theorem apply_of_ne (h : ¬(i = i' ∧ j = j')) : stdBasisMatrix i j c i' j' = 0 := by
  simp only [std_basis_matrix, and_imp, ite_eq_right_iff]; tauto
#align matrix.std_basis_matrix.apply_of_ne Matrix.StdBasisMatrix.apply_of_ne

/- warning: matrix.std_basis_matrix.apply_of_row_ne -> Matrix.StdBasisMatrix.apply_of_row_ne is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u3} α] {i : m} {i' : m}, (Ne.{succ u1} m i i') -> (forall (j : n) (j' : n) (a : α), Eq.{succ u3} α (Matrix.stdBasisMatrix.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j a i' j') (OfNat.ofNat.{u3} α 0 (OfNat.mk.{u3} α 0 (Zero.zero.{u3} α (MulZeroClass.toHasZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4))))))))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u1}} {α : Type.{u2}} [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : Semiring.{u2} α] {i : m} {i' : m}, (Ne.{succ u3} m i i') -> (forall (j : n) (j' : n) (a : α), Eq.{succ u2} α (Matrix.stdBasisMatrix.{u3, u1, u2} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j a i' j') (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_4)))))
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix.apply_of_row_ne Matrix.StdBasisMatrix.apply_of_row_neₓ'. -/
@[simp]
theorem apply_of_row_ne {i i' : m} (hi : i ≠ i') (j j' : n) (a : α) :
    stdBasisMatrix i j a i' j' = 0 := by simp [hi]
#align matrix.std_basis_matrix.apply_of_row_ne Matrix.StdBasisMatrix.apply_of_row_ne

/- warning: matrix.std_basis_matrix.apply_of_col_ne -> Matrix.StdBasisMatrix.apply_of_col_ne is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u3} α] (i : m) (i' : m) {j : n} {j' : n}, (Ne.{succ u2} n j j') -> (forall (a : α), Eq.{succ u3} α (Matrix.stdBasisMatrix.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j a i' j') (OfNat.ofNat.{u3} α 0 (OfNat.mk.{u3} α 0 (Zero.zero.{u3} α (MulZeroClass.toHasZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4))))))))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u3}} {α : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : DecidableEq.{succ u3} n] [_inst_4 : Semiring.{u2} α] (i : m) (i' : m) {j : n} {j' : n}, (Ne.{succ u3} n j j') -> (forall (a : α), Eq.{succ u2} α (Matrix.stdBasisMatrix.{u1, u3, u2} m n α (fun (a : m) (b : m) => _inst_2 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j a i' j') (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_4)))))
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix.apply_of_col_ne Matrix.StdBasisMatrix.apply_of_col_neₓ'. -/
@[simp]
theorem apply_of_col_ne (i i' : m) {j j' : n} (hj : j ≠ j') (a : α) :
    stdBasisMatrix i j a i' j' = 0 := by simp [hj]
#align matrix.std_basis_matrix.apply_of_col_ne Matrix.StdBasisMatrix.apply_of_col_ne

end

section

variable (i j : n) (c : α) (i' j' : n)

/- warning: matrix.std_basis_matrix.diag_zero -> Matrix.StdBasisMatrix.diag_zero is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : Semiring.{u2} α] (i : n) (j : n) (c : α), (Ne.{succ u1} n j i) -> (Eq.{max (succ u1) (succ u2)} (n -> α) (Matrix.diag.{u2, u1} n α (Matrix.stdBasisMatrix.{u1, u1, u2} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c)) (OfNat.ofNat.{max u1 u2} (n -> α) 0 (OfNat.mk.{max u1 u2} (n -> α) 0 (Zero.zero.{max u1 u2} (n -> α) (Pi.instZero.{u1, u2} n (fun (i : n) => α) (fun (i : n) => MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4)))))))))
but is expected to have type
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] (i : n) (j : n) (c : α), (Ne.{succ u2} n j i) -> (Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (Matrix.stdBasisMatrix.{u2, u2, u1} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c)) (OfNat.ofNat.{max u2 u1} (n -> α) 0 (Zero.toOfNat0.{max u2 u1} (n -> α) (Pi.instZero.{u2, u1} n (fun (i : n) => α) (fun (i : n) => MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4))))))
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix.diag_zero Matrix.StdBasisMatrix.diag_zeroₓ'. -/
@[simp]
theorem diag_zero (h : j ≠ i) : diag (stdBasisMatrix i j c) = 0 :=
  funext fun k => if_neg fun ⟨e₁, e₂⟩ => h (e₂.trans e₁.symm)
#align matrix.std_basis_matrix.diag_zero Matrix.StdBasisMatrix.diag_zero

/- warning: matrix.std_basis_matrix.diag_same -> Matrix.StdBasisMatrix.diag_same is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : Semiring.{u2} α] (i : n) (c : α), Eq.{max (succ u1) (succ u2)} (n -> α) (Matrix.diag.{u2, u1} n α (Matrix.stdBasisMatrix.{u1, u1, u2} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i i c)) (Pi.single.{u1, u2} n (fun (i : n) => α) (fun (a : n) (b : n) => _inst_3 a b) (fun (i : n) => MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4)))) i c)
but is expected to have type
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] (i : n) (c : α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (Matrix.stdBasisMatrix.{u2, u2, u1} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i i c)) (Pi.single.{u2, u1} n (fun (i : n) => α) (fun (a : n) (b : n) => _inst_3 a b) (fun (i : n) => MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)) i c)
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix.diag_same Matrix.StdBasisMatrix.diag_sameₓ'. -/
@[simp]
theorem diag_same : diag (stdBasisMatrix i i c) = Pi.single i c := by ext j;
  by_cases hij : i = j <;> try rw [hij] <;> simp [hij]
#align matrix.std_basis_matrix.diag_same Matrix.StdBasisMatrix.diag_same

variable [Fintype n]

/- warning: matrix.std_basis_matrix.trace_zero -> Matrix.StdBasisMatrix.trace_zero is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : Semiring.{u2} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u1} n], (Ne.{succ u1} n j i) -> (Eq.{succ u2} α (Matrix.trace.{u1, u2} n α _inst_5 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))) (Matrix.stdBasisMatrix.{u1, u1, u2} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c)) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))))))))
but is expected to have type
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u2} n], (Ne.{succ u2} n j i) -> (Eq.{succ u1} α (Matrix.trace.{u2, u1} n α _inst_5 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) (Matrix.stdBasisMatrix.{u2, u2, u1} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)))))
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix.trace_zero Matrix.StdBasisMatrix.trace_zeroₓ'. -/
@[simp]
theorem trace_zero (h : j ≠ i) : trace (stdBasisMatrix i j c) = 0 := by simp [trace, h]
#align matrix.std_basis_matrix.trace_zero Matrix.StdBasisMatrix.trace_zero

#print Matrix.StdBasisMatrix.trace_eq /-
@[simp]
theorem trace_eq : trace (stdBasisMatrix i i c) = c := by simp [trace]
#align matrix.std_basis_matrix.trace_eq Matrix.StdBasisMatrix.trace_eq
-/

/- warning: matrix.std_basis_matrix.mul_left_apply_same -> Matrix.StdBasisMatrix.mul_left_apply_same is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : Semiring.{u2} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u1} n] (b : n) (M : Matrix.{u1, u1, u2} n n α), Eq.{succ u2} α (Matrix.mul.{u2, u1, u1, u1} n n n α _inst_5 (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))) (Matrix.stdBasisMatrix.{u1, u1, u2} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c) M i b) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))))) c (M j b))
but is expected to have type
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u2} n] (b : n) (M : Matrix.{u2, u2, u1} n n α), Eq.{succ u1} α (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_5 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) (Matrix.stdBasisMatrix.{u2, u2, u1} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c) M i b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))) c (M j b))
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix.mul_left_apply_same Matrix.StdBasisMatrix.mul_left_apply_sameₓ'. -/
@[simp]
theorem mul_left_apply_same (b : n) (M : Matrix n n α) :
    (stdBasisMatrix i j c ⬝ M) i b = c * M j b := by simp [mul_apply, std_basis_matrix]
#align matrix.std_basis_matrix.mul_left_apply_same Matrix.StdBasisMatrix.mul_left_apply_same

/- warning: matrix.std_basis_matrix.mul_right_apply_same -> Matrix.StdBasisMatrix.mul_right_apply_same is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : Semiring.{u2} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u1} n] (a : n) (M : Matrix.{u1, u1, u2} n n α), Eq.{succ u2} α (Matrix.mul.{u2, u1, u1, u1} n n n α _inst_5 (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))) M (Matrix.stdBasisMatrix.{u1, u1, u2} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c) a j) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))))) (M a i) c)
but is expected to have type
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u2} n] (a : n) (M : Matrix.{u2, u2, u1} n n α), Eq.{succ u1} α (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_5 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) M (Matrix.stdBasisMatrix.{u2, u2, u1} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c) a j) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))) (M a i) c)
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix.mul_right_apply_same Matrix.StdBasisMatrix.mul_right_apply_sameₓ'. -/
@[simp]
theorem mul_right_apply_same (a : n) (M : Matrix n n α) :
    (M ⬝ stdBasisMatrix i j c) a j = M a i * c := by simp [mul_apply, std_basis_matrix, mul_comm]
#align matrix.std_basis_matrix.mul_right_apply_same Matrix.StdBasisMatrix.mul_right_apply_same

/- warning: matrix.std_basis_matrix.mul_left_apply_of_ne -> Matrix.StdBasisMatrix.mul_left_apply_of_ne is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : Semiring.{u2} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u1} n] (a : n) (b : n), (Ne.{succ u1} n a i) -> (forall (M : Matrix.{u1, u1, u2} n n α), Eq.{succ u2} α (Matrix.mul.{u2, u1, u1, u1} n n n α _inst_5 (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))) (Matrix.stdBasisMatrix.{u1, u1, u2} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c) M a b) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))))))))
but is expected to have type
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u2} n] (a : n) (b : n), (Ne.{succ u2} n a i) -> (forall (M : Matrix.{u2, u2, u1} n n α), Eq.{succ u1} α (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_5 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) (Matrix.stdBasisMatrix.{u2, u2, u1} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c) M a b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)))))
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix.mul_left_apply_of_ne Matrix.StdBasisMatrix.mul_left_apply_of_neₓ'. -/
@[simp]
theorem mul_left_apply_of_ne (a b : n) (h : a ≠ i) (M : Matrix n n α) :
    (stdBasisMatrix i j c ⬝ M) a b = 0 := by simp [mul_apply, h.symm]
#align matrix.std_basis_matrix.mul_left_apply_of_ne Matrix.StdBasisMatrix.mul_left_apply_of_ne

/- warning: matrix.std_basis_matrix.mul_right_apply_of_ne -> Matrix.StdBasisMatrix.mul_right_apply_of_ne is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : Semiring.{u2} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u1} n] (a : n) (b : n), (Ne.{succ u1} n b j) -> (forall (M : Matrix.{u1, u1, u2} n n α), Eq.{succ u2} α (Matrix.mul.{u2, u1, u1, u1} n n n α _inst_5 (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))) M (Matrix.stdBasisMatrix.{u1, u1, u2} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c) a b) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))))))))
but is expected to have type
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u2} n] (a : n) (b : n), (Ne.{succ u2} n b j) -> (forall (M : Matrix.{u2, u2, u1} n n α), Eq.{succ u1} α (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_5 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) M (Matrix.stdBasisMatrix.{u2, u2, u1} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c) a b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)))))
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix.mul_right_apply_of_ne Matrix.StdBasisMatrix.mul_right_apply_of_neₓ'. -/
@[simp]
theorem mul_right_apply_of_ne (a b : n) (hbj : b ≠ j) (M : Matrix n n α) :
    (M ⬝ stdBasisMatrix i j c) a b = 0 := by simp [mul_apply, hbj.symm]
#align matrix.std_basis_matrix.mul_right_apply_of_ne Matrix.StdBasisMatrix.mul_right_apply_of_ne

/- warning: matrix.std_basis_matrix.mul_same -> Matrix.StdBasisMatrix.mul_same is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : Semiring.{u2} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u1} n] (k : n) (d : α), Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} n n α) (Matrix.mul.{u2, u1, u1, u1} n n n α _inst_5 (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))) (Matrix.stdBasisMatrix.{u1, u1, u2} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c) (Matrix.stdBasisMatrix.{u1, u1, u2} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 j k d)) (Matrix.stdBasisMatrix.{u1, u1, u2} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i k (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))))) c d))
but is expected to have type
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u2} n] (k : n) (d : α), Eq.{max (succ u2) (succ u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_5 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) (Matrix.stdBasisMatrix.{u2, u2, u1} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c) (Matrix.stdBasisMatrix.{u2, u2, u1} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 j k d)) (Matrix.stdBasisMatrix.{u2, u2, u1} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i k (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))) c d))
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix.mul_same Matrix.StdBasisMatrix.mul_sameₓ'. -/
@[simp]
theorem mul_same (k : n) (d : α) :
    stdBasisMatrix i j c ⬝ stdBasisMatrix j k d = stdBasisMatrix i k (c * d) :=
  by
  ext (a b)
  simp only [mul_apply, std_basis_matrix, boole_mul]
  by_cases h₁ : i = a <;> by_cases h₂ : k = b <;> simp [h₁, h₂]
#align matrix.std_basis_matrix.mul_same Matrix.StdBasisMatrix.mul_same

/- warning: matrix.std_basis_matrix.mul_of_ne -> Matrix.StdBasisMatrix.mul_of_ne is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : Semiring.{u2} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u1} n] {k : n} {l : n}, (Ne.{succ u1} n j k) -> (forall (d : α), Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} n n α) (Matrix.mul.{u2, u1, u1, u1} n n n α _inst_5 (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))) (Matrix.stdBasisMatrix.{u1, u1, u2} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c) (Matrix.stdBasisMatrix.{u1, u1, u2} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 k l d)) (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} n n α) 0 (OfNat.mk.{max u1 u2} (Matrix.{u1, u1, u2} n n α) 0 (Zero.zero.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.hasZero.{u2, u1, u1} n n α (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4)))))))))
but is expected to have type
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : Semiring.{u1} α] (i : n) (j : n) (c : α) [_inst_5 : Fintype.{u2} n] {k : n} {l : n}, (Ne.{succ u2} n j k) -> (forall (d : α), Eq.{max (succ u2) (succ u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_5 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))) (Matrix.stdBasisMatrix.{u2, u2, u1} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 i j c) (Matrix.stdBasisMatrix.{u2, u2, u1} n n α (fun (a : n) (b : n) => _inst_3 a b) (fun (a : n) (b : n) => _inst_3 a b) _inst_4 k l d)) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 0 (Zero.toOfNat0.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.zero.{u1, u2, u2} n n α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4))))))
Case conversion may be inaccurate. Consider using '#align matrix.std_basis_matrix.mul_of_ne Matrix.StdBasisMatrix.mul_of_neₓ'. -/
@[simp]
theorem mul_of_ne {k l : n} (h : j ≠ k) (d : α) : stdBasisMatrix i j c ⬝ stdBasisMatrix k l d = 0 :=
  by
  ext (a b)
  simp only [mul_apply, boole_mul, std_basis_matrix]
  by_cases h₁ : i = a <;> simp [h₁, h, h.symm]
#align matrix.std_basis_matrix.mul_of_ne Matrix.StdBasisMatrix.mul_of_ne

end

end StdBasisMatrix

end Matrix

