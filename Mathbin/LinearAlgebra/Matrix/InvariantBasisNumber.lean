/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module linear_algebra.matrix.invariant_basis_number
! leanprover-community/mathlib commit 843240b048bbb19942c581fd64caecbbe96337be
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

/- warning: matrix.square_of_invertible -> Matrix.square_of_invertible is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {m : Type.{u2}} [_inst_1 : Fintype.{u1} n] [_inst_2 : DecidableEq.{succ u1} n] [_inst_3 : Fintype.{u2} m] [_inst_4 : DecidableEq.{succ u2} m] {R : Type.{u3}} [_inst_5 : Semiring.{u3} R] [_inst_6 : InvariantBasisNumber.{u3} R _inst_5] (M : Matrix.{u1, u2, u3} n m R) (N : Matrix.{u2, u1, u3} m n R), (Eq.{succ (max u1 u3)} (Matrix.{u1, u1, u3} n n R) (Matrix.mul.{u3, u1, u2, u1} n m n R _inst_3 (Distrib.toHasMul.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_5)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_5))) M N) (OfNat.ofNat.{max u1 u3} (Matrix.{u1, u1, u3} n n R) 1 (OfNat.mk.{max u1 u3} (Matrix.{u1, u1, u3} n n R) 1 (One.one.{max u1 u3} (Matrix.{u1, u1, u3} n n R) (Matrix.hasOne.{u3, u1} n R (fun (a : n) (b : n) => _inst_2 a b) (MulZeroClass.toHasZero.{u3} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_5)))) (AddMonoidWithOne.toOne.{u3} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} R (NonAssocSemiring.toAddCommMonoidWithOne.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_5))))))))) -> (Eq.{succ (max u2 u3)} (Matrix.{u2, u2, u3} m m R) (Matrix.mul.{u3, u2, u1, u2} m n m R _inst_1 (Distrib.toHasMul.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_5)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_5))) N M) (OfNat.ofNat.{max u2 u3} (Matrix.{u2, u2, u3} m m R) 1 (OfNat.mk.{max u2 u3} (Matrix.{u2, u2, u3} m m R) 1 (One.one.{max u2 u3} (Matrix.{u2, u2, u3} m m R) (Matrix.hasOne.{u3, u2} m R (fun (a : m) (b : m) => _inst_4 a b) (MulZeroClass.toHasZero.{u3} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_5)))) (AddMonoidWithOne.toOne.{u3} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} R (NonAssocSemiring.toAddCommMonoidWithOne.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_5))))))))) -> (Eq.{1} Nat (Fintype.card.{u1} n _inst_1) (Fintype.card.{u2} m _inst_3))
but is expected to have type
  forall {n : Type.{u3}} {m : Type.{u2}} [_inst_1 : Fintype.{u3} n] [_inst_2 : DecidableEq.{succ u3} n] [_inst_3 : Fintype.{u2} m] [_inst_4 : DecidableEq.{succ u2} m] {R : Type.{u1}} [_inst_5 : Semiring.{u1} R] [_inst_6 : InvariantBasisNumber.{u1} R _inst_5] (M : Matrix.{u3, u2, u1} n m R) (N : Matrix.{u2, u3, u1} m n R), (Eq.{max (succ u3) (succ u1)} (Matrix.{u3, u3, u1} n n R) (Matrix.mul.{u1, u3, u2, u3} n m n R _inst_3 (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5))) M N) (OfNat.ofNat.{max u3 u1} (Matrix.{u3, u3, u1} n n R) 1 (One.toOfNat1.{max u3 u1} (Matrix.{u3, u3, u1} n n R) (Matrix.one.{u1, u3} n R (fun (a : n) (b : n) => _inst_2 a b) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_5)) (Semiring.toOne.{u1} R _inst_5))))) -> (Eq.{max (succ u2) (succ u1)} (Matrix.{u2, u2, u1} m m R) (Matrix.mul.{u1, u2, u3, u2} m n m R _inst_1 (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5))) N M) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} m m R) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u2, u2, u1} m m R) (Matrix.one.{u1, u2} m R (fun (a : m) (b : m) => _inst_4 a b) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_5)) (Semiring.toOne.{u1} R _inst_5))))) -> (Eq.{1} Nat (Fintype.card.{u3} n _inst_1) (Fintype.card.{u2} m _inst_3))
Case conversion may be inaccurate. Consider using '#align matrix.square_of_invertible Matrix.square_of_invertibleₓ'. -/
theorem Matrix.square_of_invertible (M : Matrix n m R) (N : Matrix m n R) (h : M ⬝ N = 1)
    (h' : N ⬝ M = 1) : Fintype.card n = Fintype.card m :=
  card_eq_of_linearEquiv R (Matrix.toLinearEquivRight'OfInv h' h)
#align matrix.square_of_invertible Matrix.square_of_invertible

