/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang

! This file was ported from Lean 3 source module data.matrix.hadamard
! leanprover-community/mathlib commit 3e068ece210655b7b9a9477c3aff38a492400aa1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.Trace

/-!
# Hadamard product of matrices

This file defines the Hadamard product `matrix.hadamard`
and contains basic properties about them.

## Main definition

- `matrix.hadamard`: defines the Hadamard product,
  which is the pointwise product of two matrices of the same size.

## Notation

* `⊙`: the Hadamard product `matrix.hadamard`;

## References

*  <https://en.wikipedia.org/wiki/hadamard_product_(matrices)>

## Tags

hadamard product, hadamard
-/


variable {α β γ m n : Type _}

variable {R : Type _}

namespace Matrix

open Matrix BigOperators

#print Matrix.hadamard /-
/-- `matrix.hadamard` defines the Hadamard product,
    which is the pointwise product of two matrices of the same size.-/
def hadamard [Mul α] (A : Matrix m n α) (B : Matrix m n α) : Matrix m n α :=
  of fun i j => A i j * B i j
#align matrix.hadamard Matrix.hadamard
-/

/- warning: matrix.hadamard_apply -> Matrix.hadamard_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} [_inst_1 : Mul.{u1} α] (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u3, u1} m n α) (i : m) (j : n), Eq.{succ u1} α (Matrix.hadamard.{u1, u2, u3} α m n _inst_1 A B i j) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (A i j) (B i j))
but is expected to have type
  forall {α : Type.{u3}} {m : Type.{u2}} {n : Type.{u1}} [_inst_1 : Mul.{u3} α] (A : Matrix.{u2, u1, u3} m n α) (B : Matrix.{u2, u1, u3} m n α) (i : m) (j : n), Eq.{succ u3} α (Matrix.hadamard.{u3, u2, u1} α m n _inst_1 A B i j) (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α _inst_1) (A i j) (B i j))
Case conversion may be inaccurate. Consider using '#align matrix.hadamard_apply Matrix.hadamard_applyₓ'. -/
-- TODO: set as an equation lemma for `hadamard`, see mathlib4#3024
@[simp]
theorem hadamard_apply [Mul α] (A : Matrix m n α) (B : Matrix m n α) (i j) :
    hadamard A B i j = A i j * B i j :=
  rfl
#align matrix.hadamard_apply Matrix.hadamard_apply

-- mathport name: matrix.hadamard
scoped infixl:100 " ⊙ " => Matrix.hadamard

section BasicProperties

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

/- warning: matrix.hadamard_comm -> Matrix.hadamard_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u3, u1} m n α) [_inst_1 : CommSemigroup.{u1} α], Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.hadamard.{u1, u2, u3} α m n (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) A B) (Matrix.hadamard.{u1, u2, u3} α m n (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) B A)
but is expected to have type
  forall {α : Type.{u3}} {m : Type.{u2}} {n : Type.{u1}} (A : Matrix.{u2, u1, u3} m n α) (B : Matrix.{u2, u1, u3} m n α) [_inst_1 : CommSemigroup.{u3} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.hadamard.{u3, u2, u1} α m n (Semigroup.toMul.{u3} α (CommSemigroup.toSemigroup.{u3} α _inst_1)) A B) (Matrix.hadamard.{u3, u2, u1} α m n (Semigroup.toMul.{u3} α (CommSemigroup.toSemigroup.{u3} α _inst_1)) B A)
Case conversion may be inaccurate. Consider using '#align matrix.hadamard_comm Matrix.hadamard_commₓ'. -/
-- commutativity
theorem hadamard_comm [CommSemigroup α] : A ⊙ B = B ⊙ A :=
  ext fun _ _ => mul_comm _ _
#align matrix.hadamard_comm Matrix.hadamard_comm

/- warning: matrix.hadamard_assoc -> Matrix.hadamard_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u3, u1} m n α) (C : Matrix.{u2, u3, u1} m n α) [_inst_1 : Semigroup.{u1} α], Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.hadamard.{u1, u2, u3} α m n (Semigroup.toHasMul.{u1} α _inst_1) (Matrix.hadamard.{u1, u2, u3} α m n (Semigroup.toHasMul.{u1} α _inst_1) A B) C) (Matrix.hadamard.{u1, u2, u3} α m n (Semigroup.toHasMul.{u1} α _inst_1) A (Matrix.hadamard.{u1, u2, u3} α m n (Semigroup.toHasMul.{u1} α _inst_1) B C))
but is expected to have type
  forall {α : Type.{u3}} {m : Type.{u2}} {n : Type.{u1}} (A : Matrix.{u2, u1, u3} m n α) (B : Matrix.{u2, u1, u3} m n α) (C : Matrix.{u2, u1, u3} m n α) [_inst_1 : Semigroup.{u3} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.hadamard.{u3, u2, u1} α m n (Semigroup.toMul.{u3} α _inst_1) (Matrix.hadamard.{u3, u2, u1} α m n (Semigroup.toMul.{u3} α _inst_1) A B) C) (Matrix.hadamard.{u3, u2, u1} α m n (Semigroup.toMul.{u3} α _inst_1) A (Matrix.hadamard.{u3, u2, u1} α m n (Semigroup.toMul.{u3} α _inst_1) B C))
Case conversion may be inaccurate. Consider using '#align matrix.hadamard_assoc Matrix.hadamard_assocₓ'. -/
-- associativity
theorem hadamard_assoc [Semigroup α] : A ⊙ B ⊙ C = A ⊙ (B ⊙ C) :=
  ext fun _ _ => mul_assoc _ _ _
#align matrix.hadamard_assoc Matrix.hadamard_assoc

/- warning: matrix.hadamard_add -> Matrix.hadamard_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u3, u1} m n α) (C : Matrix.{u2, u3, u1} m n α) [_inst_1 : Distrib.{u1} α], Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.hadamard.{u1, u2, u3} α m n (Distrib.toHasMul.{u1} α _inst_1) A (HAdd.hAdd.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHAdd.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u2, u3} m n α (Distrib.toHasAdd.{u1} α _inst_1))) B C)) (HAdd.hAdd.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHAdd.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u2, u3} m n α (Distrib.toHasAdd.{u1} α _inst_1))) (Matrix.hadamard.{u1, u2, u3} α m n (Distrib.toHasMul.{u1} α _inst_1) A B) (Matrix.hadamard.{u1, u2, u3} α m n (Distrib.toHasMul.{u1} α _inst_1) A C))
but is expected to have type
  forall {α : Type.{u3}} {m : Type.{u2}} {n : Type.{u1}} (A : Matrix.{u2, u1, u3} m n α) (B : Matrix.{u2, u1, u3} m n α) (C : Matrix.{u2, u1, u3} m n α) [_inst_1 : Distrib.{u3} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.hadamard.{u3, u2, u1} α m n (Distrib.toMul.{u3} α _inst_1) A (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHAdd.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.add.{u3, u2, u1} m n α (Distrib.toAdd.{u3} α _inst_1))) B C)) (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHAdd.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.add.{u3, u2, u1} m n α (Distrib.toAdd.{u3} α _inst_1))) (Matrix.hadamard.{u3, u2, u1} α m n (Distrib.toMul.{u3} α _inst_1) A B) (Matrix.hadamard.{u3, u2, u1} α m n (Distrib.toMul.{u3} α _inst_1) A C))
Case conversion may be inaccurate. Consider using '#align matrix.hadamard_add Matrix.hadamard_addₓ'. -/
-- distributivity
theorem hadamard_add [Distrib α] : A ⊙ (B + C) = A ⊙ B + A ⊙ C :=
  ext fun _ _ => left_distrib _ _ _
#align matrix.hadamard_add Matrix.hadamard_add

/- warning: matrix.add_hadamard -> Matrix.add_hadamard is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u3, u1} m n α) (C : Matrix.{u2, u3, u1} m n α) [_inst_1 : Distrib.{u1} α], Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.hadamard.{u1, u2, u3} α m n (Distrib.toHasMul.{u1} α _inst_1) (HAdd.hAdd.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHAdd.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u2, u3} m n α (Distrib.toHasAdd.{u1} α _inst_1))) B C) A) (HAdd.hAdd.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHAdd.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u2, u3} m n α (Distrib.toHasAdd.{u1} α _inst_1))) (Matrix.hadamard.{u1, u2, u3} α m n (Distrib.toHasMul.{u1} α _inst_1) B A) (Matrix.hadamard.{u1, u2, u3} α m n (Distrib.toHasMul.{u1} α _inst_1) C A))
but is expected to have type
  forall {α : Type.{u3}} {m : Type.{u2}} {n : Type.{u1}} (A : Matrix.{u2, u1, u3} m n α) (B : Matrix.{u2, u1, u3} m n α) (C : Matrix.{u2, u1, u3} m n α) [_inst_1 : Distrib.{u3} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.hadamard.{u3, u2, u1} α m n (Distrib.toMul.{u3} α _inst_1) (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHAdd.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.add.{u3, u2, u1} m n α (Distrib.toAdd.{u3} α _inst_1))) B C) A) (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHAdd.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.add.{u3, u2, u1} m n α (Distrib.toAdd.{u3} α _inst_1))) (Matrix.hadamard.{u3, u2, u1} α m n (Distrib.toMul.{u3} α _inst_1) B A) (Matrix.hadamard.{u3, u2, u1} α m n (Distrib.toMul.{u3} α _inst_1) C A))
Case conversion may be inaccurate. Consider using '#align matrix.add_hadamard Matrix.add_hadamardₓ'. -/
theorem add_hadamard [Distrib α] : (B + C) ⊙ A = B ⊙ A + C ⊙ A :=
  ext fun _ _ => right_distrib _ _ _
#align matrix.add_hadamard Matrix.add_hadamard

-- scalar multiplication
section Scalar

/- warning: matrix.smul_hadamard -> Matrix.smul_hadamard is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u3, u1} m n α) [_inst_1 : Mul.{u1} α] [_inst_2 : SMul.{u4, u1} R α] [_inst_3 : IsScalarTower.{u4, u1, u1} R α α _inst_2 (Mul.toSMul.{u1} α _inst_1) _inst_2] (k : R), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.hadamard.{u1, u2, u3} α m n _inst_1 (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α _inst_2) k A) B) (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α _inst_2) k (Matrix.hadamard.{u1, u2, u3} α m n _inst_1 A B))
but is expected to have type
  forall {α : Type.{u4}} {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} (A : Matrix.{u2, u1, u4} m n α) (B : Matrix.{u2, u1, u4} m n α) [_inst_1 : Mul.{u4} α] [_inst_2 : SMul.{u3, u4} R α] [_inst_3 : IsScalarTower.{u3, u4, u4} R α α _inst_2 (Mul.toSMul.{u4} α _inst_1) _inst_2] (k : R), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u2, u1, u4} m n α) (Matrix.hadamard.{u4, u2, u1} α m n _inst_1 (HSMul.hSMul.{u3, max (max u4 u2) u1, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u4} m n α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.smul.{u4, u2, u1, u3} m n R α _inst_2)) k A) B) (HSMul.hSMul.{u3, max (max u1 u2) u4, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u4} m n α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.smul.{u4, u2, u1, u3} m n R α _inst_2)) k (Matrix.hadamard.{u4, u2, u1} α m n _inst_1 A B))
Case conversion may be inaccurate. Consider using '#align matrix.smul_hadamard Matrix.smul_hadamardₓ'. -/
@[simp]
theorem smul_hadamard [Mul α] [SMul R α] [IsScalarTower R α α] (k : R) : (k • A) ⊙ B = k • A ⊙ B :=
  ext fun _ _ => smul_mul_assoc _ _ _
#align matrix.smul_hadamard Matrix.smul_hadamard

/- warning: matrix.hadamard_smul -> Matrix.hadamard_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u3, u1} m n α) [_inst_1 : Mul.{u1} α] [_inst_2 : SMul.{u4, u1} R α] [_inst_3 : SMulCommClass.{u4, u1, u1} R α α _inst_2 (Mul.toSMul.{u1} α _inst_1)] (k : R), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.hadamard.{u1, u2, u3} α m n _inst_1 A (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α _inst_2) k B)) (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α _inst_2) k (Matrix.hadamard.{u1, u2, u3} α m n _inst_1 A B))
but is expected to have type
  forall {α : Type.{u4}} {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} (A : Matrix.{u2, u1, u4} m n α) (B : Matrix.{u2, u1, u4} m n α) [_inst_1 : Mul.{u4} α] [_inst_2 : SMul.{u3, u4} R α] [_inst_3 : SMulCommClass.{u3, u4, u4} R α α _inst_2 (Mul.toSMul.{u4} α _inst_1)] (k : R), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u2, u1, u4} m n α) (Matrix.hadamard.{u4, u2, u1} α m n _inst_1 A (HSMul.hSMul.{u3, max (max u4 u2) u1, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u4} m n α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.smul.{u4, u2, u1, u3} m n R α _inst_2)) k B)) (HSMul.hSMul.{u3, max (max u1 u2) u4, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u4} m n α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.smul.{u4, u2, u1, u3} m n R α _inst_2)) k (Matrix.hadamard.{u4, u2, u1} α m n _inst_1 A B))
Case conversion may be inaccurate. Consider using '#align matrix.hadamard_smul Matrix.hadamard_smulₓ'. -/
@[simp]
theorem hadamard_smul [Mul α] [SMul R α] [SMulCommClass R α α] (k : R) : A ⊙ (k • B) = k • A ⊙ B :=
  ext fun _ _ => mul_smul_comm _ _ _
#align matrix.hadamard_smul Matrix.hadamard_smul

end Scalar

section Zero

variable [MulZeroClass α]

/- warning: matrix.hadamard_zero -> Matrix.hadamard_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} (A : Matrix.{u2, u3, u1} m n α) [_inst_1 : MulZeroClass.{u1} α], Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.hadamard.{u1, u2, u3} α m n (MulZeroClass.toHasMul.{u1} α _inst_1) A (OfNat.ofNat.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (OfNat.mk.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (Zero.zero.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasZero.{u1, u2, u3} m n α (MulZeroClass.toHasZero.{u1} α _inst_1)))))) (OfNat.ofNat.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (OfNat.mk.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (Zero.zero.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasZero.{u1, u2, u3} m n α (MulZeroClass.toHasZero.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u3}} {m : Type.{u2}} {n : Type.{u1}} (A : Matrix.{u2, u1, u3} m n α) [_inst_1 : MulZeroClass.{u3} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.hadamard.{u3, u2, u1} α m n (MulZeroClass.toMul.{u3} α _inst_1) A (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.zero.{u3, u2, u1} m n α (MulZeroClass.toZero.{u3} α _inst_1))))) (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.zero.{u3, u2, u1} m n α (MulZeroClass.toZero.{u3} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align matrix.hadamard_zero Matrix.hadamard_zeroₓ'. -/
@[simp]
theorem hadamard_zero : A ⊙ (0 : Matrix m n α) = 0 :=
  ext fun _ _ => MulZeroClass.mul_zero _
#align matrix.hadamard_zero Matrix.hadamard_zero

/- warning: matrix.zero_hadamard -> Matrix.zero_hadamard is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} (A : Matrix.{u2, u3, u1} m n α) [_inst_1 : MulZeroClass.{u1} α], Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.hadamard.{u1, u2, u3} α m n (MulZeroClass.toHasMul.{u1} α _inst_1) (OfNat.ofNat.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (OfNat.mk.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (Zero.zero.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasZero.{u1, u2, u3} m n α (MulZeroClass.toHasZero.{u1} α _inst_1))))) A) (OfNat.ofNat.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (OfNat.mk.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (Zero.zero.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasZero.{u1, u2, u3} m n α (MulZeroClass.toHasZero.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u3}} {m : Type.{u2}} {n : Type.{u1}} (A : Matrix.{u2, u1, u3} m n α) [_inst_1 : MulZeroClass.{u3} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.hadamard.{u3, u2, u1} α m n (MulZeroClass.toMul.{u3} α _inst_1) (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.zero.{u3, u2, u1} m n α (MulZeroClass.toZero.{u3} α _inst_1)))) A) (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.zero.{u3, u2, u1} m n α (MulZeroClass.toZero.{u3} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align matrix.zero_hadamard Matrix.zero_hadamardₓ'. -/
@[simp]
theorem zero_hadamard : (0 : Matrix m n α) ⊙ A = 0 :=
  ext fun _ _ => MulZeroClass.zero_mul _
#align matrix.zero_hadamard Matrix.zero_hadamard

end Zero

section One

variable [DecidableEq n] [MulZeroOneClass α]

variable (M : Matrix n n α)

/- warning: matrix.hadamard_one -> Matrix.hadamard_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : MulZeroOneClass.{u1} α] (M : Matrix.{u2, u2, u1} n n α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.hadamard.{u1, u2, u2} α n n (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2)) M (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2)) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α _inst_2))))))) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2)) (fun (i : n) => M i i))
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : MulZeroOneClass.{u2} α] (M : Matrix.{u1, u1, u2} n n α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Matrix.hadamard.{u2, u1, u1} α n n (MulZeroClass.toMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_2)) M (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α _inst_2) (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_2)))))) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α _inst_2) (fun (i : n) => M i i))
Case conversion may be inaccurate. Consider using '#align matrix.hadamard_one Matrix.hadamard_oneₓ'. -/
theorem hadamard_one : M ⊙ (1 : Matrix n n α) = diagonal fun i => M i i :=
  by
  ext
  by_cases h : i = j <;> simp [h]
#align matrix.hadamard_one Matrix.hadamard_one

/- warning: matrix.one_hadamard -> Matrix.one_hadamard is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : MulZeroOneClass.{u1} α] (M : Matrix.{u2, u2, u1} n n α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.hadamard.{u1, u2, u2} α n n (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2)) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2)) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α _inst_2)))))) M) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2)) (fun (i : n) => M i i))
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : MulZeroOneClass.{u2} α] (M : Matrix.{u1, u1, u2} n n α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Matrix.hadamard.{u2, u1, u1} α n n (MulZeroClass.toMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_2)) (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α _inst_2) (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_2))))) M) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α _inst_2) (fun (i : n) => M i i))
Case conversion may be inaccurate. Consider using '#align matrix.one_hadamard Matrix.one_hadamardₓ'. -/
theorem one_hadamard : (1 : Matrix n n α) ⊙ M = diagonal fun i => M i i :=
  by
  ext
  by_cases h : i = j <;> simp [h]
#align matrix.one_hadamard Matrix.one_hadamard

end One

section Diagonal

variable [DecidableEq n] [MulZeroClass α]

/- warning: matrix.diagonal_hadamard_diagonal -> Matrix.diagonal_hadamard_diagonal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : MulZeroClass.{u1} α] (v : n -> α) (w : n -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.hadamard.{u1, u2, u2} α n n (MulZeroClass.toHasMul.{u1} α _inst_2) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α _inst_2) v) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α _inst_2) w)) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α _inst_2) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (n -> α) (n -> α) (n -> α) (instHMul.{max u2 u1} (n -> α) (Pi.instMul.{u2, u1} n (fun (ᾰ : n) => α) (fun (i : n) => MulZeroClass.toHasMul.{u1} α _inst_2))) v w))
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : MulZeroClass.{u2} α] (v : n -> α) (w : n -> α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Matrix.hadamard.{u2, u1, u1} α n n (MulZeroClass.toMul.{u2} α _inst_2) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toZero.{u2} α _inst_2) v) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toZero.{u2} α _inst_2) w)) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toZero.{u2} α _inst_2) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (n -> α) (n -> α) (n -> α) (instHMul.{max u2 u1} (n -> α) (Pi.instMul.{u1, u2} n (fun (ᾰ : n) => α) (fun (i : n) => MulZeroClass.toMul.{u2} α _inst_2))) v w))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_hadamard_diagonal Matrix.diagonal_hadamard_diagonalₓ'. -/
theorem diagonal_hadamard_diagonal (v : n → α) (w : n → α) :
    diagonal v ⊙ diagonal w = diagonal (v * w) :=
  ext fun _ _ => (apply_ite₂ _ _ _ _ _ _).trans (congr_arg _ <| MulZeroClass.zero_mul 0)
#align matrix.diagonal_hadamard_diagonal Matrix.diagonal_hadamard_diagonal

end Diagonal

section trace

variable [Fintype m] [Fintype n]

variable (R) [Semiring α] [Semiring R] [Module R α]

/- warning: matrix.sum_hadamard_eq -> Matrix.sum_hadamard_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u3, u1} m n α) [_inst_1 : Fintype.{u2} m] [_inst_2 : Fintype.{u3} n] [_inst_3 : Semiring.{u1} α], Eq.{succ u1} α (Finset.sum.{u1, u2} α m (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (Finset.univ.{u2} m _inst_1) (fun (i : m) => Finset.sum.{u1, u3} α n (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (Finset.univ.{u3} n _inst_2) (fun (j : n) => Matrix.hadamard.{u1, u2, u3} α m n (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) A B i j))) (Matrix.trace.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (Matrix.mul.{u1, u2, u3, u2} m n m α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) A (Matrix.transpose.{u1, u2, u3} m n α B)))
but is expected to have type
  forall {α : Type.{u3}} {m : Type.{u2}} {n : Type.{u1}} (A : Matrix.{u2, u1, u3} m n α) (B : Matrix.{u2, u1, u3} m n α) [_inst_1 : Fintype.{u2} m] [_inst_2 : Fintype.{u1} n] [_inst_3 : Semiring.{u3} α], Eq.{succ u3} α (Finset.sum.{u3, u2} α m (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_3))) (Finset.univ.{u2} m _inst_1) (fun (i : m) => Finset.sum.{u3, u1} α n (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_3))) (Finset.univ.{u1} n _inst_2) (fun (j : n) => Matrix.hadamard.{u3, u2, u1} α m n (NonUnitalNonAssocSemiring.toMul.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_3))) A B i j))) (Matrix.trace.{u2, u3} m α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_3))) (Matrix.mul.{u3, u2, u1, u2} m n m α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_3))) A (Matrix.transpose.{u3, u2, u1} m n α B)))
Case conversion may be inaccurate. Consider using '#align matrix.sum_hadamard_eq Matrix.sum_hadamard_eqₓ'. -/
theorem sum_hadamard_eq : (∑ (i : m) (j : n), (A ⊙ B) i j) = trace (A ⬝ Bᵀ) :=
  rfl
#align matrix.sum_hadamard_eq Matrix.sum_hadamard_eq

/- warning: matrix.dot_product_vec_mul_hadamard -> Matrix.dotProduct_vecMul_hadamard is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u3, u1} m n α) [_inst_1 : Fintype.{u2} m] [_inst_2 : Fintype.{u3} n] [_inst_3 : Semiring.{u1} α] [_inst_6 : DecidableEq.{succ u2} m] [_inst_7 : DecidableEq.{succ u3} n] (v : m -> α) (w : n -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u3} n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (Matrix.vecMul.{u1, u2, u3} m n α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)) _inst_1 v (Matrix.hadamard.{u1, u2, u3} α m n (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) A B)) w) (Matrix.trace.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (Matrix.mul.{u1, u2, u3, u2} m n m α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (Matrix.mul.{u1, u2, u2, u3} m m n α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (Matrix.diagonal.{u1, u2} m α (fun (a : m) (b : m) => _inst_6 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) v) A) (Matrix.transpose.{u1, u2, u3} m n α (Matrix.mul.{u1, u2, u3, u3} m n n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) B (Matrix.diagonal.{u1, u3} n α (fun (a : n) (b : n) => _inst_7 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)))) w)))))
but is expected to have type
  forall {α : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} (A : Matrix.{u3, u2, u1} m n α) (B : Matrix.{u3, u2, u1} m n α) [_inst_1 : Fintype.{u3} m] [_inst_2 : Fintype.{u2} n] [_inst_3 : Semiring.{u1} α] [_inst_6 : DecidableEq.{succ u3} m] [_inst_7 : DecidableEq.{succ u2} n] (v : m -> α) (w : n -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (Matrix.vecMul.{u1, u3, u2} m n α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3)) _inst_1 v (Matrix.hadamard.{u1, u3, u2} α m n (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) A B)) w) (Matrix.trace.{u3, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (Matrix.mul.{u1, u3, u2, u3} m n m α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (Matrix.mul.{u1, u3, u3, u2} m m n α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (Matrix.diagonal.{u1, u3} m α (fun (a : m) (b : m) => _inst_6 a b) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_3)) v) A) (Matrix.transpose.{u1, u3, u2} m n α (Matrix.mul.{u1, u3, u2, u2} m n n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_3))) B (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_7 a b) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_3)) w)))))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_vec_mul_hadamard Matrix.dotProduct_vecMul_hadamardₓ'. -/
theorem dotProduct_vecMul_hadamard [DecidableEq m] [DecidableEq n] (v : m → α) (w : n → α) :
    dotProduct (vecMul v (A ⊙ B)) w = trace (diagonal v ⬝ A ⬝ (B ⬝ diagonal w)ᵀ) :=
  by
  rw [← sum_hadamard_eq, Finset.sum_comm]
  simp [dot_product, vec_mul, Finset.sum_mul, mul_assoc]
#align matrix.dot_product_vec_mul_hadamard Matrix.dotProduct_vecMul_hadamard

end trace

end BasicProperties

end Matrix

