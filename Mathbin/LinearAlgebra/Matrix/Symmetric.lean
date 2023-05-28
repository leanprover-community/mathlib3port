/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang

! This file was ported from Lean 3 source module linear_algebra.matrix.symmetric
! leanprover-community/mathlib commit d64d67d000b974f0d86a2be7918cf800be6271c8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Block

/-!
# Symmetric matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition and basic results about symmetric matrices.

## Main definition

 * `matrix.is_symm `: a matrix `A : matrix n n α` is "symmetric" if `Aᵀ = A`.

## Tags

symm, symmetric, matrix
-/


variable {α β n m R : Type _}

namespace Matrix

open Matrix

#print Matrix.IsSymm /-
/-- A matrix `A : matrix n n α` is "symmetric" if `Aᵀ = A`. -/
def IsSymm (A : Matrix n n α) : Prop :=
  Aᵀ = A
#align matrix.is_symm Matrix.IsSymm
-/

#print Matrix.IsSymm.eq /-
theorem IsSymm.eq {A : Matrix n n α} (h : A.IsSymm) : Aᵀ = A :=
  h
#align matrix.is_symm.eq Matrix.IsSymm.eq
-/

#print Matrix.IsSymm.ext_iff /-
/-- A version of `matrix.ext_iff` that unfolds the `matrix.transpose`. -/
theorem IsSymm.ext_iff {A : Matrix n n α} : A.IsSymm ↔ ∀ i j, A j i = A i j :=
  Matrix.ext_iff.symm
#align matrix.is_symm.ext_iff Matrix.IsSymm.ext_iff
-/

#print Matrix.IsSymm.ext /-
/-- A version of `matrix.ext` that unfolds the `matrix.transpose`. -/
@[ext]
theorem IsSymm.ext {A : Matrix n n α} : (∀ i j, A j i = A i j) → A.IsSymm :=
  Matrix.ext
#align matrix.is_symm.ext Matrix.IsSymm.ext
-/

#print Matrix.IsSymm.apply /-
theorem IsSymm.apply {A : Matrix n n α} (h : A.IsSymm) (i j : n) : A j i = A i j :=
  IsSymm.ext_iff.1 h i j
#align matrix.is_symm.apply Matrix.IsSymm.apply
-/

/- warning: matrix.is_symm_mul_transpose_self -> Matrix.isSymm_mul_transpose_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} [_inst_1 : Fintype.{u2} n] [_inst_2 : CommSemiring.{u1} α] (A : Matrix.{u2, u2, u1} n n α), Matrix.IsSymm.{u1, u2} α n (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)))) A (Matrix.transpose.{u1, u2, u2} n n α A))
but is expected to have type
  forall {α : Type.{u1}} {n : Type.{u2}} [_inst_1 : Fintype.{u2} n] [_inst_2 : CommSemiring.{u1} α] (A : Matrix.{u2, u2, u1} n n α), Matrix.IsSymm.{u1, u2} α n (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)))) A (Matrix.transpose.{u1, u2, u2} n n α A))
Case conversion may be inaccurate. Consider using '#align matrix.is_symm_mul_transpose_self Matrix.isSymm_mul_transpose_selfₓ'. -/
theorem isSymm_mul_transpose_self [Fintype n] [CommSemiring α] (A : Matrix n n α) :
    (A ⬝ Aᵀ).IsSymm :=
  transpose_mul _ _
#align matrix.is_symm_mul_transpose_self Matrix.isSymm_mul_transpose_self

/- warning: matrix.is_symm_transpose_mul_self -> Matrix.isSymm_transpose_mul_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} [_inst_1 : Fintype.{u2} n] [_inst_2 : CommSemiring.{u1} α] (A : Matrix.{u2, u2, u1} n n α), Matrix.IsSymm.{u1, u2} α n (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)))) (Matrix.transpose.{u1, u2, u2} n n α A) A)
but is expected to have type
  forall {α : Type.{u1}} {n : Type.{u2}} [_inst_1 : Fintype.{u2} n] [_inst_2 : CommSemiring.{u1} α] (A : Matrix.{u2, u2, u1} n n α), Matrix.IsSymm.{u1, u2} α n (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)))) (Matrix.transpose.{u1, u2, u2} n n α A) A)
Case conversion may be inaccurate. Consider using '#align matrix.is_symm_transpose_mul_self Matrix.isSymm_transpose_mul_selfₓ'. -/
theorem isSymm_transpose_mul_self [Fintype n] [CommSemiring α] (A : Matrix n n α) :
    (Aᵀ ⬝ A).IsSymm :=
  transpose_mul _ _
#align matrix.is_symm_transpose_mul_self Matrix.isSymm_transpose_mul_self

/- warning: matrix.is_symm_add_transpose_self -> Matrix.isSymm_add_transpose_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} [_inst_1 : AddCommSemigroup.{u1} α] (A : Matrix.{u2, u2, u1} n n α), Matrix.IsSymm.{u1, u2} α n (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (instHAdd.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasAdd.{u1, u2, u2} n n α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_1)))) A (Matrix.transpose.{u1, u2, u2} n n α A))
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} [_inst_1 : AddCommSemigroup.{u2} α] (A : Matrix.{u1, u1, u2} n n α), Matrix.IsSymm.{u2, u1} α n (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHAdd.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.add.{u2, u1, u1} n n α (AddSemigroup.toAdd.{u2} α (AddCommSemigroup.toAddSemigroup.{u2} α _inst_1)))) A (Matrix.transpose.{u2, u1, u1} n n α A))
Case conversion may be inaccurate. Consider using '#align matrix.is_symm_add_transpose_self Matrix.isSymm_add_transpose_selfₓ'. -/
theorem isSymm_add_transpose_self [AddCommSemigroup α] (A : Matrix n n α) : (A + Aᵀ).IsSymm :=
  add_comm _ _
#align matrix.is_symm_add_transpose_self Matrix.isSymm_add_transpose_self

/- warning: matrix.is_symm_transpose_add_self -> Matrix.isSymm_transpose_add_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} [_inst_1 : AddCommSemigroup.{u1} α] (A : Matrix.{u2, u2, u1} n n α), Matrix.IsSymm.{u1, u2} α n (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (instHAdd.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasAdd.{u1, u2, u2} n n α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_1)))) (Matrix.transpose.{u1, u2, u2} n n α A) A)
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} [_inst_1 : AddCommSemigroup.{u2} α] (A : Matrix.{u1, u1, u2} n n α), Matrix.IsSymm.{u2, u1} α n (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHAdd.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.add.{u2, u1, u1} n n α (AddSemigroup.toAdd.{u2} α (AddCommSemigroup.toAddSemigroup.{u2} α _inst_1)))) (Matrix.transpose.{u2, u1, u1} n n α A) A)
Case conversion may be inaccurate. Consider using '#align matrix.is_symm_transpose_add_self Matrix.isSymm_transpose_add_selfₓ'. -/
theorem isSymm_transpose_add_self [AddCommSemigroup α] (A : Matrix n n α) : (Aᵀ + A).IsSymm :=
  add_comm _ _
#align matrix.is_symm_transpose_add_self Matrix.isSymm_transpose_add_self

/- warning: matrix.is_symm_zero -> Matrix.isSymm_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} [_inst_1 : Zero.{u1} α], Matrix.IsSymm.{u1, u2} α n (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 0 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 0 (Zero.zero.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasZero.{u1, u2, u2} n n α _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} [_inst_1 : Zero.{u2} α], Matrix.IsSymm.{u2, u1} α n (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 0 (Zero.toOfNat0.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.zero.{u2, u1, u1} n n α _inst_1)))
Case conversion may be inaccurate. Consider using '#align matrix.is_symm_zero Matrix.isSymm_zeroₓ'. -/
@[simp]
theorem isSymm_zero [Zero α] : (0 : Matrix n n α).IsSymm :=
  transpose_zero
#align matrix.is_symm_zero Matrix.isSymm_zero

#print Matrix.isSymm_one /-
@[simp]
theorem isSymm_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α).IsSymm :=
  transpose_one
#align matrix.is_symm_one Matrix.isSymm_one
-/

/- warning: matrix.is_symm.map -> Matrix.IsSymm.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {n : Type.{u3}} {A : Matrix.{u3, u3, u1} n n α}, (Matrix.IsSymm.{u1, u3} α n A) -> (forall (f : α -> β), Matrix.IsSymm.{u2, u3} β n (Matrix.map.{u1, u2, u3, u3} n n α β A f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {n : Type.{u3}} {A : Matrix.{u3, u3, u2} n n α}, (Matrix.IsSymm.{u2, u3} α n A) -> (forall (f : α -> β), Matrix.IsSymm.{u1, u3} β n (Matrix.map.{u2, u1, u3, u3} n n α β A f))
Case conversion may be inaccurate. Consider using '#align matrix.is_symm.map Matrix.IsSymm.mapₓ'. -/
@[simp]
theorem IsSymm.map {A : Matrix n n α} (h : A.IsSymm) (f : α → β) : (A.map f).IsSymm :=
  transpose_map.symm.trans (h.symm ▸ rfl)
#align matrix.is_symm.map Matrix.IsSymm.map

#print Matrix.IsSymm.transpose /-
@[simp]
theorem IsSymm.transpose {A : Matrix n n α} (h : A.IsSymm) : Aᵀ.IsSymm :=
  congr_arg _ h
#align matrix.is_symm.transpose Matrix.IsSymm.transpose
-/

/- warning: matrix.is_symm.conj_transpose -> Matrix.IsSymm.conjTranspose is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} [_inst_1 : Star.{u1} α] {A : Matrix.{u2, u2, u1} n n α}, (Matrix.IsSymm.{u1, u2} α n A) -> (Matrix.IsSymm.{u1, u2} α n (Matrix.conjTranspose.{u1, u2, u2} n n α _inst_1 A))
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} [_inst_1 : Star.{u2} α] {A : Matrix.{u1, u1, u2} n n α}, (Matrix.IsSymm.{u2, u1} α n A) -> (Matrix.IsSymm.{u2, u1} α n (Matrix.conjTranspose.{u2, u1, u1} n n α _inst_1 A))
Case conversion may be inaccurate. Consider using '#align matrix.is_symm.conj_transpose Matrix.IsSymm.conjTransposeₓ'. -/
@[simp]
theorem IsSymm.conjTranspose [Star α] {A : Matrix n n α} (h : A.IsSymm) : Aᴴ.IsSymm :=
  h.transpose.map _
#align matrix.is_symm.conj_transpose Matrix.IsSymm.conjTranspose

/- warning: matrix.is_symm.neg -> Matrix.IsSymm.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} [_inst_1 : Neg.{u1} α] {A : Matrix.{u2, u2, u1} n n α}, (Matrix.IsSymm.{u1, u2} α n A) -> (Matrix.IsSymm.{u1, u2} α n (Neg.neg.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasNeg.{u1, u2, u2} n n α _inst_1) A))
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} [_inst_1 : Neg.{u2} α] {A : Matrix.{u1, u1, u2} n n α}, (Matrix.IsSymm.{u2, u1} α n A) -> (Matrix.IsSymm.{u2, u1} α n (Neg.neg.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.neg.{u2, u1, u1} n n α _inst_1) A))
Case conversion may be inaccurate. Consider using '#align matrix.is_symm.neg Matrix.IsSymm.negₓ'. -/
@[simp]
theorem IsSymm.neg [Neg α] {A : Matrix n n α} (h : A.IsSymm) : (-A).IsSymm :=
  (transpose_neg _).trans (congr_arg _ h)
#align matrix.is_symm.neg Matrix.IsSymm.neg

#print Matrix.IsSymm.add /-
@[simp]
theorem IsSymm.add {A B : Matrix n n α} [Add α] (hA : A.IsSymm) (hB : B.IsSymm) : (A + B).IsSymm :=
  (transpose_add _ _).trans (hA.symm ▸ hB.symm ▸ rfl)
#align matrix.is_symm.add Matrix.IsSymm.add
-/

#print Matrix.IsSymm.sub /-
@[simp]
theorem IsSymm.sub {A B : Matrix n n α} [Sub α] (hA : A.IsSymm) (hB : B.IsSymm) : (A - B).IsSymm :=
  (transpose_sub _ _).trans (hA.symm ▸ hB.symm ▸ rfl)
#align matrix.is_symm.sub Matrix.IsSymm.sub
-/

/- warning: matrix.is_symm.smul -> Matrix.IsSymm.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_1 : SMul.{u3, u1} R α] {A : Matrix.{u2, u2, u1} n n α}, (Matrix.IsSymm.{u1, u2} α n A) -> (forall (k : R), Matrix.IsSymm.{u1, u2} α n (SMul.smul.{u3, max u2 u1} R (Matrix.{u2, u2, u1} n n α) (Matrix.hasSmul.{u1, u2, u2, u3} n n R α _inst_1) k A))
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} [_inst_1 : SMul.{u3, u2} R α] {A : Matrix.{u1, u1, u2} n n α}, (Matrix.IsSymm.{u2, u1} α n A) -> (forall (k : R), Matrix.IsSymm.{u2, u1} α n (HSMul.hSMul.{u3, max u2 u1, max u2 u1} R (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHSMul.{u3, max u2 u1} R (Matrix.{u1, u1, u2} n n α) (Matrix.smul.{u2, u1, u1, u3} n n R α _inst_1)) k A))
Case conversion may be inaccurate. Consider using '#align matrix.is_symm.smul Matrix.IsSymm.smulₓ'. -/
@[simp]
theorem IsSymm.smul [SMul R α] {A : Matrix n n α} (h : A.IsSymm) (k : R) : (k • A).IsSymm :=
  (transpose_smul _ _).trans (congr_arg _ h)
#align matrix.is_symm.smul Matrix.IsSymm.smul

/- warning: matrix.is_symm.submatrix -> Matrix.IsSymm.submatrix is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} {m : Type.{u3}} {A : Matrix.{u2, u2, u1} n n α}, (Matrix.IsSymm.{u1, u2} α n A) -> (forall (f : m -> n), Matrix.IsSymm.{u1, u3} α m (Matrix.submatrix.{u1, u3, u2, u2, u3} m n n m α A f f))
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u3}} {m : Type.{u1}} {A : Matrix.{u3, u3, u2} n n α}, (Matrix.IsSymm.{u2, u3} α n A) -> (forall (f : m -> n), Matrix.IsSymm.{u2, u1} α m (Matrix.submatrix.{u2, u1, u3, u3, u1} m n n m α A f f))
Case conversion may be inaccurate. Consider using '#align matrix.is_symm.submatrix Matrix.IsSymm.submatrixₓ'. -/
@[simp]
theorem IsSymm.submatrix {A : Matrix n n α} (h : A.IsSymm) (f : m → n) : (A.submatrix f f).IsSymm :=
  (transpose_submatrix _ _ _).trans (h.symm ▸ rfl)
#align matrix.is_symm.submatrix Matrix.IsSymm.submatrix

#print Matrix.isSymm_diagonal /-
/-- The diagonal matrix `diagonal v` is symmetric. -/
@[simp]
theorem isSymm_diagonal [DecidableEq n] [Zero α] (v : n → α) : (diagonal v).IsSymm :=
  diagonal_transpose _
#align matrix.is_symm_diagonal Matrix.isSymm_diagonal
-/

/- warning: matrix.is_symm.from_blocks -> Matrix.IsSymm.fromBlocks is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} {m : Type.{u3}} {A : Matrix.{u3, u3, u1} m m α} {B : Matrix.{u3, u2, u1} m n α} {C : Matrix.{u2, u3, u1} n m α} {D : Matrix.{u2, u2, u1} n n α}, (Matrix.IsSymm.{u1, u3} α m A) -> (Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} n m α) (Matrix.transpose.{u1, u3, u2} m n α B) C) -> (Matrix.IsSymm.{u1, u2} α n D) -> (Matrix.IsSymm.{u1, max u3 u2} α (Sum.{u3, u2} m n) (Matrix.fromBlocks.{u3, u2, u3, u2, u1} m n m n α A B C D))
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} {m : Type.{u3}} {A : Matrix.{u3, u3, u2} m m α} {B : Matrix.{u3, u1, u2} m n α} {C : Matrix.{u1, u3, u2} n m α} {D : Matrix.{u1, u1, u2} n n α}, (Matrix.IsSymm.{u2, u3} α m A) -> (Eq.{max (max (succ u2) (succ u1)) (succ u3)} (Matrix.{u1, u3, u2} n m α) (Matrix.transpose.{u2, u3, u1} m n α B) C) -> (Matrix.IsSymm.{u2, u1} α n D) -> (Matrix.IsSymm.{u2, max u1 u3} α (Sum.{u3, u1} m n) (Matrix.fromBlocks.{u3, u1, u3, u1, u2} m n m n α A B C D))
Case conversion may be inaccurate. Consider using '#align matrix.is_symm.from_blocks Matrix.IsSymm.fromBlocksₓ'. -/
/-- A block matrix `A.from_blocks B C D` is symmetric,
    if `A` and `D` are symmetric and `Bᵀ = C`. -/
theorem IsSymm.fromBlocks {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} (hA : A.IsSymm) (hBC : Bᵀ = C) (hD : D.IsSymm) :
    (A.fromBlocks B C D).IsSymm :=
  by
  have hCB : Cᵀ = B := by rw [← hBC]; simp
  unfold Matrix.IsSymm
  rw [from_blocks_transpose]
  congr <;> assumption
#align matrix.is_symm.from_blocks Matrix.IsSymm.fromBlocks

/- warning: matrix.is_symm_from_blocks_iff -> Matrix.isSymm_fromBlocks_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Type.{u2}} {m : Type.{u3}} {A : Matrix.{u3, u3, u1} m m α} {B : Matrix.{u3, u2, u1} m n α} {C : Matrix.{u2, u3, u1} n m α} {D : Matrix.{u2, u2, u1} n n α}, Iff (Matrix.IsSymm.{u1, max u3 u2} α (Sum.{u3, u2} m n) (Matrix.fromBlocks.{u3, u2, u3, u2, u1} m n m n α A B C D)) (And (Matrix.IsSymm.{u1, u3} α m A) (And (Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} n m α) (Matrix.transpose.{u1, u3, u2} m n α B) C) (And (Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} m n α) (Matrix.transpose.{u1, u2, u3} n m α C) B) (Matrix.IsSymm.{u1, u2} α n D))))
but is expected to have type
  forall {α : Type.{u2}} {n : Type.{u1}} {m : Type.{u3}} {A : Matrix.{u3, u3, u2} m m α} {B : Matrix.{u3, u1, u2} m n α} {C : Matrix.{u1, u3, u2} n m α} {D : Matrix.{u1, u1, u2} n n α}, Iff (Matrix.IsSymm.{u2, max u1 u3} α (Sum.{u3, u1} m n) (Matrix.fromBlocks.{u3, u1, u3, u1, u2} m n m n α A B C D)) (And (Matrix.IsSymm.{u2, u3} α m A) (And (Eq.{max (max (succ u2) (succ u1)) (succ u3)} (Matrix.{u1, u3, u2} n m α) (Matrix.transpose.{u2, u3, u1} m n α B) C) (And (Eq.{max (max (succ u2) (succ u1)) (succ u3)} (Matrix.{u3, u1, u2} m n α) (Matrix.transpose.{u2, u1, u3} n m α C) B) (Matrix.IsSymm.{u2, u1} α n D))))
Case conversion may be inaccurate. Consider using '#align matrix.is_symm_from_blocks_iff Matrix.isSymm_fromBlocks_iffₓ'. -/
/-- This is the `iff` version of `matrix.is_symm.from_blocks`. -/
theorem isSymm_fromBlocks_iff {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} : (A.fromBlocks B C D).IsSymm ↔ A.IsSymm ∧ Bᵀ = C ∧ Cᵀ = B ∧ D.IsSymm :=
  ⟨fun h =>
    ⟨(congr_arg toBlocks₁₁ h : _), (congr_arg toBlocks₂₁ h : _), (congr_arg toBlocks₁₂ h : _),
      (congr_arg toBlocks₂₂ h : _)⟩,
    fun ⟨hA, hBC, hCB, hD⟩ => IsSymm.fromBlocks hA hBC hD⟩
#align matrix.is_symm_from_blocks_iff Matrix.isSymm_fromBlocks_iff

end Matrix

