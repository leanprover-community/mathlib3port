/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Algebra.Lie.OfAssociative
import LinearAlgebra.Matrix.Reindex
import LinearAlgebra.Matrix.ToLinearEquiv

#align_import algebra.lie.matrix from "leanprover-community/mathlib"@"5c1efce12ba86d4901463f61019832f6a4b1a0d0"

/-!
# Lie algebras of matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An important class of Lie algebras are those arising from the associative algebra structure on
square matrices over a commutative ring. This file provides some very basic definitions whose
primary value stems from their utility when constructing the classical Lie algebras using matrices.

## Main definitions

  * `lie_equiv_matrix'`
  * `matrix.lie_conj`
  * `matrix.reindex_lie_equiv`

## Tags

lie algebra, matrix
-/


universe u v w w₁ w₂

section Matrices

open scoped Matrix

variable {R : Type u} [CommRing R]

variable {n : Type w} [DecidableEq n] [Fintype n]

#print lieEquivMatrix' /-
/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the Lie algebra structures. -/
def lieEquivMatrix' : Module.End R (n → R) ≃ₗ⁅R⁆ Matrix n n R :=
  { LinearMap.toMatrix' with
    map_lie' := fun T S => by
      let f := @LinearMap.toMatrix' R _ n n _ _
      change f (T.comp S - S.comp T) = f T * f S - f S * f T
      have h : ∀ T S : Module.End R _, f (T.comp S) = f T ⬝ f S := LinearMap.toMatrix'_comp
      rw [LinearEquiv.map_sub, h, h, Matrix.hMul_eq_hMul, Matrix.hMul_eq_hMul] }
#align lie_equiv_matrix' lieEquivMatrix'
-/

#print lieEquivMatrix'_apply /-
@[simp]
theorem lieEquivMatrix'_apply (f : Module.End R (n → R)) : lieEquivMatrix' f = f.toMatrix' :=
  rfl
#align lie_equiv_matrix'_apply lieEquivMatrix'_apply
-/

#print lieEquivMatrix'_symm_apply /-
@[simp]
theorem lieEquivMatrix'_symm_apply (A : Matrix n n R) :
    (@lieEquivMatrix' R _ n _ _).symm A = A.toLin' :=
  rfl
#align lie_equiv_matrix'_symm_apply lieEquivMatrix'_symm_apply
-/

#print Matrix.lieConj /-
/-- An invertible matrix induces a Lie algebra equivalence from the space of matrices to itself. -/
def Matrix.lieConj (P : Matrix n n R) (h : Invertible P) : Matrix n n R ≃ₗ⁅R⁆ Matrix n n R :=
  ((@lieEquivMatrix' R _ n _ _).symm.trans (P.toLinearEquiv' h).lieConj).trans lieEquivMatrix'
#align matrix.lie_conj Matrix.lieConj
-/

#print Matrix.lieConj_apply /-
@[simp]
theorem Matrix.lieConj_apply (P A : Matrix n n R) (h : Invertible P) :
    P.lieConj h A = P ⬝ A ⬝ P⁻¹ := by
  simp [LinearEquiv.conj_apply, Matrix.lieConj, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']
#align matrix.lie_conj_apply Matrix.lieConj_apply
-/

#print Matrix.lieConj_symm_apply /-
@[simp]
theorem Matrix.lieConj_symm_apply (P A : Matrix n n R) (h : Invertible P) :
    (P.lieConj h).symm A = P⁻¹ ⬝ A ⬝ P := by
  simp [LinearEquiv.symm_conj_apply, Matrix.lieConj, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']
#align matrix.lie_conj_symm_apply Matrix.lieConj_symm_apply
-/

variable {m : Type w₁} [DecidableEq m] [Fintype m] (e : n ≃ m)

#print Matrix.reindexLieEquiv /-
/-- For square matrices, the natural map that reindexes a matrix's rows and columns with equivalent
types, `matrix.reindex`, is an equivalence of Lie algebras. -/
def Matrix.reindexLieEquiv : Matrix n n R ≃ₗ⁅R⁆ Matrix m m R :=
  {
    Matrix.reindexLinearEquiv R R e
      e with
    toFun := Matrix.reindex e e
    map_lie' := fun M N => by
      simp only [LieRing.of_associative_ring_bracket, Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv, Matrix.hMul_eq_hMul, Matrix.submatrix_sub, Pi.sub_apply] }
#align matrix.reindex_lie_equiv Matrix.reindexLieEquiv
-/

#print Matrix.reindexLieEquiv_apply /-
@[simp]
theorem Matrix.reindexLieEquiv_apply (M : Matrix n n R) :
    Matrix.reindexLieEquiv e M = Matrix.reindex e e M :=
  rfl
#align matrix.reindex_lie_equiv_apply Matrix.reindexLieEquiv_apply
-/

#print Matrix.reindexLieEquiv_symm /-
@[simp]
theorem Matrix.reindexLieEquiv_symm :
    (Matrix.reindexLieEquiv e : _ ≃ₗ⁅R⁆ _).symm = Matrix.reindexLieEquiv e.symm :=
  rfl
#align matrix.reindex_lie_equiv_symm Matrix.reindexLieEquiv_symm
-/

end Matrices

