/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module algebra.lie.classical
! leanprover-community/mathlib commit 7e5137f579de09a059a5ce98f364a04e221aabf0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Invertible
import Mathbin.Data.Matrix.Basis
import Mathbin.Data.Matrix.Dmatrix
import Mathbin.Algebra.Lie.Abelian
import Mathbin.LinearAlgebra.Matrix.Trace
import Mathbin.Algebra.Lie.SkewAdjoint
import Mathbin.LinearAlgebra.SymplecticGroup

/-!
# Classical Lie algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is the place to find definitions and basic properties of the classical Lie algebras:
  * Aₗ = sl(l+1)
  * Bₗ ≃ so(l+1, l) ≃ so(2l+1)
  * Cₗ = sp(l)
  * Dₗ ≃ so(l, l) ≃ so(2l)

## Main definitions

  * `lie_algebra.special_linear.sl`
  * `lie_algebra.symplectic.sp`
  * `lie_algebra.orthogonal.so`
  * `lie_algebra.orthogonal.so'`
  * `lie_algebra.orthogonal.so_indefinite_equiv`
  * `lie_algebra.orthogonal.type_D`
  * `lie_algebra.orthogonal.type_B`
  * `lie_algebra.orthogonal.type_D_equiv_so'`
  * `lie_algebra.orthogonal.type_B_equiv_so'`

## Implementation notes

### Matrices or endomorphisms

Given a finite type and a commutative ring, the corresponding square matrices are equivalent to the
endomorphisms of the corresponding finite-rank free module as Lie algebras, see `lie_equiv_matrix'`.
We can thus define the classical Lie algebras as Lie subalgebras either of matrices or of
endomorphisms. We have opted for the former. At the time of writing (August 2020) it is unclear
which approach should be preferred so the choice should be assumed to be somewhat arbitrary.

### Diagonal quadratic form or diagonal Cartan subalgebra

For the algebras of type `B` and `D`, there are two natural definitions. For example since the
the `2l × 2l` matrix:
$$
  J = \left[\begin{array}{cc}
              0_l & 1_l\\
              1_l & 0_l
            \end{array}\right]
$$
defines a symmetric bilinear form equivalent to that defined by the identity matrix `I`, we can
define the algebras of type `D` to be the Lie subalgebra of skew-adjoint matrices either for `J` or
for `I`. Both definitions have their advantages (in particular the `J`-skew-adjoint matrices define
a Lie algebra for which the diagonal matrices form a Cartan subalgebra) and so we provide both.
We thus also provide equivalences `type_D_equiv_so'`, `so_indefinite_equiv` which show the two
definitions are equivalent. Similarly for the algebras of type `B`.

## Tags

classical lie algebra, special linear, symplectic, orthogonal
-/


universe u₁ u₂

namespace LieAlgebra

open Matrix

open scoped Matrix

variable (n p q l : Type _) (R : Type u₂)

variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]

variable [CommRing R]

#print LieAlgebra.matrix_trace_commutator_zero /-
@[simp]
theorem matrix_trace_commutator_zero [Fintype n] (X Y : Matrix n n R) : Matrix.trace ⁅X, Y⁆ = 0 :=
  calc
    _ = Matrix.trace (X ⬝ Y) - Matrix.trace (Y ⬝ X) := trace_sub _ _
    _ = Matrix.trace (X ⬝ Y) - Matrix.trace (X ⬝ Y) :=
      (congr_arg (fun x => _ - x) (Matrix.trace_mul_comm Y X))
    _ = 0 := sub_self _
#align lie_algebra.matrix_trace_commutator_zero LieAlgebra.matrix_trace_commutator_zero
-/

namespace SpecialLinear

#print LieAlgebra.SpecialLinear.sl /-
/-- The special linear Lie algebra: square matrices of trace zero. -/
def sl [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  { LinearMap.ker (Matrix.traceLinearMap n R R) with
    lie_mem' := fun X Y _ _ => LinearMap.mem_ker.2 <| matrix_trace_commutator_zero _ _ _ _ }
#align lie_algebra.special_linear.sl LieAlgebra.SpecialLinear.sl
-/

#print LieAlgebra.SpecialLinear.sl_bracket /-
theorem sl_bracket [Fintype n] (A B : sl n R) : ⁅A, B⁆.val = A.val ⬝ B.val - B.val ⬝ A.val :=
  rfl
#align lie_algebra.special_linear.sl_bracket LieAlgebra.SpecialLinear.sl_bracket
-/

section ElementaryBasis

variable {n} [Fintype n] (i j : n)

#print LieAlgebra.SpecialLinear.Eb /-
/-- When j ≠ i, the elementary matrices are elements of sl n R, in fact they are part of a natural
basis of sl n R. -/
def Eb (h : j ≠ i) : sl n R :=
  ⟨Matrix.stdBasisMatrix i j (1 : R),
    show Matrix.stdBasisMatrix i j (1 : R) ∈ LinearMap.ker (Matrix.traceLinearMap n R R) from
      Matrix.StdBasisMatrix.trace_zero i j (1 : R) h⟩
#align lie_algebra.special_linear.Eb LieAlgebra.SpecialLinear.Eb
-/

#print LieAlgebra.SpecialLinear.eb_val /-
@[simp]
theorem eb_val (h : j ≠ i) : (Eb R i j h).val = Matrix.stdBasisMatrix i j 1 :=
  rfl
#align lie_algebra.special_linear.Eb_val LieAlgebra.SpecialLinear.eb_val
-/

end ElementaryBasis

#print LieAlgebra.SpecialLinear.sl_non_abelian /-
theorem sl_non_abelian [Fintype n] [Nontrivial R] (h : 1 < Fintype.card n) :
    ¬IsLieAbelian ↥(sl n R) :=
  by
  rcases Fintype.exists_pair_of_one_lt_card h with ⟨j, i, hij⟩
  let A := Eb R i j hij
  let B := Eb R j i hij.symm
  intro c
  have c' : A.val ⬝ B.val = B.val ⬝ A.val := by rw [← sub_eq_zero, ← sl_bracket, c.trivial]; rfl
  simpa [std_basis_matrix, Matrix.mul_apply, hij] using congr_fun (congr_fun c' i) i
#align lie_algebra.special_linear.sl_non_abelian LieAlgebra.SpecialLinear.sl_non_abelian
-/

end SpecialLinear

namespace Symplectic

#print LieAlgebra.Symplectic.sp /-
/-- The symplectic Lie algebra: skew-adjoint matrices with respect to the canonical skew-symmetric
bilinear form. -/
def sp [Fintype l] : LieSubalgebra R (Matrix (Sum l l) (Sum l l) R) :=
  skewAdjointMatricesLieSubalgebra (Matrix.J l R)
#align lie_algebra.symplectic.sp LieAlgebra.Symplectic.sp
-/

end Symplectic

namespace Orthogonal

#print LieAlgebra.Orthogonal.so /-
/-- The definite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the identity matrix. -/
def so [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  skewAdjointMatricesLieSubalgebra (1 : Matrix n n R)
#align lie_algebra.orthogonal.so LieAlgebra.Orthogonal.so
-/

#print LieAlgebra.Orthogonal.mem_so /-
@[simp]
theorem mem_so [Fintype n] (A : Matrix n n R) : A ∈ so n R ↔ Aᵀ = -A :=
  by
  erw [mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul]
#align lie_algebra.orthogonal.mem_so LieAlgebra.Orthogonal.mem_so
-/

#print LieAlgebra.Orthogonal.indefiniteDiagonal /-
/-- The indefinite diagonal matrix with `p` 1s and `q` -1s. -/
def indefiniteDiagonal : Matrix (Sum p q) (Sum p q) R :=
  Matrix.diagonal <| Sum.elim (fun _ => 1) fun _ => -1
#align lie_algebra.orthogonal.indefinite_diagonal LieAlgebra.Orthogonal.indefiniteDiagonal
-/

#print LieAlgebra.Orthogonal.so' /-
/-- The indefinite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the indefinite diagonal matrix. -/
def so' [Fintype p] [Fintype q] : LieSubalgebra R (Matrix (Sum p q) (Sum p q) R) :=
  skewAdjointMatricesLieSubalgebra <| indefiniteDiagonal p q R
#align lie_algebra.orthogonal.so' LieAlgebra.Orthogonal.so'
-/

#print LieAlgebra.Orthogonal.Pso /-
/-- A matrix for transforming the indefinite diagonal bilinear form into the definite one, provided
the parameter `i` is a square root of -1. -/
def Pso (i : R) : Matrix (Sum p q) (Sum p q) R :=
  Matrix.diagonal <| Sum.elim (fun _ => 1) fun _ => i
#align lie_algebra.orthogonal.Pso LieAlgebra.Orthogonal.Pso
-/

variable [Fintype p] [Fintype q]

#print LieAlgebra.Orthogonal.pso_inv /-
theorem pso_inv {i : R} (hi : i * i = -1) : Pso p q R i * Pso p q R (-i) = 1 :=
  by
  ext (x y); rcases x with ⟨⟩ <;> rcases y with ⟨⟩
  ·-- x y : p
      by_cases h : x = y <;>
      simp [Pso, indefinite_diagonal, h]
  ·-- x : p, y : q
    simp [Pso, indefinite_diagonal]
  ·-- x : q, y : p
    simp [Pso, indefinite_diagonal]
  ·-- x y : q
      by_cases h : x = y <;>
      simp [Pso, indefinite_diagonal, h, hi]
#align lie_algebra.orthogonal.Pso_inv LieAlgebra.Orthogonal.pso_inv
-/

#print LieAlgebra.Orthogonal.invertiblePso /-
/-- There is a constructive inverse of `Pso p q R i`. -/
def invertiblePso {i : R} (hi : i * i = -1) : Invertible (Pso p q R i) :=
  invertibleOfRightInverse _ _ (pso_inv p q R hi)
#align lie_algebra.orthogonal.invertible_Pso LieAlgebra.Orthogonal.invertiblePso
-/

#print LieAlgebra.Orthogonal.indefiniteDiagonal_transform /-
theorem indefiniteDiagonal_transform {i : R} (hi : i * i = -1) :
    (Pso p q R i)ᵀ ⬝ indefiniteDiagonal p q R ⬝ Pso p q R i = 1 :=
  by
  ext (x y); rcases x with ⟨⟩ <;> rcases y with ⟨⟩
  ·-- x y : p
      by_cases h : x = y <;>
      simp [Pso, indefinite_diagonal, h]
  ·-- x : p, y : q
    simp [Pso, indefinite_diagonal]
  ·-- x : q, y : p
    simp [Pso, indefinite_diagonal]
  ·-- x y : q
      by_cases h : x = y <;>
      simp [Pso, indefinite_diagonal, h, hi]
#align lie_algebra.orthogonal.indefinite_diagonal_transform LieAlgebra.Orthogonal.indefiniteDiagonal_transform
-/

#print LieAlgebra.Orthogonal.soIndefiniteEquiv /-
/-- An equivalence between the indefinite and definite orthogonal Lie algebras, over a ring
containing a square root of -1. -/
def soIndefiniteEquiv {i : R} (hi : i * i = -1) : so' p q R ≃ₗ⁅R⁆ so (Sum p q) R :=
  by
  apply
    (skewAdjointMatricesLieSubalgebraEquiv (indefinite_diagonal p q R) (Pso p q R i)
        (invertible_Pso p q R hi)).trans
  apply LieEquiv.ofEq
  ext A; rw [indefinite_diagonal_transform p q R hi]; rfl
#align lie_algebra.orthogonal.so_indefinite_equiv LieAlgebra.Orthogonal.soIndefiniteEquiv
-/

#print LieAlgebra.Orthogonal.soIndefiniteEquiv_apply /-
theorem soIndefiniteEquiv_apply {i : R} (hi : i * i = -1) (A : so' p q R) :
    (soIndefiniteEquiv p q R hi A : Matrix (Sum p q) (Sum p q) R) =
      (Pso p q R i)⁻¹ ⬝ (A : Matrix (Sum p q) (Sum p q) R) ⬝ Pso p q R i :=
  by erw [LieEquiv.trans_apply, LieEquiv.ofEq_apply, skewAdjointMatricesLieSubalgebraEquiv_apply]
#align lie_algebra.orthogonal.so_indefinite_equiv_apply LieAlgebra.Orthogonal.soIndefiniteEquiv_apply
-/

#print LieAlgebra.Orthogonal.JD /-
/-- A matrix defining a canonical even-rank symmetric bilinear form.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 0 1 ]
   [ 1 0 ]
-/
def JD : Matrix (Sum l l) (Sum l l) R :=
  Matrix.fromBlocks 0 1 1 0
#align lie_algebra.orthogonal.JD LieAlgebra.Orthogonal.JD
-/

#print LieAlgebra.Orthogonal.typeD /-
/-- The classical Lie algebra of type D as a Lie subalgebra of matrices associated to the matrix
`JD`. -/
def typeD [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JD l R)
#align lie_algebra.orthogonal.type_D LieAlgebra.Orthogonal.typeD
-/

#print LieAlgebra.Orthogonal.PD /-
/-- A matrix transforming the bilinear form defined by the matrix `JD` into a split-signature
diagonal matrix.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 1 -1 ]
   [ 1  1 ]
-/
def PD : Matrix (Sum l l) (Sum l l) R :=
  Matrix.fromBlocks 1 (-1) 1 1
#align lie_algebra.orthogonal.PD LieAlgebra.Orthogonal.PD
-/

#print LieAlgebra.Orthogonal.S /-
/-- The split-signature diagonal matrix. -/
def S :=
  indefiniteDiagonal l l R
#align lie_algebra.orthogonal.S LieAlgebra.Orthogonal.S
-/

#print LieAlgebra.Orthogonal.s_as_blocks /-
theorem s_as_blocks : S l R = Matrix.fromBlocks 1 0 0 (-1) :=
  by
  rw [← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.fromBlocks_diagonal]
  rfl
#align lie_algebra.orthogonal.S_as_blocks LieAlgebra.Orthogonal.s_as_blocks
-/

#print LieAlgebra.Orthogonal.jd_transform /-
theorem jd_transform [Fintype l] : (PD l R)ᵀ ⬝ JD l R ⬝ PD l R = (2 : R) • S l R :=
  by
  have h : (PD l R)ᵀ ⬝ JD l R = Matrix.fromBlocks 1 1 1 (-1) := by
    simp [PD, JD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  erw [h, S_as_blocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  congr <;> simp [two_smul]
#align lie_algebra.orthogonal.JD_transform LieAlgebra.Orthogonal.jd_transform
-/

#print LieAlgebra.Orthogonal.pd_inv /-
theorem pd_inv [Fintype l] [Invertible (2 : R)] : PD l R * ⅟ (2 : R) • (PD l R)ᵀ = 1 :=
  by
  have h : ⅟ (2 : R) • (1 : Matrix l l R) + ⅟ (2 : R) • 1 = 1 := by
    rw [← smul_add, ← two_smul R _, smul_smul, invOf_mul_self, one_smul]
  erw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul, Matrix.mul_eq_mul,
    Matrix.fromBlocks_multiply]
  simp [h]
#align lie_algebra.orthogonal.PD_inv LieAlgebra.Orthogonal.pd_inv
-/

#print LieAlgebra.Orthogonal.invertiblePD /-
instance invertiblePD [Fintype l] [Invertible (2 : R)] : Invertible (PD l R) :=
  invertibleOfRightInverse _ _ (pd_inv l R)
#align lie_algebra.orthogonal.invertible_PD LieAlgebra.Orthogonal.invertiblePD
-/

#print LieAlgebra.Orthogonal.typeDEquivSo' /-
/-- An equivalence between two possible definitions of the classical Lie algebra of type D. -/
def typeDEquivSo' [Fintype l] [Invertible (2 : R)] : typeD l R ≃ₗ⁅R⁆ so' l l R :=
  by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JD l R) (PD l R) (by infer_instance)).trans
  apply LieEquiv.ofEq
  ext A
  rw [JD_transform, ← unitOfInvertible_val (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  rfl
#align lie_algebra.orthogonal.type_D_equiv_so' LieAlgebra.Orthogonal.typeDEquivSo'
-/

#print LieAlgebra.Orthogonal.JB /-
/-- A matrix defining a canonical odd-rank symmetric bilinear form.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

   [ 2 0 0 ]
   [ 0 0 1 ]
   [ 0 1 0 ]

where sizes of the blocks are:

   [`1 x 1` `1 x l` `1 x l`]
   [`l x 1` `l x l` `l x l`]
   [`l x 1` `l x l` `l x l`]
-/
def JB :=
  Matrix.fromBlocks ((2 : R) • 1 : Matrix Unit Unit R) 0 0 (JD l R)
#align lie_algebra.orthogonal.JB LieAlgebra.Orthogonal.JB
-/

#print LieAlgebra.Orthogonal.typeB /-
/-- The classical Lie algebra of type B as a Lie subalgebra of matrices associated to the matrix
`JB`. -/
def typeB [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JB l R)
#align lie_algebra.orthogonal.type_B LieAlgebra.Orthogonal.typeB
-/

#print LieAlgebra.Orthogonal.PB /-
/-- A matrix transforming the bilinear form defined by the matrix `JB` into an
almost-split-signature diagonal matrix.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

   [ 1 0  0 ]
   [ 0 1 -1 ]
   [ 0 1  1 ]

where sizes of the blocks are:

   [`1 x 1` `1 x l` `1 x l`]
   [`l x 1` `l x l` `l x l`]
   [`l x 1` `l x l` `l x l`]
-/
def PB :=
  Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 (PD l R)
#align lie_algebra.orthogonal.PB LieAlgebra.Orthogonal.PB
-/

variable [Fintype l]

#print LieAlgebra.Orthogonal.pb_inv /-
theorem pb_inv [Invertible (2 : R)] : PB l R * Matrix.fromBlocks 1 0 0 (⅟ (PD l R)) = 1 :=
  by
  rw [PB, Matrix.mul_eq_mul, Matrix.fromBlocks_multiply, Matrix.mul_invOf_self]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.fromBlocks_one]
#align lie_algebra.orthogonal.PB_inv LieAlgebra.Orthogonal.pb_inv
-/

#print LieAlgebra.Orthogonal.invertiblePB /-
instance invertiblePB [Invertible (2 : R)] : Invertible (PB l R) :=
  invertibleOfRightInverse _ _ (pb_inv l R)
#align lie_algebra.orthogonal.invertible_PB LieAlgebra.Orthogonal.invertiblePB
-/

#print LieAlgebra.Orthogonal.jb_transform /-
theorem jb_transform : (PB l R)ᵀ ⬝ JB l R ⬝ PB l R = (2 : R) • Matrix.fromBlocks 1 0 0 (S l R) := by
  simp [PB, JB, JD_transform, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]
#align lie_algebra.orthogonal.JB_transform LieAlgebra.Orthogonal.jb_transform
-/

#print LieAlgebra.Orthogonal.indefiniteDiagonal_assoc /-
theorem indefiniteDiagonal_assoc :
    indefiniteDiagonal (Sum Unit l) l R =
      Matrix.reindexLieEquiv (Equiv.sumAssoc Unit l l).symm
        (Matrix.fromBlocks 1 0 0 (indefiniteDiagonal l l R)) :=
  by
  ext (i j)
  rcases i with ⟨⟨i₁ | i₂⟩ | i₃⟩ <;> rcases j with ⟨⟨j₁ | j₂⟩ | j₃⟩ <;>
      simp only [indefinite_diagonal, Matrix.diagonal_apply, Equiv.sumAssoc_apply_inl_inl,
        Matrix.reindexLieEquiv_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.reindex_apply,
        Sum.elim_inl, if_true, eq_self_iff_true, Matrix.one_apply_eq, Matrix.fromBlocks_apply₁₁,
        DMatrix.zero_apply, Equiv.sumAssoc_apply_inl_inr, if_false, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Equiv.sumAssoc_apply_inr,
        Sum.elim_inr] <;>
    congr
#align lie_algebra.orthogonal.indefinite_diagonal_assoc LieAlgebra.Orthogonal.indefiniteDiagonal_assoc
-/

#print LieAlgebra.Orthogonal.typeBEquivSo' /-
/-- An equivalence between two possible definitions of the classical Lie algebra of type B. -/
def typeBEquivSo' [Invertible (2 : R)] : typeB l R ≃ₗ⁅R⁆ so' (Sum Unit l) l R :=
  by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JB l R) (PB l R) (by infer_instance)).trans
  symm
  apply
    (skewAdjointMatricesLieSubalgebraEquivTranspose (indefinite_diagonal (Sum Unit l) l R)
        (Matrix.reindexAlgEquiv _ (Equiv.sumAssoc PUnit l l)) (Matrix.transpose_reindex _ _)).trans
  apply LieEquiv.ofEq
  ext A
  rw [JB_transform, ← unitOfInvertible_val (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    LieSubalgebra.mem_coe, mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  simpa [indefinite_diagonal_assoc]
#align lie_algebra.orthogonal.type_B_equiv_so' LieAlgebra.Orthogonal.typeBEquivSo'
-/

end Orthogonal

end LieAlgebra

