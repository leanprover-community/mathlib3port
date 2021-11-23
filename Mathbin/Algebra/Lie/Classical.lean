import Mathbin.Algebra.Invertible 
import Mathbin.Data.Matrix.Basis 
import Mathbin.Data.Matrix.Dmatrix 
import Mathbin.Algebra.Lie.Abelian 
import Mathbin.LinearAlgebra.Matrix.Trace 
import Mathbin.Algebra.Lie.SkewAdjoint

/-!
# Classical Lie algebras

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

open_locale Matrix

variable(n p q l : Type _)(R : Type u₂)

variable[DecidableEq n][DecidableEq p][DecidableEq q][DecidableEq l]

variable[CommRingₓ R]

@[simp]
theorem matrix_trace_commutator_zero [Fintype n] (X Y : Matrix n n R) : Matrix.trace n R R ⁅X,Y⁆ = 0 :=
  calc _ = Matrix.trace n R R (X ⬝ Y) - Matrix.trace n R R (Y ⬝ X) := LinearMap.map_sub _ _ _ 
    _ = Matrix.trace n R R (X ⬝ Y) - Matrix.trace n R R (X ⬝ Y) :=
    congr_argₓ (fun x => _ - x) (Matrix.trace_mul_comm Y X)
    _ = 0 := sub_self _
    

namespace SpecialLinear

/-- The special linear Lie algebra: square matrices of trace zero. -/
def sl [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  { LinearMap.ker (Matrix.trace n R R) with
    lie_mem' := fun X Y _ _ => LinearMap.mem_ker.2$ matrix_trace_commutator_zero _ _ _ _ }

theorem sl_bracket [Fintype n] (A B : sl n R) : ⁅A,B⁆.val = A.val ⬝ B.val - B.val ⬝ A.val :=
  rfl

section ElementaryBasis

variable{n}[Fintype n](i j : n)

/-- When j ≠ i, the elementary matrices are elements of sl n R, in fact they are part of a natural
basis of sl n R. -/
def Eb (h : j ≠ i) : sl n R :=
  ⟨Matrix.stdBasisMatrix i j (1 : R),
    show Matrix.stdBasisMatrix i j (1 : R) ∈ LinearMap.ker (Matrix.trace n R R) from
      Matrix.stdBasisMatrix.trace_zero i j (1 : R) h⟩

@[simp]
theorem Eb_val (h : j ≠ i) : (Eb R i j h).val = Matrix.stdBasisMatrix i j 1 :=
  rfl

end ElementaryBasis

-- error in Algebra.Lie.Classical: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sl_non_abelian
[fintype n]
[nontrivial R]
(h : «expr < »(1, fintype.card n)) : «expr¬ »(is_lie_abelian «expr↥ »(sl n R)) :=
begin
  rcases [expr fintype.exists_pair_of_one_lt_card h, "with", "⟨", ident j, ",", ident i, ",", ident hij, "⟩"],
  let [ident A] [] [":=", expr Eb R i j hij],
  let [ident B] [] [":=", expr Eb R j i hij.symm],
  intros [ident c],
  have [ident c'] [":", expr «expr = »(«expr ⬝ »(A.val, B.val), «expr ⬝ »(B.val, A.val))] [],
  by { rw ["[", "<-", expr sub_eq_zero, ",", "<-", expr sl_bracket, ",", expr c.trivial, "]"] [],
    refl },
  simpa [] [] [] ["[", expr std_basis_matrix, ",", expr matrix.mul_apply, ",", expr hij, "]"] [] ["using", expr congr_fun (congr_fun c' i) i]
end

end SpecialLinear

namespace Symplectic

/-- The matrix defining the canonical skew-symmetric bilinear form. -/
def J : Matrix (Sum l l) (Sum l l) R :=
  Matrix.fromBlocks 0 (-1) 1 0

/-- The symplectic Lie algebra: skew-adjoint matrices with respect to the canonical skew-symmetric
bilinear form. -/
def sp [Fintype l] : LieSubalgebra R (Matrix (Sum l l) (Sum l l) R) :=
  skewAdjointMatricesLieSubalgebra (J l R)

end Symplectic

namespace Orthogonal

/-- The definite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the identity matrix. -/
def so [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  skewAdjointMatricesLieSubalgebra (1 : Matrix n n R)

@[simp]
theorem mem_so [Fintype n] (A : Matrix n n R) : A ∈ so n R ↔ (A)ᵀ = -A :=
  by 
    erw [mem_skew_adjoint_matrices_submodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul]

/-- The indefinite diagonal matrix with `p` 1s and `q` -1s. -/
def indefinite_diagonal : Matrix (Sum p q) (Sum p q) R :=
  Matrix.diagonalₓ$ Sum.elim (fun _ => 1) fun _ => -1

/-- The indefinite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the indefinite diagonal matrix. -/
def so' [Fintype p] [Fintype q] : LieSubalgebra R (Matrix (Sum p q) (Sum p q) R) :=
  skewAdjointMatricesLieSubalgebra$ indefinite_diagonal p q R

/-- A matrix for transforming the indefinite diagonal bilinear form into the definite one, provided
the parameter `i` is a square root of -1. -/
def Pso (i : R) : Matrix (Sum p q) (Sum p q) R :=
  Matrix.diagonalₓ$ Sum.elim (fun _ => 1) fun _ => i

variable[Fintype p][Fintype q]

theorem Pso_inv {i : R} (hi : (i*i) = -1) : (Pso p q R i*Pso p q R (-i)) = 1 :=
  by 
    ext x y 
    rcases x with ⟨⟩ <;> rcases y with ⟨⟩
    ·
      byCases' h : x = y <;> simp [Pso, indefinite_diagonal, h]
    ·
      simp [Pso, indefinite_diagonal]
    ·
      simp [Pso, indefinite_diagonal]
    ·
      byCases' h : x = y <;> simp [Pso, indefinite_diagonal, h, hi]

/-- There is a constructive inverse of `Pso p q R i`. -/
def invertible_Pso {i : R} (hi : (i*i) = -1) : Invertible (Pso p q R i) :=
  invertible_of_right_inverse _ _ (Pso_inv p q R hi)

theorem indefinite_diagonal_transform {i : R} (hi : (i*i) = -1) :
  (Pso p q R i)ᵀ ⬝ indefinite_diagonal p q R ⬝ Pso p q R i = 1 :=
  by 
    ext x y 
    rcases x with ⟨⟩ <;> rcases y with ⟨⟩
    ·
      byCases' h : x = y <;> simp [Pso, indefinite_diagonal, h]
    ·
      simp [Pso, indefinite_diagonal]
    ·
      simp [Pso, indefinite_diagonal]
    ·
      byCases' h : x = y <;> simp [Pso, indefinite_diagonal, h, hi]

/-- An equivalence between the indefinite and definite orthogonal Lie algebras, over a ring
containing a square root of -1. -/
def so_indefinite_equiv {i : R} (hi : (i*i) = -1) : so' p q R ≃ₗ⁅R⁆ so (Sum p q) R :=
  by 
    apply
      (skewAdjointMatricesLieSubalgebraEquiv (indefinite_diagonal p q R) (Pso p q R i) (invertible_Pso p q R hi)).trans 
    apply LieEquiv.ofEq 
    ext A 
    rw [indefinite_diagonal_transform p q R hi]
    rfl

theorem so_indefinite_equiv_apply {i : R} (hi : (i*i) = -1) (A : so' p q R) :
  (so_indefinite_equiv p q R hi A : Matrix (Sum p q) (Sum p q) R) =
    Pso p q R i⁻¹ ⬝ (A : Matrix (Sum p q) (Sum p q) R) ⬝ Pso p q R i :=
  by 
    erw [LieEquiv.trans_apply, LieEquiv.of_eq_apply, skew_adjoint_matrices_lie_subalgebra_equiv_apply]

/-- A matrix defining a canonical even-rank symmetric bilinear form.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 0 1 ]
   [ 1 0 ]
-/
def JD : Matrix (Sum l l) (Sum l l) R :=
  Matrix.fromBlocks 0 1 1 0

/-- The classical Lie algebra of type D as a Lie subalgebra of matrices associated to the matrix
`JD`. -/
def type_D [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JD l R)

/-- A matrix transforming the bilinear form defined by the matrix `JD` into a split-signature
diagonal matrix.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 1 -1 ]
   [ 1  1 ]
-/
def PD : Matrix (Sum l l) (Sum l l) R :=
  Matrix.fromBlocks 1 (-1) 1 1

/-- The split-signature diagonal matrix. -/
def S :=
  indefinite_diagonal l l R

theorem S_as_blocks : S l R = Matrix.fromBlocks 1 0 0 (-1) :=
  by 
    rw [←Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.from_blocks_diagonal]
    rfl

-- error in Algebra.Lie.Classical: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem JD_transform
[fintype l] : «expr = »(«expr ⬝ »(«expr ⬝ »(«expr ᵀ»(PD l R), JD l R), PD l R), «expr • »((2 : R), S l R)) :=
begin
  have [ident h] [":", expr «expr = »(«expr ⬝ »(«expr ᵀ»(PD l R), JD l R), matrix.from_blocks 1 1 1 «expr- »(1))] [":=", expr by { simp [] [] [] ["[", expr PD, ",", expr JD, ",", expr matrix.from_blocks_transpose, ",", expr matrix.from_blocks_multiply, "]"] [] [] }],
  erw ["[", expr h, ",", expr S_as_blocks, ",", expr matrix.from_blocks_multiply, ",", expr matrix.from_blocks_smul, "]"] [],
  congr; simp [] [] [] ["[", expr two_smul, "]"] [] []
end

-- error in Algebra.Lie.Classical: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem PD_inv
[fintype l]
[invertible (2 : R)] : «expr = »(«expr * »(PD l R, «expr • »(«expr⅟»() (2 : R), «expr ᵀ»(PD l R))), 1) :=
begin
  have [ident h] [":", expr «expr = »(«expr + »(«expr • »(«expr⅟»() (2 : R), (1 : matrix l l R)), «expr • »(«expr⅟»() (2 : R), 1)), 1)] [":=", expr by rw ["[", "<-", expr smul_add, ",", "<-", expr two_smul R _, ",", expr smul_smul, ",", expr inv_of_mul_self, ",", expr one_smul, "]"] []],
  erw ["[", expr matrix.from_blocks_transpose, ",", expr matrix.from_blocks_smul, ",", expr matrix.mul_eq_mul, ",", expr matrix.from_blocks_multiply, "]"] [],
  simp [] [] [] ["[", expr h, "]"] [] []
end

instance invertible_PD [Fintype l] [Invertible (2 : R)] : Invertible (PD l R) :=
  invertible_of_right_inverse _ _ (PD_inv l R)

/-- An equivalence between two possible definitions of the classical Lie algebra of type D. -/
def type_D_equiv_so' [Fintype l] [Invertible (2 : R)] : type_D l R ≃ₗ⁅R⁆ so' l l R :=
  by 
    apply
      (skewAdjointMatricesLieSubalgebraEquiv (JD l R) (PD l R)
          (by 
            infer_instance)).trans
        
    apply LieEquiv.ofEq 
    ext A 
    rw [JD_transform, ←coe_unit_of_invertible (2 : R), ←Units.smul_def, LieSubalgebra.mem_coe,
      mem_skew_adjoint_matrices_lie_subalgebra_unit_smul]
    rfl

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

/-- The classical Lie algebra of type B as a Lie subalgebra of matrices associated to the matrix
`JB`. -/
def type_B [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JB l R)

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

variable[Fintype l]

theorem PB_inv [Invertible (2 : R)] : (PB l R*Matrix.fromBlocks 1 0 0 (⅟ (PD l R))) = 1 :=
  by 
    rw [PB, Matrix.mul_eq_mul, Matrix.from_blocks_multiply, Matrix.mul_inv_of_self]
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_addₓ, add_zeroₓ, Matrix.from_blocks_one]

instance invertible_PB [Invertible (2 : R)] : Invertible (PB l R) :=
  invertible_of_right_inverse _ _ (PB_inv l R)

theorem JB_transform : (PB l R)ᵀ ⬝ JB l R ⬝ PB l R = (2 : R) • Matrix.fromBlocks 1 0 0 (S l R) :=
  by 
    simp [PB, JB, JD_transform, Matrix.from_blocks_transpose, Matrix.from_blocks_multiply, Matrix.from_blocks_smul]

theorem indefinite_diagonal_assoc :
  indefinite_diagonal (Sum Unit l) l R =
    Matrix.reindexLieEquiv (Equiv.sumAssoc Unit l l).symm (Matrix.fromBlocks 1 0 0 (indefinite_diagonal l l R)) :=
  by 
    ext i j 
    rcases i with ⟨⟨i₁ | i₂⟩ | i₃⟩ <;>
      rcases j with ⟨⟨j₁ | j₂⟩ | j₃⟩ <;>
        simp only [indefinite_diagonal, Matrix.diagonalₓ, Equiv.sum_assoc_apply_in1, Matrix.reindex_lie_equiv_apply,
            Matrix.minor_apply, Equiv.symm_symm, Matrix.reindex_apply, Sum.elim_inl, if_true, eq_self_iff_true,
            Matrix.one_apply_eq, Matrix.from_blocks_apply₁₁, Dmatrix.zero_apply, Equiv.sum_assoc_apply_in2, if_false,
            Matrix.from_blocks_apply₁₂, Matrix.from_blocks_apply₂₁, Matrix.from_blocks_apply₂₂,
            Equiv.sum_assoc_apply_in3, Sum.elim_inr] <;>
          congr

/-- An equivalence between two possible definitions of the classical Lie algebra of type B. -/
def type_B_equiv_so' [Invertible (2 : R)] : type_B l R ≃ₗ⁅R⁆ so' (Sum Unit l) l R :=
  by 
    apply
      (skewAdjointMatricesLieSubalgebraEquiv (JB l R) (PB l R)
          (by 
            infer_instance)).trans
        
    symm 
    apply
      (skewAdjointMatricesLieSubalgebraEquivTranspose (indefinite_diagonal (Sum Unit l) l R)
          (Matrix.reindexAlgEquiv _ (Equiv.sumAssoc PUnit l l)) (Matrix.transpose_reindex _ _)).trans
        
    apply LieEquiv.ofEq 
    ext A 
    rw [JB_transform, ←coe_unit_of_invertible (2 : R), ←Units.smul_def, LieSubalgebra.mem_coe, LieSubalgebra.mem_coe,
      mem_skew_adjoint_matrices_lie_subalgebra_unit_smul]
    simpa [indefinite_diagonal_assoc]

end Orthogonal

end LieAlgebra

