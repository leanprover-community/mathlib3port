import Mathbin.Algebra.Lie.OfAssociative 
import Mathbin.LinearAlgebra.Matrix.Reindex 
import Mathbin.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Lie algebras of matrices

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

open_locale Matrix

variable {R : Type u} [CommRingₓ R]

variable {n : Type w} [DecidableEq n] [Fintype n]

-- error in Algebra.Lie.Matrix: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the Lie algebra structures. -/
def lie_equiv_matrix' : «expr ≃ₗ⁅ ⁆ »(module.End R (n → R), R, matrix n n R) :=
{ map_lie' := λ T S, begin
    let [ident f] [] [":=", expr @linear_map.to_matrix' R _ n n _ _],
    change [expr «expr = »(f «expr - »(T.comp S, S.comp T), «expr - »(«expr * »(f T, f S), «expr * »(f S, f T)))] [] [],
    have [ident h] [":", expr ∀
     T S : module.End R _, «expr = »(f (T.comp S), «expr ⬝ »(f T, f S))] [":=", expr linear_map.to_matrix'_comp],
    rw ["[", expr linear_equiv.map_sub, ",", expr h, ",", expr h, ",", expr matrix.mul_eq_mul, ",", expr matrix.mul_eq_mul, "]"] []
  end,
  ..linear_map.to_matrix' }

@[simp]
theorem lie_equiv_matrix'_apply (f : Module.End R (n → R)) : lieEquivMatrix' f = f.to_matrix' :=
  rfl

@[simp]
theorem lie_equiv_matrix'_symm_apply (A : Matrix n n R) : (@lieEquivMatrix' R _ n _ _).symm A = A.to_lin' :=
  rfl

/-- An invertible matrix induces a Lie algebra equivalence from the space of matrices to itself. -/
def Matrix.lieConj (P : Matrix n n R) (h : Invertible P) : Matrix n n R ≃ₗ⁅R⁆ Matrix n n R :=
  ((@lieEquivMatrix' R _ n _ _).symm.trans (P.to_linear_equiv' h).lieConj).trans lieEquivMatrix'

@[simp]
theorem Matrix.lie_conj_apply (P A : Matrix n n R) (h : Invertible P) : P.lie_conj h A = P ⬝ A ⬝ P⁻¹ :=
  by 
    simp [LinearEquiv.conj_apply, Matrix.lieConj, LinearMap.to_matrix'_comp, LinearMap.to_matrix'_to_lin']

@[simp]
theorem Matrix.lie_conj_symm_apply (P A : Matrix n n R) (h : Invertible P) : (P.lie_conj h).symm A = P⁻¹ ⬝ A ⬝ P :=
  by 
    simp [LinearEquiv.symm_conj_apply, Matrix.lieConj, LinearMap.to_matrix'_comp, LinearMap.to_matrix'_to_lin']

variable {m : Type w₁} [DecidableEq m] [Fintype m] (e : n ≃ m)

/-- For square matrices, the natural map that reindexes a matrix's rows and columns with equivalent
types, `matrix.reindex`, is an equivalence of Lie algebras. -/
def Matrix.reindexLieEquiv : Matrix n n R ≃ₗ⁅R⁆ Matrix m m R :=
  { Matrix.reindexLinearEquiv R R e e with toFun := Matrix.reindex e e,
    map_lie' :=
      fun M N =>
        by 
          simp only [LieRing.of_associative_ring_bracket, Matrix.reindex_apply, ←Matrix.minor_mul_equiv _ _ _ _,
            Matrix.mul_eq_mul, Matrix.minor_sub, Pi.sub_apply] }

@[simp]
theorem Matrix.reindex_lie_equiv_apply (M : Matrix n n R) : Matrix.reindexLieEquiv e M = Matrix.reindex e e M :=
  rfl

@[simp]
theorem Matrix.reindex_lie_equiv_symm : (Matrix.reindexLieEquiv e : _ ≃ₗ⁅R⁆ _).symm = Matrix.reindexLieEquiv e.symm :=
  rfl

end Matrices

