import Mathbin.LinearAlgebra.Charpoly.Basic 
import Mathbin.LinearAlgebra.Matrix.Basis

/-!

# Characteristic polynomial

## Main result

* `linear_map.charpoly_to_matrix f` : `charpoly f` is the characteristic polynomial of the matrix
of `f` in any basis.

-/


universe u v w

variable{R : Type u}{M : Type v}[CommRingₓ R][Nontrivial R]

variable[AddCommGroupₓ M][Module R M][Module.Free R M][Module.Finite R M](f : M →ₗ[R] M)

open_locale Classical Matrix

noncomputable theory

open Module.Free Polynomial Matrix

namespace LinearMap

section Basic

-- error in LinearAlgebra.Charpoly.ToMatrix: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `charpoly f` is the characteristic polynomial of the matrix of `f` in any basis. -/
@[simp]
theorem charpoly_to_matrix
{ι : Type w}
[fintype ι]
(b : basis ι R M) : «expr = »((to_matrix b b f).charpoly, f.charpoly) :=
begin
  set [] [ident A] [] [":="] [expr to_matrix b b f] [],
  set [] [ident b'] [] [":="] [expr choose_basis R M] [],
  set [] [ident ι'] [] [":="] [expr choose_basis_index R M] [],
  set [] [ident A'] [] [":="] [expr to_matrix b' b' f] [],
  set [] [ident e] [] [":="] [expr basis.index_equiv b b'] [],
  set [] [ident φ] [] [":="] [expr reindex_linear_equiv R R e e] [],
  set [] [ident φ₁] [] [":="] [expr reindex_linear_equiv R R e (equiv.refl ι')] [],
  set [] [ident φ₂] [] [":="] [expr reindex_linear_equiv R R (equiv.refl ι') (equiv.refl ι')] [],
  set [] [ident φ₃] [] [":="] [expr reindex_linear_equiv R R (equiv.refl ι') e] [],
  set [] [ident P] [] [":="] [expr b.to_matrix b'] [],
  set [] [ident Q] [] [":="] [expr b'.to_matrix b] [],
  have [ident hPQ] [":", expr «expr = »(«expr ⬝ »(C.map_matrix (φ₁ P), C.map_matrix (φ₃ Q)), 1)] [],
  { rw ["[", expr ring_hom.map_matrix_apply, ",", expr ring_hom.map_matrix_apply, ",", "<-", expr matrix.map_mul, ",", "<-", expr @reindex_linear_equiv_mul _ ι' _ _ _ _ R R, ",", expr basis.to_matrix_mul_to_matrix_flip, ",", expr reindex_linear_equiv_one, ",", "<-", expr ring_hom.map_matrix_apply, ",", expr ring_hom.map_one, "]"] [] },
  calc
    «expr = »(A.charpoly, (reindex e e A).charpoly) : (charpoly_reindex _ _).symm
    «expr = »(..., «expr - »(scalar ι' X, C.map_matrix (φ A)).det) : rfl
    «expr = »(..., «expr - »(scalar ι' X, C.map_matrix (φ «expr ⬝ »(«expr ⬝ »(P, A'), Q))).det) : by rw ["[", expr basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix, "]"] []
    «expr = »(..., «expr - »(scalar ι' X, C.map_matrix «expr ⬝ »(«expr ⬝ »(φ₁ P, φ₂ A'), φ₃ Q)).det) : by rw ["[", expr reindex_linear_equiv_mul R R _ _ e, ",", expr reindex_linear_equiv_mul R R e _ _, "]"] []
    «expr = »(..., «expr - »(scalar ι' X, «expr ⬝ »(«expr ⬝ »(C.map_matrix (φ₁ P), C.map_matrix A'), C.map_matrix (φ₃ Q))).det) : by simp [] [] [] [] [] []
    «expr = »(..., «expr - »(«expr ⬝ »(«expr ⬝ »(scalar ι' X, C.map_matrix (φ₁ P)), C.map_matrix (φ₃ Q)), «expr ⬝ »(«expr ⬝ »(C.map_matrix (φ₁ P), C.map_matrix A'), C.map_matrix (φ₃ Q))).det) : by { rw ["[", expr matrix.mul_assoc (scalar ι' X), ",", expr hPQ, ",", expr matrix.mul_one, "]"] [] }
    «expr = »(..., «expr - »(«expr ⬝ »(«expr ⬝ »(C.map_matrix (φ₁ P), scalar ι' X), C.map_matrix (φ₃ Q)), «expr ⬝ »(«expr ⬝ »(C.map_matrix (φ₁ P), C.map_matrix A'), C.map_matrix (φ₃ Q))).det) : by simp [] [] [] [] [] []
    «expr = »(..., «expr ⬝ »(«expr ⬝ »(C.map_matrix (φ₁ P), «expr - »(scalar ι' X, C.map_matrix A')), C.map_matrix (φ₃ Q)).det) : by rw ["[", "<-", expr matrix.sub_mul, ",", "<-", expr matrix.mul_sub, "]"] []
    «expr = »(..., «expr * »(«expr * »((C.map_matrix (φ₁ P)).det, «expr - »(scalar ι' X, C.map_matrix A').det), (C.map_matrix (φ₃ Q)).det)) : by rw ["[", expr det_mul, ",", expr det_mul, "]"] []
    «expr = »(..., «expr * »(«expr * »((C.map_matrix (φ₁ P)).det, (C.map_matrix (φ₃ Q)).det), «expr - »(scalar ι' X, C.map_matrix A').det)) : by ring []
    «expr = »(..., «expr - »(scalar ι' X, C.map_matrix A').det) : by rw ["[", "<-", expr det_mul, ",", expr hPQ, ",", expr det_one, ",", expr one_mul, "]"] []
    «expr = »(..., f.charpoly) : rfl
end

end Basic

end LinearMap

