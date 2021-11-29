import Mathbin.LinearAlgebra.Matrix.Reindex 
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Bases and matrices

This file defines the map `basis.to_matrix` that sends a family of vectors to
the matrix of their coordinates with respect to some basis.

## Main definitions

 * `basis.to_matrix e v` is the matrix whose `i, j`th entry is `e.repr (v j) i`
 * `basis.to_matrix_equiv` is `basis.to_matrix` bundled as a linear equiv

## Main results

 * `linear_map.to_matrix_id_eq_basis_to_matrix`: `linear_map.to_matrix b c id`
   is equal to `basis.to_matrix b c`
 * `basis.to_matrix_mul_to_matrix`: multiplying `basis.to_matrix` with another
   `basis.to_matrix` gives a `basis.to_matrix`

## Tags

matrix, basis
-/


noncomputable theory

open LinearMap Matrix Set Submodule

open_locale BigOperators

open_locale Matrix

section BasisToMatrix

variable {ι ι' κ κ' : Type _}

variable {R M : Type _} [CommRingₓ R] [AddCommGroupₓ M] [Module R M]

open Function Matrix

/-- From a basis `e : ι → M` and a family of vectors `v : ι' → M`, make the matrix whose columns
are the vectors `v i` written in the basis `e`. -/
def Basis.toMatrix (e : Basis ι R M) (v : ι' → M) : Matrix ι ι' R :=
  fun i j => e.repr (v j) i

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

namespace Basis

theorem to_matrix_apply : e.to_matrix v i j = e.repr (v j) i :=
  rfl

theorem to_matrix_transpose_apply : (e.to_matrix v)ᵀ j = e.repr (v j) :=
  funext$ fun _ => rfl

theorem to_matrix_eq_to_matrix_constr [Fintype ι] [DecidableEq ι] (v : ι → M) :
  e.to_matrix v = LinearMap.toMatrix e e (e.constr ℕ v) :=
  by 
    ext 
    rw [Basis.to_matrix_apply, LinearMap.to_matrix_apply, Basis.constr_basis]

theorem coe_pi_basis_fun.to_matrix_eq_transpose [Fintype ι] :
  ((Pi.basisFun R ι).toMatrix : Matrix ι ι R → Matrix ι ι R) = Matrix.transposeₓ :=
  by 
    ext M i j 
    rfl

@[simp]
theorem to_matrix_self [DecidableEq ι] : e.to_matrix e = 1 :=
  by 
    rw [Basis.toMatrix]
    ext i j 
    simp [Basis.equivFun, Matrix.one_apply, Finsupp.single, eq_comm]

theorem to_matrix_update [DecidableEq ι'] (x : M) :
  e.to_matrix (Function.update v j x) = Matrix.updateColumn (e.to_matrix v) j (e.repr x) :=
  by 
    ext i' k 
    rw [Basis.toMatrix, Matrix.update_column_apply, e.to_matrix_apply]
    splitIfs
    ·
      rw [h, update_same j x v]
    ·
      rw [update_noteq h]

@[simp]
theorem sum_to_matrix_smul_self [Fintype ι] : (∑i : ι, e.to_matrix v i j • e i) = v j :=
  by 
    simpRw [e.to_matrix_apply, e.sum_repr]

@[simp]
theorem to_lin_to_matrix [Fintype ι] [Fintype ι'] [DecidableEq ι'] (v : Basis ι' R M) :
  Matrix.toLin v e (e.to_matrix v) = id :=
  v.ext
    fun i =>
      by 
        rw [to_lin_self, id_apply, e.sum_to_matrix_smul_self]

/-- From a basis `e : ι → M`, build a linear equivalence between families of vectors `v : ι → M`,
and matrices, making the matrix whose columns are the vectors `v i` written in the basis `e`. -/
def to_matrix_equiv [Fintype ι] (e : Basis ι R M) : (ι → M) ≃ₗ[R] Matrix ι ι R :=
  { toFun := e.to_matrix,
    map_add' :=
      fun v w =>
        by 
          ext i j 
          change _ = _+_ 
          rw [e.to_matrix_apply, Pi.add_apply, LinearEquiv.map_add]
          rfl,
    map_smul' :=
      by 
        intro c v 
        ext i j 
        rw [e.to_matrix_apply, Pi.smul_apply, LinearEquiv.map_smul]
        rfl,
    invFun := fun m j => ∑i, m i j • e i,
    left_inv :=
      by 
        intro v 
        ext j 
        exact e.sum_to_matrix_smul_self v j,
    right_inv :=
      by 
        intro m 
        ext k l 
        simp only [e.to_matrix_apply, ←e.equiv_fun_apply, ←e.equiv_fun_symm_apply, LinearEquiv.apply_symm_apply] }

end Basis

section MulLinearMapToMatrix

variable {N : Type _} [AddCommGroupₓ N] [Module R N]

variable (b : Basis ι R M) (b' : Basis ι' R M) (c : Basis κ R N) (c' : Basis κ' R N)

variable (f : M →ₗ[R] N)

open LinearMap

section Fintype

variable [Fintype ι'] [Fintype κ] [Fintype κ']

-- error in LinearAlgebra.Matrix.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem basis_to_matrix_mul_linear_map_to_matrix
[decidable_eq ι'] : «expr = »(«expr ⬝ »(c.to_matrix c', linear_map.to_matrix b' c' f), linear_map.to_matrix b' c f) :=
(matrix.to_lin b' c).injective (by haveI [] [] [":=", expr classical.dec_eq κ']; rw ["[", expr to_lin_to_matrix, ",", expr to_lin_mul b' c' c, ",", expr to_lin_to_matrix, ",", expr c.to_lin_to_matrix, ",", expr id_comp, "]"] [])

variable [Fintype ι]

@[simp]
theorem linear_map_to_matrix_mul_basis_to_matrix [DecidableEq ι] [DecidableEq ι'] :
  LinearMap.toMatrix b' c' f ⬝ b'.to_matrix b = LinearMap.toMatrix b c' f :=
  (Matrix.toLin b c').Injective
    (by 
      rw [to_lin_to_matrix, to_lin_mul b b' c', to_lin_to_matrix, b'.to_lin_to_matrix, comp_id])

theorem basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix [DecidableEq ι] [DecidableEq ι'] :
  c.to_matrix c' ⬝ LinearMap.toMatrix b' c' f ⬝ b'.to_matrix b = LinearMap.toMatrix b c f :=
  by 
    rw [basis_to_matrix_mul_linear_map_to_matrix, linear_map_to_matrix_mul_basis_to_matrix]

-- error in LinearAlgebra.Matrix.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A generalization of `linear_map.to_matrix_id`. -/
@[simp]
theorem linear_map.to_matrix_id_eq_basis_to_matrix
[decidable_eq ι] : «expr = »(linear_map.to_matrix b b' id, b'.to_matrix b) :=
by { haveI [] [] [":=", expr classical.dec_eq ι'],
  rw ["[", "<-", expr @basis_to_matrix_mul_linear_map_to_matrix _ _ ι, ",", expr to_matrix_id, ",", expr matrix.mul_one, "]"] [] }

/-- See also `basis.to_matrix_reindex` which gives the `simp` normal form of this result. -/
theorem Basis.to_matrix_reindex' [DecidableEq ι] [DecidableEq ι'] (b : Basis ι R M) (v : ι' → M) (e : ι ≃ ι') :
  (b.reindex e).toMatrix v = Matrix.reindexAlgEquiv _ e (b.to_matrix (v ∘ e)) :=
  by 
    ext 
    simp only [Basis.to_matrix_apply, Basis.reindex_repr, Matrix.reindex_alg_equiv_apply, Matrix.reindex_apply,
      Matrix.minor_apply, Function.comp_app, e.apply_symm_apply]

end Fintype

-- error in LinearAlgebra.Matrix.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A generalization of `basis.to_matrix_self`, in the opposite direction. -/
@[simp]
theorem basis.to_matrix_mul_to_matrix
{ι'' : Type*}
[fintype ι']
(b'' : ι'' → M) : «expr = »(«expr ⬝ »(b.to_matrix b', b'.to_matrix b''), b.to_matrix b'') :=
begin
  have [] [] [":=", expr classical.dec_eq ι],
  have [] [] [":=", expr classical.dec_eq ι'],
  haveI [] [] [":=", expr classical.dec_eq ι''],
  ext [] [ident i, ident j] [],
  simp [] [] ["only"] ["[", expr matrix.mul_apply, ",", expr basis.to_matrix_apply, ",", expr basis.sum_repr_mul_repr, "]"] [] []
end

/-- `b.to_matrix b'` and `b'.to_matrix b` are inverses. -/
theorem Basis.to_matrix_mul_to_matrix_flip [DecidableEq ι] [Fintype ι'] : b.to_matrix b' ⬝ b'.to_matrix b = 1 :=
  by 
    rw [Basis.to_matrix_mul_to_matrix, Basis.to_matrix_self]

@[simp]
theorem Basis.to_matrix_reindex (b : Basis ι R M) (v : ι' → M) (e : ι ≃ ι') :
  (b.reindex e).toMatrix v = (b.to_matrix v).minor e.symm id :=
  by 
    ext 
    simp only [Basis.to_matrix_apply, Basis.reindex_repr, Matrix.minor_apply, id.def]

@[simp]
theorem Basis.to_matrix_map (b : Basis ι R M) (f : M ≃ₗ[R] N) (v : ι → N) :
  (b.map f).toMatrix v = b.to_matrix (f.symm ∘ v) :=
  by 
    ext 
    simp only [Basis.to_matrix_apply, Basis.map, LinearEquiv.trans_apply]

end MulLinearMapToMatrix

end BasisToMatrix

