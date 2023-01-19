/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Moritz Doll

! This file was ported from Lean 3 source module linear_algebra.matrix.sesquilinear_form
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.FinsuppVectorSpace
import Mathbin.LinearAlgebra.Matrix.Basis
import Mathbin.LinearAlgebra.Matrix.Nondegenerate
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.LinearAlgebra.Matrix.ToLinearEquiv
import Mathbin.LinearAlgebra.SesquilinearForm

/-!
# Sesquilinear form

This file defines the conversion between sesquilinear forms and matrices.

## Main definitions

 * `matrix.to_linear_map₂` given a basis define a bilinear form
 * `matrix.to_linear_map₂'` define the bilinear form on `n → R`
 * `linear_map.to_matrix₂`: calculate the matrix coefficients of a bilinear form
 * `linear_map.to_matrix₂'`: calculate the matrix coefficients of a bilinear form on `n → R`

## Todos

At the moment this is quite a literal port from `matrix.bilinear_form`. Everything should be
generalized to fully semibilinear forms.

## Tags

sesquilinear_form, matrix, basis

-/


variable {R R₁ R₂ M M₁ M₂ M₁' M₂' n m n' m' ι : Type _}

open BigOperators

open Finset LinearMap Matrix

open Matrix

section AuxToLinearMap

variable [CommSemiring R] [CommSemiring R₁] [CommSemiring R₂]

variable [Fintype n] [Fintype m]

variable (σ₁ : R₁ →+* R) (σ₂ : R₂ →+* R)

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- The map from `matrix n n R` to bilinear forms on `n → R`.

This is an auxiliary definition for the equivalence `matrix.to_linear_map₂'`. -/
def Matrix.toLinearMap₂'Aux (f : Matrix n m R) : (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R :=
  mk₂'ₛₗ σ₁ σ₂ (fun (v : n → R₁) (w : m → R₂) => ∑ (i) (j), σ₁ (v i) * f i j * σ₂ (w j))
    (fun _ _ _ => by simp only [Pi.add_apply, map_add, add_mul, sum_add_distrib])
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.map_mul, mul_assoc, mul_sum])
    (fun _ _ _ => by simp only [Pi.add_apply, map_add, mul_add, sum_add_distrib]) fun _ _ _ => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.map_mul, mul_assoc, mul_left_comm, mul_sum]
#align matrix.to_linear_map₂'_aux Matrix.toLinearMap₂'Aux

variable [DecidableEq n] [DecidableEq m]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' j') -/
theorem Matrix.to_linear_map₂'_aux_std_basis (f : Matrix n m R) (i : n) (j : m) :
    f.toLinearMap₂'Aux σ₁ σ₂ (stdBasis R₁ (fun _ => R₁) i 1) (stdBasis R₂ (fun _ => R₂) j 1) =
      f i j :=
  by
  rw [Matrix.toLinearMap₂'Aux, mk₂'ₛₗ_apply]
  have : (∑ (i') (j'), (if i = i' then 1 else 0) * f i' j' * if j = j' then 1 else 0) = f i j :=
    by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    simp only [boole_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_comm (f _ _)]
  rw [← this]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp
#align matrix.to_linear_map₂'_aux_std_basis Matrix.to_linear_map₂'_aux_std_basis

end AuxToLinearMap

section AuxToMatrix

section CommSemiring

variable [CommSemiring R] [CommSemiring R₁] [CommSemiring R₂]

variable [AddCommMonoid M₁] [Module R₁ M₁] [AddCommMonoid M₂] [Module R₂ M₂]

variable {σ₁ : R₁ →+* R} {σ₂ : R₂ →+* R}

/-- The linear map from sesquilinear forms to `matrix n m R` given an `n`-indexed basis for `M₁`
and an `m`-indexed basis for `M₂`.

This is an auxiliary definition for the equivalence `matrix.to_linear_mapₛₗ₂'`. -/
def LinearMap.toMatrix₂Aux (b₁ : n → M₁) (b₂ : m → M₂) :
    (M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] R) →ₗ[R] Matrix n m R
    where
  toFun f := of fun i j => f (b₁ i) (b₂ j)
  map_add' f g := rfl
  map_smul' f g := rfl
#align linear_map.to_matrix₂_aux LinearMap.toMatrix₂Aux

@[simp]
theorem LinearMap.to_matrix₂_aux_apply (f : M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] R) (b₁ : n → M₁) (b₂ : m → M₂)
    (i : n) (j : m) : LinearMap.toMatrix₂Aux b₁ b₂ f i j = f (b₁ i) (b₂ j) :=
  rfl
#align linear_map.to_matrix₂_aux_apply LinearMap.to_matrix₂_aux_apply

end CommSemiring

section CommRing

variable [CommRing R] [CommRing R₁] [CommRing R₂]

variable [AddCommMonoid M₁] [Module R₁ M₁] [AddCommMonoid M₂] [Module R₂ M₂]

variable [Fintype n] [Fintype m]

variable [DecidableEq n] [DecidableEq m]

variable {σ₁ : R₁ →+* R} {σ₂ : R₂ →+* R}

theorem LinearMap.to_linear_map₂'_aux_to_matrix₂_aux (f : (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R) :
    Matrix.toLinearMap₂'Aux σ₁ σ₂
        (LinearMap.toMatrix₂Aux (fun i => stdBasis R₁ (fun _ => R₁) i 1)
          (fun j => stdBasis R₂ (fun _ => R₂) j 1) f) =
      f :=
  by
  refine' ext_basis (Pi.basisFun R₁ n) (Pi.basisFun R₂ m) fun i j => _
  simp_rw [Pi.basis_fun_apply, Matrix.to_linear_map₂'_aux_std_basis, LinearMap.to_matrix₂_aux_apply]
#align linear_map.to_linear_map₂'_aux_to_matrix₂_aux LinearMap.to_linear_map₂'_aux_to_matrix₂_aux

theorem Matrix.to_matrix₂_aux_to_linear_map₂'_aux (f : Matrix n m R) :
    LinearMap.toMatrix₂Aux (fun i => stdBasis R₁ (fun _ => R₁) i 1)
        (fun j => stdBasis R₂ (fun _ => R₂) j 1) (f.toLinearMap₂'Aux σ₁ σ₂) =
      f :=
  by
  ext (i j)
  simp_rw [LinearMap.to_matrix₂_aux_apply, Matrix.to_linear_map₂'_aux_std_basis]
#align matrix.to_matrix₂_aux_to_linear_map₂'_aux Matrix.to_matrix₂_aux_to_linear_map₂'_aux

end CommRing

end AuxToMatrix

section ToMatrix'

/-! ### Bilinear forms over `n → R`

This section deals with the conversion between matrices and sesquilinear forms on `n → R`.
-/


variable [CommRing R] [CommRing R₁] [CommRing R₂]

variable [Fintype n] [Fintype m]

variable [DecidableEq n] [DecidableEq m]

variable {σ₁ : R₁ →+* R} {σ₂ : R₂ →+* R}

/-- The linear equivalence between sesquilinear forms and `n × m` matrices -/
def LinearMap.toMatrixₛₗ₂' : ((n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R) ≃ₗ[R] Matrix n m R :=
  {
    LinearMap.toMatrix₂Aux (fun i => stdBasis R₁ (fun _ => R₁) i 1) fun j =>
      stdBasis R₂ (fun _ => R₂) j
        1 with
    toFun := LinearMap.toMatrix₂Aux _ _
    invFun := Matrix.toLinearMap₂'Aux σ₁ σ₂
    left_inv := LinearMap.to_linear_map₂'_aux_to_matrix₂_aux
    right_inv := Matrix.to_matrix₂_aux_to_linear_map₂'_aux }
#align linear_map.to_matrixₛₗ₂' LinearMap.toMatrixₛₗ₂'

/-- The linear equivalence between bilinear forms and `n × m` matrices -/
def LinearMap.toMatrix₂' : ((n → R) →ₗ[R] (m → R) →ₗ[R] R) ≃ₗ[R] Matrix n m R :=
  LinearMap.toMatrixₛₗ₂'
#align linear_map.to_matrix₂' LinearMap.toMatrix₂'

variable (σ₁ σ₂)

/-- The linear equivalence between `n × n` matrices and sesquilinear forms on `n → R` -/
def Matrix.toLinearMapₛₗ₂' : Matrix n m R ≃ₗ[R] (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R :=
  LinearMap.toMatrixₛₗ₂'.symm
#align matrix.to_linear_mapₛₗ₂' Matrix.toLinearMapₛₗ₂'

/-- The linear equivalence between `n × n` matrices and bilinear forms on `n → R` -/
def Matrix.toLinearMap₂' : Matrix n m R ≃ₗ[R] (n → R) →ₗ[R] (m → R) →ₗ[R] R :=
  LinearMap.toMatrix₂'.symm
#align matrix.to_linear_map₂' Matrix.toLinearMap₂'

theorem Matrix.to_linear_mapₛₗ₂'_aux_eq (M : Matrix n m R) :
    Matrix.toLinearMap₂'Aux σ₁ σ₂ M = Matrix.toLinearMapₛₗ₂' σ₁ σ₂ M :=
  rfl
#align matrix.to_linear_mapₛₗ₂'_aux_eq Matrix.to_linear_mapₛₗ₂'_aux_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Matrix.to_linear_mapₛₗ₂'_apply (M : Matrix n m R) (x : n → R₁) (y : m → R₂) :
    Matrix.toLinearMapₛₗ₂' σ₁ σ₂ M x y = ∑ (i) (j), σ₁ (x i) * M i j * σ₂ (y j) :=
  rfl
#align matrix.to_linear_mapₛₗ₂'_apply Matrix.to_linear_mapₛₗ₂'_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Matrix.to_linear_map₂'_apply (M : Matrix n m R) (x : n → R) (y : m → R) :
    Matrix.toLinearMap₂' M x y = ∑ (i) (j), x i * M i j * y j :=
  rfl
#align matrix.to_linear_map₂'_apply Matrix.to_linear_map₂'_apply

theorem Matrix.to_linear_map₂'_apply' (M : Matrix n m R) (v : n → R) (w : m → R) :
    Matrix.toLinearMap₂' M v w = Matrix.dotProduct v (M.mulVec w) :=
  by
  simp_rw [Matrix.to_linear_map₂'_apply, Matrix.dotProduct, Matrix.mulVec, Matrix.dotProduct]
  refine' Finset.sum_congr rfl fun _ _ => _
  rw [Finset.mul_sum]
  refine' Finset.sum_congr rfl fun _ _ => _
  rw [← mul_assoc]
#align matrix.to_linear_map₂'_apply' Matrix.to_linear_map₂'_apply'

@[simp]
theorem Matrix.to_linear_mapₛₗ₂'_std_basis (M : Matrix n m R) (i : n) (j : m) :
    Matrix.toLinearMapₛₗ₂' σ₁ σ₂ M (stdBasis R₁ (fun _ => R₁) i 1) (stdBasis R₂ (fun _ => R₂) j 1) =
      M i j :=
  Matrix.to_linear_map₂'_aux_std_basis σ₁ σ₂ M i j
#align matrix.to_linear_mapₛₗ₂'_std_basis Matrix.to_linear_mapₛₗ₂'_std_basis

@[simp]
theorem Matrix.to_linear_map₂'_std_basis (M : Matrix n m R) (i : n) (j : m) :
    Matrix.toLinearMap₂' M (stdBasis R (fun _ => R) i 1) (stdBasis R (fun _ => R) j 1) = M i j :=
  Matrix.to_linear_map₂'_aux_std_basis _ _ M i j
#align matrix.to_linear_map₂'_std_basis Matrix.to_linear_map₂'_std_basis

@[simp]
theorem LinearMap.to_matrixₛₗ₂'_symm :
    (LinearMap.toMatrixₛₗ₂'.symm : Matrix n m R ≃ₗ[R] _) = Matrix.toLinearMapₛₗ₂' σ₁ σ₂ :=
  rfl
#align linear_map.to_matrixₛₗ₂'_symm LinearMap.to_matrixₛₗ₂'_symm

@[simp]
theorem Matrix.to_linear_mapₛₗ₂'_symm :
    ((Matrix.toLinearMapₛₗ₂' σ₁ σ₂).symm : _ ≃ₗ[R] Matrix n m R) = LinearMap.toMatrixₛₗ₂' :=
  LinearMap.toMatrixₛₗ₂'.symm_symm
#align matrix.to_linear_mapₛₗ₂'_symm Matrix.to_linear_mapₛₗ₂'_symm

@[simp]
theorem Matrix.to_linear_mapₛₗ₂'_to_matrix' (B : (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R) :
    Matrix.toLinearMapₛₗ₂' σ₁ σ₂ (LinearMap.toMatrixₛₗ₂' B) = B :=
  (Matrix.toLinearMapₛₗ₂' σ₁ σ₂).apply_symm_apply B
#align matrix.to_linear_mapₛₗ₂'_to_matrix' Matrix.to_linear_mapₛₗ₂'_to_matrix'

@[simp]
theorem Matrix.to_linear_map₂'_to_matrix' (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) :
    Matrix.toLinearMap₂' (LinearMap.toMatrix₂' B) = B :=
  Matrix.toLinearMap₂'.apply_symm_apply B
#align matrix.to_linear_map₂'_to_matrix' Matrix.to_linear_map₂'_to_matrix'

@[simp]
theorem LinearMap.to_matrix'_to_linear_mapₛₗ₂' (M : Matrix n m R) :
    LinearMap.toMatrixₛₗ₂' (Matrix.toLinearMapₛₗ₂' σ₁ σ₂ M) = M :=
  LinearMap.toMatrixₛₗ₂'.apply_symm_apply M
#align linear_map.to_matrix'_to_linear_mapₛₗ₂' LinearMap.to_matrix'_to_linear_mapₛₗ₂'

@[simp]
theorem LinearMap.to_matrix'_to_linear_map₂' (M : Matrix n m R) :
    LinearMap.toMatrix₂' (Matrix.toLinearMap₂' M) = M :=
  LinearMap.toMatrixₛₗ₂'.apply_symm_apply M
#align linear_map.to_matrix'_to_linear_map₂' LinearMap.to_matrix'_to_linear_map₂'

@[simp]
theorem LinearMap.to_matrixₛₗ₂'_apply (B : (n → R₁) →ₛₗ[σ₁] (m → R₂) →ₛₗ[σ₂] R) (i : n) (j : m) :
    LinearMap.toMatrixₛₗ₂' B i j =
      B (stdBasis R₁ (fun _ => R₁) i 1) (stdBasis R₂ (fun _ => R₂) j 1) :=
  rfl
#align linear_map.to_matrixₛₗ₂'_apply LinearMap.to_matrixₛₗ₂'_apply

@[simp]
theorem LinearMap.to_matrix₂'_apply (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (i : n) (j : m) :
    LinearMap.toMatrix₂' B i j = B (stdBasis R (fun _ => R) i 1) (stdBasis R (fun _ => R) j 1) :=
  rfl
#align linear_map.to_matrix₂'_apply LinearMap.to_matrix₂'_apply

variable [Fintype n'] [Fintype m']

variable [DecidableEq n'] [DecidableEq m']

@[simp]
theorem LinearMap.to_matrix₂'_compl₁₂ (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (l : (n' → R) →ₗ[R] n → R)
    (r : (m' → R) →ₗ[R] m → R) :
    (B.compl₁₂ l r).toMatrix₂' = l.toMatrix'ᵀ ⬝ B.toMatrix₂' ⬝ r.toMatrix' :=
  by
  ext (i j)
  simp only [LinearMap.to_matrix₂'_apply, LinearMap.compl₁₂_apply, transpose_apply,
    Matrix.mul_apply, LinearMap.toMatrix', LinearEquiv.coe_mk, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← LinearMap.sum_repr_mul_repr_mul (Pi.basisFun R n) (Pi.basisFun R m) (l _) (r _)]
  rw [Finsupp.sum_fintype]
  · apply sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply sum_congr rfl
      rintro j' -
      simp only [smul_eq_mul, Pi.basis_fun_repr, mul_assoc, mul_comm, mul_left_comm,
        Pi.basis_fun_apply, of_apply]
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp only [zero_smul, Finsupp.sum_zero]
#align linear_map.to_matrix₂'_compl₁₂ LinearMap.to_matrix₂'_compl₁₂

theorem LinearMap.to_matrix₂'_comp (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (f : (n' → R) →ₗ[R] n → R) :
    (B.comp f).toMatrix₂' = f.toMatrix'ᵀ ⬝ B.toMatrix₂' :=
  by
  rw [← LinearMap.compl₂_id (B.comp f), ← LinearMap.compl₁₂]
  simp
#align linear_map.to_matrix₂'_comp LinearMap.to_matrix₂'_comp

theorem LinearMap.to_matrix₂'_compl₂ (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R)
    (f : (m' → R) →ₗ[R] m → R) : (B.compl₂ f).toMatrix₂' = B.toMatrix₂' ⬝ f.toMatrix' :=
  by
  rw [← LinearMap.comp_id B, ← LinearMap.compl₁₂]
  simp
#align linear_map.to_matrix₂'_compl₂ LinearMap.to_matrix₂'_compl₂

theorem LinearMap.mul_to_matrix₂'_mul (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (M : Matrix n' n R)
    (N : Matrix m m' R) : M ⬝ B.toMatrix₂' ⬝ N = (B.compl₁₂ Mᵀ.toLin' N.toLin').toMatrix₂' := by
  simp
#align linear_map.mul_to_matrix₂'_mul LinearMap.mul_to_matrix₂'_mul

theorem LinearMap.mul_to_matrix' (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (M : Matrix n' n R) :
    M ⬝ B.toMatrix₂' = (B.comp Mᵀ.toLin').toMatrix₂' := by
  simp only [B.to_matrix₂'_comp, transpose_transpose, to_matrix'_to_lin']
#align linear_map.mul_to_matrix' LinearMap.mul_to_matrix'

theorem LinearMap.to_matrix₂'_mul (B : (n → R) →ₗ[R] (m → R) →ₗ[R] R) (M : Matrix m m' R) :
    B.toMatrix₂' ⬝ M = (B.compl₂ M.toLin').toMatrix₂' := by
  simp only [B.to_matrix₂'_compl₂, to_matrix'_to_lin']
#align linear_map.to_matrix₂'_mul LinearMap.to_matrix₂'_mul

theorem Matrix.to_linear_map₂'_comp (M : Matrix n m R) (P : Matrix n n' R) (Q : Matrix m m' R) :
    M.toLinearMap₂'.compl₁₂ P.toLin' Q.toLin' = (Pᵀ ⬝ M ⬝ Q).toLinearMap₂' :=
  LinearMap.toMatrix₂'.Injective (by simp)
#align matrix.to_linear_map₂'_comp Matrix.to_linear_map₂'_comp

end ToMatrix'

section ToMatrix

/-! ### Bilinear forms over arbitrary vector spaces

This section deals with the conversion between matrices and bilinear forms on
a module with a fixed basis.
-/


variable [CommRing R]

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

variable [DecidableEq n] [Fintype n]

variable [DecidableEq m] [Fintype m]

variable (b₁ : Basis n R M₁) (b₂ : Basis m R M₂)

/-- `linear_map.to_matrix₂ b₁ b₂` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
noncomputable def LinearMap.toMatrix₂ : (M₁ →ₗ[R] M₂ →ₗ[R] R) ≃ₗ[R] Matrix n m R :=
  (b₁.equivFun.arrowCongr (b₂.equivFun.arrowCongr (LinearEquiv.refl R R))).trans
    LinearMap.toMatrix₂'
#align linear_map.to_matrix₂ LinearMap.toMatrix₂

/-- `bilin_form.to_matrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
noncomputable def Matrix.toLinearMap₂ : Matrix n m R ≃ₗ[R] M₁ →ₗ[R] M₂ →ₗ[R] R :=
  (LinearMap.toMatrix₂ b₁ b₂).symm
#align matrix.to_linear_map₂ Matrix.toLinearMap₂

-- We make this and not `linear_map.to_matrix₂` a `simp` lemma to avoid timeouts
@[simp]
theorem LinearMap.to_matrix₂_apply (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (i : n) (j : m) :
    LinearMap.toMatrix₂ b₁ b₂ B i j = B (b₁ i) (b₂ j) := by
  simp only [LinearMap.toMatrix₂, LinearEquiv.trans_apply, LinearMap.to_matrix₂'_apply,
    LinearEquiv.trans_apply, LinearMap.to_matrix₂'_apply, LinearEquiv.arrow_congr_apply,
    Basis.equiv_fun_symm_std_basis, LinearEquiv.refl_apply]
#align linear_map.to_matrix₂_apply LinearMap.to_matrix₂_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem Matrix.to_linear_map₂_apply (M : Matrix n m R) (x : M₁) (y : M₂) :
    Matrix.toLinearMap₂ b₁ b₂ M x y = ∑ (i) (j), b₁.repr x i * M i j * b₂.repr y j :=
  rfl
#align matrix.to_linear_map₂_apply Matrix.to_linear_map₂_apply

-- Not a `simp` lemma since `linear_map.to_matrix₂` needs an extra argument
theorem LinearMap.to_matrix₂_aux_eq (B : M₁ →ₗ[R] M₂ →ₗ[R] R) :
    LinearMap.toMatrix₂Aux b₁ b₂ B = LinearMap.toMatrix₂ b₁ b₂ B :=
  ext fun i j => by rw [LinearMap.to_matrix₂_apply, LinearMap.to_matrix₂_aux_apply]
#align linear_map.to_matrix₂_aux_eq LinearMap.to_matrix₂_aux_eq

@[simp]
theorem LinearMap.to_matrix₂_symm : (LinearMap.toMatrix₂ b₁ b₂).symm = Matrix.toLinearMap₂ b₁ b₂ :=
  rfl
#align linear_map.to_matrix₂_symm LinearMap.to_matrix₂_symm

@[simp]
theorem Matrix.to_linear_map₂_symm : (Matrix.toLinearMap₂ b₁ b₂).symm = LinearMap.toMatrix₂ b₁ b₂ :=
  (LinearMap.toMatrix₂ b₁ b₂).symm_symm
#align matrix.to_linear_map₂_symm Matrix.to_linear_map₂_symm

theorem Matrix.to_linear_map₂_basis_fun :
    Matrix.toLinearMap₂ (Pi.basisFun R n) (Pi.basisFun R m) = Matrix.toLinearMap₂' :=
  by
  ext M
  simp only [Matrix.to_linear_map₂_apply, Matrix.to_linear_map₂'_apply, Pi.basis_fun_repr, coe_comp,
    Function.comp_apply]
#align matrix.to_linear_map₂_basis_fun Matrix.to_linear_map₂_basis_fun

theorem LinearMap.to_matrix₂_basis_fun :
    LinearMap.toMatrix₂ (Pi.basisFun R n) (Pi.basisFun R m) = LinearMap.toMatrix₂' :=
  by
  ext B
  rw [LinearMap.to_matrix₂_apply, LinearMap.to_matrix₂'_apply, Pi.basis_fun_apply,
    Pi.basis_fun_apply]
#align linear_map.to_matrix₂_basis_fun LinearMap.to_matrix₂_basis_fun

@[simp]
theorem Matrix.to_linear_map₂_to_matrix₂ (B : M₁ →ₗ[R] M₂ →ₗ[R] R) :
    Matrix.toLinearMap₂ b₁ b₂ (LinearMap.toMatrix₂ b₁ b₂ B) = B :=
  (Matrix.toLinearMap₂ b₁ b₂).apply_symm_apply B
#align matrix.to_linear_map₂_to_matrix₂ Matrix.to_linear_map₂_to_matrix₂

@[simp]
theorem LinearMap.to_matrix₂_to_linear_map₂ (M : Matrix n m R) :
    LinearMap.toMatrix₂ b₁ b₂ (Matrix.toLinearMap₂ b₁ b₂ M) = M :=
  (LinearMap.toMatrix₂ b₁ b₂).apply_symm_apply M
#align linear_map.to_matrix₂_to_linear_map₂ LinearMap.to_matrix₂_to_linear_map₂

variable [AddCommMonoid M₁'] [Module R M₁']

variable [AddCommMonoid M₂'] [Module R M₂']

variable (b₁' : Basis n' R M₁')

variable (b₂' : Basis m' R M₂')

variable [Fintype n'] [Fintype m']

variable [DecidableEq n'] [DecidableEq m']

-- Cannot be a `simp` lemma because `b₁` and `b₂` must be inferred.
theorem LinearMap.to_matrix₂_compl₁₂ (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (l : M₁' →ₗ[R] M₁)
    (r : M₂' →ₗ[R] M₂) :
    LinearMap.toMatrix₂ b₁' b₂' (B.compl₁₂ l r) =
      (toMatrix b₁' b₁ l)ᵀ ⬝ LinearMap.toMatrix₂ b₁ b₂ B ⬝ toMatrix b₂' b₂ r :=
  by
  ext (i j)
  simp only [LinearMap.to_matrix₂_apply, compl₁₂_apply, transpose_apply, Matrix.mul_apply,
    LinearMap.to_matrix_apply, LinearEquiv.coe_mk, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← LinearMap.sum_repr_mul_repr_mul b₁ b₂]
  rw [Finsupp.sum_fintype]
  · apply sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply sum_congr rfl
      rintro j' -
      simp only [smul_eq_mul, LinearMap.to_matrix_apply, Basis.equiv_fun_apply, mul_assoc, mul_comm,
        mul_left_comm]
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp only [zero_smul, Finsupp.sum_zero]
#align linear_map.to_matrix₂_compl₁₂ LinearMap.to_matrix₂_compl₁₂

theorem LinearMap.to_matrix₂_comp (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (f : M₁' →ₗ[R] M₁) :
    LinearMap.toMatrix₂ b₁' b₂ (B.comp f) = (toMatrix b₁' b₁ f)ᵀ ⬝ LinearMap.toMatrix₂ b₁ b₂ B :=
  by
  rw [← LinearMap.compl₂_id (B.comp f), ← LinearMap.compl₁₂, LinearMap.to_matrix₂_compl₁₂ b₁ b₂]
  simp
#align linear_map.to_matrix₂_comp LinearMap.to_matrix₂_comp

theorem LinearMap.to_matrix₂_compl₂ (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (f : M₂' →ₗ[R] M₂) :
    LinearMap.toMatrix₂ b₁ b₂' (B.compl₂ f) = LinearMap.toMatrix₂ b₁ b₂ B ⬝ toMatrix b₂' b₂ f :=
  by
  rw [← LinearMap.comp_id B, ← LinearMap.compl₁₂, LinearMap.to_matrix₂_compl₁₂ b₁ b₂]
  simp
#align linear_map.to_matrix₂_compl₂ LinearMap.to_matrix₂_compl₂

@[simp]
theorem LinearMap.to_matrix₂_mul_basis_to_matrix (c₁ : Basis n' R M₁) (c₂ : Basis m' R M₂)
    (B : M₁ →ₗ[R] M₂ →ₗ[R] R) :
    (b₁.toMatrix c₁)ᵀ ⬝ LinearMap.toMatrix₂ b₁ b₂ B ⬝ b₂.toMatrix c₂ =
      LinearMap.toMatrix₂ c₁ c₂ B :=
  by
  simp_rw [← LinearMap.to_matrix_id_eq_basis_to_matrix]
  rw [← LinearMap.to_matrix₂_compl₁₂, LinearMap.compl₁₂_id_id]
#align linear_map.to_matrix₂_mul_basis_to_matrix LinearMap.to_matrix₂_mul_basis_to_matrix

theorem LinearMap.mul_to_matrix₂_mul (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (M : Matrix n' n R)
    (N : Matrix m m' R) :
    M ⬝ LinearMap.toMatrix₂ b₁ b₂ B ⬝ N =
      LinearMap.toMatrix₂ b₁' b₂' (B.compl₁₂ (toLin b₁' b₁ Mᵀ) (toLin b₂' b₂ N)) :=
  by simp_rw [LinearMap.to_matrix₂_compl₁₂ b₁ b₂, to_matrix_to_lin, transpose_transpose]
#align linear_map.mul_to_matrix₂_mul LinearMap.mul_to_matrix₂_mul

theorem LinearMap.mul_to_matrix₂ (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (M : Matrix n' n R) :
    M ⬝ LinearMap.toMatrix₂ b₁ b₂ B = LinearMap.toMatrix₂ b₁' b₂ (B.comp (toLin b₁' b₁ Mᵀ)) := by
  rw [LinearMap.to_matrix₂_comp b₁, to_matrix_to_lin, transpose_transpose]
#align linear_map.mul_to_matrix₂ LinearMap.mul_to_matrix₂

theorem LinearMap.to_matrix₂_mul (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (M : Matrix m m' R) :
    LinearMap.toMatrix₂ b₁ b₂ B ⬝ M = LinearMap.toMatrix₂ b₁ b₂' (B.compl₂ (toLin b₂' b₂ M)) := by
  rw [LinearMap.to_matrix₂_compl₂ b₁, to_matrix_to_lin]
#align linear_map.to_matrix₂_mul LinearMap.to_matrix₂_mul

theorem Matrix.to_linear_map₂_compl₁₂ (M : Matrix n m R) (P : Matrix n n' R) (Q : Matrix m m' R) :
    (Matrix.toLinearMap₂ b₁ b₂ M).compl₁₂ (toLin b₁' b₁ P) (toLin b₂' b₂ Q) =
      Matrix.toLinearMap₂ b₁' b₂' (Pᵀ ⬝ M ⬝ Q) :=
  (LinearMap.toMatrix₂ b₁' b₂').Injective
    (by
      simp only [LinearMap.to_matrix₂_compl₁₂ b₁ b₂, LinearMap.to_matrix₂_to_linear_map₂,
        to_matrix_to_lin])
#align matrix.to_linear_map₂_compl₁₂ Matrix.to_linear_map₂_compl₁₂

end ToMatrix

/-! ### Adjoint pairs-/


section MatrixAdjoints

open Matrix

variable [CommRing R]

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

variable [Fintype n] [Fintype n']

variable (b₁ : Basis n R M₁) (b₂ : Basis n' R M₂)

variable (J J₂ : Matrix n n R) (J' : Matrix n' n' R)

variable (A : Matrix n' n R) (A' : Matrix n n' R)

variable (A₁ : Matrix n n R)

/-- The condition for the matrices `A`, `A'` to be an adjoint pair with respect to the square
matrices `J`, `J₃`. -/
def Matrix.IsAdjointPair :=
  Aᵀ ⬝ J' = J ⬝ A'
#align matrix.is_adjoint_pair Matrix.IsAdjointPair

/-- The condition for a square matrix `A` to be self-adjoint with respect to the square matrix
`J`. -/
def Matrix.IsSelfAdjoint :=
  Matrix.IsAdjointPair J J A₁ A₁
#align matrix.is_self_adjoint Matrix.IsSelfAdjoint

/-- The condition for a square matrix `A` to be skew-adjoint with respect to the square matrix
`J`. -/
def Matrix.IsSkewAdjoint :=
  Matrix.IsAdjointPair J J A₁ (-A₁)
#align matrix.is_skew_adjoint Matrix.IsSkewAdjoint

variable [DecidableEq n] [DecidableEq n']

@[simp]
theorem is_adjoint_pair_to_linear_map₂' :
    IsAdjointPair (Matrix.toLinearMap₂' J) (Matrix.toLinearMap₂' J') (Matrix.toLin' A)
        (Matrix.toLin' A') ↔
      Matrix.IsAdjointPair J J' A A' :=
  by
  rw [is_adjoint_pair_iff_comp_eq_compl₂]
  have h :
    ∀ B B' : (n → R) →ₗ[R] (n' → R) →ₗ[R] R,
      B = B' ↔ LinearMap.toMatrix₂' B = LinearMap.toMatrix₂' B' :=
    by
    intro B B'
    constructor <;> intro h
    · rw [h]
    · exact linear_map.to_matrix₂'.injective h
  simp_rw [h, LinearMap.to_matrix₂'_comp, LinearMap.to_matrix₂'_compl₂,
    LinearMap.to_matrix'_to_lin', LinearMap.to_matrix'_to_linear_map₂']
  rfl
#align is_adjoint_pair_to_linear_map₂' is_adjoint_pair_to_linear_map₂'

@[simp]
theorem is_adjoint_pair_to_linear_map₂ :
    IsAdjointPair (Matrix.toLinearMap₂ b₁ b₁ J) (Matrix.toLinearMap₂ b₂ b₂ J')
        (Matrix.toLin b₁ b₂ A) (Matrix.toLin b₂ b₁ A') ↔
      Matrix.IsAdjointPair J J' A A' :=
  by
  rw [is_adjoint_pair_iff_comp_eq_compl₂]
  have h :
    ∀ B B' : M₁ →ₗ[R] M₂ →ₗ[R] R,
      B = B' ↔ LinearMap.toMatrix₂ b₁ b₂ B = LinearMap.toMatrix₂ b₁ b₂ B' :=
    by
    intro B B'
    constructor <;> intro h
    · rw [h]
    · exact (LinearMap.toMatrix₂ b₁ b₂).Injective h
  simp_rw [h, LinearMap.to_matrix₂_comp b₂ b₂, LinearMap.to_matrix₂_compl₂ b₁ b₁,
    LinearMap.to_matrix_to_lin, LinearMap.to_matrix₂_to_linear_map₂]
  rfl
#align is_adjoint_pair_to_linear_map₂ is_adjoint_pair_to_linear_map₂

theorem Matrix.is_adjoint_pair_equiv (P : Matrix n n R) (h : IsUnit P) :
    (Pᵀ ⬝ J ⬝ P).IsAdjointPair (Pᵀ ⬝ J ⬝ P) A₁ A₁ ↔
      J.IsAdjointPair J (P ⬝ A₁ ⬝ P⁻¹) (P ⬝ A₁ ⬝ P⁻¹) :=
  by
  have h' : IsUnit P.det := P.is_unit_iff_is_unit_det.mp h
  let u := P.nonsing_inv_unit h'
  let v := Pᵀ.nonsingInvUnit (P.is_unit_det_transpose h')
  let x := A₁ᵀ * Pᵀ * J
  let y := J * P * A₁
  suffices x * ↑u = ↑v * y ↔ ↑v⁻¹ * x = y * ↑u⁻¹
    by
    dsimp only [Matrix.IsAdjointPair]
    repeat' rw [Matrix.transpose_mul]
    simp only [← Matrix.mul_eq_mul, ← mul_assoc, P.transpose_nonsing_inv]
    conv_lhs =>
      rhs
      rw [mul_assoc, mul_assoc]
      congr
      skip
      rw [← mul_assoc]
    conv_rhs =>
      rw [mul_assoc, mul_assoc]
      conv =>
        lhs
        congr
        skip
        rw [← mul_assoc]
    exact this
  rw [Units.eq_mul_inv_iff_mul_eq]
  conv_rhs => rw [mul_assoc]
  rw [v.inv_mul_eq_iff_eq_mul]
#align matrix.is_adjoint_pair_equiv Matrix.is_adjoint_pair_equiv

/-- The submodule of pair-self-adjoint matrices with respect to bilinear forms corresponding to
given matrices `J`, `J₂`. -/
def pairSelfAdjointMatricesSubmodule : Submodule R (Matrix n n R) :=
  (isPairSelfAdjointSubmodule (Matrix.toLinearMap₂' J) (Matrix.toLinearMap₂' J₂)).map
    ((LinearMap.toMatrix' : ((n → R) →ₗ[R] n → R) ≃ₗ[R] Matrix n n R) :
      ((n → R) →ₗ[R] n → R) →ₗ[R] Matrix n n R)
#align pair_self_adjoint_matrices_submodule pairSelfAdjointMatricesSubmodule

@[simp]
theorem mem_pair_self_adjoint_matrices_submodule :
    A₁ ∈ pairSelfAdjointMatricesSubmodule J J₂ ↔ Matrix.IsAdjointPair J J₂ A₁ A₁ :=
  by
  simp only [pairSelfAdjointMatricesSubmodule, LinearEquiv.coe_coe, LinearMap.to_matrix'_apply,
    Submodule.mem_map, mem_is_pair_self_adjoint_submodule]
  constructor
  · rintro ⟨f, hf, hA⟩
    have hf' : f = A₁.to_lin' := by rw [← hA, Matrix.to_lin'_to_matrix']
    rw [hf'] at hf
    rw [← is_adjoint_pair_to_linear_map₂']
    exact hf
  · intro h
    refine' ⟨A₁.to_lin', _, LinearMap.to_matrix'_to_lin' _⟩
    exact (is_adjoint_pair_to_linear_map₂' _ _ _ _).mpr h
#align mem_pair_self_adjoint_matrices_submodule mem_pair_self_adjoint_matrices_submodule

/-- The submodule of self-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def selfAdjointMatricesSubmodule : Submodule R (Matrix n n R) :=
  pairSelfAdjointMatricesSubmodule J J
#align self_adjoint_matrices_submodule selfAdjointMatricesSubmodule

@[simp]
theorem mem_self_adjoint_matrices_submodule :
    A₁ ∈ selfAdjointMatricesSubmodule J ↔ J.IsSelfAdjoint A₁ :=
  by
  erw [mem_pair_self_adjoint_matrices_submodule]
  rfl
#align mem_self_adjoint_matrices_submodule mem_self_adjoint_matrices_submodule

/-- The submodule of skew-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def skewAdjointMatricesSubmodule : Submodule R (Matrix n n R) :=
  pairSelfAdjointMatricesSubmodule (-J) J
#align skew_adjoint_matrices_submodule skewAdjointMatricesSubmodule

@[simp]
theorem mem_skew_adjoint_matrices_submodule :
    A₁ ∈ skewAdjointMatricesSubmodule J ↔ J.IsSkewAdjoint A₁ :=
  by
  erw [mem_pair_self_adjoint_matrices_submodule]
  simp [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
#align mem_skew_adjoint_matrices_submodule mem_skew_adjoint_matrices_submodule

end MatrixAdjoints

namespace LinearMap

/-! ### Nondegenerate bilinear forms-/


section Det

open Matrix

variable [CommRing R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable [DecidableEq ι] [Fintype ι]

theorem Matrix.separating_left_to_linear_map₂'_iff_separating_left_to_linear_map₂
    {M : Matrix ι ι R₁} (b : Basis ι R₁ M₁) :
    M.toLinearMap₂'.SeparatingLeft ↔ (Matrix.toLinearMap₂ b b M).SeparatingLeft :=
  (separating_left_congr_iff b.equivFun.symm b.equivFun.symm).symm
#align
  matrix.separating_left_to_linear_map₂'_iff_separating_left_to_linear_map₂ Matrix.separating_left_to_linear_map₂'_iff_separating_left_to_linear_map₂

variable (B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁)

-- Lemmas transferring nondegeneracy between a matrix and its associated bilinear form
theorem Matrix.Nondegenerate.toLinearMap₂' {M : Matrix ι ι R₁} (h : M.Nondegenerate) :
    M.toLinearMap₂'.SeparatingLeft := fun x hx =>
  h.eq_zero_of_ortho fun y => by simpa only [to_linear_map₂'_apply'] using hx y
#align matrix.nondegenerate.to_linear_map₂' Matrix.Nondegenerate.toLinearMap₂'

@[simp]
theorem Matrix.separating_left_to_linear_map₂'_iff {M : Matrix ι ι R₁} :
    M.toLinearMap₂'.SeparatingLeft ↔ M.Nondegenerate :=
  ⟨fun h v hv => h v fun w => (M.to_linear_map₂'_apply' _ _).trans <| hv w,
    Matrix.Nondegenerate.toLinearMap₂'⟩
#align matrix.separating_left_to_linear_map₂'_iff Matrix.separating_left_to_linear_map₂'_iff

theorem Matrix.Nondegenerate.toLinearMap₂ {M : Matrix ι ι R₁} (h : M.Nondegenerate)
    (b : Basis ι R₁ M₁) : (toLinearMap₂ b b M).SeparatingLeft :=
  (Matrix.separating_left_to_linear_map₂'_iff_separating_left_to_linear_map₂ b).mp h.toLinearMap₂'
#align matrix.nondegenerate.to_linear_map₂ Matrix.Nondegenerate.toLinearMap₂

@[simp]
theorem Matrix.separating_left_to_linear_map₂_iff {M : Matrix ι ι R₁} (b : Basis ι R₁ M₁) :
    (toLinearMap₂ b b M).SeparatingLeft ↔ M.Nondegenerate := by
  rw [← Matrix.separating_left_to_linear_map₂'_iff_separating_left_to_linear_map₂,
    Matrix.separating_left_to_linear_map₂'_iff]
#align matrix.separating_left_to_linear_map₂_iff Matrix.separating_left_to_linear_map₂_iff

-- Lemmas transferring nondegeneracy between a bilinear form and its associated matrix
@[simp]
theorem nondegenerate_to_matrix₂'_iff {B : (ι → R₁) →ₗ[R₁] (ι → R₁) →ₗ[R₁] R₁} :
    B.toMatrix₂'.Nondegenerate ↔ B.SeparatingLeft :=
  Matrix.separating_left_to_linear_map₂'_iff.symm.trans <|
    (Matrix.to_linear_map₂'_to_matrix' B).symm ▸ Iff.rfl
#align linear_map.nondegenerate_to_matrix₂'_iff LinearMap.nondegenerate_to_matrix₂'_iff

theorem SeparatingLeft.to_matrix₂' {B : (ι → R₁) →ₗ[R₁] (ι → R₁) →ₗ[R₁] R₁} (h : B.SeparatingLeft) :
    B.toMatrix₂'.Nondegenerate :=
  nondegenerate_to_matrix₂'_iff.mpr h
#align linear_map.separating_left.to_matrix₂' LinearMap.SeparatingLeft.to_matrix₂'

@[simp]
theorem nondegenerate_to_matrix_iff {B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁} (b : Basis ι R₁ M₁) :
    (toMatrix₂ b b B).Nondegenerate ↔ B.SeparatingLeft :=
  (Matrix.separating_left_to_linear_map₂_iff b).symm.trans <|
    (Matrix.to_linear_map₂_to_matrix₂ b b B).symm ▸ Iff.rfl
#align linear_map.nondegenerate_to_matrix_iff LinearMap.nondegenerate_to_matrix_iff

theorem SeparatingLeft.to_matrix₂ {B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁} (h : B.SeparatingLeft)
    (b : Basis ι R₁ M₁) : (toMatrix₂ b b B).Nondegenerate :=
  (nondegenerate_to_matrix_iff b).mpr h
#align linear_map.separating_left.to_matrix₂ LinearMap.SeparatingLeft.to_matrix₂

-- Some shorthands for combining the above with `matrix.nondegenerate_of_det_ne_zero`
variable [IsDomain R₁]

theorem separating_left_to_linear_map₂'_iff_det_ne_zero {M : Matrix ι ι R₁} :
    M.toLinearMap₂'.SeparatingLeft ↔ M.det ≠ 0 := by
  rw [Matrix.separating_left_to_linear_map₂'_iff, Matrix.nondegenerate_iff_det_ne_zero]
#align
  linear_map.separating_left_to_linear_map₂'_iff_det_ne_zero LinearMap.separating_left_to_linear_map₂'_iff_det_ne_zero

theorem separatingLeftToLinearMap₂'OfDetNeZero' (M : Matrix ι ι R₁) (h : M.det ≠ 0) :
    M.toLinearMap₂'.SeparatingLeft :=
  separating_left_to_linear_map₂'_iff_det_ne_zero.mpr h
#align
  linear_map.separating_left_to_linear_map₂'_of_det_ne_zero' LinearMap.separatingLeftToLinearMap₂'OfDetNeZero'

theorem separating_left_iff_det_ne_zero {B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁} (b : Basis ι R₁ M₁) :
    B.SeparatingLeft ↔ (toMatrix₂ b b B).det ≠ 0 := by
  rw [← Matrix.nondegenerate_iff_det_ne_zero, nondegenerate_to_matrix_iff]
#align linear_map.separating_left_iff_det_ne_zero LinearMap.separating_left_iff_det_ne_zero

theorem separatingLeftOfDetNeZero {B : M₁ →ₗ[R₁] M₁ →ₗ[R₁] R₁} (b : Basis ι R₁ M₁)
    (h : (toMatrix₂ b b B).det ≠ 0) : B.SeparatingLeft :=
  (separating_left_iff_det_ne_zero b).mpr h
#align linear_map.separating_left_of_det_ne_zero LinearMap.separatingLeftOfDetNeZero

end Det

end LinearMap

