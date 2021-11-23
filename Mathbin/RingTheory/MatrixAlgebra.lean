import Mathbin.Data.Matrix.Basis 
import Mathbin.RingTheory.TensorProduct

/-!
We show `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)`.
-/


universe u v w

open_locale TensorProduct

open_locale BigOperators

open TensorProduct

open Algebra.TensorProduct

open Matrix

variable{R : Type u}[CommSemiringₓ R]

variable{A : Type v}[Semiringₓ A][Algebra R A]

variable{n : Type w}

variable(R A n)

namespace matrixEquivTensor

/--
(Implementation detail).
The bare function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`, on pure tensors.
-/
def to_fun (a : A) (m : Matrix n n R) : Matrix n n A :=
  fun i j => a*algebraMap R A (m i j)

/--
(Implementation detail).
The function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`,
as an `R`-linear map in the second tensor factor.
-/
def to_fun_right_linear (a : A) : Matrix n n R →ₗ[R] Matrix n n A :=
  { toFun := to_fun R A n a,
    map_add' :=
      fun x y =>
        by 
          dsimp only [to_fun]
          ext 
          simp [mul_addₓ],
    map_smul' :=
      fun r x =>
        by 
          dsimp only [to_fun]
          ext 
          simp only [Pi.smul_apply, RingHom.map_mul, Algebra.id.smul_eq_mul]
          dsimp 
          rw [Algebra.smul_def r, ←_root_.mul_assoc, ←_root_.mul_assoc, Algebra.commutes] }

/--
(Implementation detail).
The function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`,
as an `R`-bilinear map.
-/
def to_fun_bilinear : A →ₗ[R] Matrix n n R →ₗ[R] Matrix n n A :=
  { toFun := to_fun_right_linear R A n,
    map_add' :=
      fun x y =>
        by 
          ext 
          simp [to_fun_right_linear, to_fun, add_mulₓ],
    map_smul' :=
      fun r x =>
        by 
          ext 
          simp [to_fun_right_linear, to_fun] }

/--
(Implementation detail).
The function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`,
as an `R`-linear map.
-/
def to_fun_linear : A ⊗[R] Matrix n n R →ₗ[R] Matrix n n A :=
  TensorProduct.lift (to_fun_bilinear R A n)

variable[DecidableEq n][Fintype n]

/--
The function `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`, as an algebra homomorphism.
-/
def to_fun_alg_hom : A ⊗[R] Matrix n n R →ₐ[R] Matrix n n A :=
  alg_hom_of_linear_map_tensor_product (to_fun_linear R A n)
    (by 
      intros 
      ext 
      simpRw [to_fun_linear, to_fun_bilinear, lift.tmul]
      dsimp 
      simpRw [to_fun_right_linear]
      dsimp 
      simpRw [to_fun, Matrix.mul_mul_left, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, ←_root_.mul_assoc _ a₂ _,
        Algebra.commutes, _root_.mul_assoc a₂ _ _, ←Finset.mul_sum, RingHom.map_sum, RingHom.map_mul, _root_.mul_assoc])
    (by 
      intros 
      ext 
      simp only [to_fun_linear, to_fun_bilinear, to_fun_right_linear, to_fun, Matrix.one_apply,
        algebra_map_matrix_apply, lift.tmul, LinearMap.coe_mk]
      splitIfs <;> simp )

@[simp]
theorem to_fun_alg_hom_apply (a : A) (m : Matrix n n R) :
  to_fun_alg_hom R A n (a ⊗ₜ m) = fun i j => a*algebraMap R A (m i j) :=
  by 
    simp [to_fun_alg_hom, alg_hom_of_linear_map_tensor_product, to_fun_linear]
    rfl

/--
(Implementation detail.)

The bare function `matrix n n A → A ⊗[R] matrix n n R`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
def inv_fun (M : Matrix n n A) : A ⊗[R] Matrix n n R :=
  ∑p : n × n, M p.1 p.2 ⊗ₜ std_basis_matrix p.1 p.2 1

@[simp]
theorem inv_fun_zero : inv_fun R A n 0 = 0 :=
  by 
    simp [inv_fun]

@[simp]
theorem inv_fun_add (M N : Matrix n n A) : inv_fun R A n (M+N) = inv_fun R A n M+inv_fun R A n N :=
  by 
    simp [inv_fun, add_tmul, Finset.sum_add_distrib]

@[simp]
theorem inv_fun_smul (a : A) (M : Matrix n n A) : (inv_fun R A n fun i j => a*M i j) = (a ⊗ₜ 1)*inv_fun R A n M :=
  by 
    simp [inv_fun, Finset.mul_sum]

@[simp]
theorem inv_fun_algebra_map (M : Matrix n n R) : (inv_fun R A n fun i j => algebraMap R A (M i j)) = 1 ⊗ₜ M :=
  by 
    dsimp [inv_fun]
    simp only [Algebra.algebra_map_eq_smul_one, smul_tmul, ←tmul_sum, mul_boole]
    congr 
    convRHS => rw [matrix_eq_sum_std_basis M]
    convert Finset.sum_product 
    simp 

theorem right_inv (M : Matrix n n A) : (to_fun_alg_hom R A n) (inv_fun R A n M) = M :=
  by 
    simp only [inv_fun, AlgHom.map_sum, std_basis_matrix, apply_ite («expr⇑ » (algebraMap R A)), mul_boole,
      to_fun_alg_hom_apply, RingHom.map_zero, RingHom.map_one]
    convert Finset.sum_product 
    apply matrix_eq_sum_std_basis

theorem left_inv (M : A ⊗[R] Matrix n n R) : inv_fun R A n (to_fun_alg_hom R A n M) = M :=
  by 
    apply TensorProduct.induction_on M
    ·
      simp 
    ·
      intro a m 
      simp 
    ·
      intro x y hx hy 
      simp [AlgHom.map_sum, hx, hy]

/--
(Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] matrix n n R) ≃ matrix n n A`.
-/
def Equiv : A ⊗[R] Matrix n n R ≃ Matrix n n A :=
  { toFun := to_fun_alg_hom R A n, invFun := inv_fun R A n, left_inv := left_inv R A n, right_inv := right_inv R A n }

end matrixEquivTensor

variable[Fintype n][DecidableEq n]

/--
The `R`-algebra isomorphism `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)`.
-/
def matrixEquivTensor : Matrix n n A ≃ₐ[R] A ⊗[R] Matrix n n R :=
  AlgEquiv.symm { MatrixEquivTensor.toFunAlgHom R A n, MatrixEquivTensor.equiv R A n with  }

open matrixEquivTensor

@[simp]
theorem matrix_equiv_tensor_apply (M : Matrix n n A) :
  matrixEquivTensor R A n M = ∑p : n × n, M p.1 p.2 ⊗ₜ std_basis_matrix p.1 p.2 1 :=
  rfl

-- error in RingTheory.MatrixAlgebra: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem matrix_equiv_tensor_apply_std_basis
(i j : n)
(x : A) : «expr = »(matrix_equiv_tensor R A n (std_basis_matrix i j x), «expr ⊗ₜ »(x, std_basis_matrix i j 1)) :=
begin
  have [ident t] [":", expr ∀
   p : «expr × »(n, n), «expr ↔ »(«expr ∧ »(«expr = »(i, p.1), «expr = »(j, p.2)), «expr = »(p, (i, j)))] [":=", expr by tidy []],
  simp [] [] [] ["[", expr ite_tmul, ",", expr t, ",", expr std_basis_matrix, "]"] [] []
end

@[simp]
theorem matrix_equiv_tensor_apply_symm (a : A) (M : Matrix n n R) :
  (matrixEquivTensor R A n).symm (a ⊗ₜ M) = fun i j => a*algebraMap R A (M i j) :=
  by 
    simp [matrixEquivTensor, to_fun_alg_hom, alg_hom_of_linear_map_tensor_product, to_fun_linear]
    rfl

