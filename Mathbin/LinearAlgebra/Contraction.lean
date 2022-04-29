/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Antoine Labelle
-/
import Mathbin.LinearAlgebra.Dual
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.LinearAlgebra.TensorProductBasis
import Mathbin.LinearAlgebra.FreeModule.Finite.Rank

/-!
# Contractions

Given modules $M, N$ over a commutative ring $R$, this file defines the natural linear maps:
$M^* \otimes M \to R$, $M \otimes M^* \to R$, and $M^* \otimes N → Hom(M, N)$, as well as proving
some basic properties of these maps.

## Tags

contraction, dual module, tensor product
-/


section Contraction

open TensorProduct LinearMap Matrix

open TensorProduct BigOperators

variable (R M N : Type _) [AddCommGroupₓ M] [AddCommGroupₓ N]

section CommRingₓ

variable [CommRingₓ R] [Module R M] [Module R N]

variable {ι : Type _} [DecidableEq ι] [Fintype ι] (b : Basis ι R M)

/-- The natural left-handed pairing between a module and its dual. -/
def contractLeft : Module.Dual R M ⊗ M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun LinearMap.id

/-- The natural right-handed pairing between a module and its dual. -/
def contractRight : M ⊗ Module.Dual R M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun (LinearMap.flip LinearMap.id)

/-- The natural map associating a linear map to the tensor product of two modules. -/
def dualTensorHom : Module.Dual R M ⊗ N →ₗ[R] M →ₗ[R] N :=
  let M' := Module.Dual R M
  (uncurry R M' N (M →ₗ[R] N) : _ → M' ⊗ N →ₗ[R] M →ₗ[R] N) LinearMap.smulRightₗ

variable {R M N}

@[simp]
theorem contract_left_apply (f : Module.Dual R M) (m : M) : contractLeft R M (f ⊗ₜ m) = f m := by
  apply uncurry_apply

@[simp]
theorem contract_right_apply (f : Module.Dual R M) (m : M) : contractRight R M (m ⊗ₜ f) = f m := by
  apply uncurry_apply

@[simp]
theorem dual_tensor_hom_apply (f : Module.Dual R M) (m : M) (n : N) : dualTensorHom R M N (f ⊗ₜ n) m = f m • n := by
  dunfold dualTensorHom
  rw [uncurry_apply]
  rfl

/-- As a matrix, `dual_tensor_hom` evaluated on a basis element of `M* ⊗ N` is a matrix with a
single one and zeros elsewhere -/
theorem to_matrix_dual_tensor_hom {m : Type _} {n : Type _} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (bM : Basis m R M) (bN : Basis n R N) (j : m) (i : n) :
    toMatrix bM bN (dualTensorHom R M N (bM.Coord j ⊗ₜ bN i)) = stdBasisMatrix i j 1 := by
  ext i' j'
  by_cases' hij : i = i' ∧ j = j' <;> simp [LinearMap.to_matrix_apply, Finsupp.single_eq_pi_single, hij]
  rw [and_iff_not_or_not, not_not] at hij
  cases hij <;> simp [hij]

attribute [local ext] TensorProduct.ext

/-- If `M` is free, the natural linear map $M^* ⊗ N → Hom(M, N)$ is an equivalence. This function
provides this equivalence in return for a basis of `M`. -/
@[simps]
noncomputable def dualTensorHomEquivOfBasis {ι : Type _} [DecidableEq ι] [Fintype ι] (b : Basis ι R M) :
    Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
  LinearEquiv.ofLinear (dualTensorHom R M N) (∑ i, TensorProduct.mk R _ N (b.dualBasis i) ∘ₗ LinearMap.applyₗ (b i))
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_fn_sum, dual_tensor_hom_apply, mk_apply, id_coe, id.def, Fintype.sum_apply,
        Function.comp_app, Basis.coe_dual_basis, coe_comp, Basis.coord_apply, ← f.map_smul,
        (dualTensorHom R M N).map_sum, ← f.map_sum, b.sum_repr])
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_fn_sum, dual_tensor_hom_apply, mk_apply, id_coe, id.def, Fintype.sum_apply,
        Function.comp_app, Basis.coe_dual_basis, coe_comp, compr₂_apply, tmul_smul, smul_tmul', ← sum_tmul,
        Basis.sum_dual_apply_smul_coord])

@[simp]
theorem dual_tensor_hom_equiv_of_basis_to_linear_map :
    (dualTensorHomEquivOfBasis b : Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N).toLinearMap = dualTensorHom R M N :=
  rfl

variable [Module.Free R M] [Module.Finite R M] [Nontrivial R]

open Classical

/-- If `M` is finite free, the natural map $M^* ⊗ N → Hom(M, N)$ is an
equivalence. -/
@[simp]
noncomputable def dualTensorHomEquiv : Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
  dualTensorHomEquivOfBasis (Module.Free.chooseBasis R M)

end CommRingₓ

end Contraction

