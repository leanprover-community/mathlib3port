/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathbin.CategoryTheory.Monoidal.Rigid
import Mathbin.LinearAlgebra.TensorProductBasis
import Mathbin.LinearAlgebra.Coevaluation
import Mathbin.Algebra.Category.Module.Monoidal

/-!
# The category of finite dimensional vector spaces

This introduces `FinVect K`, the category of finite dimensional vector spaces on a field `K`.
It is implemented as a full subcategory on a subtype of  `Module K`.
We first create the instance as a category, then as a monoidal category and then as a rigid monoidal
category.

## Future work

* Show that `FinVect K` is a symmetric monoidal category.

-/


noncomputable section

open CategoryTheory ModuleCat.monoidalCategory

open Classical BigOperators

universe u

variable (K : Type u) [Field K]

-- ././Mathport/Syntax/Translate/Basic.lean:979:9: unsupported derive handler λ α, has_coe_to_sort α (Sort*)
/-- Define `FinVect` as the subtype of `Module.{u} K` of finite dimensional vector spaces. -/
def FinVect :=
  { V : ModuleCat.{u} K // FiniteDimensional K V }deriving Category, [anonymous]

namespace FinVect

instance finite_dimensional (V : FinVect K) : FiniteDimensional K V :=
  V.Prop

instance : Inhabited (FinVect K) :=
  ⟨⟨ModuleCat.of K K, FiniteDimensional.finite_dimensional_self K⟩⟩

instance : Coe (FinVect.{u} K) (ModuleCat.{u} K) where
  coe := fun V => V.1

protected theorem coe_comp {U V W : FinVect K} (f : U ⟶ V) (g : V ⟶ W) : (f ≫ g : U → W) = (g : V → W) ∘ (f : U → V) :=
  rfl

instance monoidalCategory : MonoidalCategory (FinVect K) :=
  MonoidalCategory.fullMonoidalSubcategory (fun V => FiniteDimensional K V)
    (FiniteDimensional.finite_dimensional_self K) fun X Y hX hY => finite_dimensional_tensor_product X Y

variable (V : FinVect K)

/-- The dual module is the dual in the rigid monoidal category `FinVect K`. -/
def finVectDual : FinVect K :=
  ⟨ModuleCat.of K (Module.Dual K V), Subspace.Module.Dual.finite_dimensional⟩

instance : CoeFun (finVectDual K V) fun _ => V → K where
  coe := fun v => by
    change V →ₗ[K] K at v
    exact v

open CategoryTheory.MonoidalCategory

/-- The coevaluation map is defined in `linear_algebra.coevaluation`. -/
def finVectCoevaluation : 𝟙_ (FinVect K) ⟶ V ⊗ finVectDual K V := by
  apply coevaluation K V

theorem FinVect_coevaluation_apply_one :
    finVectCoevaluation K V (1 : K) =
      ∑ i : Basis.OfVectorSpaceIndex K V, (Basis.ofVectorSpace K V) i ⊗ₜ[K] (Basis.ofVectorSpace K V).Coord i :=
  by
  apply coevaluation_apply_one K V

/-- The evaluation morphism is given by the contraction map. -/
def finVectEvaluation : finVectDual K V ⊗ V ⟶ 𝟙_ (FinVect K) := by
  apply contractLeft K V

@[simp]
theorem FinVect_evaluation_apply (f : finVectDual K V) (x : V) : (finVectEvaluation K V) (f ⊗ₜ x) = f x := by
  apply contract_left_apply f x

private theorem coevaluation_evaluation :
    let V' : FinVect K := finVectDual K V
    𝟙 V' ⊗ finVectCoevaluation K V ≫ (α_ V' V V').inv ≫ finVectEvaluation K V ⊗ 𝟙 V' = (ρ_ V').Hom ≫ (λ_ V').inv :=
  by
  apply contract_left_assoc_coevaluation K V

private theorem evaluation_coevaluation :
    finVectCoevaluation K V ⊗ 𝟙 V ≫ (α_ V (finVectDual K V) V).Hom ≫ 𝟙 V ⊗ finVectEvaluation K V =
      (λ_ V).Hom ≫ (ρ_ V).inv :=
  by
  apply contract_left_assoc_coevaluation' K V

instance exactPairing : ExactPairing V (finVectDual K V) where
  coevaluation := finVectCoevaluation K V
  evaluation := finVectEvaluation K V
  coevaluation_evaluation' := coevaluation_evaluation K V
  evaluation_coevaluation' := evaluation_coevaluation K V

instance rightDual : HasRightDual V :=
  ⟨finVectDual K V⟩

instance rightRigidCategory : RightRigidCategory (FinVect K) :=
  {  }

end FinVect

