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

open_locale Classical BigOperators

universe u

variable (K : Type u) [Field K]

-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler category
-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler λ α, has_coe_to_sort α (Sort*)
/-- Define `FinVect` as the subtype of `Module.{u} K` of finite dimensional vector spaces. -/
def FinVect :=
  { V : ModuleCat.{u} K // FiniteDimensional K V }deriving [anonymous], [anonymous]

namespace FinVect

instance FiniteDimensional (V : FinVect K) : FiniteDimensional K V :=
  V.prop

instance : Inhabited (FinVect K) :=
  ⟨⟨ModuleCat.of K K, FiniteDimensional.finite_dimensional_self K⟩⟩

instance : Coe (FinVect.{u} K) (ModuleCat.{u} K) :=
  { coe := fun V => V.1 }

protected theorem coe_comp {U V W : FinVect K} (f : U ⟶ V) (g : V ⟶ W) : (f ≫ g : U → W) = (g : V → W) ∘ (f : U → V) :=
  rfl

instance monoidal_category : monoidal_category (FinVect K) :=
  monoidal_category.full_monoidal_subcategory (fun V => FiniteDimensional K V)
    (FiniteDimensional.finite_dimensional_self K)
    fun X Y hX hY =>
      by 
        exact finite_dimensional_tensor_product X Y

variable (V : FinVect K)

/-- The dual module is the dual in the rigid monoidal category `FinVect K`. -/
def FinVect_dual : FinVect K :=
  ⟨ModuleCat.of K (Module.Dual K V), Subspace.Module.Dual.finite_dimensional⟩

instance : CoeFun (FinVect_dual K V) fun _ => V → K :=
  { coe :=
      fun v =>
        by 
          change V →ₗ[K] K at v 
          exact v }

open CategoryTheory.MonoidalCategory

/-- The coevaluation map is defined in `linear_algebra.coevaluation`. -/
def FinVect_coevaluation : 𝟙_ (FinVect K) ⟶ V ⊗ FinVect_dual K V :=
  by 
    apply coevaluation K V

theorem FinVect_coevaluation_apply_one :
  FinVect_coevaluation K V (1 : K) =
    ∑ i : Basis.OfVectorSpaceIndex K V, (Basis.ofVectorSpace K V) i ⊗ₜ[K] (Basis.ofVectorSpace K V).Coord i :=
  by 
    apply coevaluation_apply_one K V

/-- The evaluation morphism is given by the contraction map. -/
def FinVect_evaluation : FinVect_dual K V ⊗ V ⟶ 𝟙_ (FinVect K) :=
  by 
    apply contractLeft K V

@[simp]
theorem FinVect_evaluation_apply (f : FinVect_dual K V) (x : V) : (FinVect_evaluation K V) (f ⊗ₜ x) = f x :=
  by 
    apply contract_left_apply f x

private theorem coevaluation_evaluation :
  let V' : FinVect K := FinVect_dual K V
  𝟙 V' ⊗ FinVect_coevaluation K V ≫ (α_ V' V V').inv ≫ FinVect_evaluation K V ⊗ 𝟙 V' = (ρ_ V').Hom ≫ (λ_ V').inv :=
  by 
    apply contract_left_assoc_coevaluation K V

private theorem evaluation_coevaluation :
  FinVect_coevaluation K V ⊗ 𝟙 V ≫ (α_ V (FinVect_dual K V) V).Hom ≫ 𝟙 V ⊗ FinVect_evaluation K V =
    (λ_ V).Hom ≫ (ρ_ V).inv :=
  by 
    apply contract_left_assoc_coevaluation' K V

instance exact_pairing : exact_pairing V (FinVect_dual K V) :=
  { coevaluation := FinVect_coevaluation K V, evaluation := FinVect_evaluation K V,
    coevaluation_evaluation' := coevaluation_evaluation K V, evaluation_coevaluation' := evaluation_coevaluation K V }

instance right_dual : has_right_dual V :=
  ⟨FinVect_dual K V⟩

instance right_rigid_category : right_rigid_category (FinVect K) :=
  {  }

end FinVect

