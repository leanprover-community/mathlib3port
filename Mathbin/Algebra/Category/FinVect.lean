/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathbin.CategoryTheory.Monoidal.Rigid.Basic
import Mathbin.CategoryTheory.Monoidal.Subcategory
import Mathbin.LinearAlgebra.TensorProductBasis
import Mathbin.LinearAlgebra.Coevaluation
import Mathbin.Algebra.Category.Module.Monoidal

/-!
# The category of finite dimensional vector spaces

This introduces `FinVect K`, the category of finite dimensional vector spaces over a field `K`.
It is implemented as a full subcategory on a subtype of `Module K`, which inherits monoidal and
symmetric structure as `finite_dimensional K` is a monoidal predicate.
We also provide a right rigid monoidal category instance.
-/


noncomputable section

open CategoryTheory ModuleCat.monoidalCategory

open Classical BigOperators

universe u

variable (K : Type u) [Field K]

instance monoidal_predicate_finite_dimensional :
    MonoidalCategory.MonoidalPredicate fun V : ModuleCat.{u} K => FiniteDimensional K V where
  prop_id' := FiniteDimensional.finite_dimensional_self K
  prop_tensor' := fun X Y hX hY => Module.Finite.tensor_product K X Y

instance closed_predicate_finite_dimensional :
    MonoidalCategory.ClosedPredicate fun V : ModuleCat.{u} K =>
      FiniteDimensional K V where prop_ihom' := fun X Y hX hY => @LinearMap.finite_dimensional K _ X _ _ hX Y _ _ hY

/-- Define `FinVect` as the subtype of `Module.{u} K` of finite dimensional vector spaces. -/
def FinVect :=
  FullSubcategory fun V : ModuleCat.{u} K => FiniteDimensional K V deriving LargeCategory, ConcreteCategory,
  MonoidalCategory, SymmetricCategory, MonoidalClosed

namespace FinVect

instance finite_dimensional (V : FinVect K) : FiniteDimensional K V.obj :=
  V.property

instance : Inhabited (FinVect K) :=
  ⟨⟨ModuleCat.of K K, FiniteDimensional.finite_dimensional_self K⟩⟩

/-- Lift an unbundled vector space to `FinVect K`. -/
def of (V : Type u) [AddCommGroupₓ V] [Module K V] [FiniteDimensional K V] : FinVect K :=
  ⟨ModuleCat.of K V, by
    change FiniteDimensional K V
    infer_instance⟩

instance : HasForget₂ (FinVect.{u} K) (ModuleCat.{u} K) := by
  dsimp' [FinVect]
  infer_instance

instance : Full (forget₂ (FinVect K) (ModuleCat.{u} K)) where preimage := fun X Y f => f

variable (V W : FinVect K)

@[simp]
theorem ihom_obj : (ihom V).obj W = FinVect.of K (V.obj →ₗ[K] W.obj) :=
  rfl

/-- The dual module is the dual in the rigid monoidal category `FinVect K`. -/
def finVectDual : FinVect K :=
  ⟨ModuleCat.of K (Module.Dual K V.obj), Subspace.Module.Dual.finite_dimensional⟩

open CategoryTheory.MonoidalCategory

/-- The coevaluation map is defined in `linear_algebra.coevaluation`. -/
def finVectCoevaluation : 𝟙_ (FinVect K) ⟶ V ⊗ finVectDual K V := by
  apply coevaluation K V.obj

theorem FinVect_coevaluation_apply_one :
    finVectCoevaluation K V (1 : K) =
      ∑ i : Basis.OfVectorSpaceIndex K V.obj,
        (Basis.ofVectorSpace K V.obj) i ⊗ₜ[K] (Basis.ofVectorSpace K V.obj).Coord i :=
  by
  apply coevaluation_apply_one K V.obj

/-- The evaluation morphism is given by the contraction map. -/
def finVectEvaluation : finVectDual K V ⊗ V ⟶ 𝟙_ (FinVect K) := by
  apply contractLeft K V.obj

@[simp]
theorem FinVect_evaluation_apply (f : (finVectDual K V).obj) (x : V.obj) :
    (finVectEvaluation K V) (f ⊗ₜ x) = f.toFun x := by
  apply contract_left_apply f x

private theorem coevaluation_evaluation :
    let V' : FinVect K := finVectDual K V
    𝟙 V' ⊗ finVectCoevaluation K V ≫ (α_ V' V V').inv ≫ finVectEvaluation K V ⊗ 𝟙 V' = (ρ_ V').Hom ≫ (λ_ V').inv :=
  by
  apply contract_left_assoc_coevaluation K V.obj

private theorem evaluation_coevaluation :
    finVectCoevaluation K V ⊗ 𝟙 V ≫ (α_ V (finVectDual K V) V).Hom ≫ 𝟙 V ⊗ finVectEvaluation K V =
      (λ_ V).Hom ≫ (ρ_ V).inv :=
  by
  apply contract_left_assoc_coevaluation' K V.obj

instance exactPairing : ExactPairing V (finVectDual K V) where
  coevaluation := finVectCoevaluation K V
  evaluation := finVectEvaluation K V
  coevaluation_evaluation' := coevaluation_evaluation K V
  evaluation_coevaluation' := evaluation_coevaluation K V

instance rightDual : HasRightDual V :=
  ⟨finVectDual K V⟩

instance rightRigidCategory : RightRigidCategory (FinVect K) where

variable {K V}

/-- Converts and isomorphism in the category `FinVect` to a `linear_equiv` between the underlying
vector spaces. -/
def isoToLinearEquiv {V W : FinVect K} (i : V ≅ W) : V.obj ≃ₗ[K] W.obj :=
  ((forget₂ (FinVect.{u} K) (ModuleCat.{u} K)).mapIso i).toLinearEquiv

theorem Iso.conj_eq_conj {V W : FinVect K} (i : V ≅ W) (f : End V) :
    Iso.conj i f = LinearEquiv.conj (isoToLinearEquiv i) f :=
  rfl

end FinVect

variable {K}

/-- Converts a `linear_equiv` to an isomorphism in the category `FinVect`. -/
@[simps]
def LinearEquiv.toFinVectIso {V W : Type u} [AddCommGroupₓ V] [Module K V] [FiniteDimensional K V] [AddCommGroupₓ W]
    [Module K W] [FiniteDimensional K W] (e : V ≃ₗ[K] W) : FinVect.of K V ≅ FinVect.of K W where
  Hom := e.toLinearMap
  inv := e.symm.toLinearMap
  hom_inv_id' := by
    ext
    exact e.left_inv x
  inv_hom_id' := by
    ext
    exact e.right_inv x

