/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathbin.CategoryTheory.Monoidal.Rigid.Basic
import Mathbin.CategoryTheory.Monoidal.Subcategory
import Mathbin.LinearAlgebra.Coevaluation
import Mathbin.Algebra.Category.ModuleCat.Monoidal

/-!
# The category of finite dimensional vector spaces

This introduces `FinVect K`, the category of finite dimensional vector spaces over a field `K`.
It is implemented as a full subcategory on a subtype of `Module K`.

We first create the instance as a `K`-linear category,
then as a `K`-linear monoidal category and then as a right-rigid monoidal category.

## Future work

* Show that `FinVect K` is a symmetric monoidal category (it is already monoidal).
* Show that `FinVect K` is abelian.
* Show that `FinVect K` is rigid (it is already right rigid).

-/


noncomputable section

open CategoryTheory ModuleCat.monoidalCategory

open Classical BigOperators

universe u

variable (K : Type u) [Field K]

instance monoidal_predicate_finite_dimensional :
    MonoidalCategory.MonoidalPredicate fun V : ModuleCat.{u} K => FiniteDimensional K V where
  prop_id' := FiniteDimensional.finiteDimensionalSelf K
  prop_tensor' X Y hX hY := Module.Finite.tensor_product K X Y
#align monoidal_predicate_finite_dimensional monoidal_predicate_finite_dimensional

instance closedPredicateFiniteDimensional :
    MonoidalCategory.ClosedPredicate fun V : ModuleCat.{u} K =>
      FiniteDimensional K V where prop_ihom' X Y hX hY := @LinearMap.finiteDimensional K _ X _ _ hX Y _ _ hY
#align closed_predicate_finite_dimensional closedPredicateFiniteDimensional

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler linear[category_theory.linear] K -/
/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler monoidal_linear[category_theory.monoidal_linear] K -/
/-- Define `FinVect` as the subtype of `Module.{u} K` of finite dimensional vector spaces. -/
def FinVectCat :=
  FullSubcategory fun V : ModuleCat.{u} K => FiniteDimensional K V deriving LargeCategory, ConcreteCategory,
  Preadditive,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler linear[category_theory.linear] K»,
  MonoidalCategory, SymmetricCategory, MonoidalPreadditive,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler monoidal_linear[category_theory.monoidal_linear] K»,
  MonoidalClosed
#align FinVect FinVectCat

namespace FinVectCat

instance finiteDimensional (V : FinVectCat K) : FiniteDimensional K V.obj :=
  V.property
#align FinVect.finite_dimensional FinVectCat.finiteDimensional

instance : Inhabited (FinVectCat K) :=
  ⟨⟨ModuleCat.of K K, FiniteDimensional.finiteDimensionalSelf K⟩⟩

/-- Lift an unbundled vector space to `FinVect K`. -/
def of (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] : FinVectCat K :=
  ⟨ModuleCat.of K V, by
    change FiniteDimensional K V
    infer_instance⟩
#align FinVect.of FinVectCat.of

instance (V W : FinVectCat K) : FiniteDimensional K (V ⟶ W) :=
  (by infer_instance : FiniteDimensional K (V.obj →ₗ[K] W.obj))

instance : HasForget₂ (FinVectCat.{u} K) (ModuleCat.{u} K) := by
  dsimp [FinVectCat]
  infer_instance

instance : Full (forget₂ (FinVectCat K) (ModuleCat.{u} K)) where preimage X Y f := f

/-- The forgetful functor `FinVect K ⥤ Module K` as a monoidal functor. -/
def forget₂Monoidal : MonoidalFunctor (FinVectCat K) (ModuleCat.{u} K) :=
  MonoidalCategory.fullMonoidalSubcategoryInclusion _
#align FinVect.forget₂_monoidal FinVectCat.forget₂Monoidal

instance forget₂_monoidal_faithful : Faithful (forget₂Monoidal K).toFunctor := by
  dsimp [forget₂_monoidal]
  infer_instance
#align FinVect.forget₂_monoidal_faithful FinVectCat.forget₂_monoidal_faithful

instance forget₂_monoidal_additive : (forget₂Monoidal K).toFunctor.Additive := by
  dsimp [forget₂_monoidal]
  infer_instance
#align FinVect.forget₂_monoidal_additive FinVectCat.forget₂_monoidal_additive

instance forget₂_monoidal_linear : (forget₂Monoidal K).toFunctor.Linear K := by
  dsimp [forget₂_monoidal]
  infer_instance
#align FinVect.forget₂_monoidal_linear FinVectCat.forget₂_monoidal_linear

variable (V W : FinVectCat K)

@[simp]
theorem ihom_obj : (ihom V).obj W = FinVectCat.of K (V.obj →ₗ[K] W.obj) :=
  rfl
#align FinVect.ihom_obj FinVectCat.ihom_obj

/-- The dual module is the dual in the rigid monoidal category `FinVect K`. -/
def finVectDual : FinVectCat K :=
  ⟨ModuleCat.of K (Module.Dual K V.obj), Subspace.Module.Dual.finiteDimensional⟩
#align FinVect.FinVect_dual FinVectCat.finVectDual

open CategoryTheory.MonoidalCategory

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The coevaluation map is defined in `linear_algebra.coevaluation`. -/
def finVectCoevaluation : 𝟙_ (FinVectCat K) ⟶ V ⊗ finVectDual K V := by apply coevaluation K V.obj
#align FinVect.FinVect_coevaluation FinVectCat.finVectCoevaluation

theorem FinVect_coevaluation_apply_one :
    finVectCoevaluation K V (1 : K) =
      ∑ i : Basis.ofVectorSpaceIndex K V.obj,
        (Basis.ofVectorSpace K V.obj) i ⊗ₜ[K] (Basis.ofVectorSpace K V.obj).Coord i :=
  by apply coevaluation_apply_one K V.obj
#align FinVect.FinVect_coevaluation_apply_one FinVectCat.FinVect_coevaluation_apply_one

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The evaluation morphism is given by the contraction map. -/
def finVectEvaluation : finVectDual K V ⊗ V ⟶ 𝟙_ (FinVectCat K) := by apply contractLeft K V.obj
#align FinVect.FinVect_evaluation FinVectCat.finVectEvaluation

@[simp]
theorem FinVect_evaluation_apply (f : (finVectDual K V).obj) (x : V.obj) :
    (finVectEvaluation K V) (f ⊗ₜ x) = f.toFun x := by apply contract_left_apply f x
#align FinVect.FinVect_evaluation_apply FinVectCat.FinVect_evaluation_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private theorem coevaluation_evaluation :
    let V' : FinVectCat K := finVectDual K V
    (𝟙 V' ⊗ finVectCoevaluation K V) ≫ (α_ V' V V').inv ≫ (finVectEvaluation K V ⊗ 𝟙 V') = (ρ_ V').Hom ≫ (λ_ V').inv :=
  by apply contract_left_assoc_coevaluation K V.obj
#align FinVect.coevaluation_evaluation FinVect.coevaluation_evaluation

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private theorem evaluation_coevaluation :
    (finVectCoevaluation K V ⊗ 𝟙 V) ≫ (α_ V (finVectDual K V) V).Hom ≫ (𝟙 V ⊗ finVectEvaluation K V) =
      (λ_ V).Hom ≫ (ρ_ V).inv :=
  by apply contract_left_assoc_coevaluation' K V.obj
#align FinVect.evaluation_coevaluation FinVect.evaluation_coevaluation

instance exactPairing : ExactPairing V (finVectDual K V) where
  coevaluation := finVectCoevaluation K V
  evaluation := finVectEvaluation K V
  coevaluation_evaluation' := coevaluation_evaluation K V
  evaluation_coevaluation' := evaluation_coevaluation K V
#align FinVect.exact_pairing FinVectCat.exactPairing

instance rightDual : HasRightDual V :=
  ⟨finVectDual K V⟩
#align FinVect.right_dual FinVectCat.rightDual

instance rightRigidCategory : RightRigidCategory (FinVectCat K) where
#align FinVect.right_rigid_category FinVectCat.rightRigidCategory

variable {K V}

/-- Converts and isomorphism in the category `FinVect` to a `linear_equiv` between the underlying
vector spaces. -/
def isoToLinearEquiv {V W : FinVectCat K} (i : V ≅ W) : V.obj ≃ₗ[K] W.obj :=
  ((forget₂ (FinVectCat.{u} K) (ModuleCat.{u} K)).mapIso i).toLinearEquiv
#align FinVect.iso_to_linear_equiv FinVectCat.isoToLinearEquiv

theorem Iso.conj_eq_conj {V W : FinVectCat K} (i : V ≅ W) (f : EndCat V) :
    Iso.conj i f = LinearEquiv.conj (isoToLinearEquiv i) f :=
  rfl
#align FinVect.iso.conj_eq_conj FinVectCat.Iso.conj_eq_conj

end FinVectCat

variable {K}

/-- Converts a `linear_equiv` to an isomorphism in the category `FinVect`. -/
@[simps]
def LinearEquiv.toFinVectIso {V W : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (e : V ≃ₗ[K] W) : FinVectCat.of K V ≅ FinVectCat.of K W where
  Hom := e.toLinearMap
  inv := e.symm.toLinearMap
  hom_inv_id' := by
    ext
    exact e.left_inv x
  inv_hom_id' := by
    ext
    exact e.right_inv x
#align linear_equiv.to_FinVect_iso LinearEquiv.toFinVectIso

