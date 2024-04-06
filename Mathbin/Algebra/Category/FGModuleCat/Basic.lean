/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import CategoryTheory.Monoidal.Rigid.Basic
import CategoryTheory.Monoidal.Subcategory
import LinearAlgebra.Coevaluation
import LinearAlgebra.FreeModule.Finite.Matrix
import Algebra.Category.ModuleCat.Monoidal.Closed

#align_import algebra.category.fgModule.basic from "leanprover-community/mathlib"@"08b63ab58a6ec1157ebeafcbbe6c7a3fb3c9f6d5"

/-!
# The category of finitely generated modules over a ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This introduces `fgModule R`, the category of finitely generated modules over a ring `R`.
It is implemented as a full subcategory on a subtype of `Module R`.

When `K` is a field, `fgModule K` is the category of finite dimensional vector spaces over `K`.

We first create the instance as a preadditive category.
When `R` is commutative we then give the structure as an `R`-linear monoidal category.
When `R` is a field we give it the structure of a closed monoidal category
and then as a right-rigid monoidal category.

## Future work

* Show that `fgModule R` is abelian when `R` is (left)-noetherian.

-/


noncomputable section

open CategoryTheory ModuleCat.monoidalCategory

open scoped Classical BigOperators

universe u

section Ring

variable (R : Type u) [Ring R]

#print FGModuleCat /-
/-- Define `fgModule` as the subtype of `Module.{u} R` of finitely generated modules. -/
def FGModuleCat :=
  FullSubcategory fun V : ModuleCat.{u} R => Module.Finite R V
deriving LargeCategory, ConcreteCategory, Preadditive
#align fgModule FGModuleCat
-/

end Ring

namespace FGModuleCat

section Ring

variable (R : Type u) [Ring R]

#print FGModuleCat.finite /-
instance finite (V : FGModuleCat R) : Module.Finite R V.obj :=
  V.property
#align fgModule.finite FGModuleCat.finite
-/

instance : Inhabited (FGModuleCat R) :=
  ⟨⟨ModuleCat.of R R, Module.Finite.self R⟩⟩

#print FGModuleCat.of /-
/-- Lift an unbundled finitely generated module to `fgModule R`. -/
def of (V : Type u) [AddCommGroup V] [Module R V] [Module.Finite R V] : FGModuleCat R :=
  ⟨ModuleCat.of R V, by change Module.Finite R V; infer_instance⟩
#align fgModule.of FGModuleCat.of
-/

instance (V : FGModuleCat R) : Module.Finite R V.obj :=
  V.property

instance : HasForget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) := by dsimp [FGModuleCat];
  infer_instance

instance : Full (forget₂ (FGModuleCat R) (ModuleCat.{u} R)) where preimage X Y f := f

variable {R}

#print FGModuleCat.isoToLinearEquiv /-
/-- Converts and isomorphism in the category `fgModule R` to a `linear_equiv` between the underlying
modules. -/
def isoToLinearEquiv {V W : FGModuleCat R} (i : V ≅ W) : V.obj ≃ₗ[R] W.obj :=
  ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).mapIso i).toLinearEquiv
#align fgModule.iso_to_linear_equiv FGModuleCat.isoToLinearEquiv
-/

#print LinearEquiv.toFGModuleCatIso /-
/-- Converts a `linear_equiv` to an isomorphism in the category `fgModule R`. -/
@[simps]
def LinearEquiv.toFGModuleCatIso {V W : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] (e : V ≃ₗ[R] W) :
    FGModuleCat.of R V ≅ FGModuleCat.of R W
    where
  Hom := e.toLinearMap
  inv := e.symm.toLinearMap
  hom_inv_id' := by ext; exact e.left_inv x
  inv_hom_id' := by ext; exact e.right_inv x
#align linear_equiv.to_fgModule_iso LinearEquiv.toFGModuleCatIso
-/

end Ring

section CommRing

variable (R : Type u) [CommRing R]

instance : Linear R (FGModuleCat R) := by dsimp_result => dsimp [FGModuleCat]; infer_instance

#print FGModuleCat.monoidalPredicate_module_finite /-
instance monoidalPredicate_module_finite :
    MonoidalCategory.MonoidalPredicate fun V : ModuleCat.{u} R => Module.Finite R V
    where
  prop_id' := Module.Finite.self R
  prop_tensor' X Y hX hY := Module.Finite.tensorProduct R X Y
#align fgModule.monoidal_predicate_module_finite FGModuleCat.monoidalPredicate_module_finite
-/

instance : MonoidalCategory (FGModuleCat R) := by
  dsimp_result => dsimp [FGModuleCat]; infer_instance

instance : SymmetricCategory (FGModuleCat R) := by
  dsimp_result => dsimp [FGModuleCat]; infer_instance

instance : MonoidalPreadditive (FGModuleCat R) := by
  dsimp_result => dsimp [FGModuleCat]; infer_instance

instance : MonoidalLinear R (FGModuleCat R) := by
  dsimp_result => dsimp [FGModuleCat]; infer_instance

#print FGModuleCat.forget₂Monoidal /-
/-- The forgetful functor `fgModule R ⥤ Module R` as a monoidal functor. -/
def forget₂Monoidal : MonoidalFunctor (FGModuleCat R) (ModuleCat.{u} R) :=
  MonoidalCategory.fullMonoidalSubcategoryInclusion _
#align fgModule.forget₂_monoidal FGModuleCat.forget₂Monoidal
-/

#print FGModuleCat.forget₂Monoidal_faithful /-
instance forget₂Monoidal_faithful : Faithful (forget₂Monoidal R).toFunctor := by
  dsimp [forget₂_monoidal]; infer_instance
#align fgModule.forget₂_monoidal_faithful FGModuleCat.forget₂Monoidal_faithful
-/

#print FGModuleCat.forget₂Monoidal_additive /-
instance forget₂Monoidal_additive : (forget₂Monoidal R).toFunctor.Additive := by
  dsimp [forget₂_monoidal]; infer_instance
#align fgModule.forget₂_monoidal_additive FGModuleCat.forget₂Monoidal_additive
-/

#print FGModuleCat.forget₂Monoidal_linear /-
instance forget₂Monoidal_linear : (forget₂Monoidal R).toFunctor.Linear R := by
  dsimp [forget₂_monoidal]; infer_instance
#align fgModule.forget₂_monoidal_linear FGModuleCat.forget₂Monoidal_linear
-/

#print FGModuleCat.Iso.conj_eq_conj /-
theorem Iso.conj_eq_conj {V W : FGModuleCat R} (i : V ≅ W) (f : End V) :
    Iso.conj i f = LinearEquiv.conj (isoToLinearEquiv i) f :=
  rfl
#align fgModule.iso.conj_eq_conj FGModuleCat.Iso.conj_eq_conj
-/

end CommRing

section Field

variable (K : Type u) [Field K]

instance (V W : FGModuleCat K) : Module.Finite K (V ⟶ W) :=
  (by infer_instance : Module.Finite K (V.obj →ₗ[K] W.obj))

#print FGModuleCat.closedPredicateModuleFinite /-
instance closedPredicateModuleFinite :
    MonoidalCategory.ClosedPredicate fun V : ModuleCat.{u} K => Module.Finite K V
    where prop_ihom' X Y hX hY := @Module.Finite.linearMap K X Y _ _ _ _ _ _ _ hX hY
#align fgModule.closed_predicate_module_finite FGModuleCat.closedPredicateModuleFinite
-/

instance : MonoidalClosed (FGModuleCat K) := by dsimp_result => dsimp [FGModuleCat]; infer_instance

variable (V W : FGModuleCat K)

#print FGModuleCat.ihom_obj /-
@[simp]
theorem ihom_obj : (ihom V).obj W = FGModuleCat.of K (V.obj →ₗ[K] W.obj) :=
  rfl
#align fgModule.ihom_obj FGModuleCat.ihom_obj
-/

#print FGModuleCat.FGModuleCatDual /-
/-- The dual module is the dual in the rigid monoidal category `fgModule K`. -/
def FGModuleCatDual : FGModuleCat K :=
  ⟨ModuleCat.of K (Module.Dual K V.obj), Subspace.instModuleDualFiniteDimensional⟩
#align fgModule.fgModule_dual FGModuleCat.FGModuleCatDual
-/

open CategoryTheory.MonoidalCategory

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FGModuleCat.FGModuleCatCoevaluation /-
/-- The coevaluation map is defined in `linear_algebra.coevaluation`. -/
def FGModuleCatCoevaluation : 𝟙_ (FGModuleCat K) ⟶ V ⊗ FGModuleCatDual K V := by
  apply coevaluation K V.obj
#align fgModule.fgModule_coevaluation FGModuleCat.FGModuleCatCoevaluation
-/

#print FGModuleCat.FGModuleCatCoevaluation_apply_one /-
theorem FGModuleCatCoevaluation_apply_one :
    FGModuleCatCoevaluation K V (1 : K) =
      ∑ i : Basis.ofVectorSpaceIndex K V.obj,
        (Basis.ofVectorSpace K V.obj) i ⊗ₜ[K] (Basis.ofVectorSpace K V.obj).Coord i :=
  by apply coevaluation_apply_one K V.obj
#align fgModule.fgModule_coevaluation_apply_one FGModuleCat.FGModuleCatCoevaluation_apply_one
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FGModuleCat.FGModuleCatEvaluation /-
/-- The evaluation morphism is given by the contraction map. -/
def FGModuleCatEvaluation : FGModuleCatDual K V ⊗ V ⟶ 𝟙_ (FGModuleCat K) := by
  apply contractLeft K V.obj
#align fgModule.fgModule_evaluation FGModuleCat.FGModuleCatEvaluation
-/

#print FGModuleCat.FGModuleCatEvaluation_apply /-
@[simp]
theorem FGModuleCatEvaluation_apply (f : (FGModuleCatDual K V).obj) (x : V.obj) :
    (FGModuleCatEvaluation K V) (f ⊗ₜ x) = f.toFun x := by apply contractLeft_apply f x
#align fgModule.fgModule_evaluation_apply FGModuleCat.FGModuleCatEvaluation_apply
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private theorem coevaluation_evaluation :
    let V' : FGModuleCat K := FGModuleCatDual K V
    (𝟙 V' ⊗ FGModuleCatCoevaluation K V) ≫ (α_ V' V V').inv ≫ (FGModuleCatEvaluation K V ⊗ 𝟙 V') =
      (ρ_ V').Hom ≫ (λ_ V').inv :=
  by apply contractLeft_assoc_coevaluation K V.obj

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private theorem evaluation_coevaluation :
    (FGModuleCatCoevaluation K V ⊗ 𝟙 V) ≫
        (α_ V (FGModuleCatDual K V) V).Hom ≫ (𝟙 V ⊗ FGModuleCatEvaluation K V) =
      (λ_ V).Hom ≫ (ρ_ V).inv :=
  by apply contractLeft_assoc_coevaluation' K V.obj

#print FGModuleCat.exactPairing /-
instance exactPairing : ExactPairing V (FGModuleCatDual K V)
    where
  coevaluation := FGModuleCatCoevaluation K V
  evaluation := FGModuleCatEvaluation K V
  coevaluation_evaluation' := coevaluation_evaluation K V
  evaluation_coevaluation' := evaluation_coevaluation K V
#align fgModule.exact_pairing FGModuleCat.exactPairing
-/

#print FGModuleCat.rightDual /-
instance rightDual : HasRightDual V :=
  ⟨FGModuleCatDual K V⟩
#align fgModule.right_dual FGModuleCat.rightDual
-/

#print FGModuleCat.rightRigidCategory /-
instance rightRigidCategory : RightRigidCategory (FGModuleCat K) where
#align fgModule.right_rigid_category FGModuleCat.rightRigidCategory
-/

end Field

end FGModuleCat

