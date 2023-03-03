/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.yoneda
! leanprover-community/mathlib commit e83fa8324dbec147a1d1f6d11751361235ce3806
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.FunctorCategory
import Mathbin.Tactic.AssertExists

/-!
# Limit properties relating to the (co)yoneda embedding.

We calculate the colimit of `Y ↦ (X ⟶ Y)`, which is just `punit`.
(This is used in characterising cofinal functors.)

We also show the (co)yoneda embeddings preserve limits and jointly reflect them.
-/


open Opposite

open CategoryTheory

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

namespace Coyoneda

variable {C : Type v} [SmallCategory C]

/- warning: category_theory.coyoneda.colimit_cocone -> CategoryTheory.Coyoneda.colimitCocone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} C] (X : Opposite.{succ u1} C), CategoryTheory.Limits.Cocone.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.obj.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_1) (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u1} C _inst_1) X)
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} C] (X : Opposite.{succ u1} C), CategoryTheory.Limits.Cocone.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} (Prefunctor.obj.{succ u1, succ u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (Opposite.{succ u1} C) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_1) (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u1} C _inst_1)) X)
Case conversion may be inaccurate. Consider using '#align category_theory.coyoneda.colimit_cocone CategoryTheory.Coyoneda.colimitCoconeₓ'. -/
/-- The colimit cocone over `coyoneda.obj X`, with cocone point `punit`.
-/
@[simps]
def colimitCocone (X : Cᵒᵖ) : Cocone (coyoneda.obj X)
    where
  pt := PUnit
  ι := { app := by tidy }
#align category_theory.coyoneda.colimit_cocone CategoryTheory.Coyoneda.colimitCocone

/- warning: category_theory.coyoneda.colimit_cocone_is_colimit -> CategoryTheory.Coyoneda.colimitCoconeIsColimit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} C] (X : Opposite.{succ u1} C), CategoryTheory.Limits.IsColimit.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.obj.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_1) (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u1} C _inst_1) X) (CategoryTheory.Coyoneda.colimitCocone.{u1} C _inst_1 X)
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} C] (X : Opposite.{succ u1} C), CategoryTheory.Limits.IsColimit.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} (Prefunctor.obj.{succ u1, succ u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (Opposite.{succ u1} C) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_1) (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u1} C _inst_1)) X) (CategoryTheory.Coyoneda.colimitCocone.{u1} C _inst_1 X)
Case conversion may be inaccurate. Consider using '#align category_theory.coyoneda.colimit_cocone_is_colimit CategoryTheory.Coyoneda.colimitCoconeIsColimitₓ'. -/
/-- The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
@[simps]
def colimitCoconeIsColimit (X : Cᵒᵖ) : IsColimit (colimitCocone X)
    where
  desc s x := s.ι.app (unop X) (𝟙 _)
  fac s Y := by
    ext f
    convert congr_fun (s.w f).symm (𝟙 (unop X))
    simp
  uniq s m w := by
    ext ⟨⟩
    rw [← w]
    simp
#align category_theory.coyoneda.colimit_cocone_is_colimit CategoryTheory.Coyoneda.colimitCoconeIsColimit

instance (X : Cᵒᵖ) : HasColimit (coyoneda.obj X) :=
  HasColimit.mk
    { Cocone := _
      IsColimit := colimitCoconeIsColimit X }

/- warning: category_theory.coyoneda.colimit_coyoneda_iso -> CategoryTheory.Coyoneda.colimitCoyonedaIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} C] (X : Opposite.{succ u1} C), CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Limits.colimit.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.obj.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_1) (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u1} C _inst_1) X) (CategoryTheory.coyoneda.Obj.CategoryTheory.Limits.hasColimit.{u1} C _inst_1 X)) PUnit.{succ u1}
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} C] (X : Opposite.{succ u1} C), CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Limits.colimit.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} (Prefunctor.obj.{succ u1, succ u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (Opposite.{succ u1} C) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_1) (CategoryTheory.Functor.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u1} C _inst_1)) X) (CategoryTheory.Coyoneda.instHasColimitTypeTypesObjOppositeToQuiverToCategoryStructOppositeFunctorToQuiverToCategoryStructCategoryToPrefunctorCoyoneda.{u1} C _inst_1 X)) PUnit.{succ u1}
Case conversion may be inaccurate. Consider using '#align category_theory.coyoneda.colimit_coyoneda_iso CategoryTheory.Coyoneda.colimitCoyonedaIsoₓ'. -/
/-- The colimit of `coyoneda.obj X` is isomorphic to `punit`.
-/
noncomputable def colimitCoyonedaIso (X : Cᵒᵖ) : colimit (coyoneda.obj X) ≅ PUnit :=
  colimit.isoColimitCocone
    { Cocone := _
      IsColimit := colimitCoconeIsColimit X }
#align category_theory.coyoneda.colimit_coyoneda_iso CategoryTheory.Coyoneda.colimitCoyonedaIso

end Coyoneda

variable {C : Type u} [Category.{v} C]

open Limits

/- warning: category_theory.yoneda_preserves_limits -> CategoryTheory.yonedaPreservesLimits is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : C), CategoryTheory.Limits.PreservesLimits.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : C), CategoryTheory.Limits.PreservesLimits.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) X)
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda_preserves_limits CategoryTheory.yonedaPreservesLimitsₓ'. -/
/-- The yoneda embedding `yoneda.obj X : Cᵒᵖ ⥤ Type v` for `X : C` preserves limits. -/
instance yonedaPreservesLimits (X : C) : PreservesLimits (yoneda.obj X)
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun K =>
        {
          preserves := fun c t =>
            { lift := fun s x =>
                Quiver.Hom.unop (t.lift ⟨op X, fun j => (s.π.app j x).op, fun j₁ j₂ α => _⟩)
              fac := fun s j => funext fun x => Quiver.Hom.op_inj (t.fac _ _)
              uniq := fun s m w =>
                funext fun x =>
                  by
                  refine' Quiver.Hom.op_inj (t.uniq ⟨op X, _, _⟩ _ fun j => _)
                  · dsimp
                    simp [← s.w α]
                  -- See library note [dsimp, simp]
                  · exact Quiver.Hom.unop_inj (congr_fun (w j) x) } } }
#align category_theory.yoneda_preserves_limits CategoryTheory.yonedaPreservesLimits

/- warning: category_theory.coyoneda_preserves_limits -> CategoryTheory.coyonedaPreservesLimits is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : Opposite.{succ u2} C), CategoryTheory.Limits.PreservesLimits.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1) X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : Opposite.{succ u2} C), CategoryTheory.Limits.PreservesLimits.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1)) X)
Case conversion may be inaccurate. Consider using '#align category_theory.coyoneda_preserves_limits CategoryTheory.coyonedaPreservesLimitsₓ'. -/
/-- The coyoneda embedding `coyoneda.obj X : C ⥤ Type v` for `X : Cᵒᵖ` preserves limits. -/
instance coyonedaPreservesLimits (X : Cᵒᵖ) : PreservesLimits (coyoneda.obj X)
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun K =>
        {
          preserves := fun c t =>
            { lift := fun s x =>
                t.lift
                  ⟨unop X, fun j => s.π.app j x, fun j₁ j₂ α =>
                    by
                    dsimp
                    simp [← s.w α]⟩
              -- See library note [dsimp, simp]
              fac := fun s j => funext fun x => t.fac _ _
              uniq := fun s m w =>
                funext fun x => by
                  refine' t.uniq ⟨unop X, _⟩ _ fun j => _
                  exact congr_fun (w j) x } } }
#align category_theory.coyoneda_preserves_limits CategoryTheory.coyonedaPreservesLimits

/- warning: category_theory.yoneda_jointly_reflects_limits -> CategoryTheory.yonedaJointlyReflectsLimits is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (J : Type.{u1}) [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (K : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1)) (c : CategoryTheory.Limits.Cone.{u1, u2, u1, u3} J _inst_2 (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) K), (forall (X : C), CategoryTheory.Limits.IsLimit.{u1, u2, u1, succ u2} J _inst_2 Type.{u2} CategoryTheory.types.{u2} (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, succ u2} J _inst_2 (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2} K (CategoryTheory.Functor.obj.{u2, max u3 u2, u3, max u2 u3 (succ u2)} C _inst_1 (CategoryTheory.Functor.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.yoneda.{u2, u3} C _inst_1) X)) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, succ u2} J _inst_2 (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2} K (CategoryTheory.Functor.obj.{u2, max u3 u2, u3, max u2 u3 (succ u2)} C _inst_1 (CategoryTheory.Functor.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.yoneda.{u2, u3} C _inst_1) X) c)) -> (CategoryTheory.Limits.IsLimit.{u1, u2, u1, u3} J _inst_2 (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) K c)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (J : Type.{u1}) [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (K : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1)) (c : CategoryTheory.Limits.Cone.{u1, u2, u1, u3} J _inst_2 (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) K), (forall (X : C), CategoryTheory.Limits.IsLimit.{u1, u2, u1, succ u2} J _inst_2 Type.{u2} CategoryTheory.types.{u2} (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, succ u2} J _inst_2 (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2} K (Prefunctor.obj.{succ u2, max (succ u2) (succ u3), u3, max (succ u2) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u3 (succ u2)} (CategoryTheory.Functor.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u3 (succ u2)} (CategoryTheory.Functor.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}))) (CategoryTheory.Functor.toPrefunctor.{u2, max u3 u2, u3, max u3 (succ u2)} C _inst_1 (CategoryTheory.Functor.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.yoneda.{u2, u3} C _inst_1)) X)) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, succ u2} J _inst_2 (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2} K (Prefunctor.obj.{succ u2, max (succ u2) (succ u3), u3, max (succ u2) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u3 (succ u2)} (CategoryTheory.Functor.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u3 (succ u2)} (CategoryTheory.Functor.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}))) (CategoryTheory.Functor.toPrefunctor.{u2, max u3 u2, u3, max u3 (succ u2)} C _inst_1 (CategoryTheory.Functor.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u2, u2, u3, succ u2} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.yoneda.{u2, u3} C _inst_1)) X) c)) -> (CategoryTheory.Limits.IsLimit.{u1, u2, u1, u3} J _inst_2 (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) K c)
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda_jointly_reflects_limits CategoryTheory.yonedaJointlyReflectsLimitsₓ'. -/
/-- The yoneda embeddings jointly reflect limits. -/
def yonedaJointlyReflectsLimits (J : Type w) [SmallCategory J] (K : J ⥤ Cᵒᵖ) (c : Cone K)
    (t : ∀ X : C, IsLimit ((yoneda.obj X).mapCone c)) : IsLimit c :=
  let s' : ∀ s : Cone K, Cone (K ⋙ yoneda.obj s.pt.unop) := fun s =>
    ⟨PUnit, fun j _ => (s.π.app j).unop, fun j₁ j₂ α =>
      funext fun _ => Quiver.Hom.op_inj (s.w α).symm⟩
  { lift := fun s => ((t s.pt.unop).lift (s' s) PUnit.unit).op
    fac := fun s j => Quiver.Hom.unop_inj (congr_fun ((t s.pt.unop).fac (s' s) j) PUnit.unit)
    uniq := fun s m w => by
      apply Quiver.Hom.unop_inj
      suffices (fun x : PUnit => m.unop) = (t s.X.unop).lift (s' s) by
        apply congr_fun this PUnit.unit
      apply (t _).uniq (s' s) _ fun j => _
      ext
      exact Quiver.Hom.op_inj (w j) }
#align category_theory.yoneda_jointly_reflects_limits CategoryTheory.yonedaJointlyReflectsLimits

/- warning: category_theory.coyoneda_jointly_reflects_limits -> CategoryTheory.coyonedaJointlyReflectsLimits is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (J : Type.{u1}) [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (K : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1) (c : CategoryTheory.Limits.Cone.{u1, u2, u1, u3} J _inst_2 C _inst_1 K), (forall (X : Opposite.{succ u3} C), CategoryTheory.Limits.IsLimit.{u1, u2, u1, succ u2} J _inst_2 Type.{u2} CategoryTheory.types.{u2} (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, succ u2} J _inst_2 C _inst_1 Type.{u2} CategoryTheory.types.{u2} K (CategoryTheory.Functor.obj.{u2, max u3 u2, u3, max u2 u3 (succ u2)} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) (CategoryTheory.Functor.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.coyoneda.{u2, u3} C _inst_1) X)) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, succ u2} J _inst_2 C _inst_1 Type.{u2} CategoryTheory.types.{u2} K (CategoryTheory.Functor.obj.{u2, max u3 u2, u3, max u2 u3 (succ u2)} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) (CategoryTheory.Functor.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.coyoneda.{u2, u3} C _inst_1) X) c)) -> (CategoryTheory.Limits.IsLimit.{u1, u2, u1, u3} J _inst_2 C _inst_1 K c)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (J : Type.{u1}) [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (K : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1) (c : CategoryTheory.Limits.Cone.{u1, u2, u1, u3} J _inst_2 C _inst_1 K), (forall (X : Opposite.{succ u3} C), CategoryTheory.Limits.IsLimit.{u1, u2, u1, succ u2} J _inst_2 Type.{u2} CategoryTheory.types.{u2} (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, succ u2} J _inst_2 C _inst_1 Type.{u2} CategoryTheory.types.{u2} K (Prefunctor.obj.{succ u2, max (succ u3) (succ u2), u3, max u3 (succ u2)} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) (CategoryTheory.Functor.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u3 (succ u2)} (CategoryTheory.Functor.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u3 (succ u2)} (CategoryTheory.Functor.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}))) (CategoryTheory.Functor.toPrefunctor.{u2, max u3 u2, u3, max u3 (succ u2)} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) (CategoryTheory.Functor.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.coyoneda.{u2, u3} C _inst_1)) X)) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, succ u2} J _inst_2 C _inst_1 Type.{u2} CategoryTheory.types.{u2} K (Prefunctor.obj.{succ u2, max (succ u3) (succ u2), u3, max u3 (succ u2)} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) (CategoryTheory.Functor.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u3 (succ u2)} (CategoryTheory.Functor.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u3 (succ u2)} (CategoryTheory.Functor.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}))) (CategoryTheory.Functor.toPrefunctor.{u2, max u3 u2, u3, max u3 (succ u2)} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) (CategoryTheory.Functor.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.Functor.category.{u2, u2, u3, succ u2} C _inst_1 Type.{u2} CategoryTheory.types.{u2}) (CategoryTheory.coyoneda.{u2, u3} C _inst_1)) X) c)) -> (CategoryTheory.Limits.IsLimit.{u1, u2, u1, u3} J _inst_2 C _inst_1 K c)
Case conversion may be inaccurate. Consider using '#align category_theory.coyoneda_jointly_reflects_limits CategoryTheory.coyonedaJointlyReflectsLimitsₓ'. -/
/-- The coyoneda embeddings jointly reflect limits. -/
def coyonedaJointlyReflectsLimits (J : Type w) [SmallCategory J] (K : J ⥤ C) (c : Cone K)
    (t : ∀ X : Cᵒᵖ, IsLimit ((coyoneda.obj X).mapCone c)) : IsLimit c :=
  let s' : ∀ s : Cone K, Cone (K ⋙ coyoneda.obj (op s.pt)) := fun s =>
    ⟨PUnit, fun j _ => s.π.app j, fun j₁ j₂ α => funext fun _ => (s.w α).symm⟩
  { lift := fun s => (t (op s.pt)).lift (s' s) PUnit.unit
    fac := fun s j => congr_fun ((t _).fac (s' s) j) PUnit.unit
    uniq := fun s m w =>
      by
      suffices (fun x : PUnit => m) = (t _).lift (s' s) by apply congr_fun this PUnit.unit
      apply (t _).uniq (s' s) _ fun j => _
      ext
      exact w j }
#align category_theory.coyoneda_jointly_reflects_limits CategoryTheory.coyonedaJointlyReflectsLimits

variable {D : Type u} [SmallCategory D]

#print CategoryTheory.yonedaFunctorPreservesLimits /-
instance yonedaFunctorPreservesLimits : PreservesLimits (@yoneda D _) :=
  by
  apply preserves_limits_of_evaluation
  intro K
  change preserves_limits (coyoneda.obj K)
  infer_instance
#align category_theory.yoneda_functor_preserves_limits CategoryTheory.yonedaFunctorPreservesLimits
-/

#print CategoryTheory.coyonedaFunctorPreservesLimits /-
instance coyonedaFunctorPreservesLimits : PreservesLimits (@coyoneda D _) :=
  by
  apply preserves_limits_of_evaluation
  intro K
  change preserves_limits (yoneda.obj K)
  infer_instance
#align category_theory.coyoneda_functor_preserves_limits CategoryTheory.coyonedaFunctorPreservesLimits
-/

#print CategoryTheory.yonedaFunctorReflectsLimits /-
instance yonedaFunctorReflectsLimits : ReflectsLimits (@yoneda D _) :=
  Limits.fullyFaithfulReflectsLimits _
#align category_theory.yoneda_functor_reflects_limits CategoryTheory.yonedaFunctorReflectsLimits
-/

#print CategoryTheory.coyonedaFunctorReflectsLimits /-
instance coyonedaFunctorReflectsLimits : ReflectsLimits (@coyoneda D _) :=
  Limits.fullyFaithfulReflectsLimits _
#align category_theory.coyoneda_functor_reflects_limits CategoryTheory.coyonedaFunctorReflectsLimits
-/

end CategoryTheory

-- We don't need to have developed any algebra or set theory to reach (at least) this point
-- in the category theory hierarchy.
assert_not_exists Set.range

assert_not_exists AddCommMonoid

