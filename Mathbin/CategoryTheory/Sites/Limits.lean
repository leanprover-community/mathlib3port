/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module category_theory.sites.limits
! leanprover-community/mathlib commit 86d1873c01a723aba6788f0b9051ae3d23b4c1c3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Creates
import Mathbin.CategoryTheory.Sites.Sheafification

/-!

# Limits and colimits of sheaves

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Limits

We prove that the forgetful functor from `Sheaf J D` to presheaves creates limits.
If the target category `D` has limits (of a certain shape),
this then implies that `Sheaf J D` has limits of the same shape and that the forgetful
functor preserves these limits.

## Colimits

Given a diagram `F : K ⥤ Sheaf J D` of sheaves, and a colimit cocone on the level of presheaves,
we show that the cocone obtained by sheafifying the cocone point is a colimit cocone of sheaves.

This allows us to show that `Sheaf J D` has colimits (of a certain shape) as soon as `D` does.

-/


namespace CategoryTheory

namespace Sheaf

open CategoryTheory.Limits

open Opposite

section Limits

universe w v u z

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable {D : Type w} [Category.{max v u} D]

variable {K : Type z} [SmallCategory K]

noncomputable section

section

/- warning: category_theory.Sheaf.multifork_evaluation_cone -> CategoryTheory.Sheaf.multiforkEvaluationCone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] {K : Type.{u4}} [_inst_3 : CategoryTheory.SmallCategory.{u4} K] (F : CategoryTheory.Functor.{u4, max u2 u3, u4, max u3 u1 u2 u3} K _inst_3 (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2)) (E : CategoryTheory.Limits.Cone.{u4, max u2 u3, u4, max u2 (max u2 u3) u3 u1} K _inst_3 (CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.comp.{u4, max u2 u3, max u2 u3, u4, max u3 u1 u2 u3, max u2 (max u2 u3) u3 u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) F (CategoryTheory.sheafToPresheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2))) (X : C) (W : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X), (CategoryTheory.Limits.Multifork.{max u2 u3, u1, max u3 u2} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, u3} C _inst_1 X J D _inst_2 W (CategoryTheory.Limits.Cone.pt.{u4, max u2 u3, u4, max u2 (max u2 u3) u3 u1} K _inst_3 (CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.comp.{u4, max u2 u3, max u2 u3, u4, max u3 u1 u2 u3, max u2 (max u2 u3) u3 u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) F (CategoryTheory.sheafToPresheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2)) E))) -> (CategoryTheory.Limits.Cone.{u4, max u2 u3, u4, u1} K _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u4, max u2 u3, max u2 u3, u4, max u3 u1 u2 u3, u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) D _inst_2 F (CategoryTheory.Functor.comp.{max u2 u3, max u2 u3, max u2 u3, max u3 u1 u2 u3, max u2 (max u2 u3) u3 u1, u1} (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) D _inst_2 (CategoryTheory.sheafToPresheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.obj.{u2, max (max u2 (max u2 u3) u3 u1) u2 u3, u3, max (max u2 u3) (max u2 (max u2 u3) u3 u1) u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) (CategoryTheory.Functor.{max u2 u3, max u2 u3, max u2 (max u2 u3) u3 u1, u1} (CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u2 u3, max u2 u3, max u2 (max u2 u3) u3 u1, u1} (CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) D _inst_2) (CategoryTheory.evaluation.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (Opposite.op.{succ u3} C X)))))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] {K : Type.{u4}} [_inst_3 : CategoryTheory.SmallCategory.{u4} K] (F : CategoryTheory.Functor.{u4, max u3 u2, u4, max (max (max u1 u3) u3 u2) u2} K _inst_3 (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2)) (E : CategoryTheory.Limits.Cone.{u4, max u3 u2, u4, max (max u3 u2) u1} K _inst_3 (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.comp.{u4, max u3 u2, max u3 u2, u4, max (max u3 u2) u1, max (max u3 u2) u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) F (CategoryTheory.sheafToPresheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2))) (X : C) (W : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X), (CategoryTheory.Limits.Multifork.{max u3 u2, u1, max u3 u2} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, u3} C _inst_1 X J D _inst_2 W (CategoryTheory.Limits.Cone.pt.{u4, max u3 u2, u4, max (max u3 u2) u1} K _inst_3 (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.comp.{u4, max u3 u2, max u3 u2, u4, max (max u3 u2) u1, max (max u3 u2) u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) F (CategoryTheory.sheafToPresheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2)) E))) -> (CategoryTheory.Limits.Cone.{u4, max u3 u2, u4, u1} K _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u4, max u3 u2, max u3 u2, u4, max (max u3 u2) u1, u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) D _inst_2 F (CategoryTheory.Functor.comp.{max u3 u2, max u3 u2, max u3 u2, max (max u3 u2) u1, max (max u3 u2) u1, u1} (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) D _inst_2 (CategoryTheory.sheafToPresheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (Prefunctor.obj.{succ u2, max (max (succ u3) (succ u2)) (succ u1), u3, max (max u3 u2) u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) (CategoryTheory.Functor.{max u3 u2, max u3 u2, max (max (max u1 u3) u3 u2) u2, u1} (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max (max u3 u2) u1, max (max u3 u2) u1} (CategoryTheory.Functor.{max u3 u2, max u3 u2, max (max (max u1 u3) u3 u2) u2, u1} (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max (max u3 u2) u1, max (max u3 u2) u1} (CategoryTheory.Functor.{max u3 u2, max u3 u2, max (max (max u1 u3) u3 u2) u2, u1} (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, max u3 u2, max (max (max u3 u1) u2) u3 u2, u1} (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u2, max (max u3 u2) u1, u3, max (max u3 u2) u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) (CategoryTheory.Functor.{max u3 u2, max u3 u2, max (max (max u1 u3) u3 u2) u2, u1} (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, max u3 u2, max (max (max u3 u1) u2) u3 u2, u1} (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) D _inst_2) (CategoryTheory.evaluation.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2)) (Opposite.op.{succ u3} C X)))))
Case conversion may be inaccurate. Consider using '#align category_theory.Sheaf.multifork_evaluation_cone CategoryTheory.Sheaf.multiforkEvaluationConeₓ'. -/
/-- An auxiliary definition to be used below.

Whenever `E` is a cone of shape `K` of sheaves, and `S` is the multifork associated to a
covering `W` of an object `X`, with respect to the cone point `E.X`, this provides a cone of
shape `K` of objects in `D`, with cone point `S.X`.

See `is_limit_multifork_of_is_limit` for more on how this definition is used.
-/
def multiforkEvaluationCone (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D)) (X : C)
    (W : J.cover X) (S : Multifork (W.index E.pt)) :
    Cone (F ⋙ sheafToPresheaf J D ⋙ (evaluation Cᵒᵖ D).obj (op X))
    where
  pt := S.pt
  π :=
    { app := fun k =>
        (Presheaf.isLimitOfIsSheaf J (F.obj k).1 W (F.obj k).2).lift <|
          Multifork.ofι _ S.pt (fun i => S.ι i ≫ (E.π.app k).app (op i.y))
            (by
              intro i
              simp only [category.assoc]
              erw [← (E.π.app k).naturality, ← (E.π.app k).naturality]
              dsimp
              simp only [← category.assoc]
              congr 1
              apply S.condition)
      naturality' := by
        intro i j f
        dsimp [presheaf.is_limit_of_is_sheaf]
        rw [category.id_comp]
        apply presheaf.is_sheaf.hom_ext (F.obj j).2 W
        intro ii
        rw [presheaf.is_sheaf.amalgamate_map, category.assoc, ← (F.map f).val.naturality, ←
          category.assoc, presheaf.is_sheaf.amalgamate_map]
        dsimp [multifork.of_ι]
        erw [category.assoc, ← E.w f]
        tidy }
#align category_theory.Sheaf.multifork_evaluation_cone CategoryTheory.Sheaf.multiforkEvaluationCone

variable [HasLimitsOfShape K D]

#print CategoryTheory.Sheaf.isLimitMultiforkOfIsLimit /-
/-- If `E` is a cone of shape `K` of sheaves, which is a limit on the level of presheves,
this definition shows that the limit presheaf satisfies the multifork variant of the sheaf
condition, at a given covering `W`.

This is used below in `is_sheaf_of_is_limit` to show that the limit presheaf is indeed a sheaf.
-/
def isLimitMultiforkOfIsLimit (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D))
    (hE : IsLimit E) (X : C) (W : J.cover X) : IsLimit (W.Multifork E.pt) :=
  Multifork.IsLimit.mk _
    (fun S =>
      (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).lift <|
        multifork_evaluation_cone F E X W S)
    (by
      intro S i
      apply (is_limit_of_preserves ((evaluation Cᵒᵖ D).obj (op i.Y)) hE).hom_ext
      intro k
      dsimp [multifork.of_ι]
      erw [category.assoc, (E.π.app k).naturality]
      dsimp
      rw [← category.assoc]
      erw [(is_limit_of_preserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac
          (multifork_evaluation_cone F E X W S)]
      dsimp [multifork_evaluation_cone, presheaf.is_limit_of_is_sheaf]
      erw [presheaf.is_sheaf.amalgamate_map]
      rfl)
    (by
      intro S m hm
      apply (is_limit_of_preserves ((evaluation Cᵒᵖ D).obj (op X)) hE).hom_ext
      intro k
      dsimp
      erw [(is_limit_of_preserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac]
      apply presheaf.is_sheaf.hom_ext (F.obj k).2 W
      intro i
      erw [presheaf.is_sheaf.amalgamate_map]
      dsimp [multifork.of_ι]
      change _ = S.ι i ≫ _
      erw [← hm, category.assoc, ← (E.π.app k).naturality, category.assoc]
      rfl)
#align category_theory.Sheaf.is_limit_multifork_of_is_limit CategoryTheory.Sheaf.isLimitMultiforkOfIsLimit
-/

#print CategoryTheory.Sheaf.isSheaf_of_isLimit /-
/-- If `E` is a cone which is a limit on the level of presheaves,
then the limit presheaf is again a sheaf.

This is used to show that the forgetful functor from sheaves to presheaves creates limits.
-/
theorem isSheaf_of_isLimit (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D))
    (hE : IsLimit E) : Presheaf.IsSheaf J E.pt :=
  by
  rw [presheaf.is_sheaf_iff_multifork]
  intro X S
  exact ⟨is_limit_multifork_of_is_limit _ _ hE _ _⟩
#align category_theory.Sheaf.is_sheaf_of_is_limit CategoryTheory.Sheaf.isSheaf_of_isLimit
-/

instance (F : K ⥤ Sheaf J D) : CreatesLimit F (sheafToPresheaf J D) :=
  createsLimitOfReflectsIso fun E hE =>
    { liftedCone :=
        ⟨⟨E.pt, is_sheaf_of_is_limit _ _ hE⟩,
          ⟨fun t => ⟨E.π.app _⟩, fun u v e => Sheaf.Hom.ext _ _ <| E.π.naturality _⟩⟩
      validLift :=
        Cones.ext (eqToIso rfl) fun j => by
          dsimp
          simp
      makesLimit :=
        { lift := fun S => ⟨hE.lift ((sheafToPresheaf J D).mapCone S)⟩
          fac := fun S j => by
            ext1
            apply hE.fac ((Sheaf_to_presheaf J D).mapCone S) j
          uniq := fun S m hm => by
            ext1
            exact
              hE.uniq ((Sheaf_to_presheaf J D).mapCone S) m.val fun j =>
                congr_arg hom.val (hm j) } }

instance : CreatesLimitsOfShape K (sheafToPresheaf J D) where

instance : HasLimitsOfShape K (Sheaf J D) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J D)

end

instance [HasLimits D] : CreatesLimits (sheafToPresheaf J D) :=
  ⟨⟩

instance [HasLimits D] : HasLimits (Sheaf J D) :=
  has_limits_of_has_limits_creates_limits (sheafToPresheaf J D)

end Limits

section Colimits

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable {D : Type w} [Category.{max v u} D]

variable {K : Type max v u} [SmallCategory K]

-- Now we need a handful of instances to obtain sheafification...
variable [ConcreteCategory.{max v u} D]

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), HasMultiequalizer (S.index P)]

variable [PreservesLimits (forget D)]

variable [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ D]

variable [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget D)]

variable [ReflectsIsomorphisms (forget D)]

/- warning: category_theory.Sheaf.sheafify_cocone -> CategoryTheory.Sheaf.sheafifyCocone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] {K : Type.{max u2 u3}} [_inst_3 : CategoryTheory.SmallCategory.{max u2 u3} K] [_inst_4 : CategoryTheory.ConcreteCategory.{max u2 u3, max u2 u3, u1} D _inst_2] [_inst_5 : forall (P : CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u2 u3, u1, max u3 u2} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, u3} C _inst_1 X J D _inst_2 S P)] [_inst_6 : CategoryTheory.Limits.PreservesLimits.{max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_4)] [_inst_7 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u3 u2, max u3 u2, max u2 u3, u1} (Opposite.{succ (max u3 u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u2, u3} C _inst_1 J X))) D _inst_2] [_inst_8 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u3 u2, max u3 u2, max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (Opposite.{succ (max u3 u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u2, u3} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_4)] [_inst_9 : CategoryTheory.ReflectsIsomorphisms.{max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_4)] {F : CategoryTheory.Functor.{max u2 u3, max u2 u3, max u2 u3, max u3 u1 u2 u3} K _inst_3 (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2)}, (CategoryTheory.Limits.Cocone.{max u2 u3, max u2 u3, max u2 u3, max u2 (max u2 u3) u3 u1} K _inst_3 (CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.comp.{max u2 u3, max u2 u3, max u2 u3, max u2 u3, max u3 u1 u2 u3, max u2 (max u2 u3) u3 u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) F (CategoryTheory.sheafToPresheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2))) -> (CategoryTheory.Limits.Cocone.{max u2 u3, max u2 u3, max u2 u3, max u3 u1 u2 u3} K _inst_3 (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) F)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] {K : Type.{max u2 u3}} [_inst_3 : CategoryTheory.SmallCategory.{max u3 u2} K] [_inst_4 : CategoryTheory.ConcreteCategory.{max u2 u3, max u3 u2, u1} D _inst_2] [_inst_5 : forall (P : CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u3 u2, u1, max u3 u2} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, u3} C _inst_1 X J D _inst_2 S P)] [_inst_6 : CategoryTheory.Limits.PreservesLimits.{max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_4)] [_inst_7 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u3 u2, max u3 u2, max u3 u2, u1} (Opposite.{max (succ u3) (succ u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u2, u3} C _inst_1 J X))) D _inst_2] [_inst_8 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u3 u2, max u3 u2, max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (Opposite.{max (succ u3) (succ u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u2, u3} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_4)] [_inst_9 : CategoryTheory.ReflectsIsomorphisms.{max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_4)] {F : CategoryTheory.Functor.{max u3 u2, max u3 u2, max u3 u2, max (max (max u1 u3) u3 u2) u2} K _inst_3 (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2)}, (CategoryTheory.Limits.Cocone.{max u3 u2, max u3 u2, max u3 u2, max (max u3 u2) u1} K _inst_3 (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.comp.{max u3 u2, max u3 u2, max u3 u2, max u3 u2, max (max u3 u2) u1, max (max u3 u2) u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) F (CategoryTheory.sheafToPresheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2))) -> (CategoryTheory.Limits.Cocone.{max u3 u2, max u3 u2, max u3 u2, max (max u3 u2) u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) F)
Case conversion may be inaccurate. Consider using '#align category_theory.Sheaf.sheafify_cocone CategoryTheory.Sheaf.sheafifyCoconeₓ'. -/
/-- Construct a cocone by sheafifying a cocone point of a cocone `E` of presheaves
over a functor which factors through sheaves.
In `is_colimit_sheafify_cocone`, we show that this is a colimit cocone when `E` is a colimit. -/
@[simps]
def sheafifyCocone {F : K ⥤ Sheaf J D} (E : Cocone (F ⋙ sheafToPresheaf J D)) : Cocone F
    where
  pt := ⟨J.sheafify E.pt, GrothendieckTopology.Plus.isSheaf_plus_plus _ _⟩
  ι :=
    { app := fun k => ⟨E.ι.app k ≫ J.toSheafify E.pt⟩
      naturality' := fun i j f => by
        ext1
        dsimp
        erw [category.comp_id, ← category.assoc, E.w f] }
#align category_theory.Sheaf.sheafify_cocone CategoryTheory.Sheaf.sheafifyCocone

/- warning: category_theory.Sheaf.is_colimit_sheafify_cocone -> CategoryTheory.Sheaf.isColimitSheafifyCocone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] {K : Type.{max u2 u3}} [_inst_3 : CategoryTheory.SmallCategory.{max u2 u3} K] [_inst_4 : CategoryTheory.ConcreteCategory.{max u2 u3, max u2 u3, u1} D _inst_2] [_inst_5 : forall (P : CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u2 u3, u1, max u3 u2} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, u3} C _inst_1 X J D _inst_2 S P)] [_inst_6 : CategoryTheory.Limits.PreservesLimits.{max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_4)] [_inst_7 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u3 u2, max u3 u2, max u2 u3, u1} (Opposite.{succ (max u3 u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u2, u3} C _inst_1 J X))) D _inst_2] [_inst_8 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u3 u2, max u3 u2, max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (Opposite.{succ (max u3 u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u2, u3} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_4)] [_inst_9 : CategoryTheory.ReflectsIsomorphisms.{max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_4)] {F : CategoryTheory.Functor.{max u2 u3, max u2 u3, max u2 u3, max u3 u1 u2 u3} K _inst_3 (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2)} (E : CategoryTheory.Limits.Cocone.{max u2 u3, max u2 u3, max u2 u3, max u2 (max u2 u3) u3 u1} K _inst_3 (CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.comp.{max u2 u3, max u2 u3, max u2 u3, max u2 u3, max u3 u1 u2 u3, max u2 (max u2 u3) u3 u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) F (CategoryTheory.sheafToPresheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2))), (CategoryTheory.Limits.IsColimit.{max u2 u3, max u2 u3, max u2 u3, max u2 (max u2 u3) u3 u1} K _inst_3 (CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.comp.{max u2 u3, max u2 u3, max u2 u3, max u2 u3, max u3 u1 u2 u3, max u2 (max u2 u3) u3 u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) F (CategoryTheory.sheafToPresheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2)) E) -> (CategoryTheory.Limits.IsColimit.{max u2 u3, max u2 u3, max u2 u3, max u3 u1 u2 u3} K _inst_3 (CategoryTheory.Sheaf.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, u3, u1} C _inst_1 J D _inst_2) F (CategoryTheory.Sheaf.sheafifyCocone.{u1, u2, u3} C _inst_1 J D _inst_2 K _inst_3 _inst_4 (CategoryTheory.Sheaf.isColimitSheafifyCocone._proof_1.{u3, u2, u1} C _inst_1 J D _inst_2 _inst_5) _inst_6 (CategoryTheory.Sheaf.isColimitSheafifyCocone._proof_2.{u3, u2, u1} C _inst_1 J D _inst_2 _inst_7) (fun (X : C) => _inst_8 X) _inst_9 F E))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] {K : Type.{max u2 u3}} [_inst_3 : CategoryTheory.SmallCategory.{max u3 u2} K] [_inst_4 : CategoryTheory.ConcreteCategory.{max u2 u3, max u3 u2, u1} D _inst_2] [_inst_5 : forall (P : CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u3 u2, u1, max u3 u2} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, u3} C _inst_1 X J D _inst_2 S P)] [_inst_6 : CategoryTheory.Limits.PreservesLimits.{max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_4)] [_inst_7 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u3 u2, max u3 u2, max u3 u2, u1} (Opposite.{max (succ u3) (succ u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u2, u3} C _inst_1 J X))) D _inst_2] [_inst_8 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u3 u2, max u3 u2, max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (Opposite.{max (succ u3) (succ u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u2, u3} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_4)] [_inst_9 : CategoryTheory.ReflectsIsomorphisms.{max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_4)] {F : CategoryTheory.Functor.{max u3 u2, max u3 u2, max u3 u2, max (max (max u1 u3) u3 u2) u2} K _inst_3 (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2)} (E : CategoryTheory.Limits.Cocone.{max u3 u2, max u3 u2, max u3 u2, max (max u3 u2) u1} K _inst_3 (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.comp.{max u3 u2, max u3 u2, max u3 u2, max u3 u2, max (max u3 u2) u1, max (max u3 u2) u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) F (CategoryTheory.sheafToPresheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2))), (CategoryTheory.Limits.IsColimit.{max u3 u2, max u3 u2, max u3 u2, max (max u3 u2) u1} K _inst_3 (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.comp.{max u3 u2, max u3 u2, max u3 u2, max u3 u2, max (max u3 u2) u1, max (max u3 u2) u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) F (CategoryTheory.sheafToPresheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2)) E) -> (CategoryTheory.Limits.IsColimit.{max u3 u2, max u3 u2, max u3 u2, max (max u3 u2) u1} K _inst_3 (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) F (CategoryTheory.Sheaf.sheafifyCocone.{u1, u2, u3} C _inst_1 J D _inst_2 K _inst_3 _inst_4 (fun (P : CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) => _inst_5 P X S) _inst_6 (fun (X : C) => _inst_7 X) (fun (X : C) => _inst_8 X) _inst_9 F E))
Case conversion may be inaccurate. Consider using '#align category_theory.Sheaf.is_colimit_sheafify_cocone CategoryTheory.Sheaf.isColimitSheafifyCoconeₓ'. -/
/-- If `E` is a colimit cocone of presheaves, over a diagram factoring through sheaves,
then `sheafify_cocone E` is a colimit cocone. -/
@[simps]
def isColimitSheafifyCocone {F : K ⥤ Sheaf J D} (E : Cocone (F ⋙ sheafToPresheaf J D))
    (hE : IsColimit E) : IsColimit (sheafify_cocone E)
    where
  desc S := ⟨J.sheafifyLift (hE.desc ((sheafToPresheaf J D).mapCocone S)) S.pt.2⟩
  fac := by
    intro S j
    ext1
    dsimp [sheafify_cocone]
    erw [category.assoc, J.to_sheafify_sheafify_lift, hE.fac]
    rfl
  uniq := by
    intro S m hm
    ext1
    apply J.sheafify_lift_unique
    apply hE.uniq ((Sheaf_to_presheaf J D).mapCocone S)
    intro j
    dsimp
    simpa only [← category.assoc, ← hm]
#align category_theory.Sheaf.is_colimit_sheafify_cocone CategoryTheory.Sheaf.isColimitSheafifyCocone

instance [HasColimitsOfShape K D] : HasColimitsOfShape K (Sheaf J D) :=
  ⟨fun F =>
    HasColimit.mk
      ⟨sheafify_cocone (colimit.cocone _), is_colimit_sheafify_cocone _ (colimit.isColimit _)⟩⟩

instance [HasColimits D] : HasColimits (Sheaf J D) :=
  ⟨inferInstance⟩

end Colimits

end Sheaf

end CategoryTheory

