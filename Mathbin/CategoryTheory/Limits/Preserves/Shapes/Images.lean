/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

! This file was ported from Lean 3 source module category_theory.limits.preserves.shapes.images
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Images
import Mathbin.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Preserving images

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we show that if a functor preserves span and cospan, then it preserves images.
-/


noncomputable section

namespace CategoryTheory

namespace PreservesImage

open CategoryTheory

open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]

variable [HasEqualizers A] [HasImages A]

variable [StrongEpiCategory B] [HasImages B]

variable (L : A ⥤ B)

variable [∀ {X Y Z : A} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) L]

variable [∀ {X Y Z : A} (f : X ⟶ Y) (g : X ⟶ Z), PreservesColimit (span f g) L]

/- warning: category_theory.preserves_image.iso -> CategoryTheory.PreservesImage.iso is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} A] [_inst_2 : CategoryTheory.Category.{u4, u2} B] [_inst_3 : CategoryTheory.Limits.HasEqualizers.{u3, u1} A _inst_1] [_inst_4 : CategoryTheory.Limits.HasImages.{u3, u1} A _inst_1] [_inst_5 : CategoryTheory.StrongEpiCategory.{u4, u2} B _inst_2] [_inst_6 : CategoryTheory.Limits.HasImages.{u4, u2} B _inst_2] (L : CategoryTheory.Functor.{u3, u4, u1, u2} A _inst_1 B _inst_2) [_inst_7 : forall {X : A} {Y : A} {Z : A} (f : Quiver.Hom.{succ u3, u1} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) X Z) (g : Quiver.Hom.{succ u3, u1} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) Y Z), CategoryTheory.Limits.PreservesLimit.{0, 0, u3, u4, u1, u2} A _inst_1 B _inst_2 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Limits.cospan.{u3, u1} A _inst_1 X Y Z f g) L] [_inst_8 : forall {X : A} {Y : A} {Z : A} (f : Quiver.Hom.{succ u3, u1} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) X Y) (g : Quiver.Hom.{succ u3, u1} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) X Z), CategoryTheory.Limits.PreservesColimit.{0, 0, u3, u4, u1, u2} A _inst_1 B _inst_2 CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Limits.span.{u3, u1} A _inst_1 X Y Z f g) L] {X : A} {Y : A} (f : Quiver.Hom.{succ u3, u1} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) X Y), CategoryTheory.Iso.{u4, u2} B _inst_2 (CategoryTheory.Limits.image.{u4, u2} B _inst_2 (CategoryTheory.Functor.obj.{u3, u4, u1, u2} A _inst_1 B _inst_2 L X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} A _inst_1 B _inst_2 L Y) (CategoryTheory.Functor.map.{u3, u4, u1, u2} A _inst_1 B _inst_2 L X Y f) (CategoryTheory.PreservesImage.iso._proof_1.{u1, u2, u3, u4} A B _inst_1 _inst_2 _inst_6 L X Y f)) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} A _inst_1 B _inst_2 L (CategoryTheory.Limits.image.{u3, u1} A _inst_1 X Y f (CategoryTheory.Limits.HasImages.hasImage.{u3, u1} A _inst_1 _inst_4 X Y f)))
but is expected to have type
  forall {A : Type.{u1}} {B : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} A] [_inst_2 : CategoryTheory.Category.{u4, u2} B] [_inst_3 : CategoryTheory.Limits.HasEqualizers.{u3, u1} A _inst_1] [_inst_4 : CategoryTheory.Limits.HasImages.{u3, u1} A _inst_1] [_inst_5 : CategoryTheory.StrongEpiCategory.{u4, u2} B _inst_2] [_inst_6 : CategoryTheory.Limits.HasImages.{u4, u2} B _inst_2] (L : CategoryTheory.Functor.{u3, u4, u1, u2} A _inst_1 B _inst_2) [_inst_7 : forall {X : A} {Y : A} {Z : A} (f : Quiver.Hom.{succ u3, u1} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) X Z) (g : Quiver.Hom.{succ u3, u1} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) Y Z), CategoryTheory.Limits.PreservesLimit.{0, 0, u3, u4, u1, u2} A _inst_1 B _inst_2 CategoryTheory.Limits.WalkingCospan (CategoryTheory.Limits.WidePullbackShape.category.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Limits.cospan.{u3, u1} A _inst_1 X Y Z f g) L] [_inst_8 : forall {X : A} {Y : A} {Z : A} (f : Quiver.Hom.{succ u3, u1} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) X Y) (g : Quiver.Hom.{succ u3, u1} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) X Z), CategoryTheory.Limits.PreservesColimit.{0, 0, u3, u4, u1, u2} A _inst_1 B _inst_2 CategoryTheory.Limits.WalkingSpan (CategoryTheory.Limits.WidePushoutShape.category.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.Limits.span.{u3, u1} A _inst_1 X Y Z f g) L] {X : A} {Y : A} (f : Quiver.Hom.{succ u3, u1} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) X Y), CategoryTheory.Iso.{u4, u2} B _inst_2 (CategoryTheory.Limits.image.{u4, u2} B _inst_2 (Prefunctor.obj.{succ u3, succ u4, u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) B (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} B (CategoryTheory.Category.toCategoryStruct.{u4, u2} B _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} A _inst_1 B _inst_2 L) X) (Prefunctor.obj.{succ u3, succ u4, u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) B (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} B (CategoryTheory.Category.toCategoryStruct.{u4, u2} B _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} A _inst_1 B _inst_2 L) Y) (Prefunctor.map.{succ u3, succ u4, u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) B (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} B (CategoryTheory.Category.toCategoryStruct.{u4, u2} B _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} A _inst_1 B _inst_2 L) X Y f) (CategoryTheory.Limits.HasImages.has_image.{u4, u2} B _inst_2 _inst_6 (Prefunctor.obj.{succ u3, succ u4, u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) B (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} B (CategoryTheory.Category.toCategoryStruct.{u4, u2} B _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} A _inst_1 B _inst_2 L) X) (Prefunctor.obj.{succ u3, succ u4, u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) B (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} B (CategoryTheory.Category.toCategoryStruct.{u4, u2} B _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} A _inst_1 B _inst_2 L) Y) (Prefunctor.map.{succ u3, succ u4, u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) B (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} B (CategoryTheory.Category.toCategoryStruct.{u4, u2} B _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} A _inst_1 B _inst_2 L) X Y f))) (Prefunctor.obj.{succ u3, succ u4, u1, u2} A (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} A (CategoryTheory.Category.toCategoryStruct.{u3, u1} A _inst_1)) B (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} B (CategoryTheory.Category.toCategoryStruct.{u4, u2} B _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} A _inst_1 B _inst_2 L) (CategoryTheory.Limits.image.{u3, u1} A _inst_1 X Y f (CategoryTheory.Limits.HasImages.has_image.{u3, u1} A _inst_1 _inst_4 X Y f)))
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_image.iso CategoryTheory.PreservesImage.isoₓ'. -/
/-- If a functor preserves span and cospan, then it preserves images.
-/
@[simps]
def iso {X Y : A} (f : X ⟶ Y) : image (L.map f) ≅ L.obj (image f) :=
  let aux1 : StrongEpiMonoFactorisation (L.map f) :=
    { i := L.obj (Limits.image f)
      m := L.map <| Limits.image.ι _
      m_mono := preserves_mono_of_preservesLimit _ _
      e := L.map <| factorThruImage _
      e_strongEpi := @strongEpi_of_epi _ _ _ <| preserves_epi_of_preservesColimit L _
      fac := by rw [← L.map_comp, limits.image.fac] }
  IsImage.isoExt (Image.isImage (L.map f)) aux1.toMonoIsImage
#align category_theory.preserves_image.iso CategoryTheory.PreservesImage.iso

/- warning: category_theory.preserves_image.factor_thru_image_comp_hom -> CategoryTheory.PreservesImage.factorThruImage_comp_hom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_image.factor_thru_image_comp_hom CategoryTheory.PreservesImage.factorThruImage_comp_homₓ'. -/
@[reassoc]
theorem factorThruImage_comp_hom {X Y : A} (f : X ⟶ Y) :
    factorThruImage (L.map f) ≫ (iso L f).Hom = L.map (factorThruImage f) := by simp
#align category_theory.preserves_image.factor_thru_image_comp_hom CategoryTheory.PreservesImage.factorThruImage_comp_hom

/- warning: category_theory.preserves_image.hom_comp_map_image_ι -> CategoryTheory.PreservesImage.hom_comp_map_image_ι is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_image.hom_comp_map_image_ι CategoryTheory.PreservesImage.hom_comp_map_image_ιₓ'. -/
@[reassoc]
theorem hom_comp_map_image_ι {X Y : A} (f : X ⟶ Y) :
    (iso L f).Hom ≫ L.map (image.ι f) = image.ι (L.map f) := by simp
#align category_theory.preserves_image.hom_comp_map_image_ι CategoryTheory.PreservesImage.hom_comp_map_image_ι

/- warning: category_theory.preserves_image.inv_comp_image_ι_map -> CategoryTheory.PreservesImage.inv_comp_image_ι_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_image.inv_comp_image_ι_map CategoryTheory.PreservesImage.inv_comp_image_ι_mapₓ'. -/
@[reassoc]
theorem inv_comp_image_ι_map {X Y : A} (f : X ⟶ Y) :
    (iso L f).inv ≫ image.ι (L.map f) = L.map (image.ι f) := by simp
#align category_theory.preserves_image.inv_comp_image_ι_map CategoryTheory.PreservesImage.inv_comp_image_ι_map

end PreservesImage

end CategoryTheory

