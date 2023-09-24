/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import CategoryTheory.Limits.Shapes.Images
import CategoryTheory.Limits.Constructions.EpiMono

#align_import category_theory.limits.preserves.shapes.images from "leanprover-community/mathlib"@"10bf4f825ad729c5653adc039dafa3622e7f93c9"

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

#print CategoryTheory.PreservesImage.iso /-
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
-/

#print CategoryTheory.PreservesImage.factorThruImage_comp_hom /-
@[reassoc]
theorem factorThruImage_comp_hom {X Y : A} (f : X ⟶ Y) :
    factorThruImage (L.map f) ≫ (iso L f).Hom = L.map (factorThruImage f) := by simp
#align category_theory.preserves_image.factor_thru_image_comp_hom CategoryTheory.PreservesImage.factorThruImage_comp_hom
-/

#print CategoryTheory.PreservesImage.hom_comp_map_image_ι /-
@[reassoc]
theorem hom_comp_map_image_ι {X Y : A} (f : X ⟶ Y) :
    (iso L f).Hom ≫ L.map (image.ι f) = image.ι (L.map f) := by simp
#align category_theory.preserves_image.hom_comp_map_image_ι CategoryTheory.PreservesImage.hom_comp_map_image_ι
-/

#print CategoryTheory.PreservesImage.inv_comp_image_ι_map /-
@[reassoc]
theorem inv_comp_image_ι_map {X Y : A} (f : X ⟶ Y) :
    (iso L f).inv ≫ image.ι (L.map f) = L.map (image.ι f) := by simp
#align category_theory.preserves_image.inv_comp_image_ι_map CategoryTheory.PreservesImage.inv_comp_image_ι_map
-/

end PreservesImage

end CategoryTheory

