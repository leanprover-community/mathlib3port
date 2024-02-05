/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import CategoryTheory.NaturalIsomorphism
import CategoryTheory.FullSubcategory

#align_import category_theory.essential_image from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Essential image of a functor

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The essential image `ess_image` of a functor consists of the objects in the target category which
are isomorphic to an object in the image of the object function.
This, for instance, allows us to talk about objects belonging to a subcategory expressed as a
functor rather than a subtype, preserving the principle of equivalence. For example this lets us
define exponential ideals.

The essential image can also be seen as a subcategory of the target category, and witnesses that
a functor decomposes into a essentially surjective functor and a fully faithful functor.
(TODO: show that this decomposition forms an orthogonal factorisation system).
-/


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] {F : C ⥤ D}

namespace Functor

#print CategoryTheory.Functor.essImage /-
/-- The essential image of a functor `F` consists of those objects in the target category which are
isomorphic to an object in the image of the function `F.obj`. In other words, this is the closure
under isomorphism of the function `F.obj`.
This is the "non-evil" way of describing the image of a functor.
-/
def essImage (F : C ⥤ D) : Set D := fun Y => ∃ X : C, Nonempty (F.obj X ≅ Y)
#align category_theory.functor.ess_image CategoryTheory.Functor.essImage
-/

#print CategoryTheory.Functor.essImage.witness /-
/-- Get the witnessing object that `Y` is in the subcategory given by `F`. -/
def essImage.witness {Y : D} (h : Y ∈ F.essImage) : C :=
  h.some
#align category_theory.functor.ess_image.witness CategoryTheory.Functor.essImage.witness
-/

#print CategoryTheory.Functor.essImage.getIso /-
/-- Extract the isomorphism between `F.obj h.witness` and `Y` itself. -/
def essImage.getIso {Y : D} (h : Y ∈ F.essImage) : F.obj h.witness ≅ Y :=
  Classical.choice h.choose_spec
#align category_theory.functor.ess_image.get_iso CategoryTheory.Functor.essImage.getIso
-/

#print CategoryTheory.Functor.essImage.ofIso /-
/-- Being in the essential image is a "hygenic" property: it is preserved under isomorphism. -/
theorem essImage.ofIso {Y Y' : D} (h : Y ≅ Y') (hY : Y ∈ essImage F) : Y' ∈ essImage F :=
  hY.imp fun B => Nonempty.map (· ≪≫ h)
#align category_theory.functor.ess_image.of_iso CategoryTheory.Functor.essImage.ofIso
-/

#print CategoryTheory.Functor.essImage.ofNatIso /-
/-- If `Y` is in the essential image of `F` then it is in the essential image of `F'` as long as
`F ≅ F'`.
-/
theorem essImage.ofNatIso {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : Y ∈ essImage F) :
    Y ∈ essImage F' :=
  hY.imp fun X => Nonempty.map fun t => h.symm.app X ≪≫ t
#align category_theory.functor.ess_image.of_nat_iso CategoryTheory.Functor.essImage.ofNatIso
-/

#print CategoryTheory.Functor.essImage_eq_of_natIso /-
/-- Isomorphic functors have equal essential images. -/
theorem essImage_eq_of_natIso {F' : C ⥤ D} (h : F ≅ F') : essImage F = essImage F' :=
  funext fun _ => propext ⟨essImage.ofNatIso h, essImage.ofNatIso h.symm⟩
#align category_theory.functor.ess_image_eq_of_nat_iso CategoryTheory.Functor.essImage_eq_of_natIso
-/

#print CategoryTheory.Functor.obj_mem_essImage /-
/-- An object in the image is in the essential image. -/
theorem obj_mem_essImage (F : D ⥤ C) (Y : D) : F.obj Y ∈ essImage F :=
  ⟨Y, ⟨Iso.refl _⟩⟩
#align category_theory.functor.obj_mem_ess_image CategoryTheory.Functor.obj_mem_essImage
-/

#print CategoryTheory.Functor.EssImageSubcategory /-
/-- The essential image of a functor, interpreted of a full subcategory of the target category. -/
@[nolint has_nonempty_instance]
def EssImageSubcategory (F : C ⥤ D) :=
  FullSubcategory F.essImage
deriving Category
#align category_theory.functor.ess_image_subcategory CategoryTheory.Functor.EssImageSubcategory
-/

#print CategoryTheory.Functor.essImageInclusion /-
/-- The essential image as a subcategory has a fully faithful inclusion into the target category. -/
@[simps]
def essImageInclusion (F : C ⥤ D) : F.EssImageSubcategory ⥤ D :=
  fullSubcategoryInclusion _
deriving Full, Faithful
#align category_theory.functor.ess_image_inclusion CategoryTheory.Functor.essImageInclusion
-/

#print CategoryTheory.Functor.toEssImage /-
/--
Given a functor `F : C ⥤ D`, we have an (essentially surjective) functor from `C` to the essential
image of `F`.
-/
@[simps]
def toEssImage (F : C ⥤ D) : C ⥤ F.EssImageSubcategory :=
  FullSubcategory.lift _ F (obj_mem_essImage _)
#align category_theory.functor.to_ess_image CategoryTheory.Functor.toEssImage
-/

#print CategoryTheory.Functor.toEssImageCompEssentialImageInclusion /-
/-- The functor `F` factorises through its essential image, where the first functor is essentially
surjective and the second is fully faithful.
-/
@[simps]
def toEssImageCompEssentialImageInclusion (F : C ⥤ D) : F.toEssImage ⋙ F.essImageInclusion ≅ F :=
  FullSubcategory.lift_comp_inclusion _ _ _
#align category_theory.functor.to_ess_image_comp_essential_image_inclusion CategoryTheory.Functor.toEssImageCompEssentialImageInclusion
-/

end Functor

#print CategoryTheory.EssSurj /-
/- ./././Mathport/Syntax/Translate/Command.lean:400:30: infer kinds are unsupported in Lean 4: #[`mem_essImage] [] -/
/-- A functor `F : C ⥤ D` is essentially surjective if every object of `D` is in the essential image
of `F`. In other words, for every `Y : D`, there is some `X : C` with `F.obj X ≅ Y`.

See <https://stacks.math.columbia.edu/tag/001C>.
-/
class EssSurj (F : C ⥤ D) : Prop where
  mem_essImage (Y : D) : Y ∈ F.essImage
#align category_theory.ess_surj CategoryTheory.EssSurj
-/

instance : EssSurj F.toEssImage
    where mem_essImage := fun ⟨Y, hY⟩ => ⟨_, ⟨⟨_, _, hY.getIso.hom_inv_id, hY.getIso.inv_hom_id⟩⟩⟩

variable (F) [EssSurj F]

#print CategoryTheory.Functor.objPreimage /-
/-- Given an essentially surjective functor, we can find a preimage for every object `Y` in the
    codomain. Applying the functor to this preimage will yield an object isomorphic to `Y`, see
    `obj_obj_preimage_iso`. -/
def Functor.objPreimage (Y : D) : C :=
  (EssSurj.mem_essImage F Y).witness
#align category_theory.functor.obj_preimage CategoryTheory.Functor.objPreimage
-/

#print CategoryTheory.Functor.objObjPreimageIso /-
/-- Applying an essentially surjective functor to a preimage of `Y` yields an object that is
    isomorphic to `Y`. -/
def Functor.objObjPreimageIso (Y : D) : F.obj (F.objPreimage Y) ≅ Y :=
  (EssSurj.mem_essImage F Y).getIso
#align category_theory.functor.obj_obj_preimage_iso CategoryTheory.Functor.objObjPreimageIso
-/

#print CategoryTheory.Faithful.toEssImage /-
/-- The induced functor of a faithful functor is faithful -/
instance Faithful.toEssImage (F : C ⥤ D) [Faithful F] : Faithful F.toEssImage :=
  Faithful.of_comp_iso F.toEssImageCompEssentialImageInclusion
#align category_theory.faithful.to_ess_image CategoryTheory.Faithful.toEssImage
-/

#print CategoryTheory.Full.toEssImage /-
/-- The induced functor of a full functor is full -/
instance Full.toEssImage (F : C ⥤ D) [Full F] : Full F.toEssImage :=
  haveI := full.of_iso F.to_ess_image_comp_essential_image_inclusion.symm
  full.of_comp_faithful F.to_ess_image F.ess_image_inclusion
#align category_theory.full.to_ess_image CategoryTheory.Full.toEssImage
-/

end CategoryTheory

