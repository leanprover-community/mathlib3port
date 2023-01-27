/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.essential_image
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.NaturalIsomorphism
import Mathbin.CategoryTheory.FullSubcategory

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

/- warning: category_theory.functor.ess_image.get_iso -> CategoryTheory.Functor.essImage.getIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {Y : D} (h : Membership.Mem.{u4, u4} D (Set.{u4} D) (Set.hasMem.{u4} D) Y (CategoryTheory.Functor.essImage.{u1, u2, u3, u4} C D _inst_1 _inst_2 F)), CategoryTheory.Iso.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F (CategoryTheory.Functor.essImage.witness.{u1, u2, u3, u4} C D _inst_1 _inst_2 F Y h)) Y
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {Y : D} (h : Membership.mem.{u4, u4} D (Set.{u4} D) (Set.instMembershipSet.{u4} D) Y (CategoryTheory.Functor.essImage.{u1, u2, u3, u4} C D _inst_1 _inst_2 F)), CategoryTheory.Iso.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) (CategoryTheory.Functor.essImage.witness.{u1, u2, u3, u4} C D _inst_1 _inst_2 F Y h)) Y
Case conversion may be inaccurate. Consider using '#align category_theory.functor.ess_image.get_iso CategoryTheory.Functor.essImage.getIsoₓ'. -/
/-- Extract the isomorphism between `F.obj h.witness` and `Y` itself. -/
def essImage.getIso {Y : D} (h : Y ∈ F.essImage) : F.obj h.witness ≅ Y :=
  Classical.choice h.some_spec
#align category_theory.functor.ess_image.get_iso CategoryTheory.Functor.essImage.getIso

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

/- warning: category_theory.functor.obj_mem_ess_image -> CategoryTheory.Functor.obj_mem_essImage is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1) (Y : D), Membership.Mem.{u3, u3} C (Set.{u3} C) (Set.hasMem.{u3} C) (CategoryTheory.Functor.obj.{u2, u1, u4, u3} D _inst_2 C _inst_1 F Y) (CategoryTheory.Functor.essImage.{u2, u1, u4, u3} D C _inst_2 _inst_1 F)
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1) (Y : D), Membership.mem.{u3, u3} C (Set.{u3} C) (Set.instMembershipSet.{u3} C) (Prefunctor.obj.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 F) Y) (CategoryTheory.Functor.essImage.{u2, u1, u4, u3} D C _inst_2 _inst_1 F)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.obj_mem_ess_image CategoryTheory.Functor.obj_mem_essImageₓ'. -/
/-- An object in the image is in the essential image. -/
theorem obj_mem_essImage (F : D ⥤ C) (Y : D) : F.obj Y ∈ essImage F :=
  ⟨Y, ⟨Iso.refl _⟩⟩
#align category_theory.functor.obj_mem_ess_image CategoryTheory.Functor.obj_mem_essImage

#print CategoryTheory.Functor.EssImageSubcategory /-
/-- The essential image of a functor, interpreted of a full subcategory of the target category. -/
@[nolint has_nonempty_instance]
def EssImageSubcategory (F : C ⥤ D) :=
  FullSubcategory F.essImage deriving Category
#align category_theory.functor.ess_image_subcategory CategoryTheory.Functor.EssImageSubcategory
-/

#print CategoryTheory.Functor.essImageInclusion /-
/-- The essential image as a subcategory has a fully faithful inclusion into the target category. -/
@[simps]
def essImageInclusion (F : C ⥤ D) : F.EssImageSubcategory ⥤ D :=
  fullSubcategoryInclusion _ deriving Full, Faithful
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
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`mem_ess_image] [] -/
/-- A functor `F : C ⥤ D` is essentially surjective if every object of `D` is in the essential image
of `F`. In other words, for every `Y : D`, there is some `X : C` with `F.obj X ≅ Y`.

See <https://stacks.math.columbia.edu/tag/001C>.
-/
class EssSurj (F : C ⥤ D) : Prop where
  mem_ess_image (Y : D) : Y ∈ F.essImage
#align category_theory.ess_surj CategoryTheory.EssSurj
-/

instance : EssSurj F.toEssImage
    where mem_ess_image := fun ⟨Y, hY⟩ => ⟨_, ⟨⟨_, _, hY.getIso.hom_inv_id, hY.getIso.inv_hom_id⟩⟩⟩

variable (F) [EssSurj F]

#print CategoryTheory.Functor.objPreimage /-
/-- Given an essentially surjective functor, we can find a preimage for every object `Y` in the
    codomain. Applying the functor to this preimage will yield an object isomorphic to `Y`, see
    `obj_obj_preimage_iso`. -/
def Functor.objPreimage (Y : D) : C :=
  (EssSurj.mem_essImage F Y).witness
#align category_theory.functor.obj_preimage CategoryTheory.Functor.objPreimage
-/

/- warning: category_theory.functor.obj_obj_preimage_iso -> CategoryTheory.Functor.objObjPreimageIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.EssSurj.{u1, u2, u3, u4} C D _inst_1 _inst_2 F] (Y : D), CategoryTheory.Iso.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F (CategoryTheory.Functor.objPreimage.{u1, u2, u3, u4} C D _inst_1 _inst_2 F _inst_3 Y)) Y
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.EssSurj.{u1, u2, u3, u4} C D _inst_1 _inst_2 F] (Y : D), CategoryTheory.Iso.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) (CategoryTheory.Functor.objPreimage.{u1, u2, u3, u4} C D _inst_1 _inst_2 F _inst_3 Y)) Y
Case conversion may be inaccurate. Consider using '#align category_theory.functor.obj_obj_preimage_iso CategoryTheory.Functor.objObjPreimageIsoₓ'. -/
/-- Applying an essentially surjective functor to a preimage of `Y` yields an object that is
    isomorphic to `Y`. -/
def Functor.objObjPreimageIso (Y : D) : F.obj (F.objPreimage Y) ≅ Y :=
  (EssSurj.mem_essImage F Y).getIso
#align category_theory.functor.obj_obj_preimage_iso CategoryTheory.Functor.objObjPreimageIso

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

