/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Group.images
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Group.Abelian
import Mathbin.CategoryTheory.Limits.Shapes.Images

/-!
# The category of commutative additive groups has images.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `AddCommGroup` is an abelian category.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

namespace AddCommGroupCat

-- Note that because `injective_of_mono` is currently only proved in `Type 0`,
-- we restrict to the lowest universe here for now.
variable {G H : AddCommGroupCat.{0}} (f : G ⟶ H)

attribute [local ext] Subtype.ext_val

section

#print AddCommGroupCat.image /-
-- implementation details of `has_image` for AddCommGroup; use the API, not these
/-- the image of a morphism in AddCommGroup is just the bundling of `add_monoid_hom.range f` -/
def image : AddCommGroupCat :=
  AddCommGroupCat.of (AddMonoidHom.range f)
#align AddCommGroup.image AddCommGroupCat.image
-/

#print AddCommGroupCat.image.ι /-
/-- the inclusion of `image f` into the target -/
def image.ι : image f ⟶ H :=
  f.range.Subtype
#align AddCommGroup.image.ι AddCommGroupCat.image.ι
-/

instance : Mono (image.ι f) :=
  ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective

#print AddCommGroupCat.factorThruImage /-
/-- the corestriction map to the image -/
def factorThruImage : G ⟶ image f :=
  f.range_restrict
#align AddCommGroup.factor_thru_image AddCommGroupCat.factorThruImage
-/

#print AddCommGroupCat.image.fac /-
theorem image.fac : factorThruImage f ≫ image.ι f = f := by ext; rfl
#align AddCommGroup.image.fac AddCommGroupCat.image.fac
-/

attribute [local simp] image.fac

variable {f}

#print AddCommGroupCat.image.lift /-
/-- the universal property for the image factorisation -/
noncomputable def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.i
    where
  toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f → F'.i)
  map_zero' := by
    haveI := F'.m_mono
    apply injective_of_mono F'.m
    change (F'.e ≫ F'.m) _ = _
    rw [F'.fac, AddMonoidHom.map_zero]
    exact (Classical.indefiniteDescription (fun y => f y = 0) _).2
  map_add' := by
    intro x y
    haveI := F'.m_mono
    apply injective_of_mono F'.m
    rw [AddMonoidHom.map_add]
    change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
    rw [F'.fac]
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    rfl
#align AddCommGroup.image.lift AddCommGroupCat.image.lift
-/

#print AddCommGroupCat.image.lift_fac /-
theorem image.lift_fac (F' : MonoFactorisation f) : image.lift F' ≫ F'.m = image.ι f :=
  by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl
#align AddCommGroup.image.lift_fac AddCommGroupCat.image.lift_fac
-/

end

#print AddCommGroupCat.monoFactorisation /-
/-- the factorisation of any morphism in AddCommGroup through a mono. -/
def monoFactorisation : MonoFactorisation f
    where
  i := image f
  m := image.ι f
  e := factorThruImage f
#align AddCommGroup.mono_factorisation AddCommGroupCat.monoFactorisation
-/

#print AddCommGroupCat.isImage /-
/-- the factorisation of any morphism in AddCommGroup through a mono has the universal property of
the image. -/
noncomputable def isImage : IsImage (monoFactorisation f)
    where
  lift := image.lift
  lift_fac := image.lift_fac
#align AddCommGroup.is_image AddCommGroupCat.isImage
-/

/- warning: AddCommGroup.image_iso_range -> AddCommGroupCat.imageIsoRange is a dubious translation:
lean 3 declaration is
  forall {G : AddCommGroupCat.{0}} {H : AddCommGroupCat.{0}} (f : Quiver.Hom.{1, 1} AddCommGroupCat.{0} (CategoryTheory.CategoryStruct.toQuiver.{0, 1} AddCommGroupCat.{0} (CategoryTheory.Category.toCategoryStruct.{0, 1} AddCommGroupCat.{0} AddCommGroupCat.largeCategory.{0})) G H), CategoryTheory.Iso.{0, 1} AddCommGroupCat.{0} AddCommGroupCat.largeCategory.{0} (CategoryTheory.Limits.image.{0, 1} AddCommGroupCat.{0} AddCommGroupCat.largeCategory.{0} G H f (AddCommGroupCat.imageIsoRange._proof_1 G H f)) (AddCommGroupCat.of.{0} (coeSort.{1, 2} (AddSubgroup.{0} (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) H) (AddCommGroup.toAddGroup.{0} (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) H) (AddCommGroupCat.addCommGroupInstance.{0} H))) Type (SetLike.hasCoeToSort.{0, 0} (AddSubgroup.{0} (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) H) (AddCommGroup.toAddGroup.{0} (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) H) (AddCommGroupCat.addCommGroupInstance.{0} H))) (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) H) (AddSubgroup.setLike.{0} (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) H) (AddCommGroup.toAddGroup.{0} (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) H) (AddCommGroupCat.addCommGroupInstance.{0} H)))) (AddMonoidHom.range.{0, 0} (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) G) (AddCommGroup.toAddGroup.{0} (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) G) (AddCommGroupCat.addCommGroupInstance.{0} G)) (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) H) (AddCommGroup.toAddGroup.{0} (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) H) (AddCommGroupCat.addCommGroupInstance.{0} H)) f)) (AddSubgroup.toAddCommGroup.{0} (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) H) (AddCommGroupCat.addCommGroupInstance.{0} H) (AddMonoidHom.range.{0, 0} (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) G) (AddCommGroup.toAddGroup.{0} (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) G) (AddCommGroupCat.addCommGroupInstance.{0} G)) (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) H) (AddCommGroup.toAddGroup.{0} (coeSort.{2, 2} (CategoryTheory.Bundled.{0, 0} AddCommGroup.{0}) Type (CategoryTheory.Bundled.hasCoeToSort.{0, 0} AddCommGroup.{0}) H) (AddCommGroupCat.addCommGroupInstance.{0} H)) f)))
but is expected to have type
  forall {G : AddCommGroupCat.{0}} {H : AddCommGroupCat.{0}} (f : Quiver.Hom.{1, 1} AddCommGroupCat.{0} (CategoryTheory.CategoryStruct.toQuiver.{0, 1} AddCommGroupCat.{0} (CategoryTheory.Category.toCategoryStruct.{0, 1} AddCommGroupCat.{0} instAddCommGroupCatLargeCategory.{0})) G H), CategoryTheory.Iso.{0, 1} AddCommGroupCat.{0} instAddCommGroupCatLargeCategory.{0} (CategoryTheory.Limits.image.{0, 1} AddCommGroupCat.{0} instAddCommGroupCatLargeCategory.{0} G H f (CategoryTheory.Limits.HasImages.has_image.{0, 1} AddCommGroupCat.{0} instAddCommGroupCatLargeCategory.{0} (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{0, 1} AddCommGroupCat.{0} instAddCommGroupCatLargeCategory.{0} (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{0, 1} AddCommGroupCat.{0} instAddCommGroupCatLargeCategory.{0} AddCommGroupCat.instAbelianAddCommGroupCatInstAddCommGroupCatLargeCategory.{0})) G H f)) (AddCommGroupCat.of.{0} (Subtype.{1} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (fun (x : CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) => Membership.mem.{0, 0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (AddSubgroup.{0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (AddCommGroup.toAddGroup.{0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (AddCommGroupCat.addCommGroupInstance.{0} H))) (SetLike.instMembership.{0, 0} (AddSubgroup.{0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (AddCommGroup.toAddGroup.{0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (AddCommGroupCat.addCommGroupInstance.{0} H))) (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (AddSubgroup.instSetLikeAddSubgroup.{0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (AddCommGroup.toAddGroup.{0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (AddCommGroupCat.addCommGroupInstance.{0} H)))) x (AddMonoidHom.range.{0, 0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} G) (AddCommGroup.toAddGroup.{0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} G) (AddCommGroupCat.addCommGroupInstance.{0} G)) (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (AddCommGroup.toAddGroup.{0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (AddCommGroupCat.addCommGroupInstance.{0} H)) f))) (AddSubgroup.toAddCommGroup.{0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (AddCommGroupCat.addCommGroupInstance.{0} H) (AddMonoidHom.range.{0, 0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} G) (AddCommGroup.toAddGroup.{0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} G) (AddCommGroupCat.addCommGroupInstance.{0} G)) (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (AddCommGroup.toAddGroup.{0} (CategoryTheory.Bundled.α.{0, 0} AddCommGroup.{0} H) (AddCommGroupCat.addCommGroupInstance.{0} H)) f)))
Case conversion may be inaccurate. Consider using '#align AddCommGroup.image_iso_range AddCommGroupCat.imageIsoRangeₓ'. -/
/-- The categorical image of a morphism in `AddCommGroup`
agrees with the usual group-theoretical range.
-/
noncomputable def imageIsoRange {G H : AddCommGroupCat.{0}} (f : G ⟶ H) :
    Limits.image f ≅ AddCommGroupCat.of f.range :=
  IsImage.isoExt (Image.isImage f) (isImage f)
#align AddCommGroup.image_iso_range AddCommGroupCat.imageIsoRange

end AddCommGroupCat

