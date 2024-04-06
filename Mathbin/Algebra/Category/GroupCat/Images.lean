/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Algebra.Category.GroupCat.Abelian
import CategoryTheory.Limits.Shapes.Images

#align_import algebra.category.Group.images from "leanprover-community/mathlib"@"0b7c740e25651db0ba63648fbae9f9d6f941e31b"

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

#print AddCommGroupCat.imageIsoRange /-
/-- The categorical image of a morphism in `AddCommGroup`
agrees with the usual group-theoretical range.
-/
noncomputable def imageIsoRange {G H : AddCommGroupCat.{0}} (f : G ⟶ H) :
    Limits.image f ≅ AddCommGroupCat.of f.range :=
  IsImage.isoExt (Image.isImage f) (isImage f)
#align AddCommGroup.image_iso_range AddCommGroupCat.imageIsoRange
-/

end AddCommGroupCat

