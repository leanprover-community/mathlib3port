/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module algebra.category.Group.abelian
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Group.ZModuleEquivalence
import Mathbin.Algebra.Category.Group.Limits
import Mathbin.Algebra.Category.Group.Colimits
import Mathbin.Algebra.Category.Module.Abelian
import Mathbin.CategoryTheory.Abelian.Basic

/-!
# The category of abelian groups is abelian

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

noncomputable section

namespace AddCommGroupCat

section

variable {X Y : AddCommGroupCat.{u}} (f : X ⟶ Y)

/- warning: AddCommGroup.normal_mono -> AddCommGroupCat.normalMono is a dubious translation:
lean 3 declaration is
  forall {X : AddCommGroupCat.{u1}} {Y : AddCommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1})) X Y), (CategoryTheory.Mono.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} X Y f) -> (CategoryTheory.NormalMono.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} X Y (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.CategoryTheory.preadditive.{u1}) f)
but is expected to have type
  forall {X : AddCommGroupCat.{u1}} {Y : AddCommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1})) X Y), (CategoryTheory.Mono.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} X Y f) -> (CategoryTheory.NormalMono.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} X Y (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) f)
Case conversion may be inaccurate. Consider using '#align AddCommGroup.normal_mono AddCommGroupCat.normalMonoₓ'. -/
/-- In the category of abelian groups, every monomorphism is normal. -/
def normalMono (hf : Mono f) : NormalMono f :=
  equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} ℤ) AddCommGroupCat.{u}).inv <|
    ModuleCat.normalMono _ inferInstance
#align AddCommGroup.normal_mono AddCommGroupCat.normalMono

/- warning: AddCommGroup.normal_epi -> AddCommGroupCat.normalEpi is a dubious translation:
lean 3 declaration is
  forall {X : AddCommGroupCat.{u1}} {Y : AddCommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1})) X Y), (CategoryTheory.Epi.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} X Y f) -> (CategoryTheory.NormalEpi.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} X Y (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.CategoryTheory.preadditive.{u1}) f)
but is expected to have type
  forall {X : AddCommGroupCat.{u1}} {Y : AddCommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1})) X Y), (CategoryTheory.Epi.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} X Y f) -> (CategoryTheory.NormalEpi.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} X Y (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) f)
Case conversion may be inaccurate. Consider using '#align AddCommGroup.normal_epi AddCommGroupCat.normalEpiₓ'. -/
/-- In the category of abelian groups, every epimorphism is normal. -/
def normalEpi (hf : Epi f) : NormalEpi f :=
  equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} ℤ) AddCommGroupCat.{u}).inv <|
    ModuleCat.normalEpi _ inferInstance
#align AddCommGroup.normal_epi AddCommGroupCat.normalEpi

end

/-- The category of abelian groups is abelian. -/
instance : Abelian AddCommGroupCat.{u}
    where
  HasFiniteProducts := ⟨by infer_instance⟩
  normalMonoOfMono X Y := normalMono
  normalEpiOfEpi X Y := normalEpi
  add_comp := by
    intros
    simp only [preadditive.add_comp]
  comp_add := by
    intros
    simp only [preadditive.comp_add]

end AddCommGroupCat

