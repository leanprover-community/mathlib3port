/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.category.GroupWithZero
! leanprover-community/mathlib commit 38df578a6450a8c5142b3727e3ae894c2300cae0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Bipointed
import Mathbin.Algebra.Category.Mon.Basic

/-!
# The category of groups with zero

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `GroupWithZero`, the category of groups with zero.
-/


universe u

open CategoryTheory Order

#print GroupWithZeroCat /-
/-- The category of groups with zero. -/
def GroupWithZeroCat :=
  Bundled GroupWithZero
#align GroupWithZero GroupWithZeroCat
-/

namespace GroupWithZeroCat

instance : CoeSort GroupWithZeroCat (Type _) :=
  Bundled.hasCoeToSort

instance (X : GroupWithZeroCat) : GroupWithZero X :=
  X.str

#print GroupWithZeroCat.of /-
/-- Construct a bundled `GroupWithZero` from a `group_with_zero`. -/
def of (α : Type _) [GroupWithZero α] : GroupWithZeroCat :=
  Bundled.of α
#align GroupWithZero.of GroupWithZeroCat.of
-/

instance : Inhabited GroupWithZeroCat :=
  ⟨of (WithZero PUnit)⟩

instance : LargeCategory.{u} GroupWithZeroCat
    where
  Hom X Y := MonoidWithZeroHom X Y
  id X := MonoidWithZeroHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := MonoidWithZeroHom.comp_id
  comp_id' X Y := MonoidWithZeroHom.id_comp
  assoc' W X Y Z _ _ _ := MonoidWithZeroHom.comp_assoc _ _ _

instance : ConcreteCategory GroupWithZeroCat
    where
  forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  forget_faithful := ⟨fun X Y f g h => FunLike.coe_injective h⟩

/- warning: GroupWithZero.has_forget_to_Bipointed -> GroupWithZeroCat.hasForgetToBipointed is a dubious translation:
lean 3 declaration is
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} GroupWithZeroCat.{u1} Bipointed.{u1} GroupWithZeroCat.CategoryTheory.largeCategory.{u1} GroupWithZeroCat.CategoryTheory.concreteCategory.{u1} Bipointed.largeCategory.{u1} Bipointed.concreteCategory.{u1}
but is expected to have type
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} GroupWithZeroCat.{u1} Bipointed.{u1} GroupWithZeroCat.instLargeCategoryGroupWithZeroCat.{u1} GroupWithZeroCat.groupWithZeroConcreteCategory.{u1} Bipointed.largeCategory.{u1} Bipointed.concreteCategory.{u1}
Case conversion may be inaccurate. Consider using '#align GroupWithZero.has_forget_to_Bipointed GroupWithZeroCat.hasForgetToBipointedₓ'. -/
instance hasForgetToBipointed : HasForget₂ GroupWithZeroCat Bipointed
    where forget₂ :=
    { obj := fun X => ⟨X, 0, 1⟩
      map := fun X Y f => ⟨f, f.map_zero', f.map_one'⟩ }
#align GroupWithZero.has_forget_to_Bipointed GroupWithZeroCat.hasForgetToBipointed

/- warning: GroupWithZero.has_forget_to_Mon -> GroupWithZeroCat.hasForgetToMon is a dubious translation:
lean 3 declaration is
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} GroupWithZeroCat.{u1} MonCat.{u1} GroupWithZeroCat.CategoryTheory.largeCategory.{u1} GroupWithZeroCat.CategoryTheory.concreteCategory.{u1} MonCat.largeCategory.{u1} MonCat.concreteCategory.{u1}
but is expected to have type
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} GroupWithZeroCat.{u1} MonCat.{u1} GroupWithZeroCat.instLargeCategoryGroupWithZeroCat.{u1} GroupWithZeroCat.groupWithZeroConcreteCategory.{u1} instMonCatLargeCategory.{u1} MonCat.concreteCategory.{u1}
Case conversion may be inaccurate. Consider using '#align GroupWithZero.has_forget_to_Mon GroupWithZeroCat.hasForgetToMonₓ'. -/
instance hasForgetToMon : HasForget₂ GroupWithZeroCat MonCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => MonoidWithZeroHom.toMonoidHom }
#align GroupWithZero.has_forget_to_Mon GroupWithZeroCat.hasForgetToMon

/- warning: GroupWithZero.iso.mk -> GroupWithZeroCat.Iso.mk is a dubious translation:
lean 3 declaration is
  forall {α : GroupWithZeroCat.{u1}} {β : GroupWithZeroCat.{u1}}, (MulEquiv.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupWithZeroCat.{u1} Type.{u1} GroupWithZeroCat.hasCoeToSort.{u1} α) (coeSort.{succ (succ u1), succ (succ u1)} GroupWithZeroCat.{u1} Type.{u1} GroupWithZeroCat.hasCoeToSort.{u1} β) (MulZeroClass.toHasMul.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupWithZeroCat.{u1} Type.{u1} GroupWithZeroCat.hasCoeToSort.{u1} α) (MulZeroOneClass.toMulZeroClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupWithZeroCat.{u1} Type.{u1} GroupWithZeroCat.hasCoeToSort.{u1} α) (MonoidWithZero.toMulZeroOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupWithZeroCat.{u1} Type.{u1} GroupWithZeroCat.hasCoeToSort.{u1} α) (GroupWithZero.toMonoidWithZero.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupWithZeroCat.{u1} Type.{u1} GroupWithZeroCat.hasCoeToSort.{u1} α) (GroupWithZeroCat.groupWithZero.{u1} α))))) (MulZeroClass.toHasMul.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupWithZeroCat.{u1} Type.{u1} GroupWithZeroCat.hasCoeToSort.{u1} β) (MulZeroOneClass.toMulZeroClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupWithZeroCat.{u1} Type.{u1} GroupWithZeroCat.hasCoeToSort.{u1} β) (MonoidWithZero.toMulZeroOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupWithZeroCat.{u1} Type.{u1} GroupWithZeroCat.hasCoeToSort.{u1} β) (GroupWithZero.toMonoidWithZero.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupWithZeroCat.{u1} Type.{u1} GroupWithZeroCat.hasCoeToSort.{u1} β) (GroupWithZeroCat.groupWithZero.{u1} β)))))) -> (CategoryTheory.Iso.{u1, succ u1} GroupWithZeroCat.{u1} GroupWithZeroCat.CategoryTheory.largeCategory.{u1} α β)
but is expected to have type
  forall {α : GroupWithZeroCat.{u1}} {β : GroupWithZeroCat.{u1}}, (MulEquiv.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} GroupWithZero.{u1} α) (CategoryTheory.Bundled.α.{u1, u1} GroupWithZero.{u1} β) (MulZeroClass.toMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} GroupWithZero.{u1} α) (MulZeroOneClass.toMulZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} GroupWithZero.{u1} α) (MonoidWithZero.toMulZeroOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} GroupWithZero.{u1} α) (GroupWithZero.toMonoidWithZero.{u1} (CategoryTheory.Bundled.α.{u1, u1} GroupWithZero.{u1} α) (GroupWithZeroCat.instGroupWithZeroα.{u1} α))))) (MulZeroClass.toMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} GroupWithZero.{u1} β) (MulZeroOneClass.toMulZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} GroupWithZero.{u1} β) (MonoidWithZero.toMulZeroOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} GroupWithZero.{u1} β) (GroupWithZero.toMonoidWithZero.{u1} (CategoryTheory.Bundled.α.{u1, u1} GroupWithZero.{u1} β) (GroupWithZeroCat.instGroupWithZeroα.{u1} β)))))) -> (CategoryTheory.Iso.{u1, succ u1} GroupWithZeroCat.{u1} GroupWithZeroCat.instLargeCategoryGroupWithZeroCat.{u1} α β)
Case conversion may be inaccurate. Consider using '#align GroupWithZero.iso.mk GroupWithZeroCat.Iso.mkₓ'. -/
/-- Constructs an isomorphism of groups with zero from a group isomorphism between them. -/
@[simps]
def Iso.mk {α β : GroupWithZeroCat.{u}} (e : α ≃* β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align GroupWithZero.iso.mk GroupWithZeroCat.Iso.mk

end GroupWithZeroCat

