/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import CategoryTheory.Category.Bipointed
import Algebra.Category.MonCat.Basic

#align_import algebra.category.GroupWithZero from "leanprover-community/mathlib"@"38df578a6450a8c5142b3727e3ae894c2300cae0"

/-!
# The category of groups with zero

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `GroupWithZero`, the category of groups with zero.
-/


universe u

open CategoryTheory Order

#print GrpWithZero /-
/-- The category of groups with zero. -/
def GrpWithZero :=
  Bundled GroupWithZero
#align GroupWithZero GrpWithZero
-/

namespace GrpWithZero

instance : CoeSort GrpWithZero (Type _) :=
  Bundled.hasCoeToSort

instance (X : GrpWithZero) : GroupWithZero X :=
  X.str

#print GrpWithZero.of /-
/-- Construct a bundled `GroupWithZero` from a `group_with_zero`. -/
def of (α : Type _) [GroupWithZero α] : GrpWithZero :=
  Bundled.of α
#align GroupWithZero.of GrpWithZero.of
-/

instance : Inhabited GrpWithZero :=
  ⟨of (WithZero PUnit)⟩

instance : LargeCategory.{u} GrpWithZero
    where
  Hom X Y := MonoidWithZeroHom X Y
  id X := MonoidWithZeroHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := MonoidWithZeroHom.comp_id
  comp_id' X Y := MonoidWithZeroHom.id_comp
  assoc' W X Y Z _ _ _ := MonoidWithZeroHom.comp_assoc _ _ _

instance : ConcreteCategory GrpWithZero
    where
  forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  forget_faithful := ⟨fun X Y f g h => DFunLike.coe_injective h⟩

#print GrpWithZero.hasForgetToBipointed /-
instance hasForgetToBipointed : HasForget₂ GrpWithZero Bipointed
    where forget₂ :=
    { obj := fun X => ⟨X, 0, 1⟩
      map := fun X Y f => ⟨f, f.map_zero', f.map_one'⟩ }
#align GroupWithZero.has_forget_to_Bipointed GrpWithZero.hasForgetToBipointed
-/

#print GrpWithZero.hasForgetToMon /-
instance hasForgetToMon : HasForget₂ GrpWithZero MonCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => MonoidWithZeroHom.toMonoidHom }
#align GroupWithZero.has_forget_to_Mon GrpWithZero.hasForgetToMon
-/

#print GrpWithZero.Iso.mk /-
/-- Constructs an isomorphism of groups with zero from a group isomorphism between them. -/
@[simps]
def Iso.mk {α β : GrpWithZero.{u}} (e : α ≃* β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align GroupWithZero.iso.mk GrpWithZero.Iso.mk
-/

end GrpWithZero

