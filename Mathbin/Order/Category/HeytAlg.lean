/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Order.Category.BddDistLat
import Order.Heyting.Hom

#align_import order.category.HeytAlg from "leanprover-community/mathlib"@"8af7091a43227e179939ba132e54e54e9f3b089a"

/-!
# The category of Heyting algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `HeytAlg`, the category of Heyting algebras.
-/


universe u

open CategoryTheory Opposite Order

#print HeytAlg /-
/-- The category of Heyting algebras. -/
def HeytAlg :=
  Bundled HeytingAlgebra
#align HeytAlg HeytAlg
-/

namespace HeytAlg

instance : CoeSort HeytAlg (Type _) :=
  Bundled.hasCoeToSort

instance (X : HeytAlg) : HeytingAlgebra X :=
  X.str

#print HeytAlg.of /-
/-- Construct a bundled `HeytAlg` from a `heyting_algebra`. -/
def of (α : Type _) [HeytingAlgebra α] : HeytAlg :=
  Bundled.of α
#align HeytAlg.of HeytAlg.of
-/

#print HeytAlg.coe_of /-
@[simp]
theorem coe_of (α : Type _) [HeytingAlgebra α] : ↥(of α) = α :=
  rfl
#align HeytAlg.coe_of HeytAlg.coe_of
-/

instance : Inhabited HeytAlg :=
  ⟨of PUnit⟩

#print HeytAlg.bundledHom /-
instance bundledHom : BundledHom HeytingHom
    where
  toFun α β [HeytingAlgebra α] [HeytingAlgebra β] := (coeFn : HeytingHom α β → α → β)
  id := HeytingHom.id
  comp := @HeytingHom.comp
  hom_ext α β [HeytingAlgebra α] [HeytingAlgebra β] := FunLike.coe_injective
#align HeytAlg.bundled_hom HeytAlg.bundledHom
-/

deriving instance LargeCategory, ConcreteCategory for HeytAlg

#print HeytAlg.hasForgetToLat /-
@[simps]
instance hasForgetToLat : HasForget₂ HeytAlg BddDistLat
    where forget₂ :=
    { obj := fun X => BddDistLat.of X
      map := fun X Y f => (f : BoundedLatticeHom X Y) }
#align HeytAlg.has_forget_to_Lat HeytAlg.hasForgetToLat
-/

#print HeytAlg.Iso.mk /-
/-- Constructs an isomorphism of Heyting algebras from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : HeytAlg.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align HeytAlg.iso.mk HeytAlg.Iso.mk
-/

end HeytAlg

