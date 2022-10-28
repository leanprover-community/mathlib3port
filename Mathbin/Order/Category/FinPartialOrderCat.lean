/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.CategoryTheory.FintypeCat
import Mathbin.Order.Category.PartialOrderCat

/-!
# The category of finite partial orders

This defines `FinPartialOrder`, the category of finite partial orders.

Note: `FinPartialOrder` is NOT a subcategory of `BoundedOrder` because its morphisms do not
preserve `⊥` and `⊤`.

## TODO

`FinPartialOrder` is equivalent to a small category.
-/


universe u v

open CategoryTheory

/-- The category of finite partial orders with monotone functions. -/
structure FinPartialOrderCat where
  toPartialOrder : PartialOrderCat
  [isFintype : Fintype to_PartialOrder]

namespace FinPartialOrderCat

instance : CoeSort FinPartialOrderCat (Type _) :=
  ⟨fun X => X.toPartialOrder⟩

instance (X : FinPartialOrderCat) : PartialOrder X :=
  X.toPartialOrder.str

attribute [instance] FinPartialOrderCat.isFintype

@[simp]
theorem coe_to_PartialOrder (X : FinPartialOrderCat) : ↥X.toPartialOrder = ↥X :=
  rfl

/-- Construct a bundled `FinPartialOrder` from `fintype` + `partial_order`. -/
def of (α : Type _) [PartialOrder α] [Fintype α] : FinPartialOrderCat :=
  ⟨⟨α⟩⟩

@[simp]
theorem coe_of (α : Type _) [PartialOrder α] [Fintype α] : ↥(of α) = α :=
  rfl

instance : Inhabited FinPartialOrderCat :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinPartialOrderCat :=
  InducedCategory.category FinPartialOrderCat.toPartialOrder

instance concreteCategory : ConcreteCategory FinPartialOrderCat :=
  InducedCategory.concreteCategory FinPartialOrderCat.toPartialOrder

instance hasForgetToPartialOrder : HasForget₂ FinPartialOrderCat PartialOrderCat :=
  InducedCategory.hasForget₂ FinPartialOrderCat.toPartialOrder

instance hasForgetToFintype :
    HasForget₂ FinPartialOrderCat FintypeCat where forget₂ := { obj := fun X => ⟨X⟩, map := fun X Y => coeFn }

/-- Constructs an isomorphism of finite partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : FinPartialOrderCat.{u}} (e : α ≃o β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _

/-- `order_dual` as a functor. -/
@[simps]
def dual : FinPartialOrderCat ⥤ FinPartialOrderCat where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual

/-- The equivalence between `FinPartialOrder` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : FinPartialOrderCat ≌ FinPartialOrderCat :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end FinPartialOrderCat

theorem FinPartialOrder_dual_comp_forget_to_PartialOrder :
    FinPartialOrderCat.dual ⋙ forget₂ FinPartialOrderCat PartialOrderCat =
      forget₂ FinPartialOrderCat PartialOrderCat ⋙ PartialOrderCat.dual :=
  rfl

