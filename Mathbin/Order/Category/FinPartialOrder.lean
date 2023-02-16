/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.FinPartialOrder
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Fintype
import Mathbin.Order.Category.PartialOrder

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
structure FinPartialOrder where
  toPartialOrder : PartialOrderCat
  [isFintype : Fintype to_PartialOrder]
#align FinPartialOrder FinPartialOrder

namespace FinPartialOrder

instance : CoeSort FinPartialOrder (Type _) :=
  ⟨fun X => X.toPartialOrder⟩

instance (X : FinPartialOrder) : PartialOrder X :=
  X.toPartialOrder.str

attribute [instance] FinPartialOrder.isFintype

@[simp]
theorem coe_toPartialOrder (X : FinPartialOrder) : ↥X.toPartialOrder = ↥X :=
  rfl
#align FinPartialOrder.coe_to_PartialOrder FinPartialOrder.coe_toPartialOrder

/-- Construct a bundled `FinPartialOrder` from `fintype` + `partial_order`. -/
def of (α : Type _) [PartialOrder α] [Fintype α] : FinPartialOrder :=
  ⟨⟨α⟩⟩
#align FinPartialOrder.of FinPartialOrder.of

@[simp]
theorem coe_of (α : Type _) [PartialOrder α] [Fintype α] : ↥(of α) = α :=
  rfl
#align FinPartialOrder.coe_of FinPartialOrder.coe_of

instance : Inhabited FinPartialOrder :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinPartialOrder :=
  InducedCategory.category FinPartialOrder.toPartialOrder
#align FinPartialOrder.large_category FinPartialOrder.largeCategory

instance concreteCategory : ConcreteCategory FinPartialOrder :=
  InducedCategory.concreteCategory FinPartialOrder.toPartialOrder
#align FinPartialOrder.concrete_category FinPartialOrder.concreteCategory

instance hasForgetToPartialOrder : HasForget₂ FinPartialOrder PartialOrderCat :=
  InducedCategory.hasForget₂ FinPartialOrder.toPartialOrder
#align FinPartialOrder.has_forget_to_PartialOrder FinPartialOrder.hasForgetToPartialOrder

instance hasForgetToFintype : HasForget₂ FinPartialOrder FintypeCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => coeFn }
#align FinPartialOrder.has_forget_to_Fintype FinPartialOrder.hasForgetToFintype

/-- Constructs an isomorphism of finite partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : FinPartialOrder.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align FinPartialOrder.iso.mk FinPartialOrder.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : FinPartialOrder ⥤ FinPartialOrder
    where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align FinPartialOrder.dual FinPartialOrder.dual

/-- The equivalence between `FinPartialOrder` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : FinPartialOrder ≌ FinPartialOrder :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align FinPartialOrder.dual_equiv FinPartialOrder.dualEquiv

end FinPartialOrder

theorem finPartialOrder_dual_comp_forget_to_partialOrderCat :
    FinPartialOrder.dual ⋙ forget₂ FinPartialOrder PartialOrderCat =
      forget₂ FinPartialOrder PartialOrderCat ⋙ PartialOrderCat.dual :=
  rfl
#align FinPartialOrder_dual_comp_forget_to_PartialOrder finPartialOrder_dual_comp_forget_to_partialOrderCat

