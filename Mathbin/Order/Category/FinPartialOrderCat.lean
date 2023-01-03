/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.FinPartialOrder
! leanprover-community/mathlib commit 9830a300340708eaa85d477c3fb96dd25f9468a5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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
#align FinPartialOrder FinPartialOrderCat

namespace FinPartialOrderCat

instance : CoeSort FinPartialOrderCat (Type _) :=
  ⟨fun X => X.toPartialOrder⟩

instance (X : FinPartialOrderCat) : PartialOrder X :=
  X.toPartialOrder.str

attribute [instance] FinPartialOrderCat.isFintype

@[simp]
theorem coe_to_PartialOrder (X : FinPartialOrderCat) : ↥X.toPartialOrder = ↥X :=
  rfl
#align FinPartialOrder.coe_to_PartialOrder FinPartialOrderCat.coe_to_PartialOrder

/-- Construct a bundled `FinPartialOrder` from `fintype` + `partial_order`. -/
def of (α : Type _) [PartialOrder α] [Fintype α] : FinPartialOrderCat :=
  ⟨⟨α⟩⟩
#align FinPartialOrder.of FinPartialOrderCat.of

@[simp]
theorem coe_of (α : Type _) [PartialOrder α] [Fintype α] : ↥(of α) = α :=
  rfl
#align FinPartialOrder.coe_of FinPartialOrderCat.coe_of

instance : Inhabited FinPartialOrderCat :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinPartialOrderCat :=
  InducedCategory.category FinPartialOrderCat.toPartialOrder
#align FinPartialOrder.large_category FinPartialOrderCat.largeCategory

instance concreteCategory : ConcreteCategory FinPartialOrderCat :=
  InducedCategory.concreteCategory FinPartialOrderCat.toPartialOrder
#align FinPartialOrder.concrete_category FinPartialOrderCat.concreteCategory

instance hasForgetToPartialOrder : HasForget₂ FinPartialOrderCat PartialOrderCat :=
  InducedCategory.hasForget₂ FinPartialOrderCat.toPartialOrder
#align FinPartialOrder.has_forget_to_PartialOrder FinPartialOrderCat.hasForgetToPartialOrder

instance hasForgetToFintype : HasForget₂ FinPartialOrderCat FintypeCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => coeFn }
#align FinPartialOrder.has_forget_to_Fintype FinPartialOrderCat.hasForgetToFintype

/-- Constructs an isomorphism of finite partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : FinPartialOrderCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align FinPartialOrder.iso.mk FinPartialOrderCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : FinPartialOrderCat ⥤ FinPartialOrderCat
    where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align FinPartialOrder.dual FinPartialOrderCat.dual

/-- The equivalence between `FinPartialOrder` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : FinPartialOrderCat ≌ FinPartialOrderCat :=
  Equivalence.mk dual dual
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align FinPartialOrder.dual_equiv FinPartialOrderCat.dualEquiv

end FinPartialOrderCat

theorem FinPartialOrder_dual_comp_forget_to_PartialOrder :
    FinPartialOrderCat.dual ⋙ forget₂ FinPartialOrderCat PartialOrderCat =
      forget₂ FinPartialOrderCat PartialOrderCat ⋙ PartialOrderCat.dual :=
  rfl
#align
  FinPartialOrder_dual_comp_forget_to_PartialOrder FinPartialOrder_dual_comp_forget_to_PartialOrder

