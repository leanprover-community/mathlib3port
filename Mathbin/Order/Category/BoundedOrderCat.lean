/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.BoundedOrder
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.BipointedCat
import Mathbin.Order.Category.PartialOrderCat
import Mathbin.Order.Hom.Bounded

/-!
# The category of bounded orders

This defines `BoundedOrder`, the category of bounded orders.
-/


universe u v

open CategoryTheory

/-- The category of bounded orders with monotone functions. -/
structure BoundedOrderCat where
  toPartialOrder : PartialOrderCat
  [isBoundedOrder : BoundedOrder to_PartialOrder]
#align BoundedOrder BoundedOrderCat

namespace BoundedOrderCat

instance : CoeSort BoundedOrderCat (Type _) :=
  InducedCategory.hasCoeToSort toPartialOrder

instance (X : BoundedOrderCat) : PartialOrder X :=
  X.toPartialOrder.str

attribute [instance] BoundedOrderCat.isBoundedOrder

/-- Construct a bundled `BoundedOrder` from a `fintype` `partial_order`. -/
def of (α : Type _) [PartialOrder α] [BoundedOrder α] : BoundedOrderCat :=
  ⟨⟨α⟩⟩
#align BoundedOrder.of BoundedOrderCat.of

@[simp]
theorem coe_of (α : Type _) [PartialOrder α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BoundedOrder.coe_of BoundedOrderCat.coe_of

instance : Inhabited BoundedOrderCat :=
  ⟨of PUnit⟩

instance largeCategory :
    LargeCategory.{u} BoundedOrderCat where 
  Hom X Y := BoundedOrderHom X Y
  id X := BoundedOrderHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := BoundedOrderHom.comp_id
  comp_id' X Y := BoundedOrderHom.id_comp
  assoc' W X Y Z _ _ _ := BoundedOrderHom.comp_assoc _ _ _
#align BoundedOrder.large_category BoundedOrderCat.largeCategory

instance concreteCategory :
    ConcreteCategory
      BoundedOrderCat where 
  forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  forget_faithful := ⟨fun X Y => by convert FunLike.coe_injective⟩
#align BoundedOrder.concrete_category BoundedOrderCat.concreteCategory

instance hasForgetToPartialOrder :
    HasForget₂ BoundedOrderCat
      PartialOrderCat where forget₂ :=
    { obj := fun X => X.toPartialOrder
      map := fun X Y => BoundedOrderHom.toOrderHom }
#align BoundedOrder.has_forget_to_PartialOrder BoundedOrderCat.hasForgetToPartialOrder

instance hasForgetToBipointed :
    HasForget₂ BoundedOrderCat
      BipointedCat where 
  forget₂ :=
    { obj := fun X => ⟨X, ⊥, ⊤⟩
      map := fun X Y f => ⟨f, map_bot f, map_top f⟩ }
  forget_comp := rfl
#align BoundedOrder.has_forget_to_Bipointed BoundedOrderCat.hasForgetToBipointed

/-- `order_dual` as a functor. -/
@[simps]
def dual : BoundedOrderCat ⥤ BoundedOrderCat where 
  obj X := of Xᵒᵈ
  map X Y := BoundedOrderHom.dual
#align BoundedOrder.dual BoundedOrderCat.dual

/-- Constructs an equivalence between bounded orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoundedOrderCat.{u}} (e : α ≃o β) :
    α ≅ β where 
  Hom := e
  inv := e.symm
  hom_inv_id' := by 
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by 
    ext
    exact e.apply_symm_apply _
#align BoundedOrder.iso.mk BoundedOrderCat.Iso.mk

/-- The equivalence between `BoundedOrder` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoundedOrderCat ≌ BoundedOrderCat :=
  Equivalence.mk dual dual
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BoundedOrder.dual_equiv BoundedOrderCat.dualEquiv

end BoundedOrderCat

theorem BoundedOrder_dual_comp_forget_to_PartialOrder :
    BoundedOrderCat.dual ⋙ forget₂ BoundedOrderCat PartialOrderCat =
      forget₂ BoundedOrderCat PartialOrderCat ⋙ PartialOrderCat.dual :=
  rfl
#align BoundedOrder_dual_comp_forget_to_PartialOrder BoundedOrder_dual_comp_forget_to_PartialOrder

theorem BoundedOrder_dual_comp_forget_to_Bipointed :
    BoundedOrderCat.dual ⋙ forget₂ BoundedOrderCat BipointedCat =
      forget₂ BoundedOrderCat BipointedCat ⋙ BipointedCat.swap :=
  rfl
#align BoundedOrder_dual_comp_forget_to_Bipointed BoundedOrder_dual_comp_forget_to_Bipointed

