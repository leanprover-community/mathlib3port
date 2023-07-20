/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.CategoryTheory.Category.Bipointed
import Mathbin.Order.Category.PartOrd
import Mathbin.Order.Hom.Bounded

#align_import order.category.BddOrd from "leanprover-community/mathlib"@"d07a9c875ed7139abfde6a333b2be205c5bd404e"

/-!
# The category of bounded orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `BddOrd`, the category of bounded orders.
-/


universe u v

open CategoryTheory

#print BddOrdCat /-
/-- The category of bounded orders with monotone functions. -/
structure BddOrdCat where
  toPartOrd : PartOrdCat
  [isBoundedOrder : BoundedOrder to_PartOrd]
#align BddOrd BddOrdCat
-/

namespace BddOrdCat

instance : CoeSort BddOrdCat (Type _) :=
  InducedCategory.hasCoeToSort toPartOrd

instance (X : BddOrdCat) : PartialOrder X :=
  X.toPartOrd.str

attribute [instance] BddOrdCat.isBoundedOrder

#print BddOrdCat.of /-
/-- Construct a bundled `BddOrd` from a `fintype` `partial_order`. -/
def of (α : Type _) [PartialOrder α] [BoundedOrder α] : BddOrdCat :=
  ⟨⟨α⟩⟩
#align BddOrd.of BddOrdCat.of
-/

#print BddOrdCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [PartialOrder α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BddOrd.coe_of BddOrdCat.coe_of
-/

instance : Inhabited BddOrdCat :=
  ⟨of PUnit⟩

#print BddOrdCat.largeCategory /-
instance largeCategory : LargeCategory.{u} BddOrdCat
    where
  Hom X Y := BoundedOrderHom X Y
  id X := BoundedOrderHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := BoundedOrderHom.comp_id
  comp_id' X Y := BoundedOrderHom.id_comp
  assoc' W X Y Z _ _ _ := BoundedOrderHom.comp_assoc _ _ _
#align BddOrd.large_category BddOrdCat.largeCategory
-/

#print BddOrdCat.concreteCategory /-
instance concreteCategory : ConcreteCategory BddOrdCat
    where
  forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  forget_faithful := ⟨fun X Y => by convert FunLike.coe_injective⟩
#align BddOrd.concrete_category BddOrdCat.concreteCategory
-/

#print BddOrdCat.hasForgetToPartOrd /-
instance hasForgetToPartOrd : HasForget₂ BddOrdCat PartOrdCat
    where forget₂ :=
    { obj := fun X => X.toPartOrd
      map := fun X Y => BoundedOrderHom.toOrderHom }
#align BddOrd.has_forget_to_PartOrd BddOrdCat.hasForgetToPartOrd
-/

#print BddOrdCat.hasForgetToBipointed /-
instance hasForgetToBipointed : HasForget₂ BddOrdCat Bipointed
    where
  forget₂ :=
    { obj := fun X => ⟨X, ⊥, ⊤⟩
      map := fun X Y f => ⟨f, map_bot f, map_top f⟩ }
  forget_comp := rfl
#align BddOrd.has_forget_to_Bipointed BddOrdCat.hasForgetToBipointed
-/

#print BddOrdCat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : BddOrdCat ⥤ BddOrdCat where
  obj X := of Xᵒᵈ
  map X Y := BoundedOrderHom.dual
#align BddOrd.dual BddOrdCat.dual
-/

#print BddOrdCat.Iso.mk /-
/-- Constructs an equivalence between bounded orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : BddOrdCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align BddOrd.iso.mk BddOrdCat.Iso.mk
-/

#print BddOrdCat.dualEquiv /-
/-- The equivalence between `BddOrd` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BddOrdCat ≌ BddOrdCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BddOrd.dual_equiv BddOrdCat.dualEquiv
-/

end BddOrdCat

#print bddOrd_dual_comp_forget_to_partOrdCat /-
theorem bddOrd_dual_comp_forget_to_partOrdCat :
    BddOrdCat.dual ⋙ forget₂ BddOrdCat PartOrdCat =
      forget₂ BddOrdCat PartOrdCat ⋙ PartOrdCat.dual :=
  rfl
#align BddOrd_dual_comp_forget_to_PartOrd bddOrd_dual_comp_forget_to_partOrdCat
-/

#print bddOrd_dual_comp_forget_to_bipointed /-
theorem bddOrd_dual_comp_forget_to_bipointed :
    BddOrdCat.dual ⋙ forget₂ BddOrdCat Bipointed = forget₂ BddOrdCat Bipointed ⋙ Bipointed.swap :=
  rfl
#align BddOrd_dual_comp_forget_to_Bipointed bddOrd_dual_comp_forget_to_bipointed
-/

