/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Order.Category.Lat

#align_import order.category.LinOrd from "leanprover-community/mathlib"@"75be6b616681ab6ca66d798ead117e75cd64f125"

/-!
# Category of linear orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `LinOrd`, the category of linear orders with monotone maps.
-/


open CategoryTheory

universe u

#print LinOrd /-
/-- The category of linear orders. -/
def LinOrd :=
  Bundled LinearOrder
#align LinOrd LinOrd
-/

namespace LinOrd

instance : BundledHom.ParentProjection @LinearOrder.toPartialOrder :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for LinOrd

instance : CoeSort LinOrd (Type _) :=
  Bundled.hasCoeToSort

#print LinOrd.of /-
/-- Construct a bundled `LinOrd` from the underlying type and typeclass. -/
def of (α : Type _) [LinearOrder α] : LinOrd :=
  Bundled.of α
#align LinOrd.of LinOrd.of
-/

#print LinOrd.coe_of /-
@[simp]
theorem coe_of (α : Type _) [LinearOrder α] : ↥(of α) = α :=
  rfl
#align LinOrd.coe_of LinOrd.coe_of
-/

instance : Inhabited LinOrd :=
  ⟨of PUnit⟩

instance (α : LinOrd) : LinearOrder α :=
  α.str

#print LinOrd.hasForgetToLat /-
instance hasForgetToLat : HasForget₂ LinOrd Lat
    where forget₂ :=
    { obj := fun X => Lat.of X
      map := fun X Y f => (OrderHomClass.toLatticeHom X Y f : LatticeHom X Y) }
#align LinOrd.has_forget_to_Lat LinOrd.hasForgetToLat
-/

#print LinOrd.Iso.mk /-
/-- Constructs an equivalence between linear orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : LinOrd.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply x
  inv_hom_id' := by ext; exact e.apply_symm_apply x
#align LinOrd.iso.mk LinOrd.Iso.mk
-/

#print LinOrd.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : LinOrd ⥤ LinOrd where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align LinOrd.dual LinOrd.dual
-/

#print LinOrd.dualEquiv /-
/-- The equivalence between `LinOrd` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : LinOrd ≌ LinOrd :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align LinOrd.dual_equiv LinOrd.dualEquiv
-/

end LinOrd

#print linOrd_dual_comp_forget_to_Lat /-
theorem linOrd_dual_comp_forget_to_Lat :
    LinOrd.dual ⋙ forget₂ LinOrd Lat = forget₂ LinOrd Lat ⋙ Lat.dual :=
  rfl
#align LinOrd_dual_comp_forget_to_Lat linOrd_dual_comp_forget_to_Lat
-/

