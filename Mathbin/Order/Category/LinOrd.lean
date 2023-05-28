/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.category.LinOrd
! leanprover-community/mathlib commit 75be6b616681ab6ca66d798ead117e75cd64f125
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.Lat

/-!
# Category of linear orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `LinOrd`, the category of linear orders with monotone maps.
-/


open CategoryTheory

universe u

#print LinOrdCat /-
/-- The category of linear orders. -/
def LinOrdCat :=
  Bundled LinearOrder
#align LinOrd LinOrdCat
-/

namespace LinOrdCat

instance : BundledHom.ParentProjection @LinearOrder.toPartialOrder :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for LinOrdCat

instance : CoeSort LinOrdCat (Type _) :=
  Bundled.hasCoeToSort

#print LinOrdCat.of /-
/-- Construct a bundled `LinOrd` from the underlying type and typeclass. -/
def of (α : Type _) [LinearOrder α] : LinOrdCat :=
  Bundled.of α
#align LinOrd.of LinOrdCat.of
-/

#print LinOrdCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [LinearOrder α] : ↥(of α) = α :=
  rfl
#align LinOrd.coe_of LinOrdCat.coe_of
-/

instance : Inhabited LinOrdCat :=
  ⟨of PUnit⟩

instance (α : LinOrdCat) : LinearOrder α :=
  α.str

instance hasForgetToLatCat : HasForget₂ LinOrdCat LatCat
    where forget₂ :=
    { obj := fun X => LatCat.of X
      map := fun X Y f => (OrderHomClass.toLatticeHom X Y f : LatticeHom X Y) }
#align LinOrd.has_forget_to_Lat LinOrdCat.hasForgetToLatCat

/-- Constructs an equivalence between linear orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : LinOrdCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply x
  inv_hom_id' := by ext; exact e.apply_symm_apply x
#align LinOrd.iso.mk LinOrdCat.Iso.mk

#print LinOrdCat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : LinOrdCat ⥤ LinOrdCat where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align LinOrd.dual LinOrdCat.dual
-/

/-- The equivalence between `LinOrd` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : LinOrdCat ≌ LinOrdCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align LinOrd.dual_equiv LinOrdCat.dualEquiv

end LinOrdCat

theorem linOrdCat_dual_comp_forget_to_latCat :
    LinOrdCat.dual ⋙ forget₂ LinOrdCat LatCat = forget₂ LinOrdCat LatCat ⋙ LatCat.dual :=
  rfl
#align LinOrd_dual_comp_forget_to_Lat linOrdCat_dual_comp_forget_to_latCat

