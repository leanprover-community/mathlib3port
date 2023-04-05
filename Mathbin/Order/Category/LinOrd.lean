/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.category.LinOrd
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.Lat

/-!
# Category of linear orders

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

/- warning: LinOrd.has_forget_to_Lat -> LinOrdCat.hasForgetToLatCat is a dubious translation:
lean 3 declaration is
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} LinOrdCat.{u1} LatCat.{u1} LinOrdCat.largeCategory.{u1} LinOrdCat.concreteCategory.{u1} LatCat.CategoryTheory.largeCategory.{u1} LatCat.CategoryTheory.concreteCategory.{u1}
but is expected to have type
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} LinOrdCat.{u1} LatCat.{u1} instLinOrdCatLargeCategory.{u1} LinOrdCat.instConcreteCategoryLinOrdCatInstLinOrdCatLargeCategory.{u1} LatCat.instLargeCategoryLatCat.{u1} LatCat.instConcreteCategoryLatCatInstLargeCategoryLatCat.{u1}
Case conversion may be inaccurate. Consider using '#align LinOrd.has_forget_to_Lat LinOrdCat.hasForgetToLatCatₓ'. -/
instance hasForgetToLatCat : HasForget₂ LinOrdCat LatCat
    where forget₂ :=
    { obj := fun X => LatCat.of X
      map := fun X Y f => (OrderHomClass.toLatticeHom X Y f : LatticeHom X Y) }
#align LinOrd.has_forget_to_Lat LinOrdCat.hasForgetToLatCat

#print LinOrdCat.Iso.mk /-
/-- Constructs an equivalence between linear orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : LinOrdCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply x
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply x
#align LinOrd.iso.mk LinOrdCat.Iso.mk
-/

#print LinOrdCat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : LinOrdCat ⥤ LinOrdCat where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align LinOrd.dual LinOrdCat.dual
-/

/- warning: LinOrd.dual_equiv -> LinOrdCat.dualEquiv is a dubious translation:
lean 3 declaration is
  CategoryTheory.Equivalence.{u1, u1, succ u1, succ u1} LinOrdCat.{u1} LinOrdCat.largeCategory.{u1} LinOrdCat.{u1} LinOrdCat.largeCategory.{u1}
but is expected to have type
  CategoryTheory.Equivalence.{u1, u1, succ u1, succ u1} LinOrdCat.{u1} LinOrdCat.{u1} instLinOrdCatLargeCategory.{u1} instLinOrdCatLargeCategory.{u1}
Case conversion may be inaccurate. Consider using '#align LinOrd.dual_equiv LinOrdCat.dualEquivₓ'. -/
/-- The equivalence between `LinOrd` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : LinOrdCat ≌ LinOrdCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align LinOrd.dual_equiv LinOrdCat.dualEquiv

end LinOrdCat

/- warning: LinOrd_dual_comp_forget_to_Lat -> linOrdCat_dual_comp_forget_to_latCat is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} LinOrdCat.{u1} LinOrdCat.largeCategory.{u1} LatCat.{u1} LatCat.CategoryTheory.largeCategory.{u1}) (CategoryTheory.Functor.comp.{u1, u1, u1, succ u1, succ u1, succ u1} LinOrdCat.{u1} LinOrdCat.largeCategory.{u1} LinOrdCat.{u1} LinOrdCat.largeCategory.{u1} LatCat.{u1} LatCat.CategoryTheory.largeCategory.{u1} LinOrdCat.dual.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} LinOrdCat.{u1} LatCat.{u1} LinOrdCat.largeCategory.{u1} LinOrdCat.concreteCategory.{u1} LatCat.CategoryTheory.largeCategory.{u1} LatCat.CategoryTheory.concreteCategory.{u1} LinOrdCat.hasForgetToLatCat.{u1})) (CategoryTheory.Functor.comp.{u1, u1, u1, succ u1, succ u1, succ u1} LinOrdCat.{u1} LinOrdCat.largeCategory.{u1} LatCat.{u1} LatCat.CategoryTheory.largeCategory.{u1} LatCat.{u1} LatCat.CategoryTheory.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} LinOrdCat.{u1} LatCat.{u1} LinOrdCat.largeCategory.{u1} LinOrdCat.concreteCategory.{u1} LatCat.CategoryTheory.largeCategory.{u1} LatCat.CategoryTheory.concreteCategory.{u1} LinOrdCat.hasForgetToLatCat.{u1}) LatCat.dual.{u1})
but is expected to have type
  Eq.{succ (succ u1)} (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} LinOrdCat.{u1} instLinOrdCatLargeCategory.{u1} LatCat.{u1} LatCat.instLargeCategoryLatCat.{u1}) (CategoryTheory.Functor.comp.{u1, u1, u1, succ u1, succ u1, succ u1} LinOrdCat.{u1} instLinOrdCatLargeCategory.{u1} LinOrdCat.{u1} instLinOrdCatLargeCategory.{u1} LatCat.{u1} LatCat.instLargeCategoryLatCat.{u1} LinOrdCat.dual.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} LinOrdCat.{u1} LatCat.{u1} instLinOrdCatLargeCategory.{u1} LinOrdCat.instConcreteCategoryLinOrdCatInstLinOrdCatLargeCategory.{u1} LatCat.instLargeCategoryLatCat.{u1} LatCat.instConcreteCategoryLatCatInstLargeCategoryLatCat.{u1} LinOrdCat.hasForgetToLatCat.{u1})) (CategoryTheory.Functor.comp.{u1, u1, u1, succ u1, succ u1, succ u1} LinOrdCat.{u1} instLinOrdCatLargeCategory.{u1} LatCat.{u1} LatCat.instLargeCategoryLatCat.{u1} LatCat.{u1} LatCat.instLargeCategoryLatCat.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} LinOrdCat.{u1} LatCat.{u1} instLinOrdCatLargeCategory.{u1} LinOrdCat.instConcreteCategoryLinOrdCatInstLinOrdCatLargeCategory.{u1} LatCat.instLargeCategoryLatCat.{u1} LatCat.instConcreteCategoryLatCatInstLargeCategoryLatCat.{u1} LinOrdCat.hasForgetToLatCat.{u1}) LatCat.dual.{u1})
Case conversion may be inaccurate. Consider using '#align LinOrd_dual_comp_forget_to_Lat linOrdCat_dual_comp_forget_to_latCatₓ'. -/
theorem linOrdCat_dual_comp_forget_to_latCat :
    LinOrdCat.dual ⋙ forget₂ LinOrdCat LatCat = forget₂ LinOrdCat LatCat ⋙ LatCat.dual :=
  rfl
#align LinOrd_dual_comp_forget_to_Lat linOrdCat_dual_comp_forget_to_latCat

