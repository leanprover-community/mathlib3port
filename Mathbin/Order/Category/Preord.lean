/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.category.Preord
! leanprover-community/mathlib commit 75be6b616681ab6ca66d798ead117e75cd64f125
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Cat
import Mathbin.CategoryTheory.Category.Preorder
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.Order.Hom.Basic

/-!
# Category of preorders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `Preord`, the category of preorders with monotone maps.
-/


universe u

open CategoryTheory

#print PreordCat /-
/-- The category of preorders. -/
def PreordCat :=
  Bundled Preorder
#align Preord PreordCat
-/

namespace PreordCat

instance : BundledHom @OrderHom where
  toFun := @OrderHom.toFun
  id := @OrderHom.id
  comp := @OrderHom.comp
  hom_ext := @OrderHom.ext

deriving instance LargeCategory, ConcreteCategory for PreordCat

instance : CoeSort PreordCat (Type _) :=
  Bundled.hasCoeToSort

#print PreordCat.of /-
/-- Construct a bundled Preord from the underlying type and typeclass. -/
def of (α : Type _) [Preorder α] : PreordCat :=
  Bundled.of α
#align Preord.of PreordCat.of
-/

#print PreordCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [Preorder α] : ↥(of α) = α :=
  rfl
#align Preord.coe_of PreordCat.coe_of
-/

instance : Inhabited PreordCat :=
  ⟨of PUnit⟩

instance (α : PreordCat) : Preorder α :=
  α.str

/- warning: Preord.iso.mk -> PreordCat.Iso.mk is a dubious translation:
lean 3 declaration is
  forall {α : PreordCat.{u1}} {β : PreordCat.{u1}}, (OrderIso.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} PreordCat.{u1} Type.{u1} PreordCat.hasCoeToSort.{u1} α) (coeSort.{succ (succ u1), succ (succ u1)} PreordCat.{u1} Type.{u1} PreordCat.hasCoeToSort.{u1} β) (Preorder.toHasLe.{u1} (coeSort.{succ (succ u1), succ (succ u1)} PreordCat.{u1} Type.{u1} PreordCat.hasCoeToSort.{u1} α) (PreordCat.preorder.{u1} α)) (Preorder.toHasLe.{u1} (coeSort.{succ (succ u1), succ (succ u1)} PreordCat.{u1} Type.{u1} PreordCat.hasCoeToSort.{u1} β) (PreordCat.preorder.{u1} β))) -> (CategoryTheory.Iso.{u1, succ u1} PreordCat.{u1} PreordCat.largeCategory.{u1} α β)
but is expected to have type
  forall {α : PreordCat.{u1}} {β : PreordCat.{u1}}, (OrderIso.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Preorder.{u1} α) (CategoryTheory.Bundled.α.{u1, u1} Preorder.{u1} β) (Preorder.toLE.{u1} (CategoryTheory.Bundled.α.{u1, u1} Preorder.{u1} α) (PreordCat.instPreorderα.{u1} α)) (Preorder.toLE.{u1} (CategoryTheory.Bundled.α.{u1, u1} Preorder.{u1} β) (PreordCat.instPreorderα.{u1} β))) -> (CategoryTheory.Iso.{u1, succ u1} PreordCat.{u1} instPreordCatLargeCategory.{u1} α β)
Case conversion may be inaccurate. Consider using '#align Preord.iso.mk PreordCat.Iso.mkₓ'. -/
/-- Constructs an equivalence between preorders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : PreordCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply x
  inv_hom_id' := by ext; exact e.apply_symm_apply x
#align Preord.iso.mk PreordCat.Iso.mk

#print PreordCat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : PreordCat ⥤ PreordCat where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align Preord.dual PreordCat.dual
-/

/- warning: Preord.dual_equiv -> PreordCat.dualEquiv is a dubious translation:
lean 3 declaration is
  CategoryTheory.Equivalence.{u1, u1, succ u1, succ u1} PreordCat.{u1} PreordCat.largeCategory.{u1} PreordCat.{u1} PreordCat.largeCategory.{u1}
but is expected to have type
  CategoryTheory.Equivalence.{u1, u1, succ u1, succ u1} PreordCat.{u1} PreordCat.{u1} instPreordCatLargeCategory.{u1} instPreordCatLargeCategory.{u1}
Case conversion may be inaccurate. Consider using '#align Preord.dual_equiv PreordCat.dualEquivₓ'. -/
/-- The equivalence between `Preord` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : PreordCat ≌ PreordCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align Preord.dual_equiv PreordCat.dualEquiv

end PreordCat

#print preordCatToCat /-
/-- The embedding of `Preord` into `Cat`.
-/
@[simps]
def preordCatToCat : PreordCat.{u} ⥤ Cat
    where
  obj X := Cat.of X.1
  map X Y f := f.Monotone.Functor
  map_id' X := by apply CategoryTheory.Functor.ext; tidy
  map_comp' X Y Z f g := by apply CategoryTheory.Functor.ext; tidy
#align Preord_to_Cat preordCatToCat
-/

instance : Faithful preordCatToCat.{u}
    where map_injective' X Y f g h := by ext x; exact functor.congr_obj h x

instance : Full preordCatToCat.{u}
    where
  preimage X Y f := ⟨f.obj, f.Monotone⟩
  witness' X Y f := by apply CategoryTheory.Functor.ext; tidy

