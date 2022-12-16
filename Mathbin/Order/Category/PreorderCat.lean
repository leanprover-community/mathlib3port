/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.category.Preorder
! leanprover-community/mathlib commit d012cd09a9b256d870751284dd6a29882b0be105
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.CatCat
import Mathbin.CategoryTheory.Category.Preorder
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.Order.Hom.Basic

/-!
# Category of preorders

This defines `Preorder`, the category of preorders with monotone maps.
-/


universe u

open CategoryTheory

/-- The category of preorders. -/
def PreorderCat :=
  Bundled Preorder
#align Preorder PreorderCat

namespace PreorderCat

instance : BundledHom @OrderHom where 
  toFun := @OrderHom.toFun
  id := @OrderHom.id
  comp := @OrderHom.comp
  hom_ext := @OrderHom.ext

deriving instance LargeCategory, ConcreteCategory for PreorderCat

instance : CoeSort PreorderCat (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled Preorder from the underlying type and typeclass. -/
def of (α : Type _) [Preorder α] : PreorderCat :=
  Bundled.of α
#align Preorder.of PreorderCat.of

@[simp]
theorem coe_of (α : Type _) [Preorder α] : ↥(of α) = α :=
  rfl
#align Preorder.coe_of PreorderCat.coe_of

instance : Inhabited PreorderCat :=
  ⟨of PUnit⟩

instance (α : PreorderCat) : Preorder α :=
  α.str

/-- Constructs an equivalence between preorders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : PreorderCat.{u}} (e : α ≃o β) :
    α ≅ β where 
  Hom := e
  inv := e.symm
  hom_inv_id' := by 
    ext
    exact e.symm_apply_apply x
  inv_hom_id' := by 
    ext
    exact e.apply_symm_apply x
#align Preorder.iso.mk PreorderCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : PreorderCat ⥤ PreorderCat where 
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align Preorder.dual PreorderCat.dual

/-- The equivalence between `Preorder` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : PreorderCat ≌ PreorderCat :=
  Equivalence.mk dual dual
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align Preorder.dual_equiv PreorderCat.dualEquiv

end PreorderCat

/-- The embedding of `Preorder` into `Cat`.
-/
@[simps]
def preorderToCat : PreorderCat.{u} ⥤
      Cat where 
  obj X := CatCat.of X.1
  map X Y f := f.Monotone.Functor
  map_id' X := by apply CategoryTheory.Functor.ext; tidy
  map_comp' X Y Z f g := by apply CategoryTheory.Functor.ext; tidy
#align Preorder_to_Cat preorderToCat

instance :
    Faithful
      preorderToCat.{u} where map_injective' X Y f g h := by ext x; exact functor.congr_obj h x

instance : Full preorderToCat.{u} where 
  preimage X Y f := ⟨f.obj, f.Monotone⟩
  witness' X Y f := by apply CategoryTheory.Functor.ext; tidy

