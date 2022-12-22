/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.category.PartialOrder
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Antisymmetrization
import Mathbin.Order.Category.PreorderCat

/-!
# Category of partial orders

This defines `PartialOrder`, the category of partial orders with monotone maps.
-/


open CategoryTheory

universe u

/-- The category of partially ordered types. -/
def PartialOrderCat :=
  Bundled PartialOrder
#align PartialOrder PartialOrderCat

namespace PartialOrderCat

instance : BundledHom.ParentProjection @PartialOrder.toPreorder :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for PartialOrderCat

instance : CoeSort PartialOrderCat (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled PartialOrder from the underlying type and typeclass. -/
def of (α : Type _) [PartialOrder α] : PartialOrderCat :=
  Bundled.of α
#align PartialOrder.of PartialOrderCat.of

@[simp]
theorem coe_of (α : Type _) [PartialOrder α] : ↥(of α) = α :=
  rfl
#align PartialOrder.coe_of PartialOrderCat.coe_of

instance : Inhabited PartialOrderCat :=
  ⟨of PUnit⟩

instance (α : PartialOrderCat) : PartialOrder α :=
  α.str

instance hasForgetToPreorder : HasForget₂ PartialOrderCat PreorderCat :=
  BundledHom.forget₂ _ _
#align PartialOrder.has_forget_to_Preorder PartialOrderCat.hasForgetToPreorder

/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : PartialOrderCat.{u}} (e : α ≃o β) :
    α ≅ β where 
  Hom := e
  inv := e.symm
  hom_inv_id' := by 
    ext
    exact e.symm_apply_apply x
  inv_hom_id' := by 
    ext
    exact e.apply_symm_apply x
#align PartialOrder.iso.mk PartialOrderCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : PartialOrderCat ⥤ PartialOrderCat where 
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align PartialOrder.dual PartialOrderCat.dual

/-- The equivalence between `PartialOrder` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : PartialOrderCat ≌ PartialOrderCat :=
  Equivalence.mk dual dual
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align PartialOrder.dual_equiv PartialOrderCat.dualEquiv

end PartialOrderCat

theorem PartialOrder_dual_comp_forget_to_Preorder :
    PartialOrderCat.dual ⋙ forget₂ PartialOrderCat PreorderCat =
      forget₂ PartialOrderCat PreorderCat ⋙ PreorderCat.dual :=
  rfl
#align PartialOrder_dual_comp_forget_to_Preorder PartialOrder_dual_comp_forget_to_Preorder

/-- `antisymmetrization` as a functor. It is the free functor. -/
def preorderToPartialOrder :
    PreorderCat.{u} ⥤
      PartialOrderCat where 
  obj X := PartialOrderCat.of (Antisymmetrization X (· ≤ ·))
  map X Y f := f.Antisymmetrization
  map_id' X := by 
    ext
    exact Quotient.inductionOn' x fun x => Quotient.map'_mk' _ (fun a b => id) _
  map_comp' X Y Z f g := by 
    ext
    exact Quotient.inductionOn' x fun x => OrderHom.antisymmetrization_apply_mk _ _
#align Preorder_to_PartialOrder preorderToPartialOrder

/-- `Preorder_to_PartialOrder` is left adjoint to the forgetful functor, meaning it is the free
functor from `Preorder` to `PartialOrder`. -/
def preorderToPartialOrderForgetAdjunction :
    preorderToPartialOrder.{u} ⊣ forget₂ PartialOrderCat PreorderCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f =>
            ⟨f ∘ toAntisymmetrization (· ≤ ·), f.mono.comp toAntisymmetrization_mono⟩
          invFun := fun f =>
            ⟨fun a => (Quotient.liftOn' a f) fun a b h => (AntisymmRel.image h f.mono).Eq,
              fun a b => (Quotient.inductionOn₂' a b) fun a b h => f.mono h⟩
          left_inv := fun f =>
            OrderHom.ext _ _ <| funext fun x => (Quotient.inductionOn' x) fun x => rfl
          right_inv := fun f => OrderHom.ext _ _ <| funext fun x => rfl }
      hom_equiv_naturality_left_symm' := fun X Y Z f g =>
        OrderHom.ext _ _ <| funext fun x => (Quotient.inductionOn' x) fun x => rfl
      hom_equiv_naturality_right' := fun X Y Z f g => OrderHom.ext _ _ <| funext fun x => rfl }
#align Preorder_to_PartialOrder_forget_adjunction preorderToPartialOrderForgetAdjunction

/-- `Preorder_to_PartialOrder` and `order_dual` commute. -/
@[simps]
def preorderToPartialOrderCompToDualIsoToDualCompPreorderToPartialOrder :
    preorderToPartialOrder.{u} ⋙ PartialOrderCat.dual ≅ PreorderCat.dual ⋙ preorderToPartialOrder :=
  (NatIso.ofComponents fun X => PartialOrderCat.Iso.mk <| OrderIso.dualAntisymmetrization _)
    fun X Y f => OrderHom.ext _ _ <| funext fun x => (Quotient.inductionOn' x) fun x => rfl
#align
  Preorder_to_PartialOrder_comp_to_dual_iso_to_dual_comp_Preorder_to_PartialOrder preorderToPartialOrderCompToDualIsoToDualCompPreorderToPartialOrder

