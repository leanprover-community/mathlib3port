/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.category.PartOrd
! leanprover-community/mathlib commit 75be6b616681ab6ca66d798ead117e75cd64f125
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Antisymmetrization
import Mathbin.Order.Category.Preord

/-!
# Category of partial orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `PartOrd`, the category of partial orders with monotone maps.
-/


open CategoryTheory

universe u

#print PartOrdCat /-
/-- The category of partially ordered types. -/
def PartOrdCat :=
  Bundled PartialOrder
#align PartOrd PartOrdCat
-/

namespace PartOrdCat

instance : BundledHom.ParentProjection @PartialOrder.toPreorder :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for PartOrdCat

instance : CoeSort PartOrdCat (Type _) :=
  Bundled.hasCoeToSort

#print PartOrdCat.of /-
/-- Construct a bundled PartOrd from the underlying type and typeclass. -/
def of (α : Type _) [PartialOrder α] : PartOrdCat :=
  Bundled.of α
#align PartOrd.of PartOrdCat.of
-/

#print PartOrdCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [PartialOrder α] : ↥(of α) = α :=
  rfl
#align PartOrd.coe_of PartOrdCat.coe_of
-/

instance : Inhabited PartOrdCat :=
  ⟨of PUnit⟩

instance (α : PartOrdCat) : PartialOrder α :=
  α.str

#print PartOrdCat.hasForgetToPreordCat /-
instance hasForgetToPreordCat : HasForget₂ PartOrdCat PreordCat :=
  BundledHom.forget₂ _ _
#align PartOrd.has_forget_to_Preord PartOrdCat.hasForgetToPreordCat
-/

/- warning: PartOrd.iso.mk -> PartOrdCat.Iso.mk is a dubious translation:
lean 3 declaration is
  forall {α : PartOrdCat.{u1}} {β : PartOrdCat.{u1}}, (OrderIso.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} PartOrdCat.{u1} Type.{u1} PartOrdCat.hasCoeToSort.{u1} α) (coeSort.{succ (succ u1), succ (succ u1)} PartOrdCat.{u1} Type.{u1} PartOrdCat.hasCoeToSort.{u1} β) (Preorder.toHasLe.{u1} (coeSort.{succ (succ u1), succ (succ u1)} PartOrdCat.{u1} Type.{u1} PartOrdCat.hasCoeToSort.{u1} α) (PartialOrder.toPreorder.{u1} (coeSort.{succ (succ u1), succ (succ u1)} PartOrdCat.{u1} Type.{u1} PartOrdCat.hasCoeToSort.{u1} α) (PartOrdCat.partialOrder.{u1} α))) (Preorder.toHasLe.{u1} (coeSort.{succ (succ u1), succ (succ u1)} PartOrdCat.{u1} Type.{u1} PartOrdCat.hasCoeToSort.{u1} β) (PartialOrder.toPreorder.{u1} (coeSort.{succ (succ u1), succ (succ u1)} PartOrdCat.{u1} Type.{u1} PartOrdCat.hasCoeToSort.{u1} β) (PartOrdCat.partialOrder.{u1} β)))) -> (CategoryTheory.Iso.{u1, succ u1} PartOrdCat.{u1} PartOrdCat.largeCategory.{u1} α β)
but is expected to have type
  forall {α : PartOrdCat.{u1}} {β : PartOrdCat.{u1}}, (OrderIso.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} PartialOrder.{u1} α) (CategoryTheory.Bundled.α.{u1, u1} PartialOrder.{u1} β) (Preorder.toLE.{u1} (CategoryTheory.Bundled.α.{u1, u1} PartialOrder.{u1} α) (PartialOrder.toPreorder.{u1} (CategoryTheory.Bundled.α.{u1, u1} PartialOrder.{u1} α) (PartOrdCat.instPartialOrderα.{u1} α))) (Preorder.toLE.{u1} (CategoryTheory.Bundled.α.{u1, u1} PartialOrder.{u1} β) (PartialOrder.toPreorder.{u1} (CategoryTheory.Bundled.α.{u1, u1} PartialOrder.{u1} β) (PartOrdCat.instPartialOrderα.{u1} β)))) -> (CategoryTheory.Iso.{u1, succ u1} PartOrdCat.{u1} instPartOrdCatLargeCategory.{u1} α β)
Case conversion may be inaccurate. Consider using '#align PartOrd.iso.mk PartOrdCat.Iso.mkₓ'. -/
/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : PartOrdCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply x
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply x
#align PartOrd.iso.mk PartOrdCat.Iso.mk

#print PartOrdCat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : PartOrdCat ⥤ PartOrdCat where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align PartOrd.dual PartOrdCat.dual
-/

/- warning: PartOrd.dual_equiv -> PartOrdCat.dualEquiv is a dubious translation:
lean 3 declaration is
  CategoryTheory.Equivalence.{u1, u1, succ u1, succ u1} PartOrdCat.{u1} PartOrdCat.largeCategory.{u1} PartOrdCat.{u1} PartOrdCat.largeCategory.{u1}
but is expected to have type
  CategoryTheory.Equivalence.{u1, u1, succ u1, succ u1} PartOrdCat.{u1} PartOrdCat.{u1} instPartOrdCatLargeCategory.{u1} instPartOrdCatLargeCategory.{u1}
Case conversion may be inaccurate. Consider using '#align PartOrd.dual_equiv PartOrdCat.dualEquivₓ'. -/
/-- The equivalence between `PartOrd` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : PartOrdCat ≌ PartOrdCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align PartOrd.dual_equiv PartOrdCat.dualEquiv

end PartOrdCat

#print partOrdCat_dual_comp_forget_to_preordCat /-
theorem partOrdCat_dual_comp_forget_to_preordCat :
    PartOrdCat.dual ⋙ forget₂ PartOrdCat PreordCat =
      forget₂ PartOrdCat PreordCat ⋙ PreordCat.dual :=
  rfl
#align PartOrd_dual_comp_forget_to_Preord partOrdCat_dual_comp_forget_to_preordCat
-/

#print preordCatToPartOrdCat /-
/-- `antisymmetrization` as a functor. It is the free functor. -/
def preordCatToPartOrdCat : PreordCat.{u} ⥤ PartOrdCat
    where
  obj X := PartOrdCat.of (Antisymmetrization X (· ≤ ·))
  map X Y f := f.Antisymmetrization
  map_id' X := by
    ext
    exact Quotient.inductionOn' x fun x => Quotient.map'_mk'' _ (fun a b => id) _
  map_comp' X Y Z f g := by
    ext
    exact Quotient.inductionOn' x fun x => OrderHom.antisymmetrization_apply_mk _ _
#align Preord_to_PartOrd preordCatToPartOrdCat
-/

#print preordCatToPartOrdCatForgetAdjunction /-
/-- `Preord_to_PartOrd` is left adjoint to the forgetful functor, meaning it is the free
functor from `Preord` to `PartOrd`. -/
def preordCatToPartOrdCatForgetAdjunction :
    preordCatToPartOrdCat.{u} ⊣ forget₂ PartOrdCat PreordCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f =>
            ⟨f ∘ toAntisymmetrization (· ≤ ·), f.mono.comp toAntisymmetrization_mono⟩
          invFun := fun f =>
            ⟨fun a => Quotient.liftOn' a f fun a b h => (AntisymmRel.image h f.mono).Eq, fun a b =>
              Quotient.inductionOn₂' a b fun a b h => f.mono h⟩
          left_inv := fun f =>
            OrderHom.ext _ _ <| funext fun x => Quotient.inductionOn' x fun x => rfl
          right_inv := fun f => OrderHom.ext _ _ <| funext fun x => rfl }
      homEquiv_naturality_left_symm := fun X Y Z f g =>
        OrderHom.ext _ _ <| funext fun x => Quotient.inductionOn' x fun x => rfl
      homEquiv_naturality_right := fun X Y Z f g => OrderHom.ext _ _ <| funext fun x => rfl }
#align Preord_to_PartOrd_forget_adjunction preordCatToPartOrdCatForgetAdjunction
-/

#print preordCatToPartOrdCatCompToDualIsoToDualCompPreordCatToPartOrdCat /-
/-- `Preord_to_PartOrd` and `order_dual` commute. -/
@[simps]
def preordCatToPartOrdCatCompToDualIsoToDualCompPreordCatToPartOrdCat :
    preordCatToPartOrdCat.{u} ⋙ PartOrdCat.dual ≅ PreordCat.dual ⋙ preordCatToPartOrdCat :=
  NatIso.ofComponents (fun X => PartOrdCat.Iso.mk <| OrderIso.dualAntisymmetrization _) fun X Y f =>
    OrderHom.ext _ _ <| funext fun x => Quotient.inductionOn' x fun x => rfl
#align Preord_to_PartOrd_comp_to_dual_iso_to_dual_comp_Preord_to_PartOrd preordCatToPartOrdCatCompToDualIsoToDualCompPreordCatToPartOrdCat
-/

