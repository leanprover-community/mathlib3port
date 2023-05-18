/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.Frm
! leanprover-community/mathlib commit 2ed2c6310e6f1c5562bdf6bfbda55ebbf6891abe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.Lat
import Mathbin.Order.Hom.CompleteLattice
import Mathbin.Topology.Category.CompHaus.Basic
import Mathbin.Topology.Sets.Opens

/-!
# The category of frames

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `Frm`, the category of frames.

## References

* [nLab, *Frm*](https://ncatlab.org/nlab/show/Frm)
-/


universe u

open CategoryTheory Opposite Order TopologicalSpace

#print FrmCat /-
/-- The category of frames. -/
def FrmCat :=
  Bundled Frame
#align Frm FrmCat
-/

namespace FrmCat

instance : CoeSort FrmCat (Type _) :=
  Bundled.hasCoeToSort

instance (X : FrmCat) : Frame X :=
  X.str

#print FrmCat.of /-
/-- Construct a bundled `Frm` from a `frame`. -/
def of (α : Type _) [Frame α] : FrmCat :=
  Bundled.of α
#align Frm.of FrmCat.of
-/

#print FrmCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [Frame α] : ↥(of α) = α :=
  rfl
#align Frm.coe_of FrmCat.coe_of
-/

instance : Inhabited FrmCat :=
  ⟨of PUnit⟩

#print FrmCat.Hom /-
/-- An abbreviation of `frame_hom` that assumes `frame` instead of the weaker `complete_lattice`.
Necessary for the category theory machinery. -/
abbrev Hom (α β : Type _) [Frame α] [Frame β] : Type _ :=
  FrameHom α β
#align Frm.hom FrmCat.Hom
-/

#print FrmCat.bundledHom /-
instance bundledHom : BundledHom Hom :=
  ⟨fun α β [Frame α] [Frame β] => (coeFn : FrameHom α β → α → β), fun α [Frame α] => FrameHom.id α,
    fun α β γ [Frame α] [Frame β] [Frame γ] => FrameHom.comp, fun α β [Frame α] [Frame β] =>
    FunLike.coe_injective⟩
#align Frm.bundled_hom FrmCat.bundledHom
-/

deriving instance LargeCategory, ConcreteCategory for FrmCat

/- warning: Frm.has_forget_to_Lat -> FrmCat.hasForgetToLat is a dubious translation:
lean 3 declaration is
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} FrmCat.{u1} LatCat.{u1} FrmCat.largeCategory.{u1} FrmCat.concreteCategory.{u1} LatCat.CategoryTheory.largeCategory.{u1} LatCat.CategoryTheory.concreteCategory.{u1}
but is expected to have type
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} FrmCat.{u1} LatCat.{u1} instFrmCatCategory.{u1} FrmCat.instConcreteCategoryFrmCatInstFrmCatCategory.{u1} LatCat.instLargeCategoryLatCat.{u1} LatCat.instConcreteCategoryLatCatInstLargeCategoryLatCat.{u1}
Case conversion may be inaccurate. Consider using '#align Frm.has_forget_to_Lat FrmCat.hasForgetToLatₓ'. -/
instance hasForgetToLat : HasForget₂ FrmCat LatCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => FrameHom.toLatticeHom }
#align Frm.has_forget_to_Lat FrmCat.hasForgetToLat

/- warning: Frm.iso.mk -> FrmCat.Iso.mk is a dubious translation:
lean 3 declaration is
  forall {α : FrmCat.{u1}} {β : FrmCat.{u1}}, (OrderIso.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} FrmCat.{u1} Type.{u1} FrmCat.hasCoeToSort.{u1} α) (coeSort.{succ (succ u1), succ (succ u1)} FrmCat.{u1} Type.{u1} FrmCat.hasCoeToSort.{u1} β) (Preorder.toHasLe.{u1} (coeSort.{succ (succ u1), succ (succ u1)} FrmCat.{u1} Type.{u1} FrmCat.hasCoeToSort.{u1} α) (PartialOrder.toPreorder.{u1} (coeSort.{succ (succ u1), succ (succ u1)} FrmCat.{u1} Type.{u1} FrmCat.hasCoeToSort.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (coeSort.{succ (succ u1), succ (succ u1)} FrmCat.{u1} Type.{u1} FrmCat.hasCoeToSort.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (coeSort.{succ (succ u1), succ (succ u1)} FrmCat.{u1} Type.{u1} FrmCat.hasCoeToSort.{u1} α) (Order.Frame.toCompleteLattice.{u1} (coeSort.{succ (succ u1), succ (succ u1)} FrmCat.{u1} Type.{u1} FrmCat.hasCoeToSort.{u1} α) (FrmCat.Order.frame.{u1} α)))))) (Preorder.toHasLe.{u1} (coeSort.{succ (succ u1), succ (succ u1)} FrmCat.{u1} Type.{u1} FrmCat.hasCoeToSort.{u1} β) (PartialOrder.toPreorder.{u1} (coeSort.{succ (succ u1), succ (succ u1)} FrmCat.{u1} Type.{u1} FrmCat.hasCoeToSort.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (coeSort.{succ (succ u1), succ (succ u1)} FrmCat.{u1} Type.{u1} FrmCat.hasCoeToSort.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (coeSort.{succ (succ u1), succ (succ u1)} FrmCat.{u1} Type.{u1} FrmCat.hasCoeToSort.{u1} β) (Order.Frame.toCompleteLattice.{u1} (coeSort.{succ (succ u1), succ (succ u1)} FrmCat.{u1} Type.{u1} FrmCat.hasCoeToSort.{u1} β) (FrmCat.Order.frame.{u1} β))))))) -> (CategoryTheory.Iso.{u1, succ u1} FrmCat.{u1} FrmCat.largeCategory.{u1} α β)
but is expected to have type
  forall {α : FrmCat.{u1}} {β : FrmCat.{u1}}, (OrderIso.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Order.Frame.{u1} α) (CategoryTheory.Bundled.α.{u1, u1} Order.Frame.{u1} β) (Preorder.toLE.{u1} (CategoryTheory.Bundled.α.{u1, u1} Order.Frame.{u1} α) (PartialOrder.toPreorder.{u1} (CategoryTheory.Bundled.α.{u1, u1} Order.Frame.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (CategoryTheory.Bundled.α.{u1, u1} Order.Frame.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (CategoryTheory.Bundled.α.{u1, u1} Order.Frame.{u1} α) (Order.Frame.toCompleteLattice.{u1} (CategoryTheory.Bundled.α.{u1, u1} Order.Frame.{u1} α) (FrmCat.instFrameα.{u1} α)))))) (Preorder.toLE.{u1} (CategoryTheory.Bundled.α.{u1, u1} Order.Frame.{u1} β) (PartialOrder.toPreorder.{u1} (CategoryTheory.Bundled.α.{u1, u1} Order.Frame.{u1} β) (OmegaCompletePartialOrder.toPartialOrder.{u1} (CategoryTheory.Bundled.α.{u1, u1} Order.Frame.{u1} β) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (CategoryTheory.Bundled.α.{u1, u1} Order.Frame.{u1} β) (Order.Frame.toCompleteLattice.{u1} (CategoryTheory.Bundled.α.{u1, u1} Order.Frame.{u1} β) (FrmCat.instFrameα.{u1} β))))))) -> (CategoryTheory.Iso.{u1, succ u1} FrmCat.{u1} instFrmCatCategory.{u1} α β)
Case conversion may be inaccurate. Consider using '#align Frm.iso.mk FrmCat.Iso.mkₓ'. -/
/-- Constructs an isomorphism of frames from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : FrmCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align Frm.iso.mk FrmCat.Iso.mk

end FrmCat

#print topCatOpToFrameCat /-
/-- The forgetful functor from `Topᵒᵖ` to `Frm`. -/
@[simps]
def topCatOpToFrameCat : TopCatᵒᵖ ⥤ FrmCat
    where
  obj X := FrmCat.of (Opens (unop X : TopCat))
  map X Y f := Opens.comap <| Quiver.Hom.unop f
  map_id' X := Opens.comap_id
#align Top_op_to_Frame topCatOpToFrameCat
-/

#print CompHausOpToFrame.faithful /-
-- Note, `CompHaus` is too strong. We only need `t0_space`.
instance CompHausOpToFrame.faithful : Faithful (compHausToTop.op ⋙ topCatOpToFrameCat.{u}) :=
  ⟨fun X Y f g h => Quiver.Hom.unop_inj <| Opens.comap_injective h⟩
#align CompHaus_op_to_Frame.faithful CompHausOpToFrame.faithful
-/

