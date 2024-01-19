/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Order.Category.Lat
import Order.Hom.CompleteLattice
import Topology.Category.CompHaus.Basic
import Topology.Sets.Opens

#align_import order.category.Frm from "leanprover-community/mathlib"@"2ed2c6310e6f1c5562bdf6bfbda55ebbf6891abe"

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

#print Frm /-
/-- The category of frames. -/
def Frm :=
  Bundled Frame
#align Frm Frm
-/

namespace Frm

instance : CoeSort Frm (Type _) :=
  Bundled.hasCoeToSort

instance (X : Frm) : Frame X :=
  X.str

#print Frm.of /-
/-- Construct a bundled `Frm` from a `frame`. -/
def of (α : Type _) [Frame α] : Frm :=
  Bundled.of α
#align Frm.of Frm.of
-/

#print Frm.coe_of /-
@[simp]
theorem coe_of (α : Type _) [Frame α] : ↥(of α) = α :=
  rfl
#align Frm.coe_of Frm.coe_of
-/

instance : Inhabited Frm :=
  ⟨of PUnit⟩

#print Frm.Hom /-
/-- An abbreviation of `frame_hom` that assumes `frame` instead of the weaker `complete_lattice`.
Necessary for the category theory machinery. -/
abbrev Hom (α β : Type _) [Frame α] [Frame β] : Type _ :=
  FrameHom α β
#align Frm.hom Frm.Hom
-/

#print Frm.bundledHom /-
instance bundledHom : BundledHom Hom :=
  ⟨fun α β [Frame α] [Frame β] => (coeFn : FrameHom α β → α → β), fun α [Frame α] => FrameHom.id α,
    fun α β γ [Frame α] [Frame β] [Frame γ] => FrameHom.comp, fun α β [Frame α] [Frame β] =>
    DFunLike.coe_injective⟩
#align Frm.bundled_hom Frm.bundledHom
-/

deriving instance LargeCategory, ConcreteCategory for Frm

#print Frm.hasForgetToLat /-
instance hasForgetToLat : HasForget₂ Frm Lat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => FrameHom.toLatticeHom }
#align Frm.has_forget_to_Lat Frm.hasForgetToLat
-/

#print Frm.Iso.mk /-
/-- Constructs an isomorphism of frames from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Frm.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align Frm.iso.mk Frm.Iso.mk
-/

end Frm

#print topCatOpToFrm /-
/-- The forgetful functor from `Topᵒᵖ` to `Frm`. -/
@[simps]
def topCatOpToFrm : TopCatᵒᵖ ⥤ Frm
    where
  obj X := Frm.of (Opens (unop X : TopCat))
  map X Y f := Opens.comap <| Quiver.Hom.unop f
  map_id' X := Opens.comap_id
#align Top_op_to_Frame topCatOpToFrm
-/

#print CompHausOpToFrame.faithful /-
-- Note, `CompHaus` is too strong. We only need `t0_space`.
instance CompHausOpToFrame.faithful : Faithful (compHausToTop.op ⋙ topCatOpToFrm.{u}) :=
  ⟨fun X Y f g h => Quiver.Hom.unop_inj <| Opens.comap_injective h⟩
#align CompHaus_op_to_Frame.faithful CompHausOpToFrame.faithful
-/

