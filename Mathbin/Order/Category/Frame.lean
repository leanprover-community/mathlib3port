/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.Frame
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.Lattice
import Mathbin.Order.Hom.CompleteLattice
import Mathbin.Topology.Category.CompHaus.Basic
import Mathbin.Topology.Sets.Opens

/-!
# The category of frames

This file defines `Frame`, the category of frames.

## References

* [nLab, *Frm*](https://ncatlab.org/nlab/show/Frm)
-/


universe u

open CategoryTheory Opposite Order TopologicalSpace

/-- The category of frames. -/
def Frame :=
  Bundled Frame
#align Frame Frame

namespace Frame

instance : CoeSort Frame (Type _) :=
  Bundled.hasCoeToSort

instance (X : Frame) : Frame X :=
  X.str

/-- Construct a bundled `Frame` from a `frame`. -/
def of (α : Type _) [Frame α] : Frame :=
  Bundled.of α
#align Frame.of Frame.of

@[simp]
theorem coe_of (α : Type _) [Frame α] : ↥(of α) = α :=
  rfl
#align Frame.coe_of Frame.coe_of

instance : Inhabited Frame :=
  ⟨of PUnit⟩

/-- An abbreviation of `frame_hom` that assumes `frame` instead of the weaker `complete_lattice`.
Necessary for the category theory machinery. -/
abbrev Hom (α β : Type _) [Frame α] [Frame β] : Type _ :=
  FrameHom α β
#align Frame.hom Frame.Hom

instance bundledHom : BundledHom Hom :=
  ⟨fun α β [Frame α] [Frame β] => (coeFn : FrameHom α β → α → β), fun α [Frame α] => FrameHom.id α,
    fun α β γ [Frame α] [Frame β] [Frame γ] => FrameHom.comp, fun α β [Frame α] [Frame β] =>
    FunLike.coe_injective⟩
#align Frame.bundled_hom Frame.bundledHom

deriving instance LargeCategory, ConcreteCategory for Frame

instance hasForgetToLattice : HasForget₂ Frame LatticeCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => FrameHom.toLatticeHom }
#align Frame.has_forget_to_Lattice Frame.hasForgetToLattice

/-- Constructs an isomorphism of frames from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Frame.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align Frame.iso.mk Frame.Iso.mk

end Frame

/-- The forgetful functor from `Topᵒᵖ` to `Frame`. -/
@[simps]
def topOpToFrame : TopCatᵒᵖ ⥤ Frame
    where
  obj X := Frame.of (Opens (unop X : TopCat))
  map X Y f := Opens.comap <| Quiver.Hom.unop f
  map_id' X := Opens.comap_id
#align Top_op_to_Frame topOpToFrame

-- Note, `CompHaus` is too strong. We only need `t0_space`.
instance CompHausOpToFrame.faithful : Faithful (compHausToTop.op ⋙ topOpToFrame.{u}) :=
  ⟨fun X Y f g h => Quiver.Hom.unop_inj <| Opens.comap_injective h⟩
#align CompHaus_op_to_Frame.faithful CompHausOpToFrame.faithful

