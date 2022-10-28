/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.LatticeCat
import Mathbin.Order.Hom.CompleteLattice
import Mathbin.Topology.Category.CompHausCat.Default
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
def FrameCat :=
  Bundled Frame

namespace FrameCat

instance : CoeSort FrameCat (Type _) :=
  bundled.has_coe_to_sort

instance (X : FrameCat) : Frame X :=
  X.str

/-- Construct a bundled `Frame` from a `frame`. -/
def of (α : Type _) [Frame α] : FrameCat :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type _) [Frame α] : ↥(of α) = α :=
  rfl

instance : Inhabited FrameCat :=
  ⟨of PUnit⟩

/-- An abbreviation of `frame_hom` that assumes `frame` instead of the weaker `complete_lattice`.
Necessary for the category theory machinery. -/
abbrev Hom (α β : Type _) [Frame α] [Frame β] : Type _ :=
  FrameHom α β

instance bundledHom : BundledHom Hom :=
  ⟨fun α β [Frame α] [Frame β] => (coeFn : FrameHom α β → α → β), fun α [Frame α] => FrameHom.id α,
    fun α β γ [Frame α] [Frame β] [Frame γ] => FrameHom.comp, fun α β [Frame α] [Frame β] => FunLike.coe_injective⟩

deriving instance LargeCategory, ConcreteCategory for FrameCat

instance hasForgetToLattice :
    HasForget₂ FrameCat LatticeCat where forget₂ := { obj := fun X => ⟨X⟩, map := fun X Y => FrameHom.toLatticeHom }

/-- Constructs an isomorphism of frames from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : FrameCat.{u}} (e : α ≃o β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _

end FrameCat

/-- The forgetful functor from `Topᵒᵖ` to `Frame`. -/
@[simps]
def topOpToFrame : TopCatᵒᵖ ⥤ FrameCat where
  obj X := FrameCat.of (Opens (unop X : TopCat))
  map X Y f := opens.comap <| Quiver.Hom.unop f
  map_id' X := Opens.comap_id

-- Note, `CompHaus` is too strong. We only need `t0_space`.
instance CompHausOpToFrame.faithful : Faithful (compHausToTop.op ⋙ topOpToFrame.{u}) :=
  ⟨fun X Y f g h => Quiver.Hom.unop_inj <| Opens.comap_injective h⟩

