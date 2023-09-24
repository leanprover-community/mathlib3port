/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Order.Category.PartOrd
import Order.Hom.Lattice

#align_import order.category.Lat from "leanprover-community/mathlib"@"75be6b616681ab6ca66d798ead117e75cd64f125"

/-!
# The category of lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `Lat`, the category of lattices.

Note that `Lat` doesn't correspond to the literature definition of [`Lat`]
(https://ncatlab.org/nlab/show/Lat) as we don't require bottom or top elements. Instead, `Lat`
corresponds to `BddLat`.

## TODO

The free functor from `Lat` to `BddLat` is `X → with_top (with_bot X)`.
-/


universe u

open CategoryTheory

#print Lat /-
/-- The category of lattices. -/
def Lat :=
  Bundled Lattice
#align Lat Lat
-/

namespace Lat

instance : CoeSort Lat (Type _) :=
  Bundled.hasCoeToSort

instance (X : Lat) : Lattice X :=
  X.str

#print Lat.of /-
/-- Construct a bundled `Lat` from a `lattice`. -/
def of (α : Type _) [Lattice α] : Lat :=
  Bundled.of α
#align Lat.of Lat.of
-/

#print Lat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [Lattice α] : ↥(of α) = α :=
  rfl
#align Lat.coe_of Lat.coe_of
-/

instance : Inhabited Lat :=
  ⟨of Bool⟩

instance : BundledHom @LatticeHom where
  toFun _ _ _ _ := coeFn
  id := @LatticeHom.id
  comp := @LatticeHom.comp
  hom_ext X Y _ _ := FunLike.coe_injective

instance : LargeCategory.{u} Lat :=
  BundledHom.category LatticeHom

instance : ConcreteCategory Lat :=
  BundledHom.concreteCategory LatticeHom

#print Lat.hasForgetToPartOrd /-
instance hasForgetToPartOrd : HasForget₂ Lat PartOrd
    where
  forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => f }
  forget_comp := rfl
#align Lat.has_forget_to_PartOrd Lat.hasForgetToPartOrd
-/

#print Lat.Iso.mk /-
/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Lat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align Lat.iso.mk Lat.Iso.mk
-/

#print Lat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : Lat ⥤ Lat where
  obj X := of Xᵒᵈ
  map X Y := LatticeHom.dual
#align Lat.dual Lat.dual
-/

#print Lat.dualEquiv /-
/-- The equivalence between `Lat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : Lat ≌ Lat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align Lat.dual_equiv Lat.dualEquiv
-/

end Lat

#print Lat_dual_comp_forget_to_partOrd /-
theorem Lat_dual_comp_forget_to_partOrd :
    Lat.dual ⋙ forget₂ Lat PartOrd = forget₂ Lat PartOrd ⋙ PartOrd.dual :=
  rfl
#align Lat_dual_comp_forget_to_PartOrd Lat_dual_comp_forget_to_partOrd
-/

