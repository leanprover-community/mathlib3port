/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.Lat
! leanprover-community/mathlib commit 75be6b616681ab6ca66d798ead117e75cd64f125
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.PartOrd
import Mathbin.Order.Hom.Lattice

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

#print LatCat /-
/-- The category of lattices. -/
def LatCat :=
  Bundled Lattice
#align Lat LatCat
-/

namespace LatCat

instance : CoeSort LatCat (Type _) :=
  Bundled.hasCoeToSort

instance (X : LatCat) : Lattice X :=
  X.str

#print LatCat.of /-
/-- Construct a bundled `Lat` from a `lattice`. -/
def of (α : Type _) [Lattice α] : LatCat :=
  Bundled.of α
#align Lat.of LatCat.of
-/

#print LatCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [Lattice α] : ↥(of α) = α :=
  rfl
#align Lat.coe_of LatCat.coe_of
-/

instance : Inhabited LatCat :=
  ⟨of Bool⟩

instance : BundledHom @LatticeHom where
  toFun _ _ _ _ := coeFn
  id := @LatticeHom.id
  comp := @LatticeHom.comp
  hom_ext X Y _ _ := FunLike.coe_injective

instance : LargeCategory.{u} LatCat :=
  BundledHom.category LatticeHom

instance : ConcreteCategory LatCat :=
  BundledHom.concreteCategory LatticeHom

instance hasForgetToPartOrd : HasForget₂ LatCat PartOrdCat
    where
  forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => f }
  forget_comp := rfl
#align Lat.has_forget_to_PartOrd LatCat.hasForgetToPartOrd

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : LatCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align Lat.iso.mk LatCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : LatCat ⥤ LatCat where
  obj X := of Xᵒᵈ
  map X Y := LatticeHom.dual
#align Lat.dual LatCat.dual

/-- The equivalence between `Lat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : LatCat ≌ LatCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align Lat.dual_equiv LatCat.dualEquiv

end LatCat

theorem latCat_dual_comp_forget_to_partOrdCat :
    LatCat.dual ⋙ forget₂ LatCat PartOrdCat = forget₂ LatCat PartOrdCat ⋙ PartOrdCat.dual :=
  rfl
#align Lat_dual_comp_forget_to_PartOrd latCat_dual_comp_forget_to_partOrdCat

