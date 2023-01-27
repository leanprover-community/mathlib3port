/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.Lattice
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.PartialOrderCat
import Mathbin.Order.Hom.Lattice

/-!
# The category of lattices

This defines `Lattice`, the category of lattices.

Note that `Lattice` doesn't correspond to the literature definition of [`Lat`]
(https://ncatlab.org/nlab/show/Lat) as we don't require bottom or top elements. Instead, `Lat`
corresponds to `BoundedLattice` (not yet in mathlib).

## TODO

The free functor from `Lattice` to `BoundedLattice` is `X → with_top (with_bot X)`.
-/


universe u

open CategoryTheory

/-- The category of lattices. -/
def LatticeCat :=
  Bundled Lattice
#align Lattice LatticeCat

namespace LatticeCat

instance : CoeSort LatticeCat (Type _) :=
  bundled.has_coe_to_sort

instance (X : LatticeCat) : Lattice X :=
  X.str

/-- Construct a bundled `Lattice` from a `lattice`. -/
def of (α : Type _) [Lattice α] : LatticeCat :=
  Bundled.of α
#align Lattice.of LatticeCat.of

@[simp]
theorem coe_of (α : Type _) [Lattice α] : ↥(of α) = α :=
  rfl
#align Lattice.coe_of LatticeCat.coe_of

instance : Inhabited LatticeCat :=
  ⟨of Bool⟩

instance : BundledHom @LatticeHom where
  toFun _ _ _ _ := coeFn
  id := @LatticeHom.id
  comp := @LatticeHom.comp
  hom_ext X Y _ _ := FunLike.coe_injective

instance : LargeCategory.{u} LatticeCat :=
  BundledHom.category LatticeHom

instance : ConcreteCategory LatticeCat :=
  BundledHom.concreteCategory LatticeHom

instance hasForgetToPartialOrder : HasForget₂ LatticeCat PartialOrderCat
    where
  forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => f }
  forget_comp := rfl
#align Lattice.has_forget_to_PartialOrder LatticeCat.hasForgetToPartialOrder

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : LatticeCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align Lattice.iso.mk LatticeCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : LatticeCat ⥤ LatticeCat where
  obj X := of Xᵒᵈ
  map X Y := LatticeHom.dual
#align Lattice.dual LatticeCat.dual

/-- The equivalence between `Lattice` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : LatticeCat ≌ LatticeCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align Lattice.dual_equiv LatticeCat.dualEquiv

end LatticeCat

theorem latticeCat_dual_comp_forget_to_partialOrderCat :
    LatticeCat.dual ⋙ forget₂ LatticeCat PartialOrderCat =
      forget₂ LatticeCat PartialOrderCat ⋙ PartialOrderCat.dual :=
  rfl
#align Lattice_dual_comp_forget_to_PartialOrder latticeCat_dual_comp_forget_to_partialOrderCat

