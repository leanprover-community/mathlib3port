/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.BoundedDistribLattice
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.BoundedLattice
import Mathbin.Order.Category.DistribLattice

/-!
# The category of bounded distributive lattices

This defines `BoundedDistribLattice`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
structure BoundedDistribLattice where
  toDistribLattice : DistribLatticeCat
  [isBoundedOrder : BoundedOrder to_DistribLattice]
#align BoundedDistribLattice BoundedDistribLattice

namespace BoundedDistribLattice

instance : CoeSort BoundedDistribLattice (Type _) :=
  ⟨fun X => X.toDistribLattice⟩

instance (X : BoundedDistribLattice) : DistribLattice X :=
  X.toDistribLattice.str

attribute [instance] BoundedDistribLattice.isBoundedOrder

/-- Construct a bundled `BoundedDistribLattice` from a `bounded_order` `distrib_lattice`. -/
def of (α : Type _) [DistribLattice α] [BoundedOrder α] : BoundedDistribLattice :=
  ⟨⟨α⟩⟩
#align BoundedDistribLattice.of BoundedDistribLattice.of

@[simp]
theorem coe_of (α : Type _) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BoundedDistribLattice.coe_of BoundedDistribLattice.coe_of

instance : Inhabited BoundedDistribLattice :=
  ⟨of PUnit⟩

/-- Turn a `BoundedDistribLattice` into a `BoundedLattice` by forgetting it is distributive. -/
def toBoundedLattice (X : BoundedDistribLattice) : BoundedLattice :=
  BoundedLattice.of X
#align BoundedDistribLattice.to_BoundedLattice BoundedDistribLattice.toBoundedLattice

@[simp]
theorem coe_toBoundedLattice (X : BoundedDistribLattice) : ↥X.toBoundedLattice = ↥X :=
  rfl
#align BoundedDistribLattice.coe_to_BoundedLattice BoundedDistribLattice.coe_toBoundedLattice

instance : LargeCategory.{u} BoundedDistribLattice :=
  InducedCategory.category toBoundedLattice

instance : ConcreteCategory BoundedDistribLattice :=
  InducedCategory.concreteCategory toBoundedLattice

instance hasForgetToDistribLattice : HasForget₂ BoundedDistribLattice DistribLatticeCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toLatticeHom }
#align BoundedDistribLattice.has_forget_to_DistribLattice BoundedDistribLattice.hasForgetToDistribLattice

instance hasForgetToBoundedLattice : HasForget₂ BoundedDistribLattice BoundedLattice :=
  InducedCategory.hasForget₂ toBoundedLattice
#align BoundedDistribLattice.has_forget_to_BoundedLattice BoundedDistribLattice.hasForgetToBoundedLattice

theorem forget_boundedLattice_latticeCat_eq_forget_distribLatticeCat_latticeCat :
    forget₂ BoundedDistribLattice BoundedLattice ⋙ forget₂ BoundedLattice LatticeCat =
      forget₂ BoundedDistribLattice DistribLatticeCat ⋙ forget₂ DistribLatticeCat LatticeCat :=
  rfl
#align BoundedDistribLattice.forget_BoundedLattice_Lattice_eq_forget_DistribLattice_Lattice BoundedDistribLattice.forget_boundedLattice_latticeCat_eq_forget_distribLatticeCat_latticeCat

/-- Constructs an equivalence between bounded distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BoundedDistribLattice.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align BoundedDistribLattice.iso.mk BoundedDistribLattice.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : BoundedDistribLattice ⥤ BoundedDistribLattice
    where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align BoundedDistribLattice.dual BoundedDistribLattice.dual

/-- The equivalence between `BoundedDistribLattice` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoundedDistribLattice ≌ BoundedDistribLattice :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BoundedDistribLattice.dual_equiv BoundedDistribLattice.dualEquiv

end BoundedDistribLattice

theorem boundedDistribLattice_dual_comp_forget_to_distribLatticeCat :
    BoundedDistribLattice.dual ⋙ forget₂ BoundedDistribLattice DistribLatticeCat =
      forget₂ BoundedDistribLattice DistribLatticeCat ⋙ DistribLatticeCat.dual :=
  rfl
#align BoundedDistribLattice_dual_comp_forget_to_DistribLattice boundedDistribLattice_dual_comp_forget_to_distribLatticeCat

