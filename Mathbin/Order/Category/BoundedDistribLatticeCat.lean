/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.BoundedLatticeCat
import Mathbin.Order.Category.DistribLatticeCat

/-!
# The category of bounded distributive lattices

This defines `BoundedDistribLattice`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
structure BoundedDistribLatticeCat where
  toDistribLattice : DistribLatticeCat
  [isBoundedOrder : BoundedOrder to_DistribLattice]

namespace BoundedDistribLatticeCat

instance : CoeSort BoundedDistribLatticeCat (Type _) :=
  ⟨fun X => X.toDistribLattice⟩

instance (X : BoundedDistribLatticeCat) : DistribLattice X :=
  X.toDistribLattice.str

attribute [instance] BoundedDistribLatticeCat.isBoundedOrder

/-- Construct a bundled `BoundedDistribLattice` from a `bounded_order` `distrib_lattice`. -/
def of (α : Type _) [DistribLattice α] [BoundedOrder α] : BoundedDistribLatticeCat :=
  ⟨⟨α⟩⟩

@[simp]
theorem coe_of (α : Type _) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl

instance : Inhabited BoundedDistribLatticeCat :=
  ⟨of PUnit⟩

/-- Turn a `BoundedDistribLattice` into a `BoundedLattice` by forgetting it is distributive. -/
def toBoundedLattice (X : BoundedDistribLatticeCat) : BoundedLatticeCat :=
  BoundedLatticeCat.of X

@[simp]
theorem coe_to_BoundedLattice (X : BoundedDistribLatticeCat) : ↥X.toBoundedLattice = ↥X :=
  rfl

instance : LargeCategory.{u} BoundedDistribLatticeCat :=
  InducedCategory.category toBoundedLattice

instance : ConcreteCategory BoundedDistribLatticeCat :=
  InducedCategory.concreteCategory toBoundedLattice

instance hasForgetToDistribLattice :
    HasForget₂ BoundedDistribLatticeCat
      DistribLatticeCat where forget₂ := { obj := fun X => ⟨X⟩, map := fun X Y => BoundedLatticeHom.toLatticeHom }

instance hasForgetToBoundedLattice : HasForget₂ BoundedDistribLatticeCat BoundedLatticeCat :=
  InducedCategory.hasForget₂ toBoundedLattice

theorem forget_BoundedLattice_Lattice_eq_forget_DistribLattice_Lattice :
    forget₂ BoundedDistribLatticeCat BoundedLatticeCat ⋙ forget₂ BoundedLatticeCat LatticeCat =
      forget₂ BoundedDistribLatticeCat DistribLatticeCat ⋙ forget₂ DistribLatticeCat LatticeCat :=
  rfl

/-- Constructs an equivalence between bounded distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BoundedDistribLatticeCat.{u}} (e : α ≃o β) : α ≅ β where
  Hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _

/-- `order_dual` as a functor. -/
@[simps]
def dual : BoundedDistribLatticeCat ⥤ BoundedDistribLatticeCat where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual

/-- The equivalence between `BoundedDistribLattice` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoundedDistribLatticeCat ≌ BoundedDistribLatticeCat :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end BoundedDistribLatticeCat

theorem BoundedDistribLattice_dual_comp_forget_to_DistribLattice :
    BoundedDistribLatticeCat.dual ⋙ forget₂ BoundedDistribLatticeCat DistribLatticeCat =
      forget₂ BoundedDistribLatticeCat DistribLatticeCat ⋙ DistribLatticeCat.dual :=
  rfl

