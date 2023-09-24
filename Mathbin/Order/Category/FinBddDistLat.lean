/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Data.Fintype.Order
import Order.Category.BddDistLat
import Order.Category.FinPartOrd

#align_import order.category.FinBddDistLat from "leanprover-community/mathlib"@"cff8231f04dfa33fd8f2f45792eebd862ef30cad"

/-!
# The category of finite bounded distributive lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `FinBddDistLat`, the category of finite distributive lattices with
bounded lattice homomorphisms.
-/


universe u

open CategoryTheory

#print FinBddDistLat /-
/-- The category of finite distributive lattices with bounded lattice morphisms. -/
structure FinBddDistLat where
  toBddDistLat : BddDistLat
  [isFintype : Fintype to_BddDistLat]
#align FinBddDistLat FinBddDistLat
-/

namespace FinBddDistLat

instance : CoeSort FinBddDistLat (Type _) :=
  ⟨fun X => X.toBddDistLat⟩

instance (X : FinBddDistLat) : DistribLattice X :=
  X.toBddDistLat.toDistLat.str

instance (X : FinBddDistLat) : BoundedOrder X :=
  X.toBddDistLat.isBoundedOrder

attribute [instance] FinBddDistLat.isFintype

#print FinBddDistLat.of /-
/-- Construct a bundled `FinBddDistLat` from a `nonempty` `bounded_order` `distrib_lattice`. -/
def of (α : Type _) [DistribLattice α] [BoundedOrder α] [Fintype α] : FinBddDistLat :=
  ⟨⟨⟨α⟩⟩⟩
#align FinBddDistLat.of FinBddDistLat.of
-/

#print FinBddDistLat.of' /-
/-- Construct a bundled `FinBddDistLat` from a `nonempty` `bounded_order` `distrib_lattice`. -/
def of' (α : Type _) [DistribLattice α] [Fintype α] [Nonempty α] : FinBddDistLat :=
  haveI := Fintype.toBoundedOrder α
  ⟨⟨⟨α⟩⟩⟩
#align FinBddDistLat.of' FinBddDistLat.of'
-/

instance : Inhabited FinBddDistLat :=
  ⟨of PUnit⟩

#print FinBddDistLat.largeCategory /-
instance largeCategory : LargeCategory FinBddDistLat :=
  InducedCategory.category toBddDistLat
#align FinBddDistLat.large_category FinBddDistLat.largeCategory
-/

#print FinBddDistLat.concreteCategory /-
instance concreteCategory : ConcreteCategory FinBddDistLat :=
  InducedCategory.concreteCategory toBddDistLat
#align FinBddDistLat.concrete_category FinBddDistLat.concreteCategory
-/

#print FinBddDistLat.hasForgetToBddDistLat /-
instance hasForgetToBddDistLat : HasForget₂ FinBddDistLat BddDistLat :=
  InducedCategory.hasForget₂ FinBddDistLat.toBddDistLat
#align FinBddDistLat.has_forget_to_BddDistLat FinBddDistLat.hasForgetToBddDistLat
-/

#print FinBddDistLat.hasForgetToFinPartOrd /-
instance hasForgetToFinPartOrd : HasForget₂ FinBddDistLat FinPartOrd
    where forget₂ :=
    { obj := fun X => FinPartOrd.of X
      map := fun X Y f => (show BoundedLatticeHom X Y from f : X →o Y) }
#align FinBddDistLat.has_forget_to_FinPartOrd FinBddDistLat.hasForgetToFinPartOrd
-/

#print FinBddDistLat.Iso.mk /-
/-- Constructs an equivalence between finite distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : FinBddDistLat.{u}} (e : α ≃o β) : α ≅ β
    where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align FinBddDistLat.iso.mk FinBddDistLat.Iso.mk
-/

example {X Y : FinBddDistLat} : (X ⟶ Y) = BoundedLatticeHom X Y :=
  rfl

#print FinBddDistLat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : FinBddDistLat ⥤ FinBddDistLat
    where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align FinBddDistLat.dual FinBddDistLat.dual
-/

#print FinBddDistLat.dualEquiv /-
/-- The equivalence between `FinBddDistLat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : FinBddDistLat ≌ FinBddDistLat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align FinBddDistLat.dual_equiv FinBddDistLat.dualEquiv
-/

end FinBddDistLat

#print finBddDistLat_dual_comp_forget_to_bddDistLat /-
theorem finBddDistLat_dual_comp_forget_to_bddDistLat :
    FinBddDistLat.dual ⋙ forget₂ FinBddDistLat BddDistLat =
      forget₂ FinBddDistLat BddDistLat ⋙ BddDistLat.dual :=
  rfl
#align FinBddDistLat_dual_comp_forget_to_BddDistLat finBddDistLat_dual_comp_forget_to_bddDistLat
-/

