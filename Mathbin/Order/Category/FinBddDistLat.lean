/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.FinBddDistLat
! leanprover-community/mathlib commit cff8231f04dfa33fd8f2f45792eebd862ef30cad
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Order
import Mathbin.Order.Category.BddDistLat
import Mathbin.Order.Category.FinPartOrd

/-!
# The category of finite bounded distributive lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `FinBddDistLat`, the category of finite distributive lattices with
bounded lattice homomorphisms.
-/


universe u

open CategoryTheory

#print FinBddDistLatCat /-
/-- The category of finite distributive lattices with bounded lattice morphisms. -/
structure FinBddDistLatCat where
  toBddDistLat : BddDistLatCat
  [isFintype : Fintype to_BddDistLat]
#align FinBddDistLat FinBddDistLatCat
-/

namespace FinBddDistLatCat

instance : CoeSort FinBddDistLatCat (Type _) :=
  ⟨fun X => X.toBddDistLat⟩

instance (X : FinBddDistLatCat) : DistribLattice X :=
  X.toBddDistLat.toDistLat.str

instance (X : FinBddDistLatCat) : BoundedOrder X :=
  X.toBddDistLat.isBoundedOrder

attribute [instance] FinBddDistLatCat.isFintype

#print FinBddDistLatCat.of /-
/-- Construct a bundled `FinBddDistLat` from a `nonempty` `bounded_order` `distrib_lattice`. -/
def of (α : Type _) [DistribLattice α] [BoundedOrder α] [Fintype α] : FinBddDistLatCat :=
  ⟨⟨⟨α⟩⟩⟩
#align FinBddDistLat.of FinBddDistLatCat.of
-/

#print FinBddDistLatCat.of' /-
/-- Construct a bundled `FinBddDistLat` from a `nonempty` `bounded_order` `distrib_lattice`. -/
def of' (α : Type _) [DistribLattice α] [Fintype α] [Nonempty α] : FinBddDistLatCat :=
  haveI := Fintype.toBoundedOrder α
  ⟨⟨⟨α⟩⟩⟩
#align FinBddDistLat.of' FinBddDistLatCat.of'
-/

instance : Inhabited FinBddDistLatCat :=
  ⟨of PUnit⟩

#print FinBddDistLatCat.largeCategory /-
instance largeCategory : LargeCategory FinBddDistLatCat :=
  InducedCategory.category toBddDistLat
#align FinBddDistLat.large_category FinBddDistLatCat.largeCategory
-/

#print FinBddDistLatCat.concreteCategory /-
instance concreteCategory : ConcreteCategory FinBddDistLatCat :=
  InducedCategory.concreteCategory toBddDistLat
#align FinBddDistLat.concrete_category FinBddDistLatCat.concreteCategory
-/

#print FinBddDistLatCat.hasForgetToBddDistLatCat /-
instance hasForgetToBddDistLatCat : HasForget₂ FinBddDistLatCat BddDistLatCat :=
  InducedCategory.hasForget₂ FinBddDistLatCat.toBddDistLat
#align FinBddDistLat.has_forget_to_BddDistLat FinBddDistLatCat.hasForgetToBddDistLatCat
-/

#print FinBddDistLatCat.hasForgetToFinPartOrd /-
instance hasForgetToFinPartOrd : HasForget₂ FinBddDistLatCat FinPartOrd
    where forget₂ :=
    { obj := fun X => FinPartOrd.of X
      map := fun X Y f => (show BoundedLatticeHom X Y from f : X →o Y) }
#align FinBddDistLat.has_forget_to_FinPartOrd FinBddDistLatCat.hasForgetToFinPartOrd
-/

#print FinBddDistLatCat.Iso.mk /-
/-- Constructs an equivalence between finite distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : FinBddDistLatCat.{u}} (e : α ≃o β) : α ≅ β
    where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align FinBddDistLat.iso.mk FinBddDistLatCat.Iso.mk
-/

example {X Y : FinBddDistLatCat} : (X ⟶ Y) = BoundedLatticeHom X Y :=
  rfl

#print FinBddDistLatCat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : FinBddDistLatCat ⥤ FinBddDistLatCat
    where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align FinBddDistLat.dual FinBddDistLatCat.dual
-/

#print FinBddDistLatCat.dualEquiv /-
/-- The equivalence between `FinBddDistLat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : FinBddDistLatCat ≌ FinBddDistLatCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align FinBddDistLat.dual_equiv FinBddDistLatCat.dualEquiv
-/

end FinBddDistLatCat

#print finBddDistLatCat_dual_comp_forget_to_bddDistLatCat /-
theorem finBddDistLatCat_dual_comp_forget_to_bddDistLatCat :
    FinBddDistLatCat.dual ⋙ forget₂ FinBddDistLatCat BddDistLatCat =
      forget₂ FinBddDistLatCat BddDistLatCat ⋙ BddDistLatCat.dual :=
  rfl
#align FinBddDistLat_dual_comp_forget_to_BddDistLat finBddDistLatCat_dual_comp_forget_to_bddDistLatCat
-/

