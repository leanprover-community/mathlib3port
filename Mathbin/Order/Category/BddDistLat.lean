/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.BddDistLat
! leanprover-community/mathlib commit 8af7091a43227e179939ba132e54e54e9f3b089a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.BddLat
import Mathbin.Order.Category.DistLat

/-!
# The category of bounded distributive lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `BddDistLat`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

#print BddDistLatCat /-
/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
structure BddDistLatCat where
  toDistLat : DistLatCat
  [isBoundedOrder : BoundedOrder to_DistLat]
#align BddDistLat BddDistLatCat
-/

namespace BddDistLatCat

instance : CoeSort BddDistLatCat (Type _) :=
  ⟨fun X => X.toDistLat⟩

instance (X : BddDistLatCat) : DistribLattice X :=
  X.toDistLat.str

attribute [instance] BddDistLatCat.isBoundedOrder

#print BddDistLatCat.of /-
/-- Construct a bundled `BddDistLat` from a `bounded_order` `distrib_lattice`. -/
def of (α : Type _) [DistribLattice α] [BoundedOrder α] : BddDistLatCat :=
  ⟨⟨α⟩⟩
#align BddDistLat.of BddDistLatCat.of
-/

#print BddDistLatCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BddDistLat.coe_of BddDistLatCat.coe_of
-/

instance : Inhabited BddDistLatCat :=
  ⟨of PUnit⟩

#print BddDistLatCat.toBddLat /-
/-- Turn a `BddDistLat` into a `BddLat` by forgetting it is distributive. -/
def toBddLat (X : BddDistLatCat) : BddLatCat :=
  BddLatCat.of X
#align BddDistLat.to_BddLat BddDistLatCat.toBddLat
-/

/- warning: BddDistLat.coe_to_BddLat clashes with BddDistLatCat.coe_to_BddLat -> BddDistLatCat.coe_toBddLat
Case conversion may be inaccurate. Consider using '#align BddDistLat.coe_to_BddLat BddDistLatCat.coe_toBddLatₓ'. -/
#print BddDistLatCat.coe_toBddLat /-
@[simp]
theorem coe_toBddLat (X : BddDistLatCat) : ↥X.toBddLat = ↥X :=
  rfl
#align BddDistLat.coe_to_BddLat BddDistLatCat.coe_toBddLat
-/

instance : LargeCategory.{u} BddDistLatCat :=
  InducedCategory.category toBddLat

instance : ConcreteCategory BddDistLatCat :=
  InducedCategory.concreteCategory toBddLat

#print BddDistLatCat.hasForgetToDistLat /-
instance hasForgetToDistLat : HasForget₂ BddDistLatCat DistLatCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toLatticeHom }
#align BddDistLat.has_forget_to_DistLat BddDistLatCat.hasForgetToDistLat
-/

#print BddDistLatCat.hasForgetToBddLat /-
instance hasForgetToBddLat : HasForget₂ BddDistLatCat BddLatCat :=
  InducedCategory.hasForget₂ toBddLat
#align BddDistLat.has_forget_to_BddLat BddDistLatCat.hasForgetToBddLat
-/

#print BddDistLatCat.forget_bddLat_latCat_eq_forget_distLatCat_latCat /-
theorem forget_bddLat_latCat_eq_forget_distLatCat_latCat :
    forget₂ BddDistLatCat BddLatCat ⋙ forget₂ BddLatCat LatCat =
      forget₂ BddDistLatCat DistLatCat ⋙ forget₂ DistLatCat LatCat :=
  rfl
#align BddDistLat.forget_BddLat_Lat_eq_forget_DistLat_Lat BddDistLatCat.forget_bddLat_latCat_eq_forget_distLatCat_latCat
-/

#print BddDistLatCat.Iso.mk /-
/-- Constructs an equivalence between bounded distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BddDistLatCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align BddDistLat.iso.mk BddDistLatCat.Iso.mk
-/

#print BddDistLatCat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : BddDistLatCat ⥤ BddDistLatCat
    where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align BddDistLat.dual BddDistLatCat.dual
-/

#print BddDistLatCat.dualEquiv /-
/-- The equivalence between `BddDistLat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BddDistLatCat ≌ BddDistLatCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BddDistLat.dual_equiv BddDistLatCat.dualEquiv
-/

end BddDistLatCat

#print bddDistLatCat_dual_comp_forget_to_distLatCat /-
theorem bddDistLatCat_dual_comp_forget_to_distLatCat :
    BddDistLatCat.dual ⋙ forget₂ BddDistLatCat DistLatCat =
      forget₂ BddDistLatCat DistLatCat ⋙ DistLatCat.dual :=
  rfl
#align BddDistLat_dual_comp_forget_to_DistLat bddDistLatCat_dual_comp_forget_to_distLatCat
-/

