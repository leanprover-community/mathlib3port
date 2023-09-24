/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Order.Category.BddLat
import Order.Category.DistLat

#align_import order.category.BddDistLat from "leanprover-community/mathlib"@"8af7091a43227e179939ba132e54e54e9f3b089a"

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

#print BddDistLat /-
/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
structure BddDistLat where
  toDistLat : DistLat
  [isBoundedOrder : BoundedOrder to_DistLat]
#align BddDistLat BddDistLat
-/

namespace BddDistLat

instance : CoeSort BddDistLat (Type _) :=
  ⟨fun X => X.toDistLat⟩

instance (X : BddDistLat) : DistribLattice X :=
  X.toDistLat.str

attribute [instance] BddDistLat.isBoundedOrder

#print BddDistLat.of /-
/-- Construct a bundled `BddDistLat` from a `bounded_order` `distrib_lattice`. -/
def of (α : Type _) [DistribLattice α] [BoundedOrder α] : BddDistLat :=
  ⟨⟨α⟩⟩
#align BddDistLat.of BddDistLat.of
-/

#print BddDistLat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BddDistLat.coe_of BddDistLat.coe_of
-/

instance : Inhabited BddDistLat :=
  ⟨of PUnit⟩

#print BddDistLat.toBddLat /-
/-- Turn a `BddDistLat` into a `BddLat` by forgetting it is distributive. -/
def toBddLat (X : BddDistLat) : BddLat :=
  BddLat.of X
#align BddDistLat.to_BddLat BddDistLat.toBddLat
-/

#print BddDistLat.coe_toBddLat /-
@[simp]
theorem coe_toBddLat (X : BddDistLat) : ↥X.toBddLat = ↥X :=
  rfl
#align BddDistLat.coe_to_BddLat BddDistLat.coe_toBddLat
-/

instance : LargeCategory.{u} BddDistLat :=
  InducedCategory.category toBddLat

instance : ConcreteCategory BddDistLat :=
  InducedCategory.concreteCategory toBddLat

#print BddDistLat.hasForgetToDistLat /-
instance hasForgetToDistLat : HasForget₂ BddDistLat DistLat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toLatticeHom }
#align BddDistLat.has_forget_to_DistLat BddDistLat.hasForgetToDistLat
-/

#print BddDistLat.hasForgetToBddLat /-
instance hasForgetToBddLat : HasForget₂ BddDistLat BddLat :=
  InducedCategory.hasForget₂ toBddLat
#align BddDistLat.has_forget_to_BddLat BddDistLat.hasForgetToBddLat
-/

#print BddDistLat.forget_bddLat_lat_eq_forget_distLat_lat /-
theorem forget_bddLat_lat_eq_forget_distLat_lat :
    forget₂ BddDistLat BddLat ⋙ forget₂ BddLat Lat =
      forget₂ BddDistLat DistLat ⋙ forget₂ DistLat Lat :=
  rfl
#align BddDistLat.forget_BddLat_Lat_eq_forget_DistLat_Lat BddDistLat.forget_bddLat_lat_eq_forget_distLat_lat
-/

#print BddDistLat.Iso.mk /-
/-- Constructs an equivalence between bounded distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BddDistLat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align BddDistLat.iso.mk BddDistLat.Iso.mk
-/

#print BddDistLat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : BddDistLat ⥤ BddDistLat where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align BddDistLat.dual BddDistLat.dual
-/

#print BddDistLat.dualEquiv /-
/-- The equivalence between `BddDistLat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BddDistLat ≌ BddDistLat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BddDistLat.dual_equiv BddDistLat.dualEquiv
-/

end BddDistLat

#print bddDistLat_dual_comp_forget_to_distLat /-
theorem bddDistLat_dual_comp_forget_to_distLat :
    BddDistLat.dual ⋙ forget₂ BddDistLat DistLat = forget₂ BddDistLat DistLat ⋙ DistLat.dual :=
  rfl
#align BddDistLat_dual_comp_forget_to_DistLat bddDistLat_dual_comp_forget_to_distLat
-/

