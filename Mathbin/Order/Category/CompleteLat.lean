/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Order.Category.BddLat
import Order.Hom.CompleteLattice

#align_import order.category.CompleteLat from "leanprover-community/mathlib"@"8af7091a43227e179939ba132e54e54e9f3b089a"

/-!
# The category of complete lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `CompleteLat`, the category of complete lattices.
-/


universe u

open CategoryTheory

#print CompleteLat /-
/-- The category of complete lattices. -/
def CompleteLat :=
  Bundled CompleteLattice
#align CompleteLat CompleteLat
-/

namespace CompleteLat

instance : CoeSort CompleteLat (Type _) :=
  Bundled.hasCoeToSort

instance (X : CompleteLat) : CompleteLattice X :=
  X.str

#print CompleteLat.of /-
/-- Construct a bundled `CompleteLat` from a `complete_lattice`. -/
def of (α : Type _) [CompleteLattice α] : CompleteLat :=
  Bundled.of α
#align CompleteLat.of CompleteLat.of
-/

#print CompleteLat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [CompleteLattice α] : ↥(of α) = α :=
  rfl
#align CompleteLat.coe_of CompleteLat.coe_of
-/

instance : Inhabited CompleteLat :=
  ⟨of PUnit⟩

instance : BundledHom @CompleteLatticeHom
    where
  toFun _ _ _ _ := coeFn
  id := @CompleteLatticeHom.id
  comp := @CompleteLatticeHom.comp
  hom_ext X Y _ _ := FunLike.coe_injective

instance : LargeCategory.{u} CompleteLat :=
  BundledHom.category CompleteLatticeHom

instance : ConcreteCategory CompleteLat :=
  BundledHom.concreteCategory CompleteLatticeHom

#print CompleteLat.hasForgetToBddLat /-
instance hasForgetToBddLat : HasForget₂ CompleteLat BddLat
    where
  forget₂ :=
    { obj := fun X => BddLat.of X
      map := fun X Y => CompleteLatticeHom.toBoundedLatticeHom }
  forget_comp := rfl
#align CompleteLat.has_forget_to_BddLat CompleteLat.hasForgetToBddLat
-/

#print CompleteLat.Iso.mk /-
/-- Constructs an isomorphism of complete lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : CompleteLat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align CompleteLat.iso.mk CompleteLat.Iso.mk
-/

#print CompleteLat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : CompleteLat ⥤ CompleteLat where
  obj X := of Xᵒᵈ
  map X Y := CompleteLatticeHom.dual
#align CompleteLat.dual CompleteLat.dual
-/

#print CompleteLat.dualEquiv /-
/-- The equivalence between `CompleteLat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : CompleteLat ≌ CompleteLat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align CompleteLat.dual_equiv CompleteLat.dualEquiv
-/

end CompleteLat

#print completeLat_dual_comp_forget_to_bddLat /-
theorem completeLat_dual_comp_forget_to_bddLat :
    CompleteLat.dual ⋙ forget₂ CompleteLat BddLat = forget₂ CompleteLat BddLat ⋙ BddLat.dual :=
  rfl
#align CompleteLat_dual_comp_forget_to_BddLat completeLat_dual_comp_forget_to_bddLat
-/

