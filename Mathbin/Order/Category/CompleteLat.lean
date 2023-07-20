/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.BddLat
import Mathbin.Order.Hom.CompleteLattice

#align_import order.category.CompleteLat from "leanprover-community/mathlib"@"8af7091a43227e179939ba132e54e54e9f3b089a"

/-!
# The category of complete lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `CompleteLat`, the category of complete lattices.
-/


universe u

open CategoryTheory

#print CompleteLatCat /-
/-- The category of complete lattices. -/
def CompleteLatCat :=
  Bundled CompleteLattice
#align CompleteLat CompleteLatCat
-/

namespace CompleteLatCat

instance : CoeSort CompleteLatCat (Type _) :=
  Bundled.hasCoeToSort

instance (X : CompleteLatCat) : CompleteLattice X :=
  X.str

#print CompleteLatCat.of /-
/-- Construct a bundled `CompleteLat` from a `complete_lattice`. -/
def of (α : Type _) [CompleteLattice α] : CompleteLatCat :=
  Bundled.of α
#align CompleteLat.of CompleteLatCat.of
-/

#print CompleteLatCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [CompleteLattice α] : ↥(of α) = α :=
  rfl
#align CompleteLat.coe_of CompleteLatCat.coe_of
-/

instance : Inhabited CompleteLatCat :=
  ⟨of PUnit⟩

instance : BundledHom @CompleteLatticeHom
    where
  toFun _ _ _ _ := coeFn
  id := @CompleteLatticeHom.id
  comp := @CompleteLatticeHom.comp
  hom_ext X Y _ _ := FunLike.coe_injective

instance : LargeCategory.{u} CompleteLatCat :=
  BundledHom.category CompleteLatticeHom

instance : ConcreteCategory CompleteLatCat :=
  BundledHom.concreteCategory CompleteLatticeHom

#print CompleteLatCat.hasForgetToBddLat /-
instance hasForgetToBddLat : HasForget₂ CompleteLatCat BddLatCat
    where
  forget₂ :=
    { obj := fun X => BddLatCat.of X
      map := fun X Y => CompleteLatticeHom.toBoundedLatticeHom }
  forget_comp := rfl
#align CompleteLat.has_forget_to_BddLat CompleteLatCat.hasForgetToBddLat
-/

#print CompleteLatCat.Iso.mk /-
/-- Constructs an isomorphism of complete lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : CompleteLatCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align CompleteLat.iso.mk CompleteLatCat.Iso.mk
-/

#print CompleteLatCat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : CompleteLatCat ⥤ CompleteLatCat
    where
  obj X := of Xᵒᵈ
  map X Y := CompleteLatticeHom.dual
#align CompleteLat.dual CompleteLatCat.dual
-/

#print CompleteLatCat.dualEquiv /-
/-- The equivalence between `CompleteLat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : CompleteLatCat ≌ CompleteLatCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align CompleteLat.dual_equiv CompleteLatCat.dualEquiv
-/

end CompleteLatCat

#print completeLatCat_dual_comp_forget_to_bddLatCat /-
theorem completeLatCat_dual_comp_forget_to_bddLatCat :
    CompleteLatCat.dual ⋙ forget₂ CompleteLatCat BddLatCat =
      forget₂ CompleteLatCat BddLatCat ⋙ BddLatCat.dual :=
  rfl
#align CompleteLat_dual_comp_forget_to_BddLat completeLatCat_dual_comp_forget_to_bddLatCat
-/

