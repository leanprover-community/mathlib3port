/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.Lat

#align_import order.category.DistLat from "leanprover-community/mathlib"@"ce38d86c0b2d427ce208c3cee3159cb421d2b3c4"

/-!
# The category of distributive lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `DistLat`, the category of distributive lattices.

Note that [`DistLat`](https://ncatlab.org/nlab/show/DistLat) in the literature doesn't always
correspond to `DistLat` as we don't require bottom or top elements. Instead, this `DistLat`
corresponds to `BddDistLat`.
-/


universe u

open CategoryTheory

#print DistLatCat /-
/-- The category of distributive lattices. -/
def DistLatCat :=
  Bundled DistribLattice
#align DistLat DistLatCat
-/

namespace DistLatCat

instance : CoeSort DistLatCat (Type _) :=
  Bundled.hasCoeToSort

instance (X : DistLatCat) : DistribLattice X :=
  X.str

#print DistLatCat.of /-
/-- Construct a bundled `DistLat` from a `distrib_lattice` underlying type and typeclass. -/
def of (α : Type _) [DistribLattice α] : DistLatCat :=
  Bundled.of α
#align DistLat.of DistLatCat.of
-/

#print DistLatCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [DistribLattice α] : ↥(of α) = α :=
  rfl
#align DistLat.coe_of DistLatCat.coe_of
-/

instance : Inhabited DistLatCat :=
  ⟨of PUnit⟩

instance : BundledHom.ParentProjection @DistribLattice.toLattice :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for DistLatCat

#print DistLatCat.hasForgetToLatCat /-
instance hasForgetToLatCat : HasForget₂ DistLatCat LatCat :=
  BundledHom.forget₂ _ _
#align DistLat.has_forget_to_Lat DistLatCat.hasForgetToLatCat
-/

#print DistLatCat.Iso.mk /-
/-- Constructs an equivalence between distributive lattices from an order isomorphism between them.
-/
@[simps]
def Iso.mk {α β : DistLatCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align DistLat.iso.mk DistLatCat.Iso.mk
-/

#print DistLatCat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : DistLatCat ⥤ DistLatCat where
  obj X := of Xᵒᵈ
  map X Y := LatticeHom.dual
#align DistLat.dual DistLatCat.dual
-/

#print DistLatCat.dualEquiv /-
/-- The equivalence between `DistLat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : DistLatCat ≌ DistLatCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align DistLat.dual_equiv DistLatCat.dualEquiv
-/

end DistLatCat

#print distLatCat_dual_comp_forget_to_latCat /-
theorem distLatCat_dual_comp_forget_to_latCat :
    DistLatCat.dual ⋙ forget₂ DistLatCat LatCat = forget₂ DistLatCat LatCat ⋙ LatCat.dual :=
  rfl
#align DistLat_dual_comp_forget_to_Lat distLatCat_dual_comp_forget_to_latCat
-/

