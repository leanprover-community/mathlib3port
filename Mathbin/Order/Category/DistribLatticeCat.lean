/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.DistribLattice
! leanprover-community/mathlib commit 1e05171a5e8cf18d98d9cf7b207540acb044acae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.LatticeCat

/-!
# The category of distributive lattices

This file defines `DistribLattice`, the category of distributive lattices.

Note that [`DistLat`](https://ncatlab.org/nlab/show/DistLat) in the literature doesn't always
correspond to `DistribLattice` as we don't require bottom or top elements. Instead, this `DistLat`
corresponds to `BoundedDistribLattice`.
-/


universe u

open CategoryTheory

/-- The category of distributive lattices. -/
def DistribLatticeCat :=
  Bundled DistribLattice
#align DistribLattice DistribLatticeCat

namespace DistribLatticeCat

instance : CoeSort DistribLatticeCat (Type _) :=
  bundled.has_coe_to_sort

instance (X : DistribLatticeCat) : DistribLattice X :=
  X.str

/-- Construct a bundled `DistribLattice` from a `distrib_lattice` underlying type and typeclass. -/
def of (α : Type _) [DistribLattice α] : DistribLatticeCat :=
  Bundled.of α
#align DistribLattice.of DistribLatticeCat.of

@[simp]
theorem coe_of (α : Type _) [DistribLattice α] : ↥(of α) = α :=
  rfl
#align DistribLattice.coe_of DistribLatticeCat.coe_of

instance : Inhabited DistribLatticeCat :=
  ⟨of PUnit⟩

instance : BundledHom.ParentProjection @DistribLattice.toLattice :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for DistribLatticeCat

instance hasForgetToLattice : HasForget₂ DistribLatticeCat LatticeCat :=
  BundledHom.forget₂ _ _
#align DistribLattice.has_forget_to_Lattice DistribLatticeCat.hasForgetToLattice

/-- Constructs an equivalence between distributive lattices from an order isomorphism between them.
-/
@[simps]
def Iso.mk {α β : DistribLatticeCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align DistribLattice.iso.mk DistribLatticeCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : DistribLatticeCat ⥤ DistribLatticeCat
    where
  obj X := of Xᵒᵈ
  map X Y := LatticeHom.dual
#align DistribLattice.dual DistribLatticeCat.dual

/-- The equivalence between `DistribLattice` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : DistribLatticeCat ≌ DistribLatticeCat :=
  Equivalence.mk dual dual
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align DistribLattice.dual_equiv DistribLatticeCat.dualEquiv

end DistribLatticeCat

theorem DistribLattice_dual_comp_forget_to_Lattice :
    DistribLatticeCat.dual ⋙ forget₂ DistribLatticeCat LatticeCat =
      forget₂ DistribLatticeCat LatticeCat ⋙ LatticeCat.dual :=
  rfl
#align DistribLattice_dual_comp_forget_to_Lattice DistribLattice_dual_comp_forget_to_Lattice

