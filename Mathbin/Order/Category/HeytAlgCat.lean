/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.HeytAlg
! leanprover-community/mathlib commit d4f69d96f3532729da8ebb763f4bc26fcf640f06
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.BoundedDistribLatticeCat
import Mathbin.Order.Heyting.Hom

/-!
# The category of Heyting algebras

This file defines `HeytAlg`, the category of Heyting algebras.
-/


universe u

open CategoryTheory Opposite Order

/-- The category of Heyting algebras. -/
def HeytAlgCat :=
  Bundled HeytingAlgebra
#align HeytAlg HeytAlgCat

namespace HeytAlgCat

instance : CoeSort HeytAlgCat (Type _) :=
  bundled.has_coe_to_sort

instance (X : HeytAlgCat) : HeytingAlgebra X :=
  X.str

/-- Construct a bundled `HeytAlg` from a `heyting_algebra`. -/
def of (α : Type _) [HeytingAlgebra α] : HeytAlgCat :=
  Bundled.of α
#align HeytAlg.of HeytAlgCat.of

@[simp]
theorem coe_of (α : Type _) [HeytingAlgebra α] : ↥(of α) = α :=
  rfl
#align HeytAlg.coe_of HeytAlgCat.coe_of

instance : Inhabited HeytAlgCat :=
  ⟨of PUnit⟩

instance bundledHom :
    BundledHom
      HeytingHom where 
  toFun α β [HeytingAlgebra α] [HeytingAlgebra β] := (coeFn : HeytingHom α β → α → β)
  id := HeytingHom.id
  comp := @HeytingHom.comp
  hom_ext α β [HeytingAlgebra α] [HeytingAlgebra β] := FunLike.coe_injective
#align HeytAlg.bundled_hom HeytAlgCat.bundledHom

deriving instance LargeCategory, ConcreteCategory for HeytAlgCat

@[simps]
instance hasForgetToLattice :
    HasForget₂ HeytAlgCat
      BoundedDistribLatticeCat where forget₂ :=
    { obj := fun X => BoundedDistribLatticeCat.of X
      map := fun X Y f => (f : BoundedLatticeHom X Y) }
#align HeytAlg.has_forget_to_Lattice HeytAlgCat.hasForgetToLattice

/-- Constructs an isomorphism of Heyting algebras from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : HeytAlgCat.{u}} (e : α ≃o β) :
    α ≅ β where 
  Hom := e
  inv := e.symm
  hom_inv_id' := by 
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by 
    ext
    exact e.apply_symm_apply _
#align HeytAlg.iso.mk HeytAlgCat.Iso.mk

end HeytAlgCat

