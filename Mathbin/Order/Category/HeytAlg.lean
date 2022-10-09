/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.BoundedDistribLattice
import Mathbin.Order.Heyting.Hom

/-!
# The category of Heyting algebras

This file defines `HeytAlg`, the category of Heyting algebras.
-/


universe u

open CategoryTheory Opposite Order

/-- The category of Heyting algebras. -/
def HeytAlg :=
  Bundled HeytingAlgebra

namespace HeytAlg

instance : CoeSort HeytAlg (Type _) :=
  bundled.has_coe_to_sort

instance (X : HeytAlg) : HeytingAlgebra X :=
  X.str

/-- Construct a bundled `HeytAlg` from a `heyting_algebra`. -/
def of (α : Type _) [HeytingAlgebra α] : HeytAlg :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type _) [HeytingAlgebra α] : ↥(of α) = α :=
  rfl

instance : Inhabited HeytAlg :=
  ⟨of PUnit⟩

instance bundledHom : BundledHom HeytingHom where
  toFun := fun α β [HeytingAlgebra α] [HeytingAlgebra β] => (coeFn : HeytingHom α β → α → β)
  id := HeytingHom.id
  comp := @HeytingHom.comp
  hom_ext := fun α β [HeytingAlgebra α] [HeytingAlgebra β] => FunLike.coe_injective

deriving instance LargeCategory, ConcreteCategory for HeytAlg

@[simps]
instance hasForgetToLattice :
    HasForget₂ HeytAlg
      BoundedDistribLattice where forget₂ :=
    { obj := fun X => BoundedDistribLattice.of X, map := fun X Y f => (f : BoundedLatticeHom X Y) }

/-- Constructs an isomorphism of Heyting algebras from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : HeytAlg.{u}} (e : α ≃o β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _

end HeytAlg

