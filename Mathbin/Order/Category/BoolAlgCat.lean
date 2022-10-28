/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.HeytAlgCat

/-!
# The category of boolean algebras

This defines `BoolAlg`, the category of boolean algebras.
-/


open OrderDual Opposite Set

universe u

open CategoryTheory

/-- The category of boolean algebras. -/
def BoolAlgCat :=
  Bundled BooleanAlgebra

namespace BoolAlgCat

instance : CoeSort BoolAlgCat (Type _) :=
  bundled.has_coe_to_sort

instance (X : BoolAlgCat) : BooleanAlgebra X :=
  X.str

/-- Construct a bundled `BoolAlg` from a `boolean_algebra`. -/
def of (α : Type _) [BooleanAlgebra α] : BoolAlgCat :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type _) [BooleanAlgebra α] : ↥(of α) = α :=
  rfl

instance : Inhabited BoolAlgCat :=
  ⟨of PUnit⟩

/-- Turn a `BoolAlg` into a `BoundedDistribLattice` by forgetting its complement operation. -/
def toBoundedDistribLattice (X : BoolAlgCat) : BoundedDistribLatticeCat :=
  BoundedDistribLatticeCat.of X

@[simp]
theorem coe_to_BoundedDistribLattice (X : BoolAlgCat) : ↥X.toBoundedDistribLattice = ↥X :=
  rfl

instance : LargeCategory.{u} BoolAlgCat :=
  InducedCategory.category toBoundedDistribLattice

instance : ConcreteCategory BoolAlgCat :=
  InducedCategory.concreteCategory toBoundedDistribLattice

instance hasForgetToBoundedDistribLattice : HasForget₂ BoolAlgCat BoundedDistribLatticeCat :=
  InducedCategory.hasForget₂ toBoundedDistribLattice

section

attribute [local instance] BoundedLatticeHomClass.toBiheytingHomClass

@[simps]
instance hasForgetToHeytAlg :
    HasForget₂ BoolAlgCat
      HeytAlgCat where forget₂ := { obj := fun X => ⟨X⟩, map := fun X Y f => show BoundedLatticeHom X Y from f }

end

/-- Constructs an equivalence between Boolean algebras from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolAlgCat.{u}} (e : α ≃o β) : α ≅ β where
  Hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _

/-- `order_dual` as a functor. -/
@[simps]
def dual : BoolAlgCat ⥤ BoolAlgCat where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual

/-- The equivalence between `BoolAlg` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoolAlgCat ≌ BoolAlgCat :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end BoolAlgCat

theorem BoolAlg_dual_comp_forget_to_BoundedDistribLattice :
    BoolAlgCat.dual ⋙ forget₂ BoolAlgCat BoundedDistribLatticeCat =
      forget₂ BoolAlgCat BoundedDistribLatticeCat ⋙ BoundedDistribLatticeCat.dual :=
  rfl

