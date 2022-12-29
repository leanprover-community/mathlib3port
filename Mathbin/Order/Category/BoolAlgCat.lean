/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.BoolAlg
! leanprover-community/mathlib commit 422e70f7ce183d2900c586a8cda8381e788a0c62
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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
#align BoolAlg BoolAlgCat

namespace BoolAlgCat

instance : CoeSort BoolAlgCat (Type _) :=
  bundled.has_coe_to_sort

instance (X : BoolAlgCat) : BooleanAlgebra X :=
  X.str

/-- Construct a bundled `BoolAlg` from a `boolean_algebra`. -/
def of (α : Type _) [BooleanAlgebra α] : BoolAlgCat :=
  Bundled.of α
#align BoolAlg.of BoolAlgCat.of

@[simp]
theorem coe_of (α : Type _) [BooleanAlgebra α] : ↥(of α) = α :=
  rfl
#align BoolAlg.coe_of BoolAlgCat.coe_of

instance : Inhabited BoolAlgCat :=
  ⟨of PUnit⟩

/-- Turn a `BoolAlg` into a `BoundedDistribLattice` by forgetting its complement operation. -/
def toBoundedDistribLattice (X : BoolAlgCat) : BoundedDistribLatticeCat :=
  BoundedDistribLatticeCat.of X
#align BoolAlg.to_BoundedDistribLattice BoolAlgCat.toBoundedDistribLattice

@[simp]
theorem coe_to_BoundedDistribLattice (X : BoolAlgCat) : ↥X.toBoundedDistribLattice = ↥X :=
  rfl
#align BoolAlg.coe_to_BoundedDistribLattice BoolAlgCat.coe_to_BoundedDistribLattice

instance : LargeCategory.{u} BoolAlgCat :=
  InducedCategory.category toBoundedDistribLattice

instance : ConcreteCategory BoolAlgCat :=
  InducedCategory.concreteCategory toBoundedDistribLattice

instance hasForgetToBoundedDistribLattice : HasForget₂ BoolAlgCat BoundedDistribLatticeCat :=
  InducedCategory.hasForget₂ toBoundedDistribLattice
#align BoolAlg.has_forget_to_BoundedDistribLattice BoolAlgCat.hasForgetToBoundedDistribLattice

section

attribute [local instance] BoundedLatticeHomClass.toBiheytingHomClass

@[simps]
instance hasForgetToHeytAlg : HasForget₂ BoolAlgCat HeytAlgCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => show BoundedLatticeHom X Y from f }
#align BoolAlg.has_forget_to_HeytAlg BoolAlgCat.hasForgetToHeytAlg

end

/-- Constructs an equivalence between Boolean algebras from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolAlgCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align BoolAlg.iso.mk BoolAlgCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : BoolAlgCat ⥤ BoolAlgCat where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align BoolAlg.dual BoolAlgCat.dual

/-- The equivalence between `BoolAlg` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoolAlgCat ≌ BoolAlgCat :=
  Equivalence.mk dual dual
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BoolAlg.dual_equiv BoolAlgCat.dualEquiv

end BoolAlgCat

theorem BoolAlg_dual_comp_forget_to_BoundedDistribLattice :
    BoolAlgCat.dual ⋙ forget₂ BoolAlgCat BoundedDistribLatticeCat =
      forget₂ BoolAlgCat BoundedDistribLatticeCat ⋙ BoundedDistribLatticeCat.dual :=
  rfl
#align
  BoolAlg_dual_comp_forget_to_BoundedDistribLattice BoolAlg_dual_comp_forget_to_BoundedDistribLattice

