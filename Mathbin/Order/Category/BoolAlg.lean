/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.BoolAlg
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.HeytAlg

/-!
# The category of boolean algebras

This defines `BoolAlg`, the category of boolean algebras.
-/


open OrderDual Opposite Set

universe u

open CategoryTheory

/-- The category of boolean algebras. -/
def BoolAlg :=
  Bundled BooleanAlgebra
#align BoolAlg BoolAlg

namespace BoolAlg

instance : CoeSort BoolAlg (Type _) :=
  Bundled.hasCoeToSort

instance (X : BoolAlg) : BooleanAlgebra X :=
  X.str

/-- Construct a bundled `BoolAlg` from a `boolean_algebra`. -/
def of (α : Type _) [BooleanAlgebra α] : BoolAlg :=
  Bundled.of α
#align BoolAlg.of BoolAlg.of

@[simp]
theorem coe_of (α : Type _) [BooleanAlgebra α] : ↥(of α) = α :=
  rfl
#align BoolAlg.coe_of BoolAlg.coe_of

instance : Inhabited BoolAlg :=
  ⟨of PUnit⟩

/-- Turn a `BoolAlg` into a `BoundedDistribLattice` by forgetting its complement operation. -/
def toBoundedDistribLattice (X : BoolAlg) : BoundedDistribLattice :=
  BoundedDistribLattice.of X
#align BoolAlg.to_BoundedDistribLattice BoolAlg.toBoundedDistribLattice

@[simp]
theorem coe_toBoundedDistribLattice (X : BoolAlg) : ↥X.toBoundedDistribLattice = ↥X :=
  rfl
#align BoolAlg.coe_to_BoundedDistribLattice BoolAlg.coe_toBoundedDistribLattice

instance : LargeCategory.{u} BoolAlg :=
  InducedCategory.category toBoundedDistribLattice

instance : ConcreteCategory BoolAlg :=
  InducedCategory.concreteCategory toBoundedDistribLattice

instance hasForgetToBoundedDistribLattice : HasForget₂ BoolAlg BoundedDistribLattice :=
  InducedCategory.hasForget₂ toBoundedDistribLattice
#align BoolAlg.has_forget_to_BoundedDistribLattice BoolAlg.hasForgetToBoundedDistribLattice

section

attribute [local instance] BoundedLatticeHomClass.toBiheytingHomClass

@[simps]
instance hasForgetToHeytAlg : HasForget₂ BoolAlg HeytAlg
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => show BoundedLatticeHom X Y from f }
#align BoolAlg.has_forget_to_HeytAlg BoolAlg.hasForgetToHeytAlg

end

/-- Constructs an equivalence between Boolean algebras from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolAlg.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align BoolAlg.iso.mk BoolAlg.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : BoolAlg ⥤ BoolAlg where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align BoolAlg.dual BoolAlg.dual

/-- The equivalence between `BoolAlg` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoolAlg ≌ BoolAlg :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BoolAlg.dual_equiv BoolAlg.dualEquiv

end BoolAlg

theorem boolAlg_dual_comp_forget_to_boundedDistribLattice :
    BoolAlg.dual ⋙ forget₂ BoolAlg BoundedDistribLattice =
      forget₂ BoolAlg BoundedDistribLattice ⋙ BoundedDistribLattice.dual :=
  rfl
#align BoolAlg_dual_comp_forget_to_BoundedDistribLattice boolAlg_dual_comp_forget_to_boundedDistribLattice

