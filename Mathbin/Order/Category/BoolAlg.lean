/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.BoolAlg
! leanprover-community/mathlib commit cff8231f04dfa33fd8f2f45792eebd862ef30cad
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.HeytAlg

/-!
# The category of boolean algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `BoolAlg`, the category of boolean algebras.
-/


open OrderDual Opposite Set

universe u

open CategoryTheory

#print BoolAlgCat /-
/-- The category of boolean algebras. -/
def BoolAlgCat :=
  Bundled BooleanAlgebra
#align BoolAlg BoolAlgCat
-/

namespace BoolAlgCat

instance : CoeSort BoolAlgCat (Type _) :=
  Bundled.hasCoeToSort

instance (X : BoolAlgCat) : BooleanAlgebra X :=
  X.str

#print BoolAlgCat.of /-
/-- Construct a bundled `BoolAlg` from a `boolean_algebra`. -/
def of (α : Type _) [BooleanAlgebra α] : BoolAlgCat :=
  Bundled.of α
#align BoolAlg.of BoolAlgCat.of
-/

#print BoolAlgCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [BooleanAlgebra α] : ↥(of α) = α :=
  rfl
#align BoolAlg.coe_of BoolAlgCat.coe_of
-/

instance : Inhabited BoolAlgCat :=
  ⟨of PUnit⟩

#print BoolAlgCat.toBddDistLatCat /-
/-- Turn a `BoolAlg` into a `BddDistLat` by forgetting its complement operation. -/
def toBddDistLatCat (X : BoolAlgCat) : BddDistLatCat :=
  BddDistLatCat.of X
#align BoolAlg.to_BddDistLat BoolAlgCat.toBddDistLatCat
-/

#print BoolAlgCat.coe_toBddDistLatCat /-
@[simp]
theorem coe_toBddDistLatCat (X : BoolAlgCat) : ↥X.toBddDistLatCat = ↥X :=
  rfl
#align BoolAlg.coe_to_BddDistLat BoolAlgCat.coe_toBddDistLatCat
-/

instance : LargeCategory.{u} BoolAlgCat :=
  InducedCategory.category toBddDistLatCat

instance : ConcreteCategory BoolAlgCat :=
  InducedCategory.concreteCategory toBddDistLatCat

#print BoolAlgCat.hasForgetToBddDistLatCat /-
instance hasForgetToBddDistLatCat : HasForget₂ BoolAlgCat BddDistLatCat :=
  InducedCategory.hasForget₂ toBddDistLatCat
#align BoolAlg.has_forget_to_BddDistLat BoolAlgCat.hasForgetToBddDistLatCat
-/

section

attribute [local instance] BoundedLatticeHomClass.toBiheytingHomClass

#print BoolAlgCat.hasForgetToHeytAlgCat /-
@[simps]
instance hasForgetToHeytAlgCat : HasForget₂ BoolAlgCat HeytAlgCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => show BoundedLatticeHom X Y from f }
#align BoolAlg.has_forget_to_HeytAlg BoolAlgCat.hasForgetToHeytAlgCat
-/

end

#print BoolAlgCat.Iso.mk /-
/-- Constructs an equivalence between Boolean algebras from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolAlgCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align BoolAlg.iso.mk BoolAlgCat.Iso.mk
-/

#print BoolAlgCat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : BoolAlgCat ⥤ BoolAlgCat where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align BoolAlg.dual BoolAlgCat.dual
-/

#print BoolAlgCat.dualEquiv /-
/-- The equivalence between `BoolAlg` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoolAlgCat ≌ BoolAlgCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BoolAlg.dual_equiv BoolAlgCat.dualEquiv
-/

end BoolAlgCat

#print boolAlgCat_dual_comp_forget_to_bddDistLatCat /-
theorem boolAlgCat_dual_comp_forget_to_bddDistLatCat :
    BoolAlgCat.dual ⋙ forget₂ BoolAlgCat BddDistLatCat =
      forget₂ BoolAlgCat BddDistLatCat ⋙ BddDistLatCat.dual :=
  rfl
#align BoolAlg_dual_comp_forget_to_BddDistLat boolAlgCat_dual_comp_forget_to_bddDistLatCat
-/

