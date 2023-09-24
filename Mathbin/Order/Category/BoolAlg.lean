/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Order.Category.HeytAlg

#align_import order.category.BoolAlg from "leanprover-community/mathlib"@"cff8231f04dfa33fd8f2f45792eebd862ef30cad"

/-!
# The category of boolean algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `BoolAlg`, the category of boolean algebras.
-/


open OrderDual Opposite Set

universe u

open CategoryTheory

#print BoolAlg /-
/-- The category of boolean algebras. -/
def BoolAlg :=
  Bundled BooleanAlgebra
#align BoolAlg BoolAlg
-/

namespace BoolAlg

instance : CoeSort BoolAlg (Type _) :=
  Bundled.hasCoeToSort

instance (X : BoolAlg) : BooleanAlgebra X :=
  X.str

#print BoolAlg.of /-
/-- Construct a bundled `BoolAlg` from a `boolean_algebra`. -/
def of (α : Type _) [BooleanAlgebra α] : BoolAlg :=
  Bundled.of α
#align BoolAlg.of BoolAlg.of
-/

#print BoolAlg.coe_of /-
@[simp]
theorem coe_of (α : Type _) [BooleanAlgebra α] : ↥(of α) = α :=
  rfl
#align BoolAlg.coe_of BoolAlg.coe_of
-/

instance : Inhabited BoolAlg :=
  ⟨of PUnit⟩

#print BoolAlg.toBddDistLat /-
/-- Turn a `BoolAlg` into a `BddDistLat` by forgetting its complement operation. -/
def toBddDistLat (X : BoolAlg) : BddDistLat :=
  BddDistLat.of X
#align BoolAlg.to_BddDistLat BoolAlg.toBddDistLat
-/

#print BoolAlg.coe_toBddDistLat /-
@[simp]
theorem coe_toBddDistLat (X : BoolAlg) : ↥X.toBddDistLat = ↥X :=
  rfl
#align BoolAlg.coe_to_BddDistLat BoolAlg.coe_toBddDistLat
-/

instance : LargeCategory.{u} BoolAlg :=
  InducedCategory.category toBddDistLat

instance : ConcreteCategory BoolAlg :=
  InducedCategory.concreteCategory toBddDistLat

#print BoolAlg.hasForgetToBddDistLat /-
instance hasForgetToBddDistLat : HasForget₂ BoolAlg BddDistLat :=
  InducedCategory.hasForget₂ toBddDistLat
#align BoolAlg.has_forget_to_BddDistLat BoolAlg.hasForgetToBddDistLat
-/

section

attribute [local instance] BoundedLatticeHomClass.toBiheytingHomClass

#print BoolAlg.hasForgetToHeytAlg /-
@[simps]
instance hasForgetToHeytAlg : HasForget₂ BoolAlg HeytAlg
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => show BoundedLatticeHom X Y from f }
#align BoolAlg.has_forget_to_HeytAlg BoolAlg.hasForgetToHeytAlg
-/

end

#print BoolAlg.Iso.mk /-
/-- Constructs an equivalence between Boolean algebras from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolAlg.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align BoolAlg.iso.mk BoolAlg.Iso.mk
-/

#print BoolAlg.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : BoolAlg ⥤ BoolAlg where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align BoolAlg.dual BoolAlg.dual
-/

#print BoolAlg.dualEquiv /-
/-- The equivalence between `BoolAlg` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoolAlg ≌ BoolAlg :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BoolAlg.dual_equiv BoolAlg.dualEquiv
-/

end BoolAlg

#print boolAlg_dual_comp_forget_to_bddDistLat /-
theorem boolAlg_dual_comp_forget_to_bddDistLat :
    BoolAlg.dual ⋙ forget₂ BoolAlg BddDistLat = forget₂ BoolAlg BddDistLat ⋙ BddDistLat.dual :=
  rfl
#align BoolAlg_dual_comp_forget_to_BddDistLat boolAlg_dual_comp_forget_to_bddDistLat
-/

