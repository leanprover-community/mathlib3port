/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Data.Fintype.Powerset
import Order.Category.BoolAlg
import Order.Category.FinBddDistLat
import Order.Hom.CompleteLattice

#align_import order.category.FinBoolAlg from "leanprover-community/mathlib"@"2a0ce625dbb0ffbc7d1316597de0b25c1ec75303"

/-!
# The category of finite boolean algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `FinBoolAlg`, the category of finite boolean algebras.

## TODO

Birkhoff's representation for finite Boolean algebras.

`Fintype_to_FinBoolAlg_op.left_op ⋙ FinBoolAlg.dual ≅ Fintype_to_FinBoolAlg_op.left_op`

`FinBoolAlg` is essentially small.
-/


universe u

open CategoryTheory OrderDual Opposite

#print FinBoolAlg /-
/-- The category of finite boolean algebras with bounded lattice morphisms. -/
structure FinBoolAlg where
  toBoolAlg : BoolAlg
  [isFintype : Fintype to_BoolAlg]
#align FinBoolAlg FinBoolAlg
-/

namespace FinBoolAlg

instance : CoeSort FinBoolAlg (Type _) :=
  ⟨fun X => X.toBoolAlg⟩

instance (X : FinBoolAlg) : BooleanAlgebra X :=
  X.toBoolAlg.str

attribute [instance] FinBoolAlg.isFintype

@[simp]
theorem coe_toBoolAlg (X : FinBoolAlg) : ↥X.toBoolAlg = ↥X :=
  rfl
#align FinBoolAlg.coe_to_BoolAlg FinBoolAlg.coe_toBoolAlg

#print FinBoolAlg.of /-
/-- Construct a bundled `FinBoolAlg` from `boolean_algebra` + `fintype`. -/
def of (α : Type _) [BooleanAlgebra α] [Fintype α] : FinBoolAlg :=
  ⟨⟨α⟩⟩
#align FinBoolAlg.of FinBoolAlg.of
-/

#print FinBoolAlg.coe_of /-
@[simp]
theorem coe_of (α : Type _) [BooleanAlgebra α] [Fintype α] : ↥(of α) = α :=
  rfl
#align FinBoolAlg.coe_of FinBoolAlg.coe_of
-/

instance : Inhabited FinBoolAlg :=
  ⟨of PUnit⟩

#print FinBoolAlg.largeCategory /-
instance largeCategory : LargeCategory FinBoolAlg :=
  InducedCategory.category FinBoolAlg.toBoolAlg
#align FinBoolAlg.large_category FinBoolAlg.largeCategory
-/

#print FinBoolAlg.concreteCategory /-
instance concreteCategory : ConcreteCategory FinBoolAlg :=
  InducedCategory.concreteCategory FinBoolAlg.toBoolAlg
#align FinBoolAlg.concrete_category FinBoolAlg.concreteCategory
-/

#print FinBoolAlg.hasForgetToBoolAlg /-
instance hasForgetToBoolAlg : HasForget₂ FinBoolAlg BoolAlg :=
  InducedCategory.hasForget₂ FinBoolAlg.toBoolAlg
#align FinBoolAlg.has_forget_to_BoolAlg FinBoolAlg.hasForgetToBoolAlg
-/

#print FinBoolAlg.hasForgetToFinBddDistLat /-
instance hasForgetToFinBddDistLat : HasForget₂ FinBoolAlg FinBddDistLat
    where
  forget₂ :=
    { obj := fun X => FinBddDistLat.of X
      map := fun X Y f => f }
  forget_comp := rfl
#align FinBoolAlg.has_forget_to_FinBddDistLat FinBoolAlg.hasForgetToFinBddDistLat
-/

#print FinBoolAlg.forgetToBoolAlg_full /-
instance forgetToBoolAlg_full : CategoryTheory.Functor.Full (forget₂ FinBoolAlg BoolAlg) :=
  InducedCategory.full _
#align FinBoolAlg.forget_to_BoolAlg_full FinBoolAlg.forgetToBoolAlg_full
-/

#print FinBoolAlg.forgetToBoolAlgFaithful /-
instance forgetToBoolAlgFaithful : CategoryTheory.Functor.Faithful (forget₂ FinBoolAlg BoolAlg) :=
  InducedCategory.faithful _
#align FinBoolAlg.forget_to_BoolAlg_faithful FinBoolAlg.forgetToBoolAlgFaithful
-/

#print FinBoolAlg.hasForgetToFinPartOrd /-
@[simps]
instance hasForgetToFinPartOrd : HasForget₂ FinBoolAlg FinPartOrd
    where forget₂ :=
    { obj := fun X => FinPartOrd.of X
      map := fun X Y f => show OrderHom X Y from ↑(show BoundedLatticeHom X Y from f) }
#align FinBoolAlg.has_forget_to_FinPartOrd FinBoolAlg.hasForgetToFinPartOrd
-/

#print FinBoolAlg.forgetToFinPartOrdFaithful /-
instance forgetToFinPartOrdFaithful :
    CategoryTheory.Functor.Faithful (forget₂ FinBoolAlg FinPartOrd) :=
  ⟨fun X Y f g h =>
    haveI := congr_arg (coeFn : _ → X → Y) h
    DFunLike.coe_injective this⟩
#align FinBoolAlg.forget_to_FinPartOrd_faithful FinBoolAlg.forgetToFinPartOrdFaithful
-/

#print FinBoolAlg.Iso.mk /-
/-- Constructs an equivalence between finite Boolean algebras from an order isomorphism between
them. -/
@[simps]
def Iso.mk {α β : FinBoolAlg.{u}} (e : α ≃o β) : α ≅ β
    where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align FinBoolAlg.iso.mk FinBoolAlg.Iso.mk
-/

#print FinBoolAlg.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : FinBoolAlg ⥤ FinBoolAlg where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align FinBoolAlg.dual FinBoolAlg.dual
-/

#print FinBoolAlg.dualEquiv /-
/-- The equivalence between `FinBoolAlg` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : FinBoolAlg ≌ FinBoolAlg :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align FinBoolAlg.dual_equiv FinBoolAlg.dualEquiv
-/

end FinBoolAlg

#print finBoolAlg_dual_comp_forget_to_finBddDistLat /-
theorem finBoolAlg_dual_comp_forget_to_finBddDistLat :
    FinBoolAlg.dual ⋙ forget₂ FinBoolAlg FinBddDistLat =
      forget₂ FinBoolAlg FinBddDistLat ⋙ FinBddDistLat.dual :=
  rfl
#align FinBoolAlg_dual_comp_forget_to_FinBddDistLat finBoolAlg_dual_comp_forget_to_finBddDistLat
-/

#print fintypeToFinBoolAlgOp /-
/-- The powerset functor. `set` as a functor. -/
@[simps]
def fintypeToFinBoolAlgOp : FintypeCat ⥤ FinBoolAlgᵒᵖ
    where
  obj X := op <| FinBoolAlg.of (Set X)
  map X Y f :=
    Quiver.Hom.op <| (CompleteLatticeHom.setPreimage f : BoundedLatticeHom (Set Y) (Set X))
#align Fintype_to_FinBoolAlg_op fintypeToFinBoolAlgOp
-/

