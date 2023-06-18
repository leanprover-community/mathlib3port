/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.FinBoolAlg
! leanprover-community/mathlib commit 2a0ce625dbb0ffbc7d1316597de0b25c1ec75303
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Powerset
import Mathbin.Order.Category.BoolAlg
import Mathbin.Order.Category.FinBddDistLat
import Mathbin.Order.Hom.CompleteLattice

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

#print FinBoolAlgCat /-
/-- The category of finite boolean algebras with bounded lattice morphisms. -/
structure FinBoolAlgCat where
  toBoolAlg : BoolAlgCat
  [isFintype : Fintype to_BoolAlg]
#align FinBoolAlg FinBoolAlgCat
-/

namespace FinBoolAlgCat

instance : CoeSort FinBoolAlgCat (Type _) :=
  ⟨fun X => X.toBoolAlg⟩

instance (X : FinBoolAlgCat) : BooleanAlgebra X :=
  X.toBoolAlg.str

attribute [instance] FinBoolAlgCat.isFintype

@[simp]
theorem coe_toBoolAlg (X : FinBoolAlgCat) : ↥X.toBoolAlg = ↥X :=
  rfl
#align FinBoolAlg.coe_to_BoolAlg FinBoolAlgCat.coe_toBoolAlg

#print FinBoolAlgCat.of /-
/-- Construct a bundled `FinBoolAlg` from `boolean_algebra` + `fintype`. -/
def of (α : Type _) [BooleanAlgebra α] [Fintype α] : FinBoolAlgCat :=
  ⟨⟨α⟩⟩
#align FinBoolAlg.of FinBoolAlgCat.of
-/

#print FinBoolAlgCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [BooleanAlgebra α] [Fintype α] : ↥(of α) = α :=
  rfl
#align FinBoolAlg.coe_of FinBoolAlgCat.coe_of
-/

instance : Inhabited FinBoolAlgCat :=
  ⟨of PUnit⟩

#print FinBoolAlgCat.largeCategory /-
instance largeCategory : LargeCategory FinBoolAlgCat :=
  InducedCategory.category FinBoolAlgCat.toBoolAlg
#align FinBoolAlg.large_category FinBoolAlgCat.largeCategory
-/

#print FinBoolAlgCat.concreteCategory /-
instance concreteCategory : ConcreteCategory FinBoolAlgCat :=
  InducedCategory.concreteCategory FinBoolAlgCat.toBoolAlg
#align FinBoolAlg.concrete_category FinBoolAlgCat.concreteCategory
-/

#print FinBoolAlgCat.hasForgetToBoolAlg /-
instance hasForgetToBoolAlg : HasForget₂ FinBoolAlgCat BoolAlgCat :=
  InducedCategory.hasForget₂ FinBoolAlgCat.toBoolAlg
#align FinBoolAlg.has_forget_to_BoolAlg FinBoolAlgCat.hasForgetToBoolAlg
-/

#print FinBoolAlgCat.hasForgetToFinBddDistLat /-
instance hasForgetToFinBddDistLat : HasForget₂ FinBoolAlgCat FinBddDistLatCat
    where
  forget₂ :=
    { obj := fun X => FinBddDistLatCat.of X
      map := fun X Y f => f }
  forget_comp := rfl
#align FinBoolAlg.has_forget_to_FinBddDistLat FinBoolAlgCat.hasForgetToFinBddDistLat
-/

#print FinBoolAlgCat.forgetToBoolAlgFull /-
instance forgetToBoolAlgFull : Full (forget₂ FinBoolAlgCat BoolAlgCat) :=
  InducedCategory.full _
#align FinBoolAlg.forget_to_BoolAlg_full FinBoolAlgCat.forgetToBoolAlgFull
-/

#print FinBoolAlgCat.forgetToBoolAlgFaithful /-
instance forgetToBoolAlgFaithful : Faithful (forget₂ FinBoolAlgCat BoolAlgCat) :=
  InducedCategory.faithful _
#align FinBoolAlg.forget_to_BoolAlg_faithful FinBoolAlgCat.forgetToBoolAlgFaithful
-/

#print FinBoolAlgCat.hasForgetToFinPartOrd /-
@[simps]
instance hasForgetToFinPartOrd : HasForget₂ FinBoolAlgCat FinPartOrd
    where forget₂ :=
    { obj := fun X => FinPartOrd.of X
      map := fun X Y f => show OrderHom X Y from ↑(show BoundedLatticeHom X Y from f) }
#align FinBoolAlg.has_forget_to_FinPartOrd FinBoolAlgCat.hasForgetToFinPartOrd
-/

#print FinBoolAlgCat.forgetToFinPartOrdFaithful /-
instance forgetToFinPartOrdFaithful : Faithful (forget₂ FinBoolAlgCat FinPartOrd) :=
  ⟨fun X Y f g h =>
    haveI := congr_arg (coeFn : _ → X → Y) h
    FunLike.coe_injective this⟩
#align FinBoolAlg.forget_to_FinPartOrd_faithful FinBoolAlgCat.forgetToFinPartOrdFaithful
-/

#print FinBoolAlgCat.Iso.mk /-
/-- Constructs an equivalence between finite Boolean algebras from an order isomorphism between
them. -/
@[simps]
def Iso.mk {α β : FinBoolAlgCat.{u}} (e : α ≃o β) : α ≅ β
    where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align FinBoolAlg.iso.mk FinBoolAlgCat.Iso.mk
-/

#print FinBoolAlgCat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : FinBoolAlgCat ⥤ FinBoolAlgCat
    where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align FinBoolAlg.dual FinBoolAlgCat.dual
-/

#print FinBoolAlgCat.dualEquiv /-
/-- The equivalence between `FinBoolAlg` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : FinBoolAlgCat ≌ FinBoolAlgCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align FinBoolAlg.dual_equiv FinBoolAlgCat.dualEquiv
-/

end FinBoolAlgCat

#print finBoolAlgCat_dual_comp_forget_to_finBddDistLatCat /-
theorem finBoolAlgCat_dual_comp_forget_to_finBddDistLatCat :
    FinBoolAlgCat.dual ⋙ forget₂ FinBoolAlgCat FinBddDistLatCat =
      forget₂ FinBoolAlgCat FinBddDistLatCat ⋙ FinBddDistLatCat.dual :=
  rfl
#align FinBoolAlg_dual_comp_forget_to_FinBddDistLat finBoolAlgCat_dual_comp_forget_to_finBddDistLatCat
-/

#print fintypeToFinBoolAlgCatOp /-
/-- The powerset functor. `set` as a functor. -/
@[simps]
def fintypeToFinBoolAlgCatOp : FintypeCat ⥤ FinBoolAlgCatᵒᵖ
    where
  obj X := op <| FinBoolAlgCat.of (Set X)
  map X Y f :=
    Quiver.Hom.op <| (CompleteLatticeHom.setPreimage f : BoundedLatticeHom (Set Y) (Set X))
#align Fintype_to_FinBoolAlg_op fintypeToFinBoolAlgCatOp
-/

