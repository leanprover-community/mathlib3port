/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.Algebra.Ring.BooleanRing
import Mathbin.Order.Category.BoolAlg

#align_import algebra.category.BoolRing from "leanprover-community/mathlib"@"2a0ce625dbb0ffbc7d1316597de0b25c1ec75303"

/-!
# The category of Boolean rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `BoolRing`, the category of Boolean rings.

## TODO

Finish the equivalence with `BoolAlg`.
-/


universe u

open CategoryTheory Order

#print BoolRingCat /-
/-- The category of Boolean rings. -/
def BoolRingCat :=
  Bundled BooleanRing
#align BoolRing BoolRingCat
-/

namespace BoolRingCat

instance : CoeSort BoolRingCat (Type _) :=
  Bundled.hasCoeToSort

instance (X : BoolRingCat) : BooleanRing X :=
  X.str

#print BoolRingCat.of /-
/-- Construct a bundled `BoolRing` from a `boolean_ring`. -/
def of (α : Type _) [BooleanRing α] : BoolRingCat :=
  Bundled.of α
#align BoolRing.of BoolRingCat.of
-/

#print BoolRingCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [BooleanRing α] : ↥(of α) = α :=
  rfl
#align BoolRing.coe_of BoolRingCat.coe_of
-/

instance : Inhabited BoolRingCat :=
  ⟨of PUnit⟩

instance : BundledHom.ParentProjection @BooleanRing.toCommRing :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for BoolRingCat

#print BoolRingCat.hasForgetToCommRing /-
@[simps]
instance hasForgetToCommRing : HasForget₂ BoolRingCat CommRingCat :=
  BundledHom.forget₂ _ _
#align BoolRing.has_forget_to_CommRing BoolRingCat.hasForgetToCommRing
-/

#print BoolRingCat.Iso.mk /-
/-- Constructs an isomorphism of Boolean rings from a ring isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolRingCat.{u}} (e : α ≃+* β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align BoolRing.iso.mk BoolRingCat.Iso.mk
-/

end BoolRingCat

/-! ### Equivalence between `BoolAlg` and `BoolRing` -/


#print BoolRingCat.hasForgetToBoolAlgCat /-
@[simps]
instance BoolRingCat.hasForgetToBoolAlgCat : HasForget₂ BoolRingCat BoolAlgCat
    where forget₂ :=
    { obj := fun X => BoolAlgCat.of (AsBoolAlg X)
      map := fun X Y => RingHom.asBoolAlg }
#align BoolRing.has_forget_to_BoolAlg BoolRingCat.hasForgetToBoolAlgCat
-/

@[simps]
instance BoolAlgCat.hasForgetToBoolRing : HasForget₂ BoolAlgCat BoolRingCat
    where forget₂ :=
    { obj := fun X => BoolRingCat.of (AsBoolRing X)
      map := fun X Y => BoundedLatticeHom.asBoolRing }
#align BoolAlg.has_forget_to_BoolRing BoolAlgCat.hasForgetToBoolRing

#print boolRingCatEquivBoolAlgCat /-
/-- The equivalence between Boolean rings and Boolean algebras. This is actually an isomorphism. -/
@[simps Functor inverse]
def boolRingCatEquivBoolAlgCat : BoolRingCat ≌ BoolAlgCat :=
  Equivalence.mk (forget₂ BoolRingCat BoolAlgCat) (forget₂ BoolAlgCat BoolRingCat)
    (NatIso.ofComponents (fun X => BoolRingCat.Iso.mk <| (RingEquiv.asBoolRingAsBoolAlg X).symm)
      fun X Y f => rfl)
    (NatIso.ofComponents (fun X => BoolAlgCat.Iso.mk <| OrderIso.asBoolAlgAsBoolRing X) fun X Y f =>
      rfl)
#align BoolRing_equiv_BoolAlg boolRingCatEquivBoolAlgCat
-/

