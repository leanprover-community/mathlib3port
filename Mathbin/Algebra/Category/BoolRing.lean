/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Algebra.Category.Ring.Basic
import Algebra.Ring.BooleanRing
import Order.Category.BoolAlg

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

#print BoolRing /-
/-- The category of Boolean rings. -/
def BoolRing :=
  Bundled BooleanRing
#align BoolRing BoolRing
-/

namespace BoolRing

instance : CoeSort BoolRing (Type _) :=
  Bundled.hasCoeToSort

instance (X : BoolRing) : BooleanRing X :=
  X.str

#print BoolRing.of /-
/-- Construct a bundled `BoolRing` from a `boolean_ring`. -/
def of (α : Type _) [BooleanRing α] : BoolRing :=
  Bundled.of α
#align BoolRing.of BoolRing.of
-/

#print BoolRing.coe_of /-
@[simp]
theorem coe_of (α : Type _) [BooleanRing α] : ↥(of α) = α :=
  rfl
#align BoolRing.coe_of BoolRing.coe_of
-/

instance : Inhabited BoolRing :=
  ⟨of PUnit⟩

instance : BundledHom.ParentProjection @BooleanRing.toCommRing :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for BoolRing

#print BoolRing.hasForgetToCommRing /-
@[simps]
instance hasForgetToCommRing : HasForget₂ BoolRing CommRingCat :=
  BundledHom.forget₂ _ _
#align BoolRing.has_forget_to_CommRing BoolRing.hasForgetToCommRing
-/

#print BoolRing.Iso.mk /-
/-- Constructs an isomorphism of Boolean rings from a ring isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolRing.{u}} (e : α ≃+* β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align BoolRing.iso.mk BoolRing.Iso.mk
-/

end BoolRing

/-! ### Equivalence between `BoolAlg` and `BoolRing` -/


#print BoolRing.hasForgetToBoolAlg /-
@[simps]
instance BoolRing.hasForgetToBoolAlg : HasForget₂ BoolRing BoolAlg
    where forget₂ :=
    { obj := fun X => BoolAlg.of (AsBoolAlg X)
      map := fun X Y => RingHom.asBoolAlg }
#align BoolRing.has_forget_to_BoolAlg BoolRing.hasForgetToBoolAlg
-/

#print BoolAlg.hasForgetToBoolRing /-
@[simps]
instance BoolAlg.hasForgetToBoolRing : HasForget₂ BoolAlg BoolRing
    where forget₂ :=
    { obj := fun X => BoolRing.of (AsBoolRing X)
      map := fun X Y => BoundedLatticeHom.asBoolRing }
#align BoolAlg.has_forget_to_BoolRing BoolAlg.hasForgetToBoolRing
-/

#print boolRingCatEquivBoolAlg /-
/-- The equivalence between Boolean rings and Boolean algebras. This is actually an isomorphism. -/
@[simps Functor inverse]
def boolRingCatEquivBoolAlg : BoolRing ≌ BoolAlg :=
  Equivalence.mk (forget₂ BoolRing BoolAlg) (forget₂ BoolAlg BoolRing)
    (NatIso.ofComponents (fun X => BoolRing.Iso.mk <| (RingEquiv.asBoolRingAsBoolAlg X).symm)
      fun X Y f => rfl)
    (NatIso.ofComponents (fun X => BoolAlg.Iso.mk <| OrderIso.asBoolAlgAsBoolRing X) fun X Y f =>
      rfl)
#align BoolRing_equiv_BoolAlg boolRingCatEquivBoolAlg
-/

