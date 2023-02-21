/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.category.BoolRing
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.Algebra.Ring.BooleanRing
import Mathbin.Order.Category.BoolAlg

/-!
# The category of Boolean rings

This file defines `BoolRing`, the category of Boolean rings.

## TODO

Finish the equivalence with `BoolAlg`.
-/


universe u

open CategoryTheory Order

/-- The category of Boolean rings. -/
def BoolRing :=
  Bundled BooleanRing
#align BoolRing BoolRing

namespace BoolRing

instance : CoeSort BoolRing (Type _) :=
  Bundled.hasCoeToSort

instance (X : BoolRing) : BooleanRing X :=
  X.str

/-- Construct a bundled `BoolRing` from a `boolean_ring`. -/
def of (α : Type _) [BooleanRing α] : BoolRing :=
  Bundled.of α
#align BoolRing.of BoolRing.of

@[simp]
theorem coe_of (α : Type _) [BooleanRing α] : ↥(of α) = α :=
  rfl
#align BoolRing.coe_of BoolRing.coe_of

instance : Inhabited BoolRing :=
  ⟨of PUnit⟩

instance : BundledHom.ParentProjection @BooleanRing.toCommRing :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for BoolRing

@[simps]
instance hasForgetToCommRing : HasForget₂ BoolRing CommRingCat :=
  BundledHom.forget₂ _ _
#align BoolRing.has_forget_to_CommRing BoolRing.hasForgetToCommRing

/-- Constructs an isomorphism of Boolean rings from a ring isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolRing.{u}} (e : α ≃+* β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align BoolRing.iso.mk BoolRing.Iso.mk

end BoolRing

/-! ### Equivalence between `BoolAlg` and `BoolRing` -/


@[simps]
instance BoolRing.hasForgetToBoolAlg : HasForget₂ BoolRing BoolAlg
    where forget₂ :=
    { obj := fun X => BoolAlg.of (AsBoolalg X)
      map := fun X Y => RingHom.asBoolalg }
#align BoolRing.has_forget_to_BoolAlg BoolRing.hasForgetToBoolAlg

@[simps]
instance BoolAlg.hasForgetToBoolRing : HasForget₂ BoolAlg BoolRing
    where forget₂ :=
    { obj := fun X => BoolRing.of (AsBoolring X)
      map := fun X Y => BoundedLatticeHom.asBoolring }
#align BoolAlg.has_forget_to_BoolRing BoolAlg.hasForgetToBoolRing

/-- The equivalence between Boolean rings and Boolean algebras. This is actually an isomorphism. -/
@[simps Functor inverse]
def boolRingEquivBoolAlg : BoolRing ≌ BoolAlg :=
  Equivalence.mk (forget₂ BoolRing BoolAlg) (forget₂ BoolAlg BoolRing)
    (NatIso.ofComponents (fun X => BoolRing.Iso.mk <| (RingEquiv.asBoolringAsBoolalg X).symm)
      fun X Y f => rfl)
    (NatIso.ofComponents (fun X => BoolAlg.Iso.mk <| OrderIso.asBoolalgAsBoolring X) fun X Y f =>
      rfl)
#align BoolRing_equiv_BoolAlg boolRingEquivBoolAlg

