/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.category.BoolRing
! leanprover-community/mathlib commit d3e8e0a0237c10c2627bf52c246b15ff8e7df4c0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.RingCat.Basic
import Mathbin.Algebra.Ring.BooleanRing
import Mathbin.Order.Category.BoolAlgCat

/-!
# The category of Boolean rings

This file defines `BoolRing`, the category of Boolean rings.

## TODO

Finish the equivalence with `BoolAlg`.
-/


universe u

open CategoryTheory Order

/-- The category of Boolean rings. -/
def BoolRingCat :=
  Bundled BooleanRing
#align BoolRing BoolRingCat

namespace BoolRingCat

instance : CoeSort BoolRingCat (Type _) :=
  bundled.has_coe_to_sort

instance (X : BoolRingCat) : BooleanRing X :=
  X.str

/-- Construct a bundled `BoolRing` from a `boolean_ring`. -/
def of (α : Type _) [BooleanRing α] : BoolRingCat :=
  Bundled.of α
#align BoolRing.of BoolRingCat.of

@[simp]
theorem coe_of (α : Type _) [BooleanRing α] : ↥(of α) = α :=
  rfl
#align BoolRing.coe_of BoolRingCat.coe_of

instance : Inhabited BoolRingCat :=
  ⟨of PUnit⟩

instance : BundledHom.ParentProjection @BooleanRing.toCommRing :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for BoolRingCat

@[simps]
instance hasForgetToCommRing : HasForget₂ BoolRingCat CommRingCat :=
  BundledHom.forget₂ _ _
#align BoolRing.has_forget_to_CommRing BoolRingCat.hasForgetToCommRing

/-- Constructs an isomorphism of Boolean rings from a ring isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolRingCat.{u}} (e : α ≃+* β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align BoolRing.iso.mk BoolRingCat.Iso.mk

end BoolRingCat

/-! ### Equivalence between `BoolAlg` and `BoolRing` -/


@[simps]
instance BoolRingCat.hasForgetToBoolAlg : HasForget₂ BoolRingCat BoolAlgCat
    where forget₂ :=
    { obj := fun X => BoolAlgCat.of (AsBoolalg X)
      map := fun X Y => RingHom.asBoolalg }
#align BoolRing.has_forget_to_BoolAlg BoolRingCat.hasForgetToBoolAlg

@[simps]
instance BoolAlgCat.hasForgetToBoolRing : HasForget₂ BoolAlgCat BoolRingCat
    where forget₂ :=
    { obj := fun X => BoolRingCat.of (AsBoolring X)
      map := fun X Y => BoundedLatticeHom.asBoolring }
#align BoolAlg.has_forget_to_BoolRing BoolAlgCat.hasForgetToBoolRing

/-- The equivalence between Boolean rings and Boolean algebras. This is actually an isomorphism. -/
@[simps Functor inverse]
def boolRingEquivBoolAlg : BoolRingCat ≌ BoolAlgCat :=
  Equivalence.mk (forget₂ BoolRingCat BoolAlgCat) (forget₂ BoolAlgCat BoolRingCat)
    ((NatIso.ofComponents fun X => BoolRingCat.Iso.mk <| (RingEquiv.asBoolringAsBoolalg X).symm)
      fun X Y f => rfl)
    ((NatIso.ofComponents fun X => BoolAlgCat.Iso.mk <| OrderIso.asBoolalgAsBoolring X) fun X Y f =>
      rfl)
#align BoolRing_equiv_BoolAlg boolRingEquivBoolAlg

