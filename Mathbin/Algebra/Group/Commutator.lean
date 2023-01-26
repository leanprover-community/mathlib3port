/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

! This file was ported from Lean 3 source module algebra.group.commutator
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Data.Bracket

/-!
# The bracket on a group given by commutator.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


#print commutatorElement /-
/-- The commutator of two elements `g₁` and `g₂`. -/
instance commutatorElement {G : Type _} [Group G] : Bracket G G :=
  ⟨fun g₁ g₂ => g₁ * g₂ * g₁⁻¹ * g₂⁻¹⟩
#align commutator_element commutatorElement
-/

/- warning: commutator_element_def -> commutatorElement_def is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (g₁ : G) (g₂ : G), Eq.{succ u1} G (Bracket.bracket.{u1, u1} G G (commutatorElement.{u1} G _inst_1) g₁ g₂) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) g₁ g₂) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) g₁)) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) g₂))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (g₁ : G) (g₂ : G), Eq.{succ u1} G (Bracket.bracket.{u1, u1} G G (commutatorElement.{u1} G _inst_1) g₁ g₂) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) g₁ g₂) (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) g₁)) (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) g₂))
Case conversion may be inaccurate. Consider using '#align commutator_element_def commutatorElement_defₓ'. -/
theorem commutatorElement_def {G : Type _} [Group G] (g₁ g₂ : G) :
    ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ :=
  rfl
#align commutator_element_def commutatorElement_def

