/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Data.Bracket

/-!
# The bracket on a group given by commutator.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/582
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
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] (g₁ : G) (g₂ : G), Eq.{succ u_1} G (Bracket.bracket.{u_1 u_1} G G (commutatorElement.{u_1} G _inst_1) g₁ g₂) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) g₁ g₂) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) g₁)) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) g₂))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commutator._hyg.51 : Group.{u_1} G] (g₁ : G) (g₂ : G), Eq.{succ u_1} G (Bracket.bracket.{u_1 u_1} G G (commutatorElement.{u_1} G inst._@.Mathlib.Algebra.Group.Commutator._hyg.51) g₁ g₂) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Commutator._hyg.51))))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Commutator._hyg.51))))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Commutator._hyg.51))))) g₁ g₂) (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Commutator._hyg.51)) g₁)) (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Commutator._hyg.51)) g₂))
Case conversion may be inaccurate. Consider using '#align commutator_element_def commutatorElement_defₓ'. -/
theorem commutatorElement_def {G : Type _} [Group G] (g₁ g₂ : G) : ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ :=
  rfl
#align commutator_element_def commutatorElement_def

