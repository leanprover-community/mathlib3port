/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, Robert Y. Lewis

! This file was ported from Lean 3 source module group_theory.eckmann_hilton
! leanprover-community/mathlib commit 550b58538991c8977703fdeb7c9d51a5aa27df11
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs

/-!
# Eckmann-Hilton argument

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/626
> Any changes to this file require a corresponding PR to mathlib4.

The Eckmann-Hilton argument says that if a type carries two monoid structures that distribute
over one another, then they are equal, and in addition commutative.
The main application lies in proving that higher homotopy groups (`πₙ` for `n ≥ 2`) are commutative.

## Main declarations

* `eckmann_hilton.comm_monoid`: If a type carries a unital magma structure that distributes
  over a unital binary operation, then the magma is a commutative monoid.
* `eckmann_hilton.comm_group`: If a type carries a group structure that distributes
  over a unital binary operation, then the group is commutative.

-/


universe u

namespace EckmannHilton

variable {X : Type u}

-- mathport name: «expr < > »
local notation a " <" m "> " b => m a b

#print EckmannHilton.IsUnital /-
/-- `is_unital m e` expresses that `e : X` is a left and right unit
for the binary operation `m : X → X → X`. -/
structure IsUnital (m : X → X → X) (e : X) extends IsLeftId _ m e, IsRightId _ m e : Prop
#align eckmann_hilton.is_unital EckmannHilton.IsUnital
-/

/- warning: eckmann_hilton.mul_one_class.is_unital -> EckmannHilton.MulOneClass.isUnital is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [G : MulOneClass.{u1} X], EckmannHilton.IsUnital.{u1} X (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X G))) (OfNat.ofNat.{u1} X 1 (OfNat.mk.{u1} X 1 (One.one.{u1} X (MulOneClass.toHasOne.{u1} X G))))
but is expected to have type
  forall {X : Type.{u1}} [G : MulOneClass.{u1} X], EckmannHilton.IsUnital.{u1} X (fun (x._@.Mathlib.GroupTheory.EckmannHilton._hyg.252 : X) (x._@.Mathlib.GroupTheory.EckmannHilton._hyg.254 : X) => HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X G)) x._@.Mathlib.GroupTheory.EckmannHilton._hyg.252 x._@.Mathlib.GroupTheory.EckmannHilton._hyg.254) (OfNat.ofNat.{u1} X 1 (One.toOfNat1.{u1} X (MulOneClass.toOne.{u1} X G)))
Case conversion may be inaccurate. Consider using '#align eckmann_hilton.mul_one_class.is_unital EckmannHilton.MulOneClass.isUnitalₓ'. -/
@[to_additive EckmannHilton.AddZeroClass.is_unital]
theorem MulOneClass.isUnital [G : MulOneClass X] : IsUnital (· * ·) (1 : X) :=
  IsUnital.mk (by infer_instance) (by infer_instance)
#align eckmann_hilton.mul_one_class.is_unital EckmannHilton.MulOneClass.isUnital

variable {m₁ m₂ : X → X → X} {e₁ e₂ : X}

variable (h₁ : IsUnital m₁ e₁) (h₂ : IsUnital m₂ e₂)

variable (distrib : ∀ a b c d, ((a <m₂> b) <m₁> c <m₂> d) = (a <m₁> c) <m₂> b <m₁> d)

include h₁ h₂ distrib

#print EckmannHilton.one /-
/-- If a type carries two unital binary operations that distribute over each other,
then they have the same unit elements.

In fact, the two operations are the same, and give a commutative monoid structure,
see `eckmann_hilton.comm_monoid`. -/
theorem one : e₁ = e₂ := by
  simpa only [h₁.left_id, h₁.right_id, h₂.left_id, h₂.right_id] using Distrib e₂ e₁ e₁ e₂
#align eckmann_hilton.one EckmannHilton.one
-/

#print EckmannHilton.mul /-
/-- If a type carries two unital binary operations that distribute over each other,
then these operations are equal.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
theorem mul : m₁ = m₂ := by 
  funext a b
  calc
    m₁ a b = m₁ (m₂ a e₁) (m₂ e₁ b) := by
      simp only [one h₁ h₂ Distrib, h₁.left_id, h₁.right_id, h₂.left_id, h₂.right_id]
    _ = m₂ a b := by simp only [Distrib, h₁.left_id, h₁.right_id, h₂.left_id, h₂.right_id]
    
#align eckmann_hilton.mul EckmannHilton.mul
-/

#print EckmannHilton.mul_comm /-
/-- If a type carries two unital binary operations that distribute over each other,
then these operations are commutative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
theorem mul_comm : IsCommutative _ m₂ :=
  ⟨fun a b => by simpa [mul h₁ h₂ Distrib, h₂.left_id, h₂.right_id] using Distrib e₂ a b e₂⟩
#align eckmann_hilton.mul_comm EckmannHilton.mul_comm
-/

#print EckmannHilton.mul_assoc /-
/-- If a type carries two unital binary operations that distribute over each other,
then these operations are associative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.comm_monoid`. -/
theorem mul_assoc : IsAssociative _ m₂ :=
  ⟨fun a b c => by simpa [mul h₁ h₂ Distrib, h₂.left_id, h₂.right_id] using Distrib a b e₂ c⟩
#align eckmann_hilton.mul_assoc EckmannHilton.mul_assoc
-/

omit h₁ h₂ distrib

/- warning: eckmann_hilton.comm_monoid -> EckmannHilton.commMonoid is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m₁ : X -> X -> X} {e₁ : X}, (EckmannHilton.IsUnital.{u1} X m₁ e₁) -> (forall [h : MulOneClass.{u1} X], (forall (a : X) (b : X) (c : X) (d : X), Eq.{succ u1} X (m₁ (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X h)) a b) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X h)) c d)) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X h)) (m₁ a c) (m₁ b d))) -> (CommMonoid.{u1} X))
but is expected to have type
  forall {X : Type.{u1}} {m₁ : X -> X -> X} {e₁ : X}, (EckmannHilton.IsUnital.{u1} X m₁ e₁) -> (forall [h : MulOneClass.{u1} X], (forall (a : X) (b : X) (c : X) (d : X), Eq.{succ u1} X (m₁ (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X h)) a b) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X h)) c d)) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X h)) (m₁ a c) (m₁ b d))) -> (CommMonoid.{u1} X))
Case conversion may be inaccurate. Consider using '#align eckmann_hilton.comm_monoid EckmannHilton.commMonoidₓ'. -/
/-- If a type carries a unital magma structure that distributes over a unital binary
operations, then the magma structure is a commutative monoid. -/
@[reducible,
  to_additive
      "If a type carries a unital additive magma structure that distributes over\na unital binary operations, then the additive magma structure is a commutative additive monoid."]
def commMonoid [h : MulOneClass X]
    (distrib : ∀ a b c d, ((a * b) <m₁> c * d) = (a <m₁> c) * b <m₁> d) : CommMonoid X :=
  { h with 
    mul := (· * ·)
    one := 1
    mul_comm := (mul_comm h₁ MulOneClass.isUnital Distrib).comm
    mul_assoc := (mul_assoc h₁ MulOneClass.isUnital Distrib).assoc }
#align eckmann_hilton.comm_monoid EckmannHilton.commMonoid

/- warning: eckmann_hilton.comm_group -> EckmannHilton.commGroup is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m₁ : X -> X -> X} {e₁ : X}, (EckmannHilton.IsUnital.{u1} X m₁ e₁) -> (forall [G : Group.{u1} X], (forall (a : X) (b : X) (c : X) (d : X), Eq.{succ u1} X (m₁ (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X (Monoid.toMulOneClass.{u1} X (DivInvMonoid.toMonoid.{u1} X (Group.toDivInvMonoid.{u1} X G))))) a b) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X (Monoid.toMulOneClass.{u1} X (DivInvMonoid.toMonoid.{u1} X (Group.toDivInvMonoid.{u1} X G))))) c d)) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toHasMul.{u1} X (Monoid.toMulOneClass.{u1} X (DivInvMonoid.toMonoid.{u1} X (Group.toDivInvMonoid.{u1} X G))))) (m₁ a c) (m₁ b d))) -> (CommGroup.{u1} X))
but is expected to have type
  forall {X : Type.{u1}} {m₁ : X -> X -> X} {e₁ : X}, (EckmannHilton.IsUnital.{u1} X m₁ e₁) -> (forall [G : Group.{u1} X], (forall (a : X) (b : X) (c : X) (d : X), Eq.{succ u1} X (m₁ (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X (Monoid.toMulOneClass.{u1} X (DivInvMonoid.toMonoid.{u1} X (Group.toDivInvMonoid.{u1} X G))))) a b) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X (Monoid.toMulOneClass.{u1} X (DivInvMonoid.toMonoid.{u1} X (Group.toDivInvMonoid.{u1} X G))))) c d)) (HMul.hMul.{u1, u1, u1} X X X (instHMul.{u1} X (MulOneClass.toMul.{u1} X (Monoid.toMulOneClass.{u1} X (DivInvMonoid.toMonoid.{u1} X (Group.toDivInvMonoid.{u1} X G))))) (m₁ a c) (m₁ b d))) -> (CommGroup.{u1} X))
Case conversion may be inaccurate. Consider using '#align eckmann_hilton.comm_group EckmannHilton.commGroupₓ'. -/
/-- If a type carries a group structure that distributes over a unital binary operation,
then the group is commutative. -/
@[reducible,
  to_additive
      "If a type carries an additive group structure that\ndistributes over a unital binary operation, then the additive group is commutative."]
def commGroup [G : Group X] (distrib : ∀ a b c d, ((a * b) <m₁> c * d) = (a <m₁> c) * b <m₁> d) :
    CommGroup X :=
  { EckmannHilton.commMonoid h₁ Distrib, G with }
#align eckmann_hilton.comm_group EckmannHilton.commGroup

end EckmannHilton

