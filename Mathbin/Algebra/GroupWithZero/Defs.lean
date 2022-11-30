/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Logic.Nontrivial
import Mathbin.Algebra.NeZero

/-!
# Typeclasses for groups with an adjoined zero element

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/563
> Any changes to this file require a corresponding PR to mathlib4.

This file provides just the typeclass definitions, and the projection lemmas that expose their
members.

## Main definitions

* `group_with_zero`
* `comm_group_with_zero`
-/


universe u

-- We have to fix the universe of `G₀` here, since the default argument to
-- `group_with_zero.div'` cannot contain a universe metavariable.
variable {G₀ : Type u} {M₀ M₀' G₀' : Type _}

#print MulZeroClass /-
/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
@[protect_proj]
class MulZeroClass (M₀ : Type _) extends Mul M₀, Zero M₀ where
  zero_mul : ∀ a : M₀, 0 * a = 0
  mul_zero : ∀ a : M₀, a * 0 = 0
#align mul_zero_class MulZeroClass
-/

section MulZeroClass

variable [MulZeroClass M₀] {a b : M₀}

@[ematch, simp]
theorem zero_mul (a : M₀) : 0 * a = 0 :=
  MulZeroClass.zero_mul a
#align zero_mul zero_mul

@[ematch, simp]
theorem mul_zero (a : M₀) : a * 0 = 0 :=
  MulZeroClass.mul_zero a
#align mul_zero mul_zero

end MulZeroClass

#print NoZeroDivisors /-
/-- Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`
for all `a` and `b` of type `G₀`. -/
class NoZeroDivisors (M₀ : Type _) [Mul M₀] [Zero M₀] : Prop where
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0
#align no_zero_divisors NoZeroDivisors
-/

export NoZeroDivisors (eq_zero_or_eq_zero_of_mul_eq_zero)

#print SemigroupWithZero /-
/-- A type `S₀` is a "semigroup with zero” if it is a semigroup with zero element, and `0` is left
and right absorbing. -/
@[protect_proj]
class SemigroupWithZero (S₀ : Type _) extends Semigroup S₀, MulZeroClass S₀
#align semigroup_with_zero SemigroupWithZero
-/

#print MulZeroOneClass /-
/- By defining this _after_ `semigroup_with_zero`, we ensure that searches for `mul_zero_class` find
this class first. -/
/-- A typeclass for non-associative monoids with zero elements. -/
@[protect_proj]
class MulZeroOneClass (M₀ : Type _) extends MulOneClass M₀, MulZeroClass M₀
#align mul_zero_one_class MulZeroOneClass
-/

#print MonoidWithZero /-
/-- A type `M₀` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
@[protect_proj]
class MonoidWithZero (M₀ : Type _) extends Monoid M₀, MulZeroOneClass M₀
#align monoid_with_zero MonoidWithZero
-/

#print MonoidWithZero.toSemigroupWithZero /-
-- see Note [lower instance priority]
instance (priority := 100) MonoidWithZero.toSemigroupWithZero (M₀ : Type _) [MonoidWithZero M₀] :
    SemigroupWithZero M₀ :=
  { ‹MonoidWithZero M₀› with }
#align monoid_with_zero.to_semigroup_with_zero MonoidWithZero.toSemigroupWithZero
-/

#print CancelMonoidWithZero /-
/-- A type `M` is a `cancel_monoid_with_zero` if it is a monoid with zero element, `0` is left
and right absorbing, and left/right multiplication by a non-zero element is injective. -/
@[protect_proj]
class CancelMonoidWithZero (M₀ : Type _) extends MonoidWithZero M₀ where
  mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c
  mul_right_cancel_of_ne_zero : ∀ {a b c : M₀}, b ≠ 0 → a * b = c * b → a = c
#align cancel_monoid_with_zero CancelMonoidWithZero
-/

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

/- warning: mul_left_cancel₀ -> mul_left_cancel₀ is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} M₀] {a : M₀} {b : M₀} {c : M₀}, (Ne.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_1)))))))) -> (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_1))))) a b) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_1))))) a c)) -> (Eq.{succ u_1} M₀ b c)
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.335 : CancelMonoidWithZero.{u_1} M₀] {a : M₀} {b : M₀} {c : M₀}, (Ne.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MonoidWithZero.toZero.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.335))))) -> (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.335))))) a b) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.335))))) a c)) -> (Eq.{succ u_1} M₀ b c)
Case conversion may be inaccurate. Consider using '#align mul_left_cancel₀ mul_left_cancel₀ₓ'. -/
theorem mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  CancelMonoidWithZero.mul_left_cancel_of_ne_zero ha h
#align mul_left_cancel₀ mul_left_cancel₀

/- warning: mul_right_cancel₀ -> mul_right_cancel₀ is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} M₀] {a : M₀} {b : M₀} {c : M₀}, (Ne.{succ u_1} M₀ b (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_1)))))))) -> (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_1))))) a b) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_1))))) c b)) -> (Eq.{succ u_1} M₀ a c)
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.368 : CancelMonoidWithZero.{u_1} M₀] {a : M₀} {b : M₀} {c : M₀}, (Ne.{succ u_1} M₀ b (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MonoidWithZero.toZero.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.368))))) -> (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.368))))) a b) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.368))))) c b)) -> (Eq.{succ u_1} M₀ a c)
Case conversion may be inaccurate. Consider using '#align mul_right_cancel₀ mul_right_cancel₀ₓ'. -/
theorem mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
  CancelMonoidWithZero.mul_right_cancel_of_ne_zero hb h
#align mul_right_cancel₀ mul_right_cancel₀

/- warning: mul_right_injective₀ -> mul_right_injective₀ is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} M₀] {a : M₀}, (Ne.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_1)))))))) -> (Function.Injective.{succ u_1, succ u_1} M₀ M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_1))))) a))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.401 : CancelMonoidWithZero.{u_1} M₀] {a : M₀}, (Ne.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MonoidWithZero.toZero.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.401))))) -> (Function.Injective.{succ u_1, succ u_1} M₀ M₀ ((fun (x._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.419 : M₀) (x._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.421 : M₀) => HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.401))))) x._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.419 x._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.421) a))
Case conversion may be inaccurate. Consider using '#align mul_right_injective₀ mul_right_injective₀ₓ'. -/
theorem mul_right_injective₀ (ha : a ≠ 0) : Function.Injective ((· * ·) a) := fun b c =>
  mul_left_cancel₀ ha
#align mul_right_injective₀ mul_right_injective₀

/- warning: mul_left_injective₀ -> mul_left_injective₀ is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} M₀] {b : M₀}, (Ne.{succ u_1} M₀ b (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_1)))))))) -> (Function.Injective.{succ u_1, succ u_1} M₀ M₀ (fun (a : M₀) => HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_1))))) a b))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.445 : CancelMonoidWithZero.{u_1} M₀] {b : M₀}, (Ne.{succ u_1} M₀ b (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MonoidWithZero.toZero.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.445))))) -> (Function.Injective.{succ u_1, succ u_1} M₀ M₀ (fun (a : M₀) => HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.445))))) a b))
Case conversion may be inaccurate. Consider using '#align mul_left_injective₀ mul_left_injective₀ₓ'. -/
theorem mul_left_injective₀ (hb : b ≠ 0) : Function.Injective fun a => a * b := fun a c =>
  mul_right_cancel₀ hb
#align mul_left_injective₀ mul_left_injective₀

end CancelMonoidWithZero

#print CommMonoidWithZero /-
/-- A type `M` is a commutative “monoid with zero” if it is a commutative monoid with zero
element, and `0` is left and right absorbing. -/
@[protect_proj]
class CommMonoidWithZero (M₀ : Type _) extends CommMonoid M₀, MonoidWithZero M₀
#align comm_monoid_with_zero CommMonoidWithZero
-/

#print CancelCommMonoidWithZero /-
/-- A type `M` is a `cancel_comm_monoid_with_zero` if it is a commutative monoid with zero element,
 `0` is left and right absorbing,
  and left/right multiplication by a non-zero element is injective. -/
@[protect_proj]
class CancelCommMonoidWithZero (M₀ : Type _) extends CommMonoidWithZero M₀, CancelMonoidWithZero M₀
#align cancel_comm_monoid_with_zero CancelCommMonoidWithZero
-/

#print GroupWithZero /-
/-- A type `G₀` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.

Examples include division rings and the ordered monoids that are the
target of valuations in general valuation theory.-/
@[protect_proj]
class GroupWithZero (G₀ : Type u) extends MonoidWithZero G₀, DivInvMonoid G₀, Nontrivial G₀ where
  inv_zero : (0 : G₀)⁻¹ = 0
  mul_inv_cancel : ∀ a : G₀, a ≠ 0 → a * a⁻¹ = 1
#align group_with_zero GroupWithZero
-/

section GroupWithZero

variable [GroupWithZero G₀]

@[simp]
theorem inv_zero : (0 : G₀)⁻¹ = 0 :=
  GroupWithZero.inv_zero
#align inv_zero inv_zero

/- warning: mul_inv_cancel -> mul_inv_cancel is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u}} [_inst_1 : GroupWithZero.{u} G₀] {a : G₀}, (Ne.{succ u} G₀ a (OfNat.ofNat.{u} G₀ 0 (OfNat.mk.{u} G₀ 0 (Zero.zero.{u} G₀ (MulZeroClass.toHasZero.{u} G₀ (MulZeroOneClass.toMulZeroClass.{u} G₀ (MonoidWithZero.toMulZeroOneClass.{u} G₀ (GroupWithZero.toMonoidWithZero.{u} G₀ _inst_1)))))))) -> (Eq.{succ u} G₀ (HMul.hMul.{u, u, u} G₀ G₀ G₀ (instHMul.{u} G₀ (MulZeroClass.toHasMul.{u} G₀ (MulZeroOneClass.toMulZeroClass.{u} G₀ (MonoidWithZero.toMulZeroOneClass.{u} G₀ (GroupWithZero.toMonoidWithZero.{u} G₀ _inst_1))))) a (Inv.inv.{u} G₀ (DivInvMonoid.toHasInv.{u} G₀ (GroupWithZero.toDivInvMonoid.{u} G₀ _inst_1)) a)) (OfNat.ofNat.{u} G₀ 1 (OfNat.mk.{u} G₀ 1 (One.one.{u} G₀ (MulOneClass.toHasOne.{u} G₀ (MulZeroOneClass.toMulOneClass.{u} G₀ (MonoidWithZero.toMulZeroOneClass.{u} G₀ (GroupWithZero.toMonoidWithZero.{u} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.611 : GroupWithZero.{u} G₀] {a : G₀}, (Ne.{succ u} G₀ a (OfNat.ofNat.{u} G₀ 0 (Zero.toOfNat0.{u} G₀ (MonoidWithZero.toZero.{u} G₀ (GroupWithZero.toMonoidWithZero.{u} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.611))))) -> (Eq.{succ u} G₀ (HMul.hMul.{u, u, u} G₀ G₀ G₀ (instHMul.{u} G₀ (MulZeroClass.toMul.{u} G₀ (MulZeroOneClass.toMulZeroClass.{u} G₀ (MonoidWithZero.toMulZeroOneClass.{u} G₀ (GroupWithZero.toMonoidWithZero.{u} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.611))))) a (Inv.inv.{u} G₀ (GroupWithZero.toInv.{u} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.611) a)) (OfNat.ofNat.{u} G₀ 1 (One.toOfNat1.{u} G₀ (Monoid.toOne.{u} G₀ (MonoidWithZero.toMonoid.{u} G₀ (GroupWithZero.toMonoidWithZero.{u} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.611))))))
Case conversion may be inaccurate. Consider using '#align mul_inv_cancel mul_inv_cancelₓ'. -/
@[simp]
theorem mul_inv_cancel {a : G₀} (h : a ≠ 0) : a * a⁻¹ = 1 :=
  GroupWithZero.mul_inv_cancel a h
#align mul_inv_cancel mul_inv_cancel

end GroupWithZero

#print CommGroupWithZero /-
/-- A type `G₀` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`. -/
@[protect_proj]
class CommGroupWithZero (G₀ : Type _) extends CommMonoidWithZero G₀, GroupWithZero G₀
#align comm_group_with_zero CommGroupWithZero
-/

section NeZero

attribute [field_simps] two_ne_zero three_ne_zero four_ne_zero

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

variable (M₀)

/- warning: ne_zero.one -> NeZero.one is a dubious translation:
lean 3 declaration is
  forall (M₀ : Type.{u_1}) [_inst_1 : MulZeroOneClass.{u_1} M₀] [_inst_2 : Nontrivial.{u_1} M₀], NeZero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ _inst_1)) (OfNat.ofNat.{u_1} M₀ 1 (OfNat.mk.{u_1} M₀ 1 (One.one.{u_1} M₀ (MulOneClass.toHasOne.{u_1} M₀ (MulZeroOneClass.toMulOneClass.{u_1} M₀ _inst_1)))))
but is expected to have type
  forall (M₀ : Type.{u_1}) [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.720 : MulZeroOneClass.{u_1} M₀] [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.723 : Nontrivial.{u_1} M₀], NeZero.{u_1} M₀ (MulZeroOneClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.720) (OfNat.ofNat.{u_1} M₀ 1 (One.toOfNat1.{u_1} M₀ (MulOneClass.toOne.{u_1} M₀ (MulZeroOneClass.toMulOneClass.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.720))))
Case conversion may be inaccurate. Consider using '#align ne_zero.one NeZero.oneₓ'. -/
/-- In a nontrivial monoid with zero, zero and one are different. -/
instance NeZero.one : NeZero (1 : M₀) :=
  ⟨by 
    intro h
    rcases exists_pair_ne M₀ with ⟨x, y, hx⟩
    apply hx
    calc
      x = 1 * x := by rw [one_mul]
      _ = 0 := by rw [h, zero_mul]
      _ = 1 * y := by rw [h, zero_mul]
      _ = y := by rw [one_mul]
      ⟩
#align ne_zero.one NeZero.one

variable {M₀}

/- warning: pullback_nonzero -> pullback_nonzero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} {M₀' : Type.{u_2}} [_inst_1 : MulZeroOneClass.{u_1} M₀] [_inst_2 : Nontrivial.{u_1} M₀] [_inst_3 : Zero.{u_2} M₀'] [_inst_4 : One.{u_2} M₀'] (f : M₀' -> M₀), (Eq.{succ u_1} M₀ (f (OfNat.ofNat.{u_2} M₀' 0 (OfNat.mk.{u_2} M₀' 0 (Zero.zero.{u_2} M₀' _inst_3)))) (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ _inst_1)))))) -> (Eq.{succ u_1} M₀ (f (OfNat.ofNat.{u_2} M₀' 1 (OfNat.mk.{u_2} M₀' 1 (One.one.{u_2} M₀' _inst_4)))) (OfNat.ofNat.{u_1} M₀ 1 (OfNat.mk.{u_1} M₀ 1 (One.one.{u_1} M₀ (MulOneClass.toHasOne.{u_1} M₀ (MulZeroOneClass.toMulOneClass.{u_1} M₀ _inst_1)))))) -> (Nontrivial.{u_2} M₀')
but is expected to have type
  forall {M₀ : Type.{u_2}} {M₀' : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.915 : MulZeroOneClass.{u_2} M₀] [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.918 : Nontrivial.{u_2} M₀] [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.923 : Zero.{u_1} M₀'] [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.926 : One.{u_1} M₀'] (f : M₀' -> M₀), (Eq.{succ u_2} M₀ (f (OfNat.ofNat.{u_1} M₀' 0 (Zero.toOfNat0.{u_1} M₀' inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.923))) (OfNat.ofNat.{u_2} M₀ 0 (Zero.toOfNat0.{u_2} M₀ (MulZeroOneClass.toZero.{u_2} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.915)))) -> (Eq.{succ u_2} M₀ (f (OfNat.ofNat.{u_1} M₀' 1 (One.toOfNat1.{u_1} M₀' inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.926))) (OfNat.ofNat.{u_2} M₀ 1 (One.toOfNat1.{u_2} M₀ (MulOneClass.toOne.{u_2} M₀ (MulZeroOneClass.toMulOneClass.{u_2} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.915))))) -> (Nontrivial.{u_1} M₀')
Case conversion may be inaccurate. Consider using '#align pullback_nonzero pullback_nonzeroₓ'. -/
/-- Pullback a `nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
theorem pullback_nonzero [Zero M₀'] [One M₀'] (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) :
    Nontrivial M₀' :=
  ⟨⟨0, 1,
      mt (congr_arg f) <| by 
        rw [zero, one]
        exact zero_ne_one⟩⟩
#align pullback_nonzero pullback_nonzero

end NeZero

section MulZeroClass

variable [MulZeroClass M₀]

/- warning: mul_eq_zero_of_left -> mul_eq_zero_of_left is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} M₀] {a : M₀}, (Eq.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))) -> (forall (b : M₀), Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1)) a b) (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1012 : MulZeroClass.{u_1} M₀] {a : M₀}, (Eq.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1012)))) -> (forall (b : M₀), Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1012)) a b) (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1012))))
Case conversion may be inaccurate. Consider using '#align mul_eq_zero_of_left mul_eq_zero_of_leftₓ'. -/
theorem mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) : a * b = 0 :=
  h.symm ▸ zero_mul b
#align mul_eq_zero_of_left mul_eq_zero_of_left

/- warning: mul_eq_zero_of_right -> mul_eq_zero_of_right is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} M₀] (a : M₀) {b : M₀}, (Eq.{succ u_1} M₀ b (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))) -> (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1)) a b) (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1040 : MulZeroClass.{u_1} M₀] (a : M₀) {b : M₀}, (Eq.{succ u_1} M₀ b (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1040)))) -> (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1040)) a b) (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1040))))
Case conversion may be inaccurate. Consider using '#align mul_eq_zero_of_right mul_eq_zero_of_rightₓ'. -/
theorem mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0) : a * b = 0 :=
  h.symm ▸ mul_zero a
#align mul_eq_zero_of_right mul_eq_zero_of_right

variable [NoZeroDivisors M₀] {a b : M₀}

/- warning: mul_eq_zero -> mul_eq_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} M₀] [_inst_2 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1) (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1)) a b) (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))) (Or (Eq.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))) (Eq.{succ u_1} M₀ b (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1084 : MulZeroClass.{u_1} M₀] [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1087 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1084) (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1084)] {a : M₀} {b : M₀}, Iff (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1084)) a b) (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1084)))) (Or (Eq.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1084)))) (Eq.{succ u_1} M₀ b (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1084)))))
Case conversion may be inaccurate. Consider using '#align mul_eq_zero mul_eq_zeroₓ'. -/
/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero, fun o =>
    o.elim (fun h => mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩
#align mul_eq_zero mul_eq_zero

/- warning: zero_eq_mul -> zero_eq_mul is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} M₀] [_inst_2 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1) (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Eq.{succ u_1} M₀ (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1)) a b)) (Or (Eq.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))) (Eq.{succ u_1} M₀ b (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1139 : MulZeroClass.{u_1} M₀] [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1142 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1139) (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1139)] {a : M₀} {b : M₀}, Iff (Eq.{succ u_1} M₀ (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1139))) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1139)) a b)) (Or (Eq.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1139)))) (Eq.{succ u_1} M₀ b (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1139)))))
Case conversion may be inaccurate. Consider using '#align zero_eq_mul zero_eq_mulₓ'. -/
/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 := by rw [eq_comm, mul_eq_zero]
#align zero_eq_mul zero_eq_mul

/- warning: mul_ne_zero_iff -> mul_ne_zero_iff is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} M₀] [_inst_2 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1) (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Ne.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1)) a b) (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))) (And (Ne.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))) (Ne.{succ u_1} M₀ b (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1204 : MulZeroClass.{u_1} M₀] [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1207 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1204) (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1204)] {a : M₀} {b : M₀}, Iff (Ne.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1204)) a b) (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1204)))) (And (Ne.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1204)))) (Ne.{succ u_1} M₀ b (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1204)))))
Case conversion may be inaccurate. Consider using '#align mul_ne_zero_iff mul_ne_zero_iffₓ'. -/
/-- If `α` has no zero divisors, then the product of two elements is nonzero iff both of them
are nonzero. -/
theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  mul_eq_zero.Not.trans not_or
#align mul_ne_zero_iff mul_ne_zero_iff

/- warning: mul_eq_zero_comm -> mul_eq_zero_comm is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} M₀] [_inst_2 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1) (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1)) a b) (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))) (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1)) b a) (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1244 : MulZeroClass.{u_1} M₀] [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1247 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1244) (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1244)] {a : M₀} {b : M₀}, Iff (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1244)) a b) (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1244)))) (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1244)) b a) (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1244))))
Case conversion may be inaccurate. Consider using '#align mul_eq_zero_comm mul_eq_zero_commₓ'. -/
/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` equals zero iff so is
`b * a`. -/
theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 :=
  mul_eq_zero.trans <| (or_comm' _ _).trans mul_eq_zero.symm
#align mul_eq_zero_comm mul_eq_zero_comm

/- warning: mul_ne_zero_comm -> mul_ne_zero_comm is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} M₀] [_inst_2 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1) (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Ne.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1)) a b) (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))) (Ne.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1)) b a) (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1279 : MulZeroClass.{u_1} M₀] [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1282 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1279) (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1279)] {a : M₀} {b : M₀}, Iff (Ne.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1279)) a b) (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1279)))) (Ne.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1279)) b a) (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1279))))
Case conversion may be inaccurate. Consider using '#align mul_ne_zero_comm mul_ne_zero_commₓ'. -/
/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` is nonzero iff so is
`b * a`. -/
theorem mul_ne_zero_comm : a * b ≠ 0 ↔ b * a ≠ 0 :=
  mul_eq_zero_comm.Not
#align mul_ne_zero_comm mul_ne_zero_comm

/- warning: mul_self_eq_zero -> mul_self_eq_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} M₀] [_inst_2 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1) (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)] {a : M₀}, Iff (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1)) a a) (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))) (Eq.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1314 : MulZeroClass.{u_1} M₀] [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1317 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1314) (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1314)] {a : M₀}, Iff (Eq.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1314)) a a) (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1314)))) (Eq.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1314))))
Case conversion may be inaccurate. Consider using '#align mul_self_eq_zero mul_self_eq_zeroₓ'. -/
theorem mul_self_eq_zero : a * a = 0 ↔ a = 0 := by simp
#align mul_self_eq_zero mul_self_eq_zero

/- warning: zero_eq_mul_self -> zero_eq_mul_self is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} M₀] [_inst_2 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1) (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)] {a : M₀}, Iff (Eq.{succ u_1} M₀ (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1)) a a)) (Eq.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1346 : MulZeroClass.{u_1} M₀] [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1349 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1346) (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1346)] {a : M₀}, Iff (Eq.{succ u_1} M₀ (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1346))) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1346)) a a)) (Eq.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1346))))
Case conversion may be inaccurate. Consider using '#align zero_eq_mul_self zero_eq_mul_selfₓ'. -/
theorem zero_eq_mul_self : 0 = a * a ↔ a = 0 := by simp
#align zero_eq_mul_self zero_eq_mul_self

/- warning: mul_self_ne_zero -> mul_self_ne_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} M₀] [_inst_2 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1) (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)] {a : M₀}, Iff (Ne.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1)) a a) (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1))))) (Ne.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1378 : MulZeroClass.{u_1} M₀] [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1381 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1378) (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1378)] {a : M₀}, Iff (Ne.{succ u_1} M₀ (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1378)) a a) (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1378)))) (Ne.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1378))))
Case conversion may be inaccurate. Consider using '#align mul_self_ne_zero mul_self_ne_zeroₓ'. -/
theorem mul_self_ne_zero : a * a ≠ 0 ↔ a ≠ 0 :=
  mul_self_eq_zero.Not
#align mul_self_ne_zero mul_self_ne_zero

/- warning: zero_ne_mul_self -> zero_ne_mul_self is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} M₀] [_inst_2 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1) (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)] {a : M₀}, Iff (Ne.{succ u_1} M₀ (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ _inst_1)) a a)) (Ne.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (OfNat.mk.{u_1} M₀ 0 (Zero.zero.{u_1} M₀ (MulZeroClass.toHasZero.{u_1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1409 : MulZeroClass.{u_1} M₀] [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1412 : NoZeroDivisors.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1409) (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1409)] {a : M₀}, Iff (Ne.{succ u_1} M₀ (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1409))) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1409)) a a)) (Ne.{succ u_1} M₀ a (OfNat.ofNat.{u_1} M₀ 0 (Zero.toOfNat0.{u_1} M₀ (MulZeroClass.toZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.1409))))
Case conversion may be inaccurate. Consider using '#align zero_ne_mul_self zero_ne_mul_selfₓ'. -/
theorem zero_ne_mul_self : 0 ≠ a * a ↔ a ≠ 0 :=
  zero_eq_mul_self.Not
#align zero_ne_mul_self zero_ne_mul_self

end MulZeroClass

