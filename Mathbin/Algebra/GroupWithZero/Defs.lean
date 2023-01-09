/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.group_with_zero.defs
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Logic.Nontrivial
import Mathbin.Algebra.NeZero

/-!
# Typeclasses for groups with an adjoined zero element

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
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

#print IsLeftCancelMulZero /-
/-- A mixin for left cancellative multiplication by nonzero elements. -/
@[protect_proj]
class IsLeftCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c
#align is_left_cancel_mul_zero IsLeftCancelMulZero
-/

section IsLeftCancelMulZero

variable [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a b c : M₀}

#print mul_left_cancel₀ /-
theorem mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha h
#align mul_left_cancel₀ mul_left_cancel₀
-/

#print mul_right_injective₀ /-
theorem mul_right_injective₀ (ha : a ≠ 0) : Function.Injective ((· * ·) a) := fun b c =>
  mul_left_cancel₀ ha
#align mul_right_injective₀ mul_right_injective₀
-/

end IsLeftCancelMulZero

#print IsRightCancelMulZero /-
/-- A mixin for right cancellative multiplication by nonzero elements. -/
@[protect_proj]
class IsRightCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  mul_right_cancel_of_ne_zero : ∀ {a b c : M₀}, b ≠ 0 → a * b = c * b → a = c
#align is_right_cancel_mul_zero IsRightCancelMulZero
-/

section IsRightCancelMulZero

variable [Mul M₀] [Zero M₀] [IsRightCancelMulZero M₀] {a b c : M₀}

#print mul_right_cancel₀ /-
theorem mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
  IsRightCancelMulZero.mul_right_cancel_of_ne_zero hb h
#align mul_right_cancel₀ mul_right_cancel₀
-/

#print mul_left_injective₀ /-
theorem mul_left_injective₀ (hb : b ≠ 0) : Function.Injective fun a => a * b := fun a c =>
  mul_right_cancel₀ hb
#align mul_left_injective₀ mul_left_injective₀
-/

end IsRightCancelMulZero

#print IsCancelMulZero /-
/-- A mixin for cancellative multiplication by nonzero elements. -/
@[protect_proj]
class IsCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] extends IsLeftCancelMulZero M₀,
  IsRightCancelMulZero M₀ : Prop
#align is_cancel_mul_zero IsCancelMulZero
-/

section CommSemigroupWithZero

variable [CommSemigroup M₀] [Zero M₀]

theorem IsLeftCancelMulZero.to_is_right_cancel_mul_zero [IsLeftCancelMulZero M₀] :
    IsRightCancelMulZero M₀ :=
  ⟨fun a b c ha h => mul_left_cancel₀ ha <| (mul_comm _ _).trans <| h.trans (mul_comm _ _)⟩
#align
  is_left_cancel_mul_zero.to_is_right_cancel_mul_zero IsLeftCancelMulZero.to_is_right_cancel_mul_zero

theorem IsRightCancelMulZero.to_is_left_cancel_mul_zero [IsRightCancelMulZero M₀] :
    IsLeftCancelMulZero M₀ :=
  ⟨fun a b c ha h => mul_right_cancel₀ ha <| (mul_comm _ _).trans <| h.trans (mul_comm _ _)⟩
#align
  is_right_cancel_mul_zero.to_is_left_cancel_mul_zero IsRightCancelMulZero.to_is_left_cancel_mul_zero

theorem IsLeftCancelMulZero.to_is_cancel_mul_zero [IsLeftCancelMulZero M₀] : IsCancelMulZero M₀ :=
  { ‹IsLeftCancelMulZero M₀›, IsLeftCancelMulZero.to_is_right_cancel_mul_zero with }
#align is_left_cancel_mul_zero.to_is_cancel_mul_zero IsLeftCancelMulZero.to_is_cancel_mul_zero

theorem IsRightCancelMulZero.to_is_cancel_mul_zero [IsRightCancelMulZero M₀] : IsCancelMulZero M₀ :=
  { ‹IsRightCancelMulZero M₀›, IsRightCancelMulZero.to_is_left_cancel_mul_zero with }
#align is_right_cancel_mul_zero.to_is_cancel_mul_zero IsRightCancelMulZero.to_is_cancel_mul_zero

end CommSemigroupWithZero

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

/-- A `cancel_monoid_with_zero` satisfies `is_cancel_mul_zero`. -/
instance (priority := 100) CancelMonoidWithZero.to_is_cancel_mul_zero [CancelMonoidWithZero M₀] :
    IsCancelMulZero M₀ :=
  { ‹CancelMonoidWithZero M₀› with }
#align cancel_monoid_with_zero.to_is_cancel_mul_zero CancelMonoidWithZero.to_is_cancel_mul_zero

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
class CancelCommMonoidWithZero (M₀ : Type _) extends CommMonoidWithZero M₀ where
  mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c
#align cancel_comm_monoid_with_zero CancelCommMonoidWithZero
-/

#print CancelCommMonoidWithZero.toCancelMonoidWithZero /-
instance (priority := 100) CancelCommMonoidWithZero.toCancelMonoidWithZero
    [h : CancelCommMonoidWithZero M₀] : CancelMonoidWithZero M₀ :=
  { h, @IsLeftCancelMulZero.to_is_right_cancel_mul_zero M₀ _ _ { h with } with }
#align
  cancel_comm_monoid_with_zero.to_cancel_monoid_with_zero CancelCommMonoidWithZero.toCancelMonoidWithZero
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
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a)) (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a)) (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (Monoid.toOne.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))
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
  forall (M₀ : Type.{u1}) [_inst_1 : MulZeroOneClass.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀], NeZero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1)) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1)))))
but is expected to have type
  forall (M₀ : Type.{u1}) [_inst_1 : MulZeroOneClass.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀], NeZero.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (MulOneClass.toOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1))))
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
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] [_inst_3 : Zero.{u2} M₀'] [_inst_4 : One.{u2} M₀'] (f : M₀' -> M₀), (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_3)))) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1)))))) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 1 (OfNat.mk.{u2} M₀' 1 (One.one.{u2} M₀' _inst_4)))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1)))))) -> (Nontrivial.{u2} M₀')
but is expected to have type
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] [_inst_3 : Zero.{u2} M₀'] [_inst_4 : One.{u2} M₀'] (f : M₀' -> M₀), (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (Zero.toOfNat0.{u2} M₀' _inst_3))) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1)))) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 1 (One.toOfNat1.{u2} M₀' _inst_4))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (MulOneClass.toOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1))))) -> (Nontrivial.{u2} M₀')
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
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] {a : M₀}, (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) -> (forall (b : M₀), Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] {a : M₀}, (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) -> (forall (b : M₀), Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_eq_zero_of_left mul_eq_zero_of_leftₓ'. -/
theorem mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) : a * b = 0 :=
  h.symm ▸ zero_mul b
#align mul_eq_zero_of_left mul_eq_zero_of_left

/- warning: mul_eq_zero_of_right -> mul_eq_zero_of_right is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] (a : M₀) {b : M₀}, (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] (a : M₀) {b : M₀}, (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_eq_zero_of_right mul_eq_zero_of_rightₓ'. -/
theorem mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0) : a * b = 0 :=
  h.symm ▸ mul_zero a
#align mul_eq_zero_of_right mul_eq_zero_of_right

variable [NoZeroDivisors M₀] {a b : M₀}

/- warning: mul_eq_zero -> mul_eq_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1) (MulZeroClass.toHasZero.{u1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) (Or (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1) (MulZeroClass.toZero.{u1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) (Or (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))))
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
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1) (MulZeroClass.toHasZero.{u1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a b)) (Or (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1) (MulZeroClass.toZero.{u1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a b)) (Or (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align zero_eq_mul zero_eq_mulₓ'. -/
/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 := by rw [eq_comm, mul_eq_zero]
#align zero_eq_mul zero_eq_mul

/- warning: mul_ne_zero_iff -> mul_ne_zero_iff is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1) (MulZeroClass.toHasZero.{u1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) (And (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) (Ne.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1) (MulZeroClass.toZero.{u1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) (And (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) (Ne.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align mul_ne_zero_iff mul_ne_zero_iffₓ'. -/
/-- If `α` has no zero divisors, then the product of two elements is nonzero iff both of them
are nonzero. -/
theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  mul_eq_zero.Not.trans not_or
#align mul_ne_zero_iff mul_ne_zero_iff

/- warning: mul_eq_zero_comm -> mul_eq_zero_comm is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1) (MulZeroClass.toHasZero.{u1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) b a) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1) (MulZeroClass.toZero.{u1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) b a) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_eq_zero_comm mul_eq_zero_commₓ'. -/
/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` equals zero iff so is
`b * a`. -/
theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 :=
  mul_eq_zero.trans <| (or_comm' _ _).trans mul_eq_zero.symm
#align mul_eq_zero_comm mul_eq_zero_comm

/- warning: mul_ne_zero_comm -> mul_ne_zero_comm is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1) (MulZeroClass.toHasZero.{u1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) b a) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1) (MulZeroClass.toZero.{u1} M₀ _inst_1)] {a : M₀} {b : M₀}, Iff (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) b a) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_ne_zero_comm mul_ne_zero_commₓ'. -/
/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` is nonzero iff so is
`b * a`. -/
theorem mul_ne_zero_comm : a * b ≠ 0 ↔ b * a ≠ 0 :=
  mul_eq_zero_comm.Not
#align mul_ne_zero_comm mul_ne_zero_comm

/- warning: mul_self_eq_zero -> mul_self_eq_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1) (MulZeroClass.toHasZero.{u1} M₀ _inst_1)] {a : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a a) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1) (MulZeroClass.toZero.{u1} M₀ _inst_1)] {a : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a a) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_self_eq_zero mul_self_eq_zeroₓ'. -/
theorem mul_self_eq_zero : a * a = 0 ↔ a = 0 := by simp
#align mul_self_eq_zero mul_self_eq_zero

/- warning: zero_eq_mul_self -> zero_eq_mul_self is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1) (MulZeroClass.toHasZero.{u1} M₀ _inst_1)] {a : M₀}, Iff (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a a)) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1) (MulZeroClass.toZero.{u1} M₀ _inst_1)] {a : M₀}, Iff (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a a)) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align zero_eq_mul_self zero_eq_mul_selfₓ'. -/
theorem zero_eq_mul_self : 0 = a * a ↔ a = 0 := by simp
#align zero_eq_mul_self zero_eq_mul_self

/- warning: mul_self_ne_zero -> mul_self_ne_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1) (MulZeroClass.toHasZero.{u1} M₀ _inst_1)] {a : M₀}, Iff (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a a) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1) (MulZeroClass.toZero.{u1} M₀ _inst_1)] {a : M₀}, Iff (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a a) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_self_ne_zero mul_self_ne_zeroₓ'. -/
theorem mul_self_ne_zero : a * a ≠ 0 ↔ a ≠ 0 :=
  mul_self_eq_zero.Not
#align mul_self_ne_zero mul_self_ne_zero

/- warning: zero_ne_mul_self -> zero_ne_mul_self is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1) (MulZeroClass.toHasZero.{u1} M₀ _inst_1)] {a : M₀}, Iff (Ne.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a a)) (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : NoZeroDivisors.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1) (MulZeroClass.toZero.{u1} M₀ _inst_1)] {a : M₀}, Iff (Ne.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a a)) (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align zero_ne_mul_self zero_ne_mul_selfₓ'. -/
theorem zero_ne_mul_self : 0 ≠ a * a ↔ a ≠ 0 :=
  zero_eq_mul_self.Not
#align zero_ne_mul_self zero_ne_mul_self

end MulZeroClass

