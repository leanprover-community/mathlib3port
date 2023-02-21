/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland

! This file was ported from Lean 3 source module algebra.ring.regular
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Regular.Basic
import Mathbin.Algebra.Ring.Defs

/-!
# Lemmas about regular elements in rings.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

/- warning: is_left_regular_of_non_zero_divisor -> isLeftRegular_of_non_zero_divisor is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] (k : α), (forall (x : α), (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) k x) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))))))) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))))))) -> (IsLeftRegular.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) k)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] (k : α), (forall (x : α), (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) k x) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))))) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))))))) -> (IsLeftRegular.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1) k)
Case conversion may be inaccurate. Consider using '#align is_left_regular_of_non_zero_divisor isLeftRegular_of_non_zero_divisorₓ'. -/
/-- Left `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
theorem isLeftRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, k * x = 0 → x = 0) : IsLeftRegular k :=
  by
  refine' fun x y (h' : k * x = k * y) => sub_eq_zero.mp (h _ _)
  rw [mul_sub, sub_eq_zero, h']
#align is_left_regular_of_non_zero_divisor isLeftRegular_of_non_zero_divisor

/- warning: is_right_regular_of_non_zero_divisor -> isRightRegular_of_non_zero_divisor is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] (k : α), (forall (x : α), (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) x k) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))))))) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))))))) -> (IsRightRegular.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) k)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] (k : α), (forall (x : α), (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) x k) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))))) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))))))) -> (IsRightRegular.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1) k)
Case conversion may be inaccurate. Consider using '#align is_right_regular_of_non_zero_divisor isRightRegular_of_non_zero_divisorₓ'. -/
/-- Right `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
theorem isRightRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, x * k = 0 → x = 0) : IsRightRegular k :=
  by
  refine' fun x y (h' : x * k = y * k) => sub_eq_zero.mp (h _ _)
  rw [sub_mul, sub_eq_zero, h']
#align is_right_regular_of_non_zero_divisor isRightRegular_of_non_zero_divisor

/- warning: is_regular_of_ne_zero' -> isRegular_of_ne_zero' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))] {k : α}, (Ne.{succ u1} α k (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))))))) -> (IsRegular.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) k)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1) (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))] {k : α}, (Ne.{succ u1} α k (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))))) -> (IsRegular.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1) k)
Case conversion may be inaccurate. Consider using '#align is_regular_of_ne_zero' isRegular_of_ne_zero'ₓ'. -/
theorem isRegular_of_ne_zero' [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} (hk : k ≠ 0) :
    IsRegular k :=
  ⟨isLeftRegular_of_non_zero_divisor k fun x h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left hk,
    isRightRegular_of_non_zero_divisor k fun x h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hk⟩
#align is_regular_of_ne_zero' isRegular_of_ne_zero'

/- warning: is_regular_iff_ne_zero' -> isRegular_iff_ne_zero' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Nontrivial.{u1} α] [_inst_2 : NonUnitalNonAssocRing.{u1} α] [_inst_3 : NoZeroDivisors.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))] {k : α}, Iff (IsRegular.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))) k) (Ne.{succ u1} α k (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Nontrivial.{u1} α] [_inst_2 : NonUnitalNonAssocRing.{u1} α] [_inst_3 : NoZeroDivisors.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_2) (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))] {k : α}, Iff (IsRegular.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_2) k) (Ne.{succ u1} α k (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))))
Case conversion may be inaccurate. Consider using '#align is_regular_iff_ne_zero' isRegular_iff_ne_zero'ₓ'. -/
theorem isRegular_iff_ne_zero' [Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} :
    IsRegular k ↔ k ≠ 0 :=
  ⟨fun h => by
    rintro rfl
    exact not_not.mpr h.left not_isLeftRegular_zero, isRegular_of_ne_zero'⟩
#align is_regular_iff_ne_zero' isRegular_iff_ne_zero'

/- warning: no_zero_divisors.to_cancel_monoid_with_zero -> NoZeroDivisors.toCancelMonoidWithZero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))], CancelMonoidWithZero.{u1} α
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))], CancelMonoidWithZero.{u1} α
Case conversion may be inaccurate. Consider using '#align no_zero_divisors.to_cancel_monoid_with_zero NoZeroDivisors.toCancelMonoidWithZeroₓ'. -/
/-- A ring with no zero divisors is a `cancel_monoid_with_zero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def NoZeroDivisors.toCancelMonoidWithZero [Ring α] [NoZeroDivisors α] : CancelMonoidWithZero α :=
  {
    (by infer_instance :
      MonoidWithZero
        α) with
    mul_left_cancel_of_ne_zero := fun a b c ha =>
      @IsRegular.left _ _ _ (isRegular_of_ne_zero' ha) _ _
    mul_right_cancel_of_ne_zero := fun a b c hb =>
      @IsRegular.right _ _ _ (isRegular_of_ne_zero' hb) _ _ }
#align no_zero_divisors.to_cancel_monoid_with_zero NoZeroDivisors.toCancelMonoidWithZero

/- warning: no_zero_divisors.to_cancel_comm_monoid_with_zero -> NoZeroDivisors.toCancelCommMonoidWithZero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommRing.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (CommRing.toRing.{u1} α _inst_1))) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α _inst_1))))))], CancelCommMonoidWithZero.{u1} α
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommRing.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α _inst_1)))) (CommMonoidWithZero.toZero.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1)))], CancelCommMonoidWithZero.{u1} α
Case conversion may be inaccurate. Consider using '#align no_zero_divisors.to_cancel_comm_monoid_with_zero NoZeroDivisors.toCancelCommMonoidWithZeroₓ'. -/
/-- A commutative ring with no zero divisors is a `cancel_comm_monoid_with_zero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def NoZeroDivisors.toCancelCommMonoidWithZero [CommRing α] [NoZeroDivisors α] :
    CancelCommMonoidWithZero α :=
  { NoZeroDivisors.toCancelMonoidWithZero, (by infer_instance : CommMonoidWithZero α) with }
#align no_zero_divisors.to_cancel_comm_monoid_with_zero NoZeroDivisors.toCancelCommMonoidWithZero

section IsDomain

#print IsDomain.toCancelMonoidWithZero /-
-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelMonoidWithZero [Semiring α] [IsDomain α] :
    CancelMonoidWithZero α :=
  { Semiring.toMonoidWithZero α, ‹IsDomain α› with }
#align is_domain.to_cancel_monoid_with_zero IsDomain.toCancelMonoidWithZero
-/

variable [CommSemiring α] [IsDomain α]

#print IsDomain.toCancelCommMonoidWithZero /-
-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelCommMonoidWithZero : CancelCommMonoidWithZero α :=
  { ‹CommSemiring α›, ‹IsDomain α› with }
#align is_domain.to_cancel_comm_monoid_with_zero IsDomain.toCancelCommMonoidWithZero
-/

end IsDomain

