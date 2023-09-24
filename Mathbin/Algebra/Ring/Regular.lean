/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Algebra.Regular.Basic
import Algebra.Ring.Defs

#align_import algebra.ring.regular from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Lemmas about regular elements in rings.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

#print isLeftRegular_of_non_zero_divisor /-
/-- Left `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
theorem isLeftRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, k * x = 0 → x = 0) : IsLeftRegular k :=
  by
  refine' fun x y (h' : k * x = k * y) => sub_eq_zero.mp (h _ _)
  rw [mul_sub, sub_eq_zero, h']
#align is_left_regular_of_non_zero_divisor isLeftRegular_of_non_zero_divisor
-/

#print isRightRegular_of_non_zero_divisor /-
/-- Right `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
theorem isRightRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, x * k = 0 → x = 0) : IsRightRegular k :=
  by
  refine' fun x y (h' : x * k = y * k) => sub_eq_zero.mp (h _ _)
  rw [sub_mul, sub_eq_zero, h']
#align is_right_regular_of_non_zero_divisor isRightRegular_of_non_zero_divisor
-/

#print isRegular_of_ne_zero' /-
theorem isRegular_of_ne_zero' [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} (hk : k ≠ 0) :
    IsRegular k :=
  ⟨isLeftRegular_of_non_zero_divisor k fun x h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_hMul_eq_zero h).resolve_left hk,
    isRightRegular_of_non_zero_divisor k fun x h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_hMul_eq_zero h).resolve_right hk⟩
#align is_regular_of_ne_zero' isRegular_of_ne_zero'
-/

#print isRegular_iff_ne_zero' /-
theorem isRegular_iff_ne_zero' [Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} :
    IsRegular k ↔ k ≠ 0 :=
  ⟨fun h => by rintro rfl; exact not_not.mpr h.left not_isLeftRegular_zero, isRegular_of_ne_zero'⟩
#align is_regular_iff_ne_zero' isRegular_iff_ne_zero'
-/

#print NoZeroDivisors.toCancelMonoidWithZero /-
/-- A ring with no zero divisors is a `cancel_monoid_with_zero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def NoZeroDivisors.toCancelMonoidWithZero [Ring α] [NoZeroDivisors α] : CancelMonoidWithZero α :=
  {
    (by infer_instance :
      MonoidWithZero
        α) with
    hMul_left_cancel_of_ne_zero := fun a b c ha =>
      @IsRegular.left _ _ _ (isRegular_of_ne_zero' ha) _ _
    hMul_right_cancel_of_ne_zero := fun a b c hb =>
      @IsRegular.right _ _ _ (isRegular_of_ne_zero' hb) _ _ }
#align no_zero_divisors.to_cancel_monoid_with_zero NoZeroDivisors.toCancelMonoidWithZero
-/

#print NoZeroDivisors.toCancelCommMonoidWithZero /-
/-- A commutative ring with no zero divisors is a `cancel_comm_monoid_with_zero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def NoZeroDivisors.toCancelCommMonoidWithZero [CommRing α] [NoZeroDivisors α] :
    CancelCommMonoidWithZero α :=
  { NoZeroDivisors.toCancelMonoidWithZero, (by infer_instance : CommMonoidWithZero α) with }
#align no_zero_divisors.to_cancel_comm_monoid_with_zero NoZeroDivisors.toCancelCommMonoidWithZero
-/

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

