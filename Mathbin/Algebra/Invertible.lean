/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module algebra.invertible
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Units
import Mathbin.Algebra.GroupWithZero.Units.Lemmas
import Mathbin.Algebra.Ring.Defs

/-!
# Invertible elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a typeclass `invertible a` for elements `a` with a two-sided
multiplicative inverse.

The intent of the typeclass is to provide a way to write e.g. `⅟2` in a ring
like `ℤ[1/2]` where some inverses exist but there is no general `⁻¹` operator;
or to specify that a field has characteristic `≠ 2`.
It is the `Type`-valued analogue to the `Prop`-valued `is_unit`.

For constructions of the invertible element given a characteristic, see
`algebra/char_p/invertible` and other lemmas in that file.

## Notation

 * `⅟a` is `invertible.inv_of a`, the inverse of `a`

## Implementation notes

The `invertible` class lives in `Type`, not `Prop`, to make computation easier.
If multiplication is associative, `invertible` is a subsingleton anyway.

The `simp` normal form tries to normalize `⅟a` to `a ⁻¹`. Otherwise, it pushes
`⅟` inside the expression as much as possible.

Since `invertible a` is not a `Prop` (but it is a `subsingleton`), we have to be careful about
coherence issues: we should avoid having multiple non-defeq instances for `invertible a` in the
same context.  This file plays it safe and uses `def` rather than `instance` for most definitions,
users can choose which instances to use at the point of use.

For example, here's how you can use an `invertible 1` instance:
```lean
variables {α : Type*} [monoid α]

def something_that_needs_inverses (x : α) [invertible x] := sorry

section
local attribute [instance] invertible_one
def something_one := something_that_needs_inverses 1
end
```

## Tags

invertible, inverse element, inv_of, a half, one half, a third, one third, ½, ⅓

-/


universe u

variable {α : Type u}

#print Invertible /-
/-- `invertible a` gives a two-sided multiplicative inverse of `a`. -/
class Invertible [Mul α] [One α] (a : α) : Type u where
  invOf : α
  invOf_mul_self : inv_of * a = 1
  mul_invOf_self : a * inv_of = 1
#align invertible Invertible
-/

-- mathport name: «expr⅟»
notation:1034
  "⅟" =>-- This notation has the same precedence as `has_inv.inv`.
  Invertible.invOf

#print invOf_mul_self /-
@[simp]
theorem invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : ⅟ a * a = 1 :=
  Invertible.invOf_mul_self
#align inv_of_mul_self invOf_mul_self
-/

#print mul_invOf_self /-
@[simp]
theorem mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : a * ⅟ a = 1 :=
  Invertible.mul_invOf_self
#align mul_inv_of_self mul_invOf_self
-/

/- warning: inv_of_mul_self_assoc -> invOf_mul_self_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)) b
Case conversion may be inaccurate. Consider using '#align inv_of_mul_self_assoc invOf_mul_self_assocₓ'. -/
@[simp]
theorem invOf_mul_self_assoc [Monoid α] (a b : α) [Invertible a] : ⅟ a * (a * b) = b := by
  rw [← mul_assoc, invOf_mul_self, one_mul]
#align inv_of_mul_self_assoc invOf_mul_self_assoc

/- warning: mul_inv_of_self_assoc -> mul_invOf_self_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a _inst_2) b)) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a _inst_2) b)) b
Case conversion may be inaccurate. Consider using '#align mul_inv_of_self_assoc mul_invOf_self_assocₓ'. -/
@[simp]
theorem mul_invOf_self_assoc [Monoid α] (a b : α) [Invertible a] : a * (⅟ a * b) = b := by
  rw [← mul_assoc, mul_invOf_self, one_mul]
#align mul_inv_of_self_assoc mul_invOf_self_assoc

/- warning: mul_inv_of_mul_self_cancel -> mul_invOf_mul_self_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b _inst_2)) b) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b _inst_2)) b) a
Case conversion may be inaccurate. Consider using '#align mul_inv_of_mul_self_cancel mul_invOf_mul_self_cancelₓ'. -/
@[simp]
theorem mul_invOf_mul_self_cancel [Monoid α] (a b : α) [Invertible b] : a * ⅟ b * b = a := by
  simp [mul_assoc]
#align mul_inv_of_mul_self_cancel mul_invOf_mul_self_cancel

/- warning: mul_mul_inv_of_self_cancel -> mul_mul_invOf_self_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b) (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b _inst_2)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b) (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b _inst_2)) a
Case conversion may be inaccurate. Consider using '#align mul_mul_inv_of_self_cancel mul_mul_invOf_self_cancelₓ'. -/
@[simp]
theorem mul_mul_invOf_self_cancel [Monoid α] (a b : α) [Invertible b] : a * b * ⅟ b = a := by
  simp [mul_assoc]
#align mul_mul_inv_of_self_cancel mul_mul_invOf_self_cancel

/- warning: inv_of_eq_right_inv -> invOf_eq_right_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a], (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))) -> (Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a _inst_2) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a], (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))) -> (Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a _inst_2) b)
Case conversion may be inaccurate. Consider using '#align inv_of_eq_right_inv invOf_eq_right_invₓ'. -/
theorem invOf_eq_right_inv [Monoid α] {a b : α} [Invertible a] (hac : a * b = 1) : ⅟ a = b :=
  left_inv_eq_right_inv (invOf_mul_self _) hac
#align inv_of_eq_right_inv invOf_eq_right_inv

/- warning: inv_of_eq_left_inv -> invOf_eq_left_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a], (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) b a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))) -> (Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a _inst_2) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a], (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) b a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))) -> (Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a _inst_2) b)
Case conversion may be inaccurate. Consider using '#align inv_of_eq_left_inv invOf_eq_left_invₓ'. -/
theorem invOf_eq_left_inv [Monoid α] {a b : α} [Invertible a] (hac : b * a = 1) : ⅟ a = b :=
  (left_inv_eq_right_inv hac (mul_invOf_self _)).symm
#align inv_of_eq_left_inv invOf_eq_left_inv

/- warning: invertible_unique -> invertible_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a] [_inst_3 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b], (Eq.{succ u1} α a b) -> (Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a _inst_2) (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b _inst_3))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a] [_inst_3 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b], (Eq.{succ u1} α a b) -> (Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a _inst_2) (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b _inst_3))
Case conversion may be inaccurate. Consider using '#align invertible_unique invertible_uniqueₓ'. -/
theorem invertible_unique {α : Type u} [Monoid α] (a b : α) [Invertible a] [Invertible b]
    (h : a = b) : ⅟ a = ⅟ b := by
  apply invOf_eq_right_inv
  rw [h, mul_invOf_self]
#align invertible_unique invertible_unique

instance [Monoid α] (a : α) : Subsingleton (Invertible a) :=
  ⟨fun ⟨b, hba, hab⟩ ⟨c, hca, hac⟩ => by
    congr
    exact left_inv_eq_right_inv hba hac⟩

/- warning: invertible.copy -> Invertible.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] {r : α}, (Invertible.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1) (MulOneClass.toHasOne.{u1} α _inst_1) r) -> (forall (s : α), (Eq.{succ u1} α s r) -> (Invertible.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1) (MulOneClass.toHasOne.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] {r : α}, (Invertible.{u1} α (MulOneClass.toMul.{u1} α _inst_1) (MulOneClass.toOne.{u1} α _inst_1) r) -> (forall (s : α), (Eq.{succ u1} α s r) -> (Invertible.{u1} α (MulOneClass.toMul.{u1} α _inst_1) (MulOneClass.toOne.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align invertible.copy Invertible.copyₓ'. -/
/-- If `r` is invertible and `s = r`, then `s` is invertible. -/
def Invertible.copy [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (hs : s = r) : Invertible s
    where
  invOf := ⅟ r
  invOf_mul_self := by rw [hs, invOf_mul_self]
  mul_invOf_self := by rw [hs, mul_invOf_self]
#align invertible.copy Invertible.copy

/- warning: unit_of_invertible -> unitOfInvertible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a], Units.{u1} α _inst_1
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a], Units.{u1} α _inst_1
Case conversion may be inaccurate. Consider using '#align unit_of_invertible unitOfInvertibleₓ'. -/
/-- An `invertible` element is a unit. -/
@[simps]
def unitOfInvertible [Monoid α] (a : α) [Invertible a] : αˣ
    where
  val := a
  inv := ⅟ a
  val_inv := by simp
  inv_val := by simp
#align unit_of_invertible unitOfInvertible

/- warning: is_unit_of_invertible -> isUnit_of_invertible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a], IsUnit.{u1} α _inst_1 a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a], IsUnit.{u1} α _inst_1 a
Case conversion may be inaccurate. Consider using '#align is_unit_of_invertible isUnit_of_invertibleₓ'. -/
theorem isUnit_of_invertible [Monoid α] (a : α) [Invertible a] : IsUnit a :=
  ⟨unitOfInvertible a, rfl⟩
#align is_unit_of_invertible isUnit_of_invertible

/- warning: units.invertible -> Units.invertible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (u : Units.{u1} α _inst_1), Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) u)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (u : Units.{u1} α _inst_1), Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (Units.val.{u1} α _inst_1 u)
Case conversion may be inaccurate. Consider using '#align units.invertible Units.invertibleₓ'. -/
/-- Units are invertible in their associated monoid. -/
def Units.invertible [Monoid α] (u : αˣ) : Invertible (u : α)
    where
  invOf := ↑u⁻¹
  invOf_mul_self := u.inv_mul
  mul_invOf_self := u.mul_inv
#align units.invertible Units.invertible

/- warning: inv_of_units -> invOf_units is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (u : Units.{u1} α _inst_1) [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) u)], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) u) _inst_2) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) (Inv.inv.{u1} (Units.{u1} α _inst_1) (Units.hasInv.{u1} α _inst_1) u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (u : Units.{u1} α _inst_1) [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (Units.val.{u1} α _inst_1 u)], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (Units.val.{u1} α _inst_1 u) _inst_2) (Units.val.{u1} α _inst_1 (Inv.inv.{u1} (Units.{u1} α _inst_1) (Units.instInvUnits.{u1} α _inst_1) u))
Case conversion may be inaccurate. Consider using '#align inv_of_units invOf_unitsₓ'. -/
@[simp]
theorem invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟ (u : α) = ↑u⁻¹ :=
  invOf_eq_right_inv u.mul_inv
#align inv_of_units invOf_units

/- warning: is_unit.nonempty_invertible -> IsUnit.nonempty_invertible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α}, (IsUnit.{u1} α _inst_1 a) -> (Nonempty.{succ u1} (Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α}, (IsUnit.{u1} α _inst_1 a) -> (Nonempty.{succ u1} (Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a))
Case conversion may be inaccurate. Consider using '#align is_unit.nonempty_invertible IsUnit.nonempty_invertibleₓ'. -/
theorem IsUnit.nonempty_invertible [Monoid α] {a : α} (h : IsUnit a) : Nonempty (Invertible a) :=
  let ⟨x, hx⟩ := h
  ⟨x.Invertible.copy _ hx.symm⟩
#align is_unit.nonempty_invertible IsUnit.nonempty_invertible

/- warning: is_unit.invertible -> IsUnit.invertible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α}, (IsUnit.{u1} α _inst_1 a) -> (Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α}, (IsUnit.{u1} α _inst_1 a) -> (Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align is_unit.invertible IsUnit.invertibleₓ'. -/
/-- Convert `is_unit` to `invertible` using `classical.choice`.

Prefer `casesI h.nonempty_invertible` over `letI := h.invertible` if you want to avoid choice. -/
noncomputable def IsUnit.invertible [Monoid α] {a : α} (h : IsUnit a) : Invertible a :=
  Classical.choice h.nonempty_invertible
#align is_unit.invertible IsUnit.invertible

/- warning: nonempty_invertible_iff_is_unit -> nonempty_invertible_iff_isUnit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α), Iff (Nonempty.{succ u1} (Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a)) (IsUnit.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α), Iff (Nonempty.{succ u1} (Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a)) (IsUnit.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align nonempty_invertible_iff_is_unit nonempty_invertible_iff_isUnitₓ'. -/
@[simp]
theorem nonempty_invertible_iff_isUnit [Monoid α] (a : α) : Nonempty (Invertible a) ↔ IsUnit a :=
  ⟨Nonempty.ndrec <| @isUnit_of_invertible _ _ _, IsUnit.nonempty_invertible⟩
#align nonempty_invertible_iff_is_unit nonempty_invertible_iff_isUnit

/- warning: invertible_of_group -> invertibleOfGroup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (a : α), Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (a : α), Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a
Case conversion may be inaccurate. Consider using '#align invertible_of_group invertibleOfGroupₓ'. -/
/-- Each element of a group is invertible. -/
def invertibleOfGroup [Group α] (a : α) : Invertible a :=
  ⟨a⁻¹, inv_mul_self a, mul_inv_self a⟩
#align invertible_of_group invertibleOfGroup

/- warning: inv_of_eq_group_inv -> invOf_eq_group_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) a], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) a _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a _inst_2) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)
Case conversion may be inaccurate. Consider using '#align inv_of_eq_group_inv invOf_eq_group_invₓ'. -/
@[simp]
theorem invOf_eq_group_inv [Group α] (a : α) [Invertible a] : ⅟ a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_self a)
#align inv_of_eq_group_inv invOf_eq_group_inv

/- warning: invertible_one -> invertibleOne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align invertible_one invertibleOneₓ'. -/
/-- `1` is the inverse of itself -/
def invertibleOne [Monoid α] : Invertible (1 : α) :=
  ⟨1, mul_one _, one_mul _⟩
#align invertible_one invertibleOne

/- warning: inv_of_one -> invOf_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))) _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))) _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align inv_of_one invOf_oneₓ'. -/
@[simp]
theorem invOf_one [Monoid α] [Invertible (1 : α)] : ⅟ (1 : α) = 1 :=
  invOf_eq_right_inv (mul_one _)
#align inv_of_one invOf_one

/- warning: invertible_neg -> invertibleNeg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : HasDistribNeg.{u1} α _inst_1] (a : α) [_inst_4 : Invertible.{u1} α _inst_1 _inst_2 a], Invertible.{u1} α _inst_1 _inst_2 (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α _inst_1 _inst_3)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : HasDistribNeg.{u1} α _inst_1] (a : α) [_inst_4 : Invertible.{u1} α _inst_1 _inst_2 a], Invertible.{u1} α _inst_1 _inst_2 (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α _inst_1 _inst_3)) a)
Case conversion may be inaccurate. Consider using '#align invertible_neg invertibleNegₓ'. -/
/-- `-⅟a` is the inverse of `-a` -/
def invertibleNeg [Mul α] [One α] [HasDistribNeg α] (a : α) [Invertible a] : Invertible (-a) :=
  ⟨-⅟ a, by simp, by simp⟩
#align invertible_neg invertibleNeg

/- warning: inv_of_neg -> invOf_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] (a : α) [_inst_3 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a] [_inst_4 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a)], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a) _inst_4) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a _inst_3))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))] (a : α) [_inst_3 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a] [_inst_4 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a)], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) a) _inst_4) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2)) (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a _inst_3))
Case conversion may be inaccurate. Consider using '#align inv_of_neg invOf_negₓ'. -/
@[simp]
theorem invOf_neg [Monoid α] [HasDistribNeg α] (a : α) [Invertible a] [Invertible (-a)] :
    ⅟ (-a) = -⅟ a :=
  invOf_eq_right_inv (by simp)
#align inv_of_neg invOf_neg

/- warning: one_sub_inv_of_two -> one_sub_invOf_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : Invertible.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))))))], Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))))) (Invertible.invOf.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))))) _inst_2)) (Invertible.invOf.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))))) _inst_2)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : Invertible.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))) (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))], Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))) (Invertible.invOf.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))) (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) _inst_2)) (Invertible.invOf.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))) (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) _inst_2)
Case conversion may be inaccurate. Consider using '#align one_sub_inv_of_two one_sub_invOf_twoₓ'. -/
@[simp]
theorem one_sub_invOf_two [Ring α] [Invertible (2 : α)] : 1 - (⅟ 2 : α) = ⅟ 2 :=
  (isUnit_of_invertible (2 : α)).mul_right_inj.1 <| by
    rw [mul_sub, mul_invOf_self, mul_one, bit0, add_sub_cancel]
#align one_sub_inv_of_two one_sub_invOf_two

/- warning: inv_of_two_add_inv_of_two -> invOf_two_add_invOf_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] [_inst_2 : Invertible.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1)))))))], Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (Invertible.invOf.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1))))))) _inst_2) (Invertible.invOf.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1))))))) _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] [_inst_2 : Invertible.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) (NonAssocSemiring.toOne.{u1} α _inst_1) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (NonAssocSemiring.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))], Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (Invertible.invOf.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) (NonAssocSemiring.toOne.{u1} α _inst_1) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (NonAssocSemiring.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) _inst_2) (Invertible.invOf.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) (NonAssocSemiring.toOne.{u1} α _inst_1) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (NonAssocSemiring.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocSemiring.toOne.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align inv_of_two_add_inv_of_two invOf_two_add_invOf_twoₓ'. -/
@[simp]
theorem invOf_two_add_invOf_two [NonAssocSemiring α] [Invertible (2 : α)] :
    (⅟ 2 : α) + (⅟ 2 : α) = 1 := by rw [← two_mul, mul_invOf_self]
#align inv_of_two_add_inv_of_two invOf_two_add_invOf_two

#print invertibleInvOf /-
/-- `a` is the inverse of `⅟a`. -/
instance invertibleInvOf [One α] [Mul α] {a : α} [Invertible a] : Invertible (⅟ a) :=
  ⟨a, mul_invOf_self a, invOf_mul_self a⟩
#align invertible_inv_of invertibleInvOf
-/

/- warning: inv_of_inv_of -> invOf_invOf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a] [_inst_3 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a _inst_2)], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a _inst_2) _inst_3) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a] [_inst_3 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a _inst_2)], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a _inst_2) _inst_3) a
Case conversion may be inaccurate. Consider using '#align inv_of_inv_of invOf_invOfₓ'. -/
@[simp]
theorem invOf_invOf [Monoid α] (a : α) [Invertible a] [Invertible (⅟ a)] : ⅟ (⅟ a) = a :=
  invOf_eq_right_inv (invOf_mul_self _)
#align inv_of_inv_of invOf_invOf

/- warning: inv_of_inj -> invOf_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a] [_inst_3 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b], Iff (Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a _inst_2) (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b _inst_3)) (Eq.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a] [_inst_3 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b], Iff (Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a _inst_2) (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b _inst_3)) (Eq.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align inv_of_inj invOf_injₓ'. -/
@[simp]
theorem invOf_inj [Monoid α] {a b : α} [Invertible a] [Invertible b] : ⅟ a = ⅟ b ↔ a = b :=
  ⟨invertible_unique _ _, invertible_unique _ _⟩
#align inv_of_inj invOf_inj

/- warning: invertible_mul -> invertibleMul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a] [_inst_3 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b], Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a] [_inst_3 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b], Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align invertible_mul invertibleMulₓ'. -/
/-- `⅟b * ⅟a` is the inverse of `a * b` -/
def invertibleMul [Monoid α] (a b : α) [Invertible a] [Invertible b] : Invertible (a * b) :=
  ⟨⅟ b * ⅟ a, by simp [← mul_assoc], by simp [← mul_assoc]⟩
#align invertible_mul invertibleMul

/- warning: inv_of_mul -> invOf_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a] [_inst_3 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b] [_inst_4 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b) _inst_4) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b _inst_3) (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a] [_inst_3 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b] [_inst_4 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b) _inst_4) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b _inst_3) (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) a _inst_2))
Case conversion may be inaccurate. Consider using '#align inv_of_mul invOf_mulₓ'. -/
@[simp]
theorem invOf_mul [Monoid α] (a b : α) [Invertible a] [Invertible b] [Invertible (a * b)] :
    ⅟ (a * b) = ⅟ b * ⅟ a :=
  invOf_eq_right_inv (by simp [← mul_assoc])
#align inv_of_mul invOf_mul

/- warning: commute.inv_of_right -> Commute.invOf_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b], (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a b) -> (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b], (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a b) -> (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) a (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b _inst_2))
Case conversion may be inaccurate. Consider using '#align commute.inv_of_right Commute.invOf_rightₓ'. -/
theorem Commute.invOf_right [Monoid α] {a b : α} [Invertible b] (h : Commute a b) :
    Commute a (⅟ b) :=
  calc
    a * ⅟ b = ⅟ b * (b * a * ⅟ b) := by simp [mul_assoc]
    _ = ⅟ b * (a * b * ⅟ b) := by rw [h.eq]
    _ = ⅟ b * a := by simp [mul_assoc]
    
#align commute.inv_of_right Commute.invOf_right

/- warning: commute.inv_of_left -> Commute.invOf_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} [_inst_2 : Invertible.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b], (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b a) -> (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Invertible.invOf.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b _inst_2) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} [_inst_2 : Invertible.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b], (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) b a) -> (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Invertible.invOf.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) b _inst_2) a)
Case conversion may be inaccurate. Consider using '#align commute.inv_of_left Commute.invOf_leftₓ'. -/
theorem Commute.invOf_left [Monoid α] {a b : α} [Invertible b] (h : Commute b a) :
    Commute (⅟ b) a :=
  calc
    ⅟ b * a = ⅟ b * (a * b * ⅟ b) := by simp [mul_assoc]
    _ = ⅟ b * (b * a * ⅟ b) := by rw [h.eq]
    _ = a * ⅟ b := by simp [mul_assoc]
    
#align commute.inv_of_left Commute.invOf_left

#print commute_invOf /-
theorem commute_invOf {M : Type _} [One M] [Mul M] (m : M) [Invertible m] : Commute m (⅟ m) :=
  calc
    m * ⅟ m = 1 := mul_invOf_self m
    _ = ⅟ m * m := (invOf_mul_self m).symm
    
#align commute_inv_of commute_invOf
-/

/- warning: nonzero_of_invertible -> nonzero_of_invertible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} α] (a : α) [_inst_2 : Nontrivial.{u1} α] [_inst_3 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α _inst_1)) a], Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} α] (a : α) [_inst_2 : Nontrivial.{u1} α] [_inst_3 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_1)) (MulOneClass.toOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α _inst_1)) a], Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroOneClass.toZero.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align nonzero_of_invertible nonzero_of_invertibleₓ'. -/
theorem nonzero_of_invertible [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible a] : a ≠ 0 :=
  fun ha =>
  zero_ne_one <|
    calc
      0 = ⅟ a * a := by simp [ha]
      _ = 1 := invOf_mul_self a
      
#align nonzero_of_invertible nonzero_of_invertible

/- warning: invertible.ne_zero -> Invertible.ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} α] [_inst_2 : Nontrivial.{u1} α] (a : α) [_inst_3 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α _inst_1)) a], NeZero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_1)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} α] [_inst_2 : Nontrivial.{u1} α] (a : α) [_inst_3 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_1)) (MulOneClass.toOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α _inst_1)) a], NeZero.{u1} α (MulZeroOneClass.toZero.{u1} α _inst_1) a
Case conversion may be inaccurate. Consider using '#align invertible.ne_zero Invertible.ne_zeroₓ'. -/
instance (priority := 100) Invertible.ne_zero [MulZeroOneClass α] [Nontrivial α] (a : α)
    [Invertible a] : NeZero a :=
  ⟨nonzero_of_invertible a⟩
#align invertible.ne_zero Invertible.ne_zero

section MonoidWithZero

variable [MonoidWithZero α]

/- warning: ring.inverse_invertible -> Ring.inverse_invertible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] (x : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))) x], Eq.{succ u1} α (Ring.inverse.{u1} α _inst_1 x) (Invertible.invOf.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))) x _inst_2)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] (x : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))) (Monoid.toOne.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) x], Eq.{succ u1} α (Ring.inverse.{u1} α _inst_1 x) (Invertible.invOf.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))) (Monoid.toOne.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) x _inst_2)
Case conversion may be inaccurate. Consider using '#align ring.inverse_invertible Ring.inverse_invertibleₓ'. -/
/-- A variant of `ring.inverse_unit`. -/
@[simp]
theorem Ring.inverse_invertible (x : α) [Invertible x] : Ring.inverse x = ⅟ x :=
  Ring.inverse_unit (unitOfInvertible _)
#align ring.inverse_invertible Ring.inverse_invertible

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero α]

/- warning: invertible_of_nonzero -> invertibleOfNonzero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) -> (Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) a)
Case conversion may be inaccurate. Consider using '#align invertible_of_nonzero invertibleOfNonzeroₓ'. -/
/-- `a⁻¹` is an inverse of `a` if `a ≠ 0` -/
def invertibleOfNonzero {a : α} (h : a ≠ 0) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel h, mul_inv_cancel h⟩
#align invertible_of_nonzero invertibleOfNonzero

/- warning: inv_of_eq_inv -> invOf_eq_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) a], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) a _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) a], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) a _inst_2) (Inv.inv.{u1} α (GroupWithZero.toInv.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align inv_of_eq_inv invOf_eq_invₓ'. -/
@[simp]
theorem invOf_eq_inv (a : α) [Invertible a] : ⅟ a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_cancel (nonzero_of_invertible a))
#align inv_of_eq_inv invOf_eq_inv

/- warning: inv_mul_cancel_of_invertible -> inv_mul_cancel_of_invertible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) a], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) a) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) a], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) (Inv.inv.{u1} α (GroupWithZero.toInv.{u1} α _inst_1) a) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align inv_mul_cancel_of_invertible inv_mul_cancel_of_invertibleₓ'. -/
@[simp]
theorem inv_mul_cancel_of_invertible (a : α) [Invertible a] : a⁻¹ * a = 1 :=
  inv_mul_cancel (nonzero_of_invertible a)
#align inv_mul_cancel_of_invertible inv_mul_cancel_of_invertible

/- warning: mul_inv_cancel_of_invertible -> mul_inv_cancel_of_invertible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) a], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) a)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) a], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) a (Inv.inv.{u1} α (GroupWithZero.toInv.{u1} α _inst_1) a)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align mul_inv_cancel_of_invertible mul_inv_cancel_of_invertibleₓ'. -/
@[simp]
theorem mul_inv_cancel_of_invertible (a : α) [Invertible a] : a * a⁻¹ = 1 :=
  mul_inv_cancel (nonzero_of_invertible a)
#align mul_inv_cancel_of_invertible mul_inv_cancel_of_invertible

/- warning: div_mul_cancel_of_invertible -> div_mul_cancel_of_invertible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) b], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1))) a b) b) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) b], Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (GroupWithZero.toDiv.{u1} α _inst_1)) a b) b) a
Case conversion may be inaccurate. Consider using '#align div_mul_cancel_of_invertible div_mul_cancel_of_invertibleₓ'. -/
@[simp]
theorem div_mul_cancel_of_invertible (a b : α) [Invertible b] : a / b * b = a :=
  div_mul_cancel a (nonzero_of_invertible b)
#align div_mul_cancel_of_invertible div_mul_cancel_of_invertible

/- warning: mul_div_cancel_of_invertible -> mul_div_cancel_of_invertible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) b], Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) a b) b) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) b], Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (GroupWithZero.toDiv.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) a b) b) a
Case conversion may be inaccurate. Consider using '#align mul_div_cancel_of_invertible mul_div_cancel_of_invertibleₓ'. -/
@[simp]
theorem mul_div_cancel_of_invertible (a b : α) [Invertible b] : a * b / b = a :=
  mul_div_cancel a (nonzero_of_invertible b)
#align mul_div_cancel_of_invertible mul_div_cancel_of_invertible

/- warning: div_self_of_invertible -> div_self_of_invertible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) a], Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1))) a a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) a], Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (GroupWithZero.toDiv.{u1} α _inst_1)) a a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align div_self_of_invertible div_self_of_invertibleₓ'. -/
@[simp]
theorem div_self_of_invertible (a : α) [Invertible a] : a / a = 1 :=
  div_self (nonzero_of_invertible a)
#align div_self_of_invertible div_self_of_invertible

/- warning: invertible_div -> invertibleDiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) a] [_inst_3 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) b], Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) a] [_inst_3 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) b], Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (GroupWithZero.toDiv.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align invertible_div invertibleDivₓ'. -/
/-- `b / a` is the inverse of `a / b` -/
def invertibleDiv (a b : α) [Invertible a] [Invertible b] : Invertible (a / b) :=
  ⟨b / a, by simp [← mul_div_assoc], by simp [← mul_div_assoc]⟩
#align invertible_div invertibleDiv

/- warning: inv_of_div -> invOf_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) a] [_inst_3 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) b] [_inst_4 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1))) a b)], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1))) a b) _inst_4) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (a : α) (b : α) [_inst_2 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) a] [_inst_3 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) b] [_inst_4 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (GroupWithZero.toDiv.{u1} α _inst_1)) a b)], Eq.{succ u1} α (Invertible.invOf.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (GroupWithZero.toDiv.{u1} α _inst_1)) a b) _inst_4) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (GroupWithZero.toDiv.{u1} α _inst_1)) b a)
Case conversion may be inaccurate. Consider using '#align inv_of_div invOf_divₓ'. -/
@[simp]
theorem invOf_div (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)] :
    ⅟ (a / b) = b / a :=
  invOf_eq_right_inv (by simp [← mul_div_assoc])
#align inv_of_div invOf_div

/- warning: invertible_inv -> invertibleInv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] {a : α} [_inst_2 : Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) a], Invertible.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] {a : α} [_inst_2 : Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) a], Invertible.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (GroupWithZero.toDivisionMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (GroupWithZero.toInv.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align invertible_inv invertibleInvₓ'. -/
/-- `a` is the inverse of `a⁻¹` -/
def invertibleInv {a : α} [Invertible a] : Invertible a⁻¹ :=
  ⟨a, by simp, by simp⟩
#align invertible_inv invertibleInv

end GroupWithZero

/- warning: invertible.map -> Invertible.map is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {F : Type.{u3}} [_inst_1 : MulOneClass.{u1} R] [_inst_2 : MulOneClass.{u2} S] [_inst_3 : MonoidHomClass.{u3, u1, u2} F R S _inst_1 _inst_2] (f : F) (r : R) [_inst_4 : Invertible.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1) (MulOneClass.toHasOne.{u1} R _inst_1) r], Invertible.{u2} S (MulOneClass.toHasMul.{u2} S _inst_2) (MulOneClass.toHasOne.{u2} S _inst_2) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F R (fun (_x : R) => S) (MulHomClass.toFunLike.{u3, u1, u2} F R S (MulOneClass.toHasMul.{u1} R _inst_1) (MulOneClass.toHasMul.{u2} S _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F R S _inst_1 _inst_2 _inst_3))) f r)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} {F : Type.{u3}} [_inst_1 : MulOneClass.{u1} R] [_inst_2 : MulOneClass.{u2} S] [_inst_3 : MonoidHomClass.{u3, u1, u2} F R S _inst_1 _inst_2] (f : F) (r : R) [_inst_4 : Invertible.{u1} R (MulOneClass.toMul.{u1} R _inst_1) (MulOneClass.toOne.{u1} R _inst_1) r], Invertible.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) (MulOneClass.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) _inst_2) (MulOneClass.toOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) _inst_2) (FunLike.coe.{succ u3, succ u1, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{u3, u1, u2} F R S (MulOneClass.toMul.{u1} R _inst_1) (MulOneClass.toMul.{u2} S _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F R S _inst_1 _inst_2 _inst_3)) f r)
Case conversion may be inaccurate. Consider using '#align invertible.map Invertible.mapₓ'. -/
/-- Monoid homs preserve invertibility. -/
def Invertible.map {R : Type _} {S : Type _} {F : Type _} [MulOneClass R] [MulOneClass S]
    [MonoidHomClass F R S] (f : F) (r : R) [Invertible r] : Invertible (f r)
    where
  invOf := f (⅟ r)
  invOf_mul_self := by rw [← map_mul, invOf_mul_self, map_one]
  mul_invOf_self := by rw [← map_mul, mul_invOf_self, map_one]
#align invertible.map Invertible.map

/- warning: map_inv_of -> map_invOf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {F : Type.{u3}} [_inst_1 : MulOneClass.{u1} R] [_inst_2 : Monoid.{u2} S] [_inst_3 : MonoidHomClass.{u3, u1, u2} F R S _inst_1 (Monoid.toMulOneClass.{u2} S _inst_2)] (f : F) (r : R) [_inst_4 : Invertible.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1) (MulOneClass.toHasOne.{u1} R _inst_1) r] [_inst_5 : Invertible.{u2} S (MulOneClass.toHasMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MulOneClass.toHasOne.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F R (fun (_x : R) => S) (MulHomClass.toFunLike.{u3, u1, u2} F R S (MulOneClass.toHasMul.{u1} R _inst_1) (MulOneClass.toHasMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F R S _inst_1 (Monoid.toMulOneClass.{u2} S _inst_2) _inst_3))) f r)], Eq.{succ u2} S (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F R (fun (_x : R) => S) (MulHomClass.toFunLike.{u3, u1, u2} F R S (MulOneClass.toHasMul.{u1} R _inst_1) (MulOneClass.toHasMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F R S _inst_1 (Monoid.toMulOneClass.{u2} S _inst_2) _inst_3))) f (Invertible.invOf.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1) (MulOneClass.toHasOne.{u1} R _inst_1) r _inst_4)) (Invertible.invOf.{u2} S (MulOneClass.toHasMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MulOneClass.toHasOne.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F R (fun (_x : R) => S) (MulHomClass.toFunLike.{u3, u1, u2} F R S (MulOneClass.toHasMul.{u1} R _inst_1) (MulOneClass.toHasMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F R S _inst_1 (Monoid.toMulOneClass.{u2} S _inst_2) _inst_3))) f r) _inst_5)
but is expected to have type
  forall {R : Type.{u3}} {S : Type.{u2}} {F : Type.{u1}} [_inst_1 : MulOneClass.{u3} R] [_inst_2 : Monoid.{u2} S] [_inst_3 : MonoidHomClass.{u1, u3, u2} F R S _inst_1 (Monoid.toMulOneClass.{u2} S _inst_2)] (f : F) (r : R) [_inst_4 : Invertible.{u3} R (MulOneClass.toMul.{u3} R _inst_1) (MulOneClass.toOne.{u3} R _inst_1) r] [_inst_5 : Invertible.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) (MulOneClass.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) (Monoid.toMulOneClass.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) _inst_2)) (Monoid.toOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) _inst_2) (FunLike.coe.{succ u1, succ u3, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{u1, u3, u2} F R S (MulOneClass.toMul.{u3} R _inst_1) (MulOneClass.toMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F R S _inst_1 (Monoid.toMulOneClass.{u2} S _inst_2) _inst_3)) f r)], Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) (Invertible.invOf.{u3} R (MulOneClass.toMul.{u3} R _inst_1) (MulOneClass.toOne.{u3} R _inst_1) r _inst_4)) (FunLike.coe.{succ u1, succ u3, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{u1, u3, u2} F R S (MulOneClass.toMul.{u3} R _inst_1) (MulOneClass.toMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F R S _inst_1 (Monoid.toMulOneClass.{u2} S _inst_2) _inst_3)) f (Invertible.invOf.{u3} R (MulOneClass.toMul.{u3} R _inst_1) (MulOneClass.toOne.{u3} R _inst_1) r _inst_4)) (Invertible.invOf.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) (MulOneClass.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) (Monoid.toMulOneClass.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) _inst_2)) (Monoid.toOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) _inst_2) (FunLike.coe.{succ u1, succ u3, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{u1, u3, u2} F R S (MulOneClass.toMul.{u3} R _inst_1) (MulOneClass.toMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F R S _inst_1 (Monoid.toMulOneClass.{u2} S _inst_2) _inst_3)) f r) _inst_5)
Case conversion may be inaccurate. Consider using '#align map_inv_of map_invOfₓ'. -/
/-- Note that the `invertible (f r)` argument can be satisfied by using `letI := invertible.map f r`
before applying this lemma. -/
theorem map_invOf {R : Type _} {S : Type _} {F : Type _} [MulOneClass R] [Monoid S]
    [MonoidHomClass F R S] (f : F) (r : R) [Invertible r] [Invertible (f r)] : f (⅟ r) = ⅟ (f r) :=
  by
  letI := Invertible.map f r
  convert rfl
#align map_inv_of map_invOf

/- warning: invertible.of_left_inverse -> Invertible.ofLeftInverse is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {G : Type.{u3}} [_inst_1 : MulOneClass.{u1} R] [_inst_2 : MulOneClass.{u2} S] [_inst_3 : MonoidHomClass.{u3, u2, u1} G S R _inst_2 _inst_1] (f : R -> S) (g : G) (r : R), (Function.LeftInverse.{succ u1, succ u2} R S (coeFn.{succ u3, max (succ u2) (succ u1)} G (fun (_x : G) => S -> R) (FunLike.hasCoeToFun.{succ u3, succ u2, succ u1} G S (fun (_x : S) => R) (MulHomClass.toFunLike.{u3, u2, u1} G S R (MulOneClass.toHasMul.{u2} S _inst_2) (MulOneClass.toHasMul.{u1} R _inst_1) (MonoidHomClass.toMulHomClass.{u3, u2, u1} G S R _inst_2 _inst_1 _inst_3))) g) f) -> (forall [_inst_4 : Invertible.{u2} S (MulOneClass.toHasMul.{u2} S _inst_2) (MulOneClass.toHasOne.{u2} S _inst_2) (f r)], Invertible.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1) (MulOneClass.toHasOne.{u1} R _inst_1) r)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} {G : Type.{u3}} [_inst_1 : MulOneClass.{u1} R] [_inst_2 : MulOneClass.{u2} S] [_inst_3 : MonoidHomClass.{u3, u2, u1} G S R _inst_2 _inst_1] (f : R -> S) (g : G) (r : R), (Function.LeftInverse.{succ u1, succ u2} R S (FunLike.coe.{succ u3, succ u2, succ u1} G S (fun (_x : S) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) _x) (MulHomClass.toFunLike.{u3, u2, u1} G S R (MulOneClass.toMul.{u2} S _inst_2) (MulOneClass.toMul.{u1} R _inst_1) (MonoidHomClass.toMulHomClass.{u3, u2, u1} G S R _inst_2 _inst_1 _inst_3)) g) f) -> (forall [_inst_4 : Invertible.{u2} S (MulOneClass.toMul.{u2} S _inst_2) (MulOneClass.toOne.{u2} S _inst_2) (f r)], Invertible.{u1} R (MulOneClass.toMul.{u1} R _inst_1) (MulOneClass.toOne.{u1} R _inst_1) r)
Case conversion may be inaccurate. Consider using '#align invertible.of_left_inverse Invertible.ofLeftInverseₓ'. -/
/-- If a function `f : R → S` has a left-inverse that is a monoid hom,
  then `r : R` is invertible if `f r` is.

The inverse is computed as `g (⅟(f r))` -/
@[simps (config := { attrs := [] })]
def Invertible.ofLeftInverse {R : Type _} {S : Type _} {G : Type _} [MulOneClass R] [MulOneClass S]
    [MonoidHomClass G S R] (f : R → S) (g : G) (r : R) (h : Function.LeftInverse g f)
    [Invertible (f r)] : Invertible r :=
  (Invertible.map g (f r)).copy _ (h r).symm
#align invertible.of_left_inverse Invertible.ofLeftInverse

/- warning: invertible_equiv_of_left_inverse -> invertibleEquivOfLeftInverse is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {F : Type.{u3}} {G : Type.{u4}} [_inst_1 : Monoid.{u1} R] [_inst_2 : Monoid.{u2} S] [_inst_3 : MonoidHomClass.{u3, u1, u2} F R S (Monoid.toMulOneClass.{u1} R _inst_1) (Monoid.toMulOneClass.{u2} S _inst_2)] [_inst_4 : MonoidHomClass.{u4, u2, u1} G S R (Monoid.toMulOneClass.{u2} S _inst_2) (Monoid.toMulOneClass.{u1} R _inst_1)] (f : F) (g : G) (r : R), (Function.LeftInverse.{succ u1, succ u2} R S (coeFn.{succ u4, max (succ u2) (succ u1)} G (fun (_x : G) => S -> R) (FunLike.hasCoeToFun.{succ u4, succ u2, succ u1} G S (fun (_x : S) => R) (MulHomClass.toFunLike.{u4, u2, u1} G S R (MulOneClass.toHasMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (MonoidHomClass.toMulHomClass.{u4, u2, u1} G S R (Monoid.toMulOneClass.{u2} S _inst_2) (Monoid.toMulOneClass.{u1} R _inst_1) _inst_4))) g) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F R (fun (_x : R) => S) (MulHomClass.toFunLike.{u3, u1, u2} F R S (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (MulOneClass.toHasMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F R S (Monoid.toMulOneClass.{u1} R _inst_1) (Monoid.toMulOneClass.{u2} S _inst_2) _inst_3))) f)) -> (Equiv.{succ u2, succ u1} (Invertible.{u2} S (MulOneClass.toHasMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MulOneClass.toHasOne.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F R (fun (_x : R) => S) (MulHomClass.toFunLike.{u3, u1, u2} F R S (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (MulOneClass.toHasMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F R S (Monoid.toMulOneClass.{u1} R _inst_1) (Monoid.toMulOneClass.{u2} S _inst_2) _inst_3))) f r)) (Invertible.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) r))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} {F : Type.{u3}} {G : Type.{u4}} [_inst_1 : Monoid.{u1} R] [_inst_2 : Monoid.{u2} S] [_inst_3 : MonoidHomClass.{u3, u1, u2} F R S (Monoid.toMulOneClass.{u1} R _inst_1) (Monoid.toMulOneClass.{u2} S _inst_2)] [_inst_4 : MonoidHomClass.{u4, u2, u1} G S R (Monoid.toMulOneClass.{u2} S _inst_2) (Monoid.toMulOneClass.{u1} R _inst_1)] (f : F) (g : G) (r : R), (Function.LeftInverse.{succ u1, succ u2} R S (FunLike.coe.{succ u4, succ u2, succ u1} G S (fun (_x : S) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : S) => R) _x) (MulHomClass.toFunLike.{u4, u2, u1} G S R (MulOneClass.toMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (MonoidHomClass.toMulHomClass.{u4, u2, u1} G S R (Monoid.toMulOneClass.{u2} S _inst_2) (Monoid.toMulOneClass.{u1} R _inst_1) _inst_4)) g) (FunLike.coe.{succ u3, succ u1, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{u3, u1, u2} F R S (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (MulOneClass.toMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F R S (Monoid.toMulOneClass.{u1} R _inst_1) (Monoid.toMulOneClass.{u2} S _inst_2) _inst_3)) f)) -> (Equiv.{succ u2, succ u1} (Invertible.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) (MulOneClass.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) (Monoid.toMulOneClass.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) _inst_2)) (Monoid.toOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) r) _inst_2) (FunLike.coe.{succ u3, succ u1, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{u3, u1, u2} F R S (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (MulOneClass.toMul.{u2} S (Monoid.toMulOneClass.{u2} S _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F R S (Monoid.toMulOneClass.{u1} R _inst_1) (Monoid.toMulOneClass.{u2} S _inst_2) _inst_3)) f r)) (Invertible.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (Monoid.toOne.{u1} R _inst_1) r))
Case conversion may be inaccurate. Consider using '#align invertible_equiv_of_left_inverse invertibleEquivOfLeftInverseₓ'. -/
/-- Invertibility on either side of a monoid hom with a left-inverse is equivalent. -/
@[simps]
def invertibleEquivOfLeftInverse {R : Type _} {S : Type _} {F G : Type _} [Monoid R] [Monoid S]
    [MonoidHomClass F R S] [MonoidHomClass G S R] (f : F) (g : G) (r : R)
    (h : Function.LeftInverse g f) : Invertible (f r) ≃ Invertible r
    where
  toFun _ := Invertible.ofLeftInverse f _ _ h
  invFun _ := Invertible.map f _
  left_inv x := Subsingleton.elim _ _
  right_inv x := Subsingleton.elim _ _
#align invertible_equiv_of_left_inverse invertibleEquivOfLeftInverse

