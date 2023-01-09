/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module algebra.order.sub.defs
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CovariantAndContravariant
import Mathbin.Algebra.Group.Basic
import Mathbin.Algebra.Order.Monoid.Lemmas
import Mathbin.Order.Lattice

/-!
# Ordered Subtraction

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves lemmas relating (truncated) subtraction with an order. We provide a class
`has_ordered_sub` stating that `a - b ≤ c ↔ a ≤ c + b`.

The subtraction discussed here could both be normal subtraction in an additive group or truncated
subtraction on a canonically ordered monoid (`ℕ`, `multiset`, `part_enat`, `ennreal`, ...)

## Implementation details

`has_ordered_sub` is a mixin type-class, so that we can use the results in this file even in cases
where we don't have a `canonically_ordered_add_monoid` instance
(even though that is our main focus). Conversely, this means we can use
`canonically_ordered_add_monoid` without necessarily having to define a subtraction.

The results in this file are ordered by the type-class assumption needed to prove it.
This means that similar results might not be close to each other. Furthermore, we don't prove
implications if a bi-implication can be proven under the same assumptions.

Lemmas using this class are named using `tsub` instead of `sub` (short for "truncated subtraction").
This is to avoid naming conflicts with similar lemmas about ordered groups.

We provide a second version of most results that require `[contravariant_class α α (+) (≤)]`. In the
second version we replace this type-class assumption by explicit `add_le_cancellable` assumptions.

TODO: maybe we should make a multiplicative version of this, so that we can replace some identical
lemmas about subtraction/division in `ordered_[add_]comm_group` with these.

TODO: generalize `nat.le_of_le_of_sub_le_sub_right`, `nat.sub_le_sub_right_iff`,
  `nat.mul_self_sub_mul_self_eq`
-/


variable {α β : Type _}

#print OrderedSub /-
/-- `has_ordered_sub α` means that `α` has a subtraction characterized by `a - b ≤ c ↔ a ≤ c + b`.
In other words, `a - b` is the least `c` such that `a ≤ b + c`.

This is satisfied both by the subtraction in additive ordered groups and by truncated subtraction
in canonically ordered monoids on many specific types.
-/
class OrderedSub (α : Type _) [LE α] [Add α] [Sub α] where
  tsub_le_iff_right : ∀ a b c : α, a - b ≤ c ↔ a ≤ c + b
#align has_ordered_sub OrderedSub
-/

section Add

variable [Preorder α] [Add α] [Sub α] [OrderedSub α] {a b c d : α}

#print tsub_le_iff_right /-
@[simp]
theorem tsub_le_iff_right : a - b ≤ c ↔ a ≤ c + b :=
  OrderedSub.tsub_le_iff_right a b c
#align tsub_le_iff_right tsub_le_iff_right
-/

#print add_tsub_le_right /-
/-- See `add_tsub_cancel_right` for the equality if `contravariant_class α α (+) (≤)`. -/
theorem add_tsub_le_right : a + b - b ≤ a :=
  tsub_le_iff_right.mpr le_rfl
#align add_tsub_le_right add_tsub_le_right
-/

#print le_tsub_add /-
theorem le_tsub_add : b ≤ b - a + a :=
  tsub_le_iff_right.mp le_rfl
#align le_tsub_add le_tsub_add
-/

end Add

/-! ### Preorder -/


section OrderedAddCommSemigroup

section Preorder

variable [Preorder α]

section AddCommSemigroup

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

/- warning: tsub_le_iff_left -> tsub_le_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c))
Case conversion may be inaccurate. Consider using '#align tsub_le_iff_left tsub_le_iff_leftₓ'. -/
theorem tsub_le_iff_left : a - b ≤ c ↔ a ≤ b + c := by rw [tsub_le_iff_right, add_comm]
#align tsub_le_iff_left tsub_le_iff_left

/- warning: le_add_tsub -> le_add_tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b))
Case conversion may be inaccurate. Consider using '#align le_add_tsub le_add_tsubₓ'. -/
theorem le_add_tsub : a ≤ b + (a - b) :=
  tsub_le_iff_left.mp le_rfl
#align le_add_tsub le_add_tsub

/- warning: add_tsub_le_left -> add_tsub_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) a) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) a) b
Case conversion may be inaccurate. Consider using '#align add_tsub_le_left add_tsub_le_leftₓ'. -/
/-- See `add_tsub_cancel_left` for the equality if `contravariant_class α α (+) (≤)`. -/
theorem add_tsub_le_left : a + b - a ≤ b :=
  tsub_le_iff_left.mpr le_rfl
#align add_tsub_le_left add_tsub_le_left

/- warning: tsub_le_tsub_right -> tsub_le_tsub_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (forall (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (forall (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
Case conversion may be inaccurate. Consider using '#align tsub_le_tsub_right tsub_le_tsub_rightₓ'. -/
theorem tsub_le_tsub_right (h : a ≤ b) (c : α) : a - c ≤ b - c :=
  tsub_le_iff_left.mpr <| h.trans le_add_tsub
#align tsub_le_tsub_right tsub_le_tsub_right

/- warning: tsub_le_iff_tsub_le -> tsub_le_iff_tsub_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) b)
Case conversion may be inaccurate. Consider using '#align tsub_le_iff_tsub_le tsub_le_iff_tsub_leₓ'. -/
theorem tsub_le_iff_tsub_le : a - b ≤ c ↔ a - c ≤ b := by rw [tsub_le_iff_left, tsub_le_iff_right]
#align tsub_le_iff_tsub_le tsub_le_iff_tsub_le

/- warning: tsub_tsub_le -> tsub_tsub_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b a)) a
Case conversion may be inaccurate. Consider using '#align tsub_tsub_le tsub_tsub_leₓ'. -/
/-- See `tsub_tsub_cancel_of_le` for the equality. -/
theorem tsub_tsub_le : b - (b - a) ≤ a :=
  tsub_le_iff_right.mpr le_add_tsub
#align tsub_tsub_le tsub_tsub_le

section Cov

variable [CovariantClass α α (· + ·) (· ≤ ·)]

/- warning: tsub_le_tsub_left -> tsub_le_tsub_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (forall (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c b) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.564 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.566 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.564 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.566) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.579 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.581 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.579 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.581)], (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (forall (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c b) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c a))
Case conversion may be inaccurate. Consider using '#align tsub_le_tsub_left tsub_le_tsub_leftₓ'. -/
theorem tsub_le_tsub_left (h : a ≤ b) (c : α) : c - b ≤ c - a :=
  tsub_le_iff_left.mpr <| le_add_tsub.trans <| add_le_add_right h _
#align tsub_le_tsub_left tsub_le_tsub_left

/- warning: tsub_le_tsub -> tsub_le_tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} {d : α} [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) c d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a d) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} {d : α} [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.642 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.644 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.642 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.644) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.657 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.659 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.657 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.659)], (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) c d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a d) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
Case conversion may be inaccurate. Consider using '#align tsub_le_tsub tsub_le_tsubₓ'. -/
theorem tsub_le_tsub (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
  (tsub_le_tsub_right hab _).trans <| tsub_le_tsub_left hcd _
#align tsub_le_tsub tsub_le_tsub

/- warning: antitone_const_tsub -> antitone_const_tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], Antitone.{u1, u1} α α _inst_1 _inst_1 (fun (x : α) => HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.726 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.728 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.726 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.728) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.741 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.743 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.741 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.743)], Antitone.{u1, u1} α α _inst_1 _inst_1 (fun (x : α) => HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c x)
Case conversion may be inaccurate. Consider using '#align antitone_const_tsub antitone_const_tsubₓ'. -/
theorem antitone_const_tsub : Antitone fun x => c - x := fun x y hxy => tsub_le_tsub rfl.le hxy
#align antitone_const_tsub antitone_const_tsub

/- warning: add_tsub_le_assoc -> add_tsub_le_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.799 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.801 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.799 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.801) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.814 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.816 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.814 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.816)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
Case conversion may be inaccurate. Consider using '#align add_tsub_le_assoc add_tsub_le_assocₓ'. -/
/-- See `add_tsub_assoc_of_le` for the equality. -/
theorem add_tsub_le_assoc : a + b - c ≤ a + (b - c) :=
  by
  rw [tsub_le_iff_left, add_left_comm]
  exact add_le_add_left le_add_tsub a
#align add_tsub_le_assoc add_tsub_le_assoc

/- warning: add_tsub_le_tsub_add -> add_tsub_le_tsub_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.903 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.905 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.903 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.905) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.918 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.920 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.918 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.920)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) b)
Case conversion may be inaccurate. Consider using '#align add_tsub_le_tsub_add add_tsub_le_tsub_addₓ'. -/
/-- See `tsub_add_eq_add_tsub` for the equality. -/
theorem add_tsub_le_tsub_add : a + b - c ≤ a - c + b :=
  by
  rw [add_comm, add_comm _ b]
  exact add_tsub_le_assoc
#align add_tsub_le_tsub_add add_tsub_le_tsub_add

/- warning: add_le_add_add_tsub -> add_le_add_add_tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1007 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1009 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1007 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1009) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1022 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1024 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1022 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1024)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
Case conversion may be inaccurate. Consider using '#align add_le_add_add_tsub add_le_add_add_tsubₓ'. -/
theorem add_le_add_add_tsub : a + b ≤ a + c + (b - c) :=
  by
  rw [add_assoc]
  exact add_le_add_left le_add_tsub a
#align add_le_add_add_tsub add_le_add_add_tsub

/- warning: le_tsub_add_add -> le_tsub_add_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1110 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1112 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1110 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1112) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1125 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1127 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1125 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1127)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c))
Case conversion may be inaccurate. Consider using '#align le_tsub_add_add le_tsub_add_addₓ'. -/
theorem le_tsub_add_add : a + b ≤ a - c + (b + c) :=
  by
  rw [add_comm a, add_comm (a - c)]
  exact add_le_add_add_tsub
#align le_tsub_add_add le_tsub_add_add

/- warning: tsub_le_tsub_add_tsub -> tsub_le_tsub_add_tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1220 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1222 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1220 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1222) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1235 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1237 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1235 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1237)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
Case conversion may be inaccurate. Consider using '#align tsub_le_tsub_add_tsub tsub_le_tsub_add_tsubₓ'. -/
theorem tsub_le_tsub_add_tsub : a - c ≤ a - b + (b - c) :=
  by
  rw [tsub_le_iff_left, ← add_assoc, add_right_comm]
  exact le_add_tsub.trans (add_le_add_right le_add_tsub _)
#align tsub_le_tsub_add_tsub tsub_le_tsub_add_tsub

/- warning: tsub_tsub_tsub_le_tsub -> tsub_tsub_tsub_le_tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c a) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c b)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1328 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1330 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1328 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1330) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1343 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1345 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1343 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1345)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c a) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c b)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b a)
Case conversion may be inaccurate. Consider using '#align tsub_tsub_tsub_le_tsub tsub_tsub_tsub_le_tsubₓ'. -/
theorem tsub_tsub_tsub_le_tsub : c - a - (c - b) ≤ b - a :=
  by
  rw [tsub_le_iff_left, tsub_le_iff_left, add_left_comm]
  exact le_tsub_add.trans (add_le_add_left le_add_tsub _)
#align tsub_tsub_tsub_le_tsub tsub_tsub_tsub_le_tsub

/- warning: tsub_tsub_le_tsub_add -> tsub_tsub_le_tsub_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))] {a : α} {b : α} {c : α}, LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1436 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1438 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1436 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1438) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1451 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1453 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1451 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1453)] {a : α} {b : α} {c : α}, LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c)
Case conversion may be inaccurate. Consider using '#align tsub_tsub_le_tsub_add tsub_tsub_le_tsub_addₓ'. -/
theorem tsub_tsub_le_tsub_add {a b c : α} : a - (b - c) ≤ a - b + c :=
  tsub_le_iff_right.2 <|
    calc
      a ≤ a - b + b := le_tsub_add
      _ ≤ a - b + (c + (b - c)) := add_le_add_left le_add_tsub _
      _ = a - b + c + (b - c) := (add_assoc _ _ _).symm
      
#align tsub_tsub_le_tsub_add tsub_tsub_le_tsub_add

/- warning: add_tsub_add_le_tsub_add_tsub -> add_tsub_add_le_tsub_add_tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} {d : α} [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) c d)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} {d : α} [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1560 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1562 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1560 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1562) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1575 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1577 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1575 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1577)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) c d)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b d))
Case conversion may be inaccurate. Consider using '#align add_tsub_add_le_tsub_add_tsub add_tsub_add_le_tsub_add_tsubₓ'. -/
/-- See `tsub_add_tsub_comm` for the equality. -/
theorem add_tsub_add_le_tsub_add_tsub : a + b - (c + d) ≤ a - c + (b - d) :=
  by
  rw [add_comm c, tsub_le_iff_left, add_assoc, ← tsub_le_iff_left, ← tsub_le_iff_left]
  refine' (tsub_le_tsub_right add_tsub_le_assoc c).trans _
  rw [add_comm a, add_comm (a - c)]
  exact add_tsub_le_assoc
#align add_tsub_add_le_tsub_add_tsub add_tsub_add_le_tsub_add_tsub

/- warning: add_tsub_add_le_tsub_left -> add_tsub_add_le_tsub_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1716 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1718 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1716 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1718) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1731 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1733 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1731 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1733)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)
Case conversion may be inaccurate. Consider using '#align add_tsub_add_le_tsub_left add_tsub_add_le_tsub_leftₓ'. -/
/-- See `add_tsub_add_eq_tsub_left` for the equality. -/
theorem add_tsub_add_le_tsub_left : a + b - (a + c) ≤ b - c :=
  by
  rw [tsub_le_iff_left, add_assoc]
  exact add_le_add_left le_add_tsub _
#align add_tsub_add_le_tsub_left add_tsub_add_le_tsub_left

/- warning: add_tsub_add_le_tsub_right -> add_tsub_add_le_tsub_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1820 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1822 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1820 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1822) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1835 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1837 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1835 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.1837)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b)
Case conversion may be inaccurate. Consider using '#align add_tsub_add_le_tsub_right add_tsub_add_le_tsub_rightₓ'. -/
/-- See `add_tsub_add_eq_tsub_right` for the equality. -/
theorem add_tsub_add_le_tsub_right : a + c - (b + c) ≤ a - b :=
  by
  rw [tsub_le_iff_left, add_right_comm]
  exact add_le_add_right le_add_tsub c
#align add_tsub_add_le_tsub_right add_tsub_add_le_tsub_right

end Cov

/-! #### Lemmas that assume that an element is `add_le_cancellable` -/


namespace AddLECancellable

/- warning: add_le_cancellable.le_add_tsub_swap -> AddLECancellable.le_add_tsub_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, (AddLECancellable.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α _inst_1) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b a) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, (AddLECancellable.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α _inst_1) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b a) b))
Case conversion may be inaccurate. Consider using '#align add_le_cancellable.le_add_tsub_swap AddLECancellable.le_add_tsub_swapₓ'. -/
protected theorem le_add_tsub_swap (hb : AddLECancellable b) : a ≤ b + a - b :=
  hb le_add_tsub
#align add_le_cancellable.le_add_tsub_swap AddLECancellable.le_add_tsub_swap

/- warning: add_le_cancellable.le_add_tsub -> AddLECancellable.le_add_tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, (AddLECancellable.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α _inst_1) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, (AddLECancellable.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α _inst_1) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) b))
Case conversion may be inaccurate. Consider using '#align add_le_cancellable.le_add_tsub AddLECancellable.le_add_tsubₓ'. -/
protected theorem le_add_tsub (hb : AddLECancellable b) : a ≤ a + b - b :=
  by
  rw [add_comm]
  exact hb.le_add_tsub_swap
#align add_le_cancellable.le_add_tsub AddLECancellable.le_add_tsub

/- warning: add_le_cancellable.le_tsub_of_add_le_left -> AddLECancellable.le_tsub_of_add_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α _inst_1) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α _inst_1) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c a))
Case conversion may be inaccurate. Consider using '#align add_le_cancellable.le_tsub_of_add_le_left AddLECancellable.le_tsub_of_add_le_leftₓ'. -/
protected theorem le_tsub_of_add_le_left (ha : AddLECancellable a) (h : a + b ≤ c) : b ≤ c - a :=
  ha <| h.trans le_add_tsub
#align add_le_cancellable.le_tsub_of_add_le_left AddLECancellable.le_tsub_of_add_le_left

/- warning: add_le_cancellable.le_tsub_of_add_le_right -> AddLECancellable.le_tsub_of_add_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α _inst_1) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α _inst_1) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c b))
Case conversion may be inaccurate. Consider using '#align add_le_cancellable.le_tsub_of_add_le_right AddLECancellable.le_tsub_of_add_le_rightₓ'. -/
protected theorem le_tsub_of_add_le_right (hb : AddLECancellable b) (h : a + b ≤ c) : a ≤ c - b :=
  hb.le_tsub_of_add_le_left <| by rwa [add_comm]
#align add_le_cancellable.le_tsub_of_add_le_right AddLECancellable.le_tsub_of_add_le_right

end AddLECancellable

/-! ### Lemmas where addition is order-reflecting -/


section Contra

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

/- warning: le_add_tsub_swap -> le_add_tsub_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2199 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2201 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2199 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2201) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2214 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2216 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2214 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2216)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b a) b)
Case conversion may be inaccurate. Consider using '#align le_add_tsub_swap le_add_tsub_swapₓ'. -/
theorem le_add_tsub_swap : a ≤ b + a - b :=
  Contravariant.AddLECancellable.le_add_tsub_swap
#align le_add_tsub_swap le_add_tsub_swap

/- warning: le_add_tsub' -> le_add_tsub' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2263 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2265 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2263 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2265) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2278 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2280 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2278 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2280)], LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) b)
Case conversion may be inaccurate. Consider using '#align le_add_tsub' le_add_tsub'ₓ'. -/
theorem le_add_tsub' : a ≤ a + b - b :=
  Contravariant.AddLECancellable.le_add_tsub
#align le_add_tsub' le_add_tsub'

/- warning: le_tsub_of_add_le_left -> le_tsub_of_add_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2327 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2329 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2327 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2329) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2342 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2344 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2342 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2344)], (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c a))
Case conversion may be inaccurate. Consider using '#align le_tsub_of_add_le_left le_tsub_of_add_le_leftₓ'. -/
theorem le_tsub_of_add_le_left (h : a + b ≤ c) : b ≤ c - a :=
  Contravariant.AddLECancellable.le_tsub_of_add_le_left h
#align le_tsub_of_add_le_left le_tsub_of_add_le_left

/- warning: le_tsub_of_add_le_right -> le_tsub_of_add_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1))], (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2397 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2399 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2397 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2399) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2412 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2414 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2412 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.2414)], (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) c b))
Case conversion may be inaccurate. Consider using '#align le_tsub_of_add_le_right le_tsub_of_add_le_rightₓ'. -/
theorem le_tsub_of_add_le_right (h : a + b ≤ c) : a ≤ c - b :=
  Contravariant.AddLECancellable.le_tsub_of_add_le_right h
#align le_tsub_of_add_le_right le_tsub_of_add_le_right

end Contra

end AddCommSemigroup

variable [AddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

/- warning: tsub_nonpos -> tsub_nonpos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) _inst_3] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) _inst_3] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align tsub_nonpos tsub_nonposₓ'. -/
theorem tsub_nonpos : a - b ≤ 0 ↔ a ≤ b := by rw [tsub_le_iff_left, add_zero]
#align tsub_nonpos tsub_nonpos

alias tsub_nonpos ↔ _ tsub_nonpos_of_le

end Preorder

/-! ### Partial order -/


variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

/- warning: tsub_tsub -> tsub_tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] (b : α) (a : α) (c : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b a) c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] (b : α) (a : α) (c : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b a) c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c))
Case conversion may be inaccurate. Consider using '#align tsub_tsub tsub_tsubₓ'. -/
theorem tsub_tsub (b a c : α) : b - a - c = b - (a + c) :=
  by
  apply le_antisymm
  · rw [tsub_le_iff_left, tsub_le_iff_left, ← add_assoc, ← tsub_le_iff_left]
  · rw [tsub_le_iff_left, add_assoc, ← tsub_le_iff_left, ← tsub_le_iff_left]
#align tsub_tsub tsub_tsub

/- warning: tsub_add_eq_tsub_tsub -> tsub_add_eq_tsub_tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] (a : α) (b : α) (c : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] (a : α) (b : α) (c : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c)
Case conversion may be inaccurate. Consider using '#align tsub_add_eq_tsub_tsub tsub_add_eq_tsub_tsubₓ'. -/
theorem tsub_add_eq_tsub_tsub (a b c : α) : a - (b + c) = a - b - c :=
  (tsub_tsub _ _ _).symm
#align tsub_add_eq_tsub_tsub tsub_add_eq_tsub_tsub

/- warning: tsub_add_eq_tsub_tsub_swap -> tsub_add_eq_tsub_tsub_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] (a : α) (b : α) (c : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] (a : α) (b : α) (c : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) b)
Case conversion may be inaccurate. Consider using '#align tsub_add_eq_tsub_tsub_swap tsub_add_eq_tsub_tsub_swapₓ'. -/
theorem tsub_add_eq_tsub_tsub_swap (a b c : α) : a - (b + c) = a - c - b :=
  by
  rw [add_comm]
  apply tsub_add_eq_tsub_tsub
#align tsub_add_eq_tsub_tsub_swap tsub_add_eq_tsub_tsub_swap

/- warning: tsub_right_comm -> tsub_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) b)
Case conversion may be inaccurate. Consider using '#align tsub_right_comm tsub_right_commₓ'. -/
theorem tsub_right_comm : a - b - c = a - c - b := by simp_rw [← tsub_add_eq_tsub_tsub, add_comm]
#align tsub_right_comm tsub_right_comm

/-! ### Lemmas that assume that an element is `add_le_cancellable`. -/


namespace AddLECancellable

/- warning: add_le_cancellable.tsub_eq_of_eq_add -> AddLECancellable.tsub_eq_of_eq_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) -> (Eq.{succ u1} α a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) c b)) -> (Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) -> (Eq.{succ u1} α a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) c b)) -> (Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c)
Case conversion may be inaccurate. Consider using '#align add_le_cancellable.tsub_eq_of_eq_add AddLECancellable.tsub_eq_of_eq_addₓ'. -/
protected theorem tsub_eq_of_eq_add (hb : AddLECancellable b) (h : a = c + b) : a - b = c :=
  le_antisymm (tsub_le_iff_right.mpr h.le) <| by
    rw [h]
    exact hb.le_add_tsub
#align add_le_cancellable.tsub_eq_of_eq_add AddLECancellable.tsub_eq_of_eq_add

/- warning: add_le_cancellable.eq_tsub_of_add_eq -> AddLECancellable.eq_tsub_of_add_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) c) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b) -> (Eq.{succ u1} α a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) c) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b) -> (Eq.{succ u1} α a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
Case conversion may be inaccurate. Consider using '#align add_le_cancellable.eq_tsub_of_add_eq AddLECancellable.eq_tsub_of_add_eqₓ'. -/
protected theorem eq_tsub_of_add_eq (hc : AddLECancellable c) (h : a + c = b) : a = b - c :=
  (hc.tsub_eq_of_eq_add h.symm).symm
#align add_le_cancellable.eq_tsub_of_add_eq AddLECancellable.eq_tsub_of_add_eq

/- warning: add_le_cancellable.tsub_eq_of_eq_add_rev -> AddLECancellable.tsub_eq_of_eq_add_rev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) -> (Eq.{succ u1} α a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c)) -> (Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) -> (Eq.{succ u1} α a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c)) -> (Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c)
Case conversion may be inaccurate. Consider using '#align add_le_cancellable.tsub_eq_of_eq_add_rev AddLECancellable.tsub_eq_of_eq_add_revₓ'. -/
protected theorem tsub_eq_of_eq_add_rev (hb : AddLECancellable b) (h : a = b + c) : a - b = c :=
  hb.tsub_eq_of_eq_add <| by rw [add_comm, h]
#align add_le_cancellable.tsub_eq_of_eq_add_rev AddLECancellable.tsub_eq_of_eq_add_rev

/- warning: add_le_cancellable.add_tsub_cancel_right -> AddLECancellable.add_tsub_cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, (AddLECancellable.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) -> (Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, (AddLECancellable.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) -> (Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) b) a)
Case conversion may be inaccurate. Consider using '#align add_le_cancellable.add_tsub_cancel_right AddLECancellable.add_tsub_cancel_rightₓ'. -/
@[simp]
protected theorem add_tsub_cancel_right (hb : AddLECancellable b) : a + b - b = a :=
  hb.tsub_eq_of_eq_add <| by rw [add_comm]
#align add_le_cancellable.add_tsub_cancel_right AddLECancellable.add_tsub_cancel_right

/- warning: add_le_cancellable.add_tsub_cancel_left -> AddLECancellable.add_tsub_cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, (AddLECancellable.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α}, (AddLECancellable.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) a) b)
Case conversion may be inaccurate. Consider using '#align add_le_cancellable.add_tsub_cancel_left AddLECancellable.add_tsub_cancel_leftₓ'. -/
@[simp]
protected theorem add_tsub_cancel_left (ha : AddLECancellable a) : a + b - a = b :=
  ha.tsub_eq_of_eq_add <| add_comm a b
#align add_le_cancellable.add_tsub_cancel_left AddLECancellable.add_tsub_cancel_left

/- warning: add_le_cancellable.lt_add_of_tsub_lt_left -> AddLECancellable.lt_add_of_tsub_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c))
Case conversion may be inaccurate. Consider using '#align add_le_cancellable.lt_add_of_tsub_lt_left AddLECancellable.lt_add_of_tsub_lt_leftₓ'. -/
protected theorem lt_add_of_tsub_lt_left (hb : AddLECancellable b) (h : a - b < c) : a < b + c :=
  by
  rw [lt_iff_le_and_ne, ← tsub_le_iff_left]
  refine' ⟨h.le, _⟩
  rintro rfl
  simpa [hb] using h
#align add_le_cancellable.lt_add_of_tsub_lt_left AddLECancellable.lt_add_of_tsub_lt_left

/- warning: add_le_cancellable.lt_add_of_tsub_lt_right -> AddLECancellable.lt_add_of_tsub_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c))
Case conversion may be inaccurate. Consider using '#align add_le_cancellable.lt_add_of_tsub_lt_right AddLECancellable.lt_add_of_tsub_lt_rightₓ'. -/
protected theorem lt_add_of_tsub_lt_right (hc : AddLECancellable c) (h : a - c < b) : a < b + c :=
  by
  rw [lt_iff_le_and_ne, ← tsub_le_iff_right]
  refine' ⟨h.le, _⟩
  rintro rfl
  simpa [hc] using h
#align add_le_cancellable.lt_add_of_tsub_lt_right AddLECancellable.lt_add_of_tsub_lt_right

/- warning: add_le_cancellable.lt_tsub_of_add_lt_right -> AddLECancellable.lt_tsub_of_add_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
Case conversion may be inaccurate. Consider using '#align add_le_cancellable.lt_tsub_of_add_lt_right AddLECancellable.lt_tsub_of_add_lt_rightₓ'. -/
protected theorem lt_tsub_of_add_lt_right (hc : AddLECancellable c) (h : a + c < b) : a < b - c :=
  (hc.le_tsub_of_add_le_right h.le).lt_of_ne <|
    by
    rintro rfl
    exact h.not_le le_tsub_add
#align add_le_cancellable.lt_tsub_of_add_lt_right AddLECancellable.lt_tsub_of_add_lt_right

/- warning: add_le_cancellable.lt_tsub_of_add_lt_left -> AddLECancellable.lt_tsub_of_add_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) c (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α}, (AddLECancellable.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) c (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b a))
Case conversion may be inaccurate. Consider using '#align add_le_cancellable.lt_tsub_of_add_lt_left AddLECancellable.lt_tsub_of_add_lt_leftₓ'. -/
protected theorem lt_tsub_of_add_lt_left (ha : AddLECancellable a) (h : a + c < b) : c < b - a :=
  ha.lt_tsub_of_add_lt_right <| by rwa [add_comm]
#align add_le_cancellable.lt_tsub_of_add_lt_left AddLECancellable.lt_tsub_of_add_lt_left

end AddLECancellable

/-! #### Lemmas where addition is order-reflecting. -/


section Contra

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

/- warning: tsub_eq_of_eq_add -> tsub_eq_of_eq_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))], (Eq.{succ u1} α a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) c b)) -> (Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3493 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3495 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3493 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3495) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3508 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3510 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3508 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3510)], (Eq.{succ u1} α a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) c b)) -> (Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c)
Case conversion may be inaccurate. Consider using '#align tsub_eq_of_eq_add tsub_eq_of_eq_addₓ'. -/
theorem tsub_eq_of_eq_add (h : a = c + b) : a - b = c :=
  Contravariant.AddLECancellable.tsub_eq_of_eq_add h
#align tsub_eq_of_eq_add tsub_eq_of_eq_add

/- warning: eq_tsub_of_add_eq -> eq_tsub_of_add_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))], (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b) -> (Eq.{succ u1} α a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3563 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3565 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3563 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3565) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3578 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3580 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3578 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3580)], (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b) -> (Eq.{succ u1} α a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
Case conversion may be inaccurate. Consider using '#align eq_tsub_of_add_eq eq_tsub_of_add_eqₓ'. -/
theorem eq_tsub_of_add_eq (h : a + c = b) : a = b - c :=
  Contravariant.AddLECancellable.eq_tsub_of_add_eq h
#align eq_tsub_of_add_eq eq_tsub_of_add_eq

/- warning: tsub_eq_of_eq_add_rev -> tsub_eq_of_eq_add_rev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))], (Eq.{succ u1} α a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c)) -> (Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3633 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3635 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3633 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3635) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3648 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3650 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3648 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3650)], (Eq.{succ u1} α a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c)) -> (Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c)
Case conversion may be inaccurate. Consider using '#align tsub_eq_of_eq_add_rev tsub_eq_of_eq_add_revₓ'. -/
theorem tsub_eq_of_eq_add_rev (h : a = b + c) : a - b = c :=
  Contravariant.AddLECancellable.tsub_eq_of_eq_add_rev h
#align tsub_eq_of_eq_add_rev tsub_eq_of_eq_add_rev

/- warning: add_tsub_cancel_right -> add_tsub_cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))] (a : α) (b : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) b) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3703 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3705 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3703 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3705) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3718 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3720 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3718 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3720)] (a : α) (b : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) b) a
Case conversion may be inaccurate. Consider using '#align add_tsub_cancel_right add_tsub_cancel_rightₓ'. -/
@[simp]
theorem add_tsub_cancel_right (a b : α) : a + b - b = a :=
  Contravariant.AddLECancellable.add_tsub_cancel_right
#align add_tsub_cancel_right add_tsub_cancel_right

/- warning: add_tsub_cancel_left -> add_tsub_cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))] (a : α) (b : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) a) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3769 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3771 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3769 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3771) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3784 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3786 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3784 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3786)] (a : α) (b : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) a) b
Case conversion may be inaccurate. Consider using '#align add_tsub_cancel_left add_tsub_cancel_leftₓ'. -/
@[simp]
theorem add_tsub_cancel_left (a b : α) : a + b - a = b :=
  Contravariant.AddLECancellable.add_tsub_cancel_left
#align add_tsub_cancel_left add_tsub_cancel_left

/- warning: lt_add_of_tsub_lt_left -> lt_add_of_tsub_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3835 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3837 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3835 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3837) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3850 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3852 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3850 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3852)], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c))
Case conversion may be inaccurate. Consider using '#align lt_add_of_tsub_lt_left lt_add_of_tsub_lt_leftₓ'. -/
theorem lt_add_of_tsub_lt_left (h : a - b < c) : a < b + c :=
  Contravariant.AddLECancellable.lt_add_of_tsub_lt_left h
#align lt_add_of_tsub_lt_left lt_add_of_tsub_lt_left

/- warning: lt_add_of_tsub_lt_right -> lt_add_of_tsub_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3905 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3907 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3905 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3907) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3920 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3922 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3920 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3922)], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c))
Case conversion may be inaccurate. Consider using '#align lt_add_of_tsub_lt_right lt_add_of_tsub_lt_rightₓ'. -/
theorem lt_add_of_tsub_lt_right (h : a - c < b) : a < b + c :=
  Contravariant.AddLECancellable.lt_add_of_tsub_lt_right h
#align lt_add_of_tsub_lt_right lt_add_of_tsub_lt_right

/- warning: lt_tsub_of_add_lt_left -> lt_tsub_of_add_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) c (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3975 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3977 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3975 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3977) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3990 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3992 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3990 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.3992)], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) c (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b a))
Case conversion may be inaccurate. Consider using '#align lt_tsub_of_add_lt_left lt_tsub_of_add_lt_leftₓ'. -/
/-- This lemma (and some of its corollaries) also holds for `ennreal`, but this proof doesn't work
for it. Maybe we should add this lemma as field to `has_ordered_sub`? -/
theorem lt_tsub_of_add_lt_left : a + c < b → c < b - a :=
  Contravariant.AddLECancellable.lt_tsub_of_add_lt_left
#align lt_tsub_of_add_lt_left lt_tsub_of_add_lt_left

/- warning: lt_tsub_of_add_lt_right -> lt_tsub_of_add_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] {a : α} {b : α} {c : α} [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4045 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4047 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4045 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4047) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4060 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4062 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4060 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4062)], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c))
Case conversion may be inaccurate. Consider using '#align lt_tsub_of_add_lt_right lt_tsub_of_add_lt_rightₓ'. -/
theorem lt_tsub_of_add_lt_right : a + c < b → a < b - c :=
  Contravariant.AddLECancellable.lt_tsub_of_add_lt_right
#align lt_tsub_of_add_lt_right lt_tsub_of_add_lt_right

end Contra

section Both

variable [CovariantClass α α (· + ·) (· ≤ ·)] [ContravariantClass α α (· + ·) (· ≤ ·)]

/- warning: add_tsub_add_eq_tsub_right -> add_tsub_add_eq_tsub_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))] [_inst_6 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))] (a : α) (c : α) (b : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4206 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4208 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4206 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4208) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4221 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4223 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4221 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4223)] [_inst_6 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4240 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4242 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4240 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4242) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4255 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4257 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4255 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4257)] (a : α) (c : α) (b : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) b c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b)
Case conversion may be inaccurate. Consider using '#align add_tsub_add_eq_tsub_right add_tsub_add_eq_tsub_rightₓ'. -/
theorem add_tsub_add_eq_tsub_right (a c b : α) : a + c - (b + c) = a - b :=
  by
  refine' add_tsub_add_le_tsub_right.antisymm (tsub_le_iff_right.2 <| le_of_add_le_add_right _);
  swap
  rw [add_assoc]
  exact le_tsub_add
#align add_tsub_add_eq_tsub_right add_tsub_add_eq_tsub_right

/- warning: add_tsub_add_eq_tsub_left -> add_tsub_add_eq_tsub_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))] [_inst_6 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))] (a : α) (b : α) (c : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4355 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4357 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4355 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4357) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4370 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4372 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4370 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4372)] [_inst_6 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4389 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4391 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4389 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4391) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4404 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4406 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4404 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4406)] (a : α) (b : α) (c : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)
Case conversion may be inaccurate. Consider using '#align add_tsub_add_eq_tsub_left add_tsub_add_eq_tsub_leftₓ'. -/
theorem add_tsub_add_eq_tsub_left (a b c : α) : a + b - (a + c) = b - c := by
  rw [add_comm a b, add_comm a c, add_tsub_add_eq_tsub_right]
#align add_tsub_add_eq_tsub_left add_tsub_add_eq_tsub_left

end Both

end OrderedAddCommSemigroup

/-! ### Lemmas in a linearly ordered monoid. -/


section LinearOrder

variable {a b c d : α} [LinearOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α]

/- warning: lt_of_tsub_lt_tsub_right -> lt_of_tsub_lt_tsub_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {b : α} {c : α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {b : α} {c : α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align lt_of_tsub_lt_tsub_right lt_of_tsub_lt_tsub_rightₓ'. -/
/-- See `lt_of_tsub_lt_tsub_right_of_le` for a weaker statement in a partial order. -/
theorem lt_of_tsub_lt_tsub_right (h : a - c < b - c) : a < b :=
  lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_right h c) h
#align lt_of_tsub_lt_tsub_right lt_of_tsub_lt_tsub_right

/- warning: lt_tsub_iff_right -> lt_tsub_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {b : α} {c : α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {b : α} {c : α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) a c) b)
Case conversion may be inaccurate. Consider using '#align lt_tsub_iff_right lt_tsub_iff_rightₓ'. -/
/-- See `lt_tsub_iff_right_of_le` for a weaker statement in a partial order. -/
theorem lt_tsub_iff_right : a < b - c ↔ a + c < b :=
  lt_iff_lt_of_le_iff_le tsub_le_iff_right
#align lt_tsub_iff_right lt_tsub_iff_right

/- warning: lt_tsub_iff_left -> lt_tsub_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {b : α} {c : α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) c a) b)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {b : α} {c : α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) c a) b)
Case conversion may be inaccurate. Consider using '#align lt_tsub_iff_left lt_tsub_iff_leftₓ'. -/
/-- See `lt_tsub_iff_left_of_le` for a weaker statement in a partial order. -/
theorem lt_tsub_iff_left : a < b - c ↔ c + a < b :=
  lt_iff_lt_of_le_iff_le tsub_le_iff_left
#align lt_tsub_iff_left lt_tsub_iff_left

/- warning: lt_tsub_comm -> lt_tsub_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {b : α} {c : α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) c (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b a))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {b : α} {c : α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b c)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) c (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) b a))
Case conversion may be inaccurate. Consider using '#align lt_tsub_comm lt_tsub_commₓ'. -/
theorem lt_tsub_comm : a < b - c ↔ c < b - a :=
  lt_tsub_iff_left.trans lt_tsub_iff_right.symm
#align lt_tsub_comm lt_tsub_comm

section Cov

variable [CovariantClass α α (· + ·) (· ≤ ·)]

/- warning: lt_of_tsub_lt_tsub_left -> lt_of_tsub_lt_tsub_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {b : α} {c : α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] [_inst_5 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toHasAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c)) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) c b)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {b : α} {c : α} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddCommSemigroup.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2)) _inst_3] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4741 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4743 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddSemigroup.toAdd.{u1} α (AddCommSemigroup.toAddSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4741 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4743) (fun (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4756 : α) (x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4758 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4756 x._@.Mathlib.Algebra.Order.Sub.Defs._hyg.4758)], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a c)) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) c b)
Case conversion may be inaccurate. Consider using '#align lt_of_tsub_lt_tsub_left lt_of_tsub_lt_tsub_leftₓ'. -/
/-- See `lt_of_tsub_lt_tsub_left_of_le` for a weaker statement in a partial order. -/
theorem lt_of_tsub_lt_tsub_left (h : a - b < a - c) : c < b :=
  lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_left h a) h
#align lt_of_tsub_lt_tsub_left lt_of_tsub_lt_tsub_left

end Cov

end LinearOrder

section OrderedAddCommMonoid

variable [PartialOrder α] [AddCommMonoid α] [Sub α] [OrderedSub α]

/- warning: tsub_zero -> tsub_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) _inst_3] (a : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))))))) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) _inst_3] (a : α), Eq.{succ u1} α (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))))) a
Case conversion may be inaccurate. Consider using '#align tsub_zero tsub_zeroₓ'. -/
@[simp]
theorem tsub_zero (a : α) : a - 0 = a :=
  AddLECancellable.tsub_eq_of_eq_add addLECancellable_zero (add_zero _).symm
#align tsub_zero tsub_zero

end OrderedAddCommMonoid

