/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.type_tags
! leanprover-community/mathlib commit e001509c11c4d0f549d91d89da95b4a0b43c714f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.TypeTags
import Mathbin.Algebra.Order.Monoid.Cancel.Defs
import Mathbin.Algebra.Order.Monoid.Canonical.Defs

/-! # Ordered monoid structures on `multiplicative α` and `additive α`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


universe u

variable {α : Type u}

instance : ∀ [LE α], LE (Multiplicative α) :=
  id

instance : ∀ [LE α], LE (Additive α) :=
  id

instance : ∀ [LT α], LT (Multiplicative α) :=
  id

instance : ∀ [LT α], LT (Additive α) :=
  id

instance : ∀ [Preorder α], Preorder (Multiplicative α) :=
  id

instance : ∀ [Preorder α], Preorder (Additive α) :=
  id

instance : ∀ [PartialOrder α], PartialOrder (Multiplicative α) :=
  id

instance : ∀ [PartialOrder α], PartialOrder (Additive α) :=
  id

instance : ∀ [LinearOrder α], LinearOrder (Multiplicative α) :=
  id

instance : ∀ [LinearOrder α], LinearOrder (Additive α) :=
  id

instance [LE α] : ∀ [OrderBot α], OrderBot (Multiplicative α) :=
  id

instance [LE α] : ∀ [OrderBot α], OrderBot (Additive α) :=
  id

instance [LE α] : ∀ [OrderTop α], OrderTop (Multiplicative α) :=
  id

instance [LE α] : ∀ [OrderTop α], OrderTop (Additive α) :=
  id

instance [LE α] : ∀ [BoundedOrder α], BoundedOrder (Multiplicative α) :=
  id

instance [LE α] : ∀ [BoundedOrder α], BoundedOrder (Additive α) :=
  id

instance [OrderedAddCommMonoid α] : OrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.partialOrder, Multiplicative.commMonoid with
    mul_le_mul_left := @OrderedAddCommMonoid.add_le_add_left α _ }

instance [OrderedCommMonoid α] : OrderedAddCommMonoid (Additive α) :=
  { Additive.partialOrder, Additive.addCommMonoid with
    add_le_add_left := @OrderedCommMonoid.mul_le_mul_left α _ }

instance [OrderedCancelAddCommMonoid α] : OrderedCancelCommMonoid (Multiplicative α) :=
  { Multiplicative.orderedCommMonoid with
    le_of_mul_le_mul_left := @OrderedCancelAddCommMonoid.le_of_add_le_add_left α _ }

instance [OrderedCancelCommMonoid α] : OrderedCancelAddCommMonoid (Additive α) :=
  { Additive.orderedAddCommMonoid with
    le_of_add_le_add_left := @OrderedCancelCommMonoid.le_of_mul_le_mul_left α _ }

instance [LinearOrderedAddCommMonoid α] : LinearOrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.linearOrder, Multiplicative.orderedCommMonoid with }

instance [LinearOrderedCommMonoid α] : LinearOrderedAddCommMonoid (Additive α) :=
  { Additive.linearOrder, Additive.orderedAddCommMonoid with }

instance [Add α] [LE α] [ExistsAddOfLE α] : ExistsMulOfLE (Multiplicative α) :=
  ⟨@exists_add_of_le α _ _ _⟩

instance [Mul α] [LE α] [ExistsMulOfLE α] : ExistsAddOfLE (Additive α) :=
  ⟨@exists_mul_of_le α _ _ _⟩

instance [CanonicallyOrderedAddMonoid α] : CanonicallyOrderedMonoid (Multiplicative α) :=
  { Multiplicative.orderedCommMonoid, Multiplicative.orderBot,
    Multiplicative.has_exists_mul_of_le with le_self_mul := @le_self_add α _ }

instance [CanonicallyOrderedMonoid α] : CanonicallyOrderedAddMonoid (Additive α) :=
  { Additive.orderedAddCommMonoid, Additive.orderBot, Additive.has_exists_add_of_le with
    le_self_add := @le_self_mul α _ }

instance [CanonicallyLinearOrderedAddMonoid α] :
    CanonicallyLinearOrderedMonoid (Multiplicative α) :=
  { Multiplicative.canonicallyOrderedMonoid, Multiplicative.linearOrder with }

instance [CanonicallyLinearOrderedMonoid α] : CanonicallyLinearOrderedAddMonoid (Additive α) :=
  { Additive.canonicallyOrderedAddMonoid, Additive.linearOrder with }

namespace Additive

variable [Preorder α]

#print Additive.ofMul_le /-
@[simp]
theorem ofMul_le {a b : α} : ofMul a ≤ ofMul b ↔ a ≤ b :=
  Iff.rfl
#align additive.of_mul_le Additive.ofMul_le
-/

#print Additive.ofMul_lt /-
@[simp]
theorem ofMul_lt {a b : α} : ofMul a < ofMul b ↔ a < b :=
  Iff.rfl
#align additive.of_mul_lt Additive.ofMul_lt
-/

#print Additive.toMul_le /-
@[simp]
theorem toMul_le {a b : Additive α} : toMul a ≤ toMul b ↔ a ≤ b :=
  Iff.rfl
#align additive.to_mul_le Additive.toMul_le
-/

#print Additive.toMul_lt /-
@[simp]
theorem toMul_lt {a b : Additive α} : toMul a < toMul b ↔ a < b :=
  Iff.rfl
#align additive.to_mul_lt Additive.toMul_lt
-/

end Additive

namespace Multiplicative

variable [Preorder α]

#print Multiplicative.ofAdd_le /-
@[simp]
theorem ofAdd_le {a b : α} : ofAdd a ≤ ofAdd b ↔ a ≤ b :=
  Iff.rfl
#align multiplicative.of_add_le Multiplicative.ofAdd_le
-/

#print Multiplicative.ofAdd_lt /-
@[simp]
theorem ofAdd_lt {a b : α} : ofAdd a < ofAdd b ↔ a < b :=
  Iff.rfl
#align multiplicative.of_add_lt Multiplicative.ofAdd_lt
-/

#print Multiplicative.toAdd_le /-
@[simp]
theorem toAdd_le {a b : Multiplicative α} : toAdd a ≤ toAdd b ↔ a ≤ b :=
  Iff.rfl
#align multiplicative.to_add_le Multiplicative.toAdd_le
-/

#print Multiplicative.toAdd_lt /-
@[simp]
theorem toAdd_lt {a b : Multiplicative α} : toAdd a < toAdd b ↔ a < b :=
  Iff.rfl
#align multiplicative.to_add_lt Multiplicative.toAdd_lt
-/

end Multiplicative

