/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.type_tags
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
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
  { Multiplicative.orderedCommMonoid, Multiplicative.orderBot, Multiplicative.existsMulOfLE with
    le_self_mul := @le_self_add α _ }

instance [CanonicallyOrderedMonoid α] : CanonicallyOrderedAddMonoid (Additive α) :=
  { Additive.orderedAddCommMonoid, Additive.orderBot, Additive.existsAddOfLE with
    le_self_add := @le_self_mul α _ }

instance [CanonicallyLinearOrderedAddMonoid α] :
    CanonicallyLinearOrderedMonoid (Multiplicative α) :=
  { Multiplicative.canonicallyOrderedMonoid, Multiplicative.linearOrder with }

instance [CanonicallyLinearOrderedMonoid α] : CanonicallyLinearOrderedAddMonoid (Additive α) :=
  { Additive.canonicallyOrderedAddMonoid, Additive.linearOrder with }

namespace Additive

variable [Preorder α]

/- warning: additive.of_mul_le -> Additive.ofMul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} (Additive.{u1} α) (Additive.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Additive.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Additive.{u1} α)) => α -> (Additive.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Additive.{u1} α)) (Additive.ofMul.{u1} α) a) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Additive.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Additive.{u1} α)) => α -> (Additive.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Additive.{u1} α)) (Additive.ofMul.{u1} α) b)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Additive.{u1} α) a) (instForAllLEAdditive.{u1} α (Preorder.toLE.{u1} α _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Additive.{u1} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Additive.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α (Additive.{u1} α)) (Additive.ofMul.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Additive.{u1} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Additive.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α (Additive.{u1} α)) (Additive.ofMul.{u1} α) b)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align additive.of_mul_le Additive.ofMul_leₓ'. -/
@[simp]
theorem ofMul_le {a b : α} : ofMul a ≤ ofMul b ↔ a ≤ b :=
  Iff.rfl
#align additive.of_mul_le Additive.ofMul_le

/- warning: additive.of_mul_lt -> Additive.ofMul_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (LT.lt.{u1} (Additive.{u1} α) (Additive.hasLt.{u1} α (Preorder.toHasLt.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Additive.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Additive.{u1} α)) => α -> (Additive.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Additive.{u1} α)) (Additive.ofMul.{u1} α) a) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Additive.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Additive.{u1} α)) => α -> (Additive.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Additive.{u1} α)) (Additive.ofMul.{u1} α) b)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (LT.lt.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Additive.{u1} α) a) (instForAllLTAdditive.{u1} α (Preorder.toLT.{u1} α _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Additive.{u1} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Additive.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α (Additive.{u1} α)) (Additive.ofMul.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Additive.{u1} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Additive.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α (Additive.{u1} α)) (Additive.ofMul.{u1} α) b)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align additive.of_mul_lt Additive.ofMul_ltₓ'. -/
@[simp]
theorem ofMul_lt {a b : α} : ofMul a < ofMul b ↔ a < b :=
  Iff.rfl
#align additive.of_mul_lt Additive.ofMul_lt

/- warning: additive.to_mul_le -> Additive.toMul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : Additive.{u1} α} {b : Additive.{u1} α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Additive.{u1} α) α) => (Additive.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.toMul.{u1} α) a) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Additive.{u1} α) α) => (Additive.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.toMul.{u1} α) b)) (LE.le.{u1} (Additive.{u1} α) (Additive.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : Additive.{u1} α} {b : Additive.{u1} α}, Iff (LE.le.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Additive.{u1} α) => α) a) (Preorder.toLE.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Additive.{u1} α) => α) a) _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.{u1} α) (fun (_x : Additive.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Additive.{u1} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.toMul.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.{u1} α) (fun (_x : Additive.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Additive.{u1} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.toMul.{u1} α) b)) (LE.le.{u1} (Additive.{u1} α) (instForAllLEAdditive.{u1} α (Preorder.toLE.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align additive.to_mul_le Additive.toMul_leₓ'. -/
@[simp]
theorem toMul_le {a b : Additive α} : toMul a ≤ toMul b ↔ a ≤ b :=
  Iff.rfl
#align additive.to_mul_le Additive.toMul_le

/- warning: additive.to_mul_lt -> Additive.toMul_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : Additive.{u1} α} {b : Additive.{u1} α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Additive.{u1} α) α) => (Additive.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.toMul.{u1} α) a) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Additive.{u1} α) α) => (Additive.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.toMul.{u1} α) b)) (LT.lt.{u1} (Additive.{u1} α) (Additive.hasLt.{u1} α (Preorder.toHasLt.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : Additive.{u1} α} {b : Additive.{u1} α}, Iff (LT.lt.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Additive.{u1} α) => α) a) (Preorder.toLT.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Additive.{u1} α) => α) a) _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.{u1} α) (fun (_x : Additive.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Additive.{u1} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.toMul.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.{u1} α) (fun (_x : Additive.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Additive.{u1} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.toMul.{u1} α) b)) (LT.lt.{u1} (Additive.{u1} α) (instForAllLTAdditive.{u1} α (Preorder.toLT.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align additive.to_mul_lt Additive.toMul_ltₓ'. -/
@[simp]
theorem toMul_lt {a b : Additive α} : toMul a < toMul b ↔ a < b :=
  Iff.rfl
#align additive.to_mul_lt Additive.toMul_lt

end Additive

namespace Multiplicative

variable [Preorder α]

/- warning: multiplicative.of_add_le -> Multiplicative.ofAdd_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} (Multiplicative.{u1} α) (Multiplicative.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) => α -> (Multiplicative.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Multiplicative.{u1} α)) (Multiplicative.ofAdd.{u1} α) a) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) => α -> (Multiplicative.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Multiplicative.{u1} α)) (Multiplicative.ofAdd.{u1} α) b)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Multiplicative.{u1} α) a) (instForAllLEMultiplicative.{u1} α (Preorder.toLE.{u1} α _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Multiplicative.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) (Multiplicative.ofAdd.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Multiplicative.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) (Multiplicative.ofAdd.{u1} α) b)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align multiplicative.of_add_le Multiplicative.ofAdd_leₓ'. -/
@[simp]
theorem ofAdd_le {a b : α} : ofAdd a ≤ ofAdd b ↔ a ≤ b :=
  Iff.rfl
#align multiplicative.of_add_le Multiplicative.ofAdd_le

/- warning: multiplicative.of_add_lt -> Multiplicative.ofAdd_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (LT.lt.{u1} (Multiplicative.{u1} α) (Multiplicative.hasLt.{u1} α (Preorder.toHasLt.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) => α -> (Multiplicative.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Multiplicative.{u1} α)) (Multiplicative.ofAdd.{u1} α) a) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) => α -> (Multiplicative.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Multiplicative.{u1} α)) (Multiplicative.ofAdd.{u1} α) b)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} {b : α}, Iff (LT.lt.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Multiplicative.{u1} α) a) (instForAllLTMultiplicative.{u1} α (Preorder.toLT.{u1} α _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Multiplicative.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) (Multiplicative.ofAdd.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => Multiplicative.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) (Multiplicative.ofAdd.{u1} α) b)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align multiplicative.of_add_lt Multiplicative.ofAdd_ltₓ'. -/
@[simp]
theorem ofAdd_lt {a b : α} : ofAdd a < ofAdd b ↔ a < b :=
  Iff.rfl
#align multiplicative.of_add_lt Multiplicative.ofAdd_lt

/- warning: multiplicative.to_add_le -> Multiplicative.toAdd_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : Multiplicative.{u1} α} {b : Multiplicative.{u1} α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) => (Multiplicative.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.toAdd.{u1} α) a) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) => (Multiplicative.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.toAdd.{u1} α) b)) (LE.le.{u1} (Multiplicative.{u1} α) (Multiplicative.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : Multiplicative.{u1} α} {b : Multiplicative.{u1} α}, Iff (LE.le.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Multiplicative.{u1} α) => α) a) (Preorder.toLE.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Multiplicative.{u1} α) => α) a) _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.{u1} α) (fun (_x : Multiplicative.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Multiplicative.{u1} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.toAdd.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.{u1} α) (fun (_x : Multiplicative.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Multiplicative.{u1} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.toAdd.{u1} α) b)) (LE.le.{u1} (Multiplicative.{u1} α) (instForAllLEMultiplicative.{u1} α (Preorder.toLE.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align multiplicative.to_add_le Multiplicative.toAdd_leₓ'. -/
@[simp]
theorem toAdd_le {a b : Multiplicative α} : toAdd a ≤ toAdd b ↔ a ≤ b :=
  Iff.rfl
#align multiplicative.to_add_le Multiplicative.toAdd_le

/- warning: multiplicative.to_add_lt -> Multiplicative.toAdd_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : Multiplicative.{u1} α} {b : Multiplicative.{u1} α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) => (Multiplicative.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.toAdd.{u1} α) a) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) => (Multiplicative.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.toAdd.{u1} α) b)) (LT.lt.{u1} (Multiplicative.{u1} α) (Multiplicative.hasLt.{u1} α (Preorder.toHasLt.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : Multiplicative.{u1} α} {b : Multiplicative.{u1} α}, Iff (LT.lt.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Multiplicative.{u1} α) => α) a) (Preorder.toLT.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Multiplicative.{u1} α) => α) a) _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.{u1} α) (fun (_x : Multiplicative.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Multiplicative.{u1} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.toAdd.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.{u1} α) (fun (_x : Multiplicative.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Multiplicative.{u1} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.toAdd.{u1} α) b)) (LT.lt.{u1} (Multiplicative.{u1} α) (instForAllLTMultiplicative.{u1} α (Preorder.toLT.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align multiplicative.to_add_lt Multiplicative.toAdd_ltₓ'. -/
@[simp]
theorem toAdd_lt {a b : Multiplicative α} : toAdd a < toAdd b ↔ a < b :=
  Iff.rfl
#align multiplicative.to_add_lt Multiplicative.toAdd_lt

end Multiplicative

