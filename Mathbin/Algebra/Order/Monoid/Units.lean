/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.units
! leanprover-community/mathlib commit 09597669f02422ed388036273d8848119699c22f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Hom.Basic
import Mathbin.Order.MinMax
import Mathbin.Algebra.Group.Units

/-!
# Units in ordered monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/873
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

namespace Units

@[to_additive]
instance [Monoid α] [Preorder α] : Preorder αˣ :=
  Preorder.lift (coe : αˣ → α)

#print Units.val_le_val /-
@[simp, norm_cast, to_additive]
theorem val_le_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) ≤ b ↔ a ≤ b :=
  Iff.rfl
#align units.coe_le_coe Units.val_le_val
-/

#print Units.val_lt_val /-
@[simp, norm_cast, to_additive]
theorem val_lt_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) < b ↔ a < b :=
  Iff.rfl
#align units.coe_lt_coe Units.val_lt_val
-/

@[to_additive]
instance [Monoid α] [PartialOrder α] : PartialOrder αˣ :=
  PartialOrder.lift coe Units.ext

@[to_additive]
instance [Monoid α] [LinearOrder α] : LinearOrder αˣ :=
  LinearOrder.lift' coe Units.ext

#print Units.orderEmbeddingVal /-
/-- `coe : αˣ → α` as an order embedding. -/
@[to_additive "`coe : add_units α → α` as an order embedding.",
  simps (config := { fullyApplied := false })]
def orderEmbeddingVal [Monoid α] [LinearOrder α] : αˣ ↪o α :=
  ⟨⟨coe, ext⟩, fun _ _ => Iff.rfl⟩
#align units.order_embedding_coe Units.orderEmbeddingVal
-/

/- warning: units.max_coe -> Units.max_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : LinearOrder.{u1} α] {a : Units.{u1} α _inst_1} {b : Units.{u1} α _inst_1}, Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) (LinearOrder.max.{u1} (Units.{u1} α _inst_1) (Units.linearOrder.{u1} α _inst_1 _inst_2) a b)) (LinearOrder.max.{u1} α _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) a) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : LinearOrder.{u1} α] {a : Units.{u1} α _inst_1} {b : Units.{u1} α _inst_1}, Eq.{succ u1} α (Units.val.{u1} α _inst_1 (Max.max.{u1} (Units.{u1} α _inst_1) (LinearOrder.toMax.{u1} (Units.{u1} α _inst_1) (Units.instLinearOrderUnits.{u1} α _inst_1 _inst_2)) a b)) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_2) (Units.val.{u1} α _inst_1 a) (Units.val.{u1} α _inst_1 b))
Case conversion may be inaccurate. Consider using '#align units.max_coe Units.max_valₓ'. -/
@[simp, norm_cast, to_additive]
theorem max_val [Monoid α] [LinearOrder α] {a b : αˣ} : (↑(max a b) : α) = max a b :=
  Monotone.map_max orderEmbeddingVal.Monotone
#align units.max_coe Units.max_val

/- warning: units.min_coe -> Units.min_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : LinearOrder.{u1} α] {a : Units.{u1} α _inst_1} {b : Units.{u1} α _inst_1}, Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) (LinearOrder.min.{u1} (Units.{u1} α _inst_1) (Units.linearOrder.{u1} α _inst_1 _inst_2) a b)) (LinearOrder.min.{u1} α _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) a) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : LinearOrder.{u1} α] {a : Units.{u1} α _inst_1} {b : Units.{u1} α _inst_1}, Eq.{succ u1} α (Units.val.{u1} α _inst_1 (Min.min.{u1} (Units.{u1} α _inst_1) (LinearOrder.toMin.{u1} (Units.{u1} α _inst_1) (Units.instLinearOrderUnits.{u1} α _inst_1 _inst_2)) a b)) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_2) (Units.val.{u1} α _inst_1 a) (Units.val.{u1} α _inst_1 b))
Case conversion may be inaccurate. Consider using '#align units.min_coe Units.min_valₓ'. -/
@[simp, norm_cast, to_additive]
theorem min_val [Monoid α] [LinearOrder α] {a b : αˣ} : (↑(min a b) : α) = min a b :=
  Monotone.map_min orderEmbeddingVal.Monotone
#align units.min_coe Units.min_val

end Units

