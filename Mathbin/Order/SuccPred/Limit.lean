/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios

! This file was ported from Lean 3 source module order.succ_pred.limit
! leanprover-community/mathlib commit baba818b9acea366489e8ba32d2cc0fcaf50a1f7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.SuccPred.Basic

/-!
# Successor and predecessor limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the predicate `order.is_succ_limit` for "successor limits", values that don't cover any
others. They are so named since they can't be the successors of anything smaller. We define
`order.is_pred_limit` analogously, and prove basic results.

## Todo

The plan is to eventually replace `ordinal.is_limit` and `cardinal.is_limit` with the common
predicate `order.is_succ_limit`.
-/


variable {α : Type _}

namespace Order

open Function Set OrderDual

/-! ### Successor limits -/


section LT

variable [LT α]

#print Order.IsSuccLimit /-
/-- A successor limit is a value that doesn't cover any other.

It's so named because in a successor order, a successor limit can't be the successor of anything
smaller. -/
def IsSuccLimit (a : α) : Prop :=
  ∀ b, ¬b ⋖ a
#align order.is_succ_limit Order.IsSuccLimit
-/

#print Order.not_isSuccLimit_iff_exists_covby /-
theorem not_isSuccLimit_iff_exists_covby (a : α) : ¬IsSuccLimit a ↔ ∃ b, b ⋖ a := by
  simp [is_succ_limit]
#align order.not_is_succ_limit_iff_exists_covby Order.not_isSuccLimit_iff_exists_covby
-/

#print Order.isSuccLimit_of_dense /-
@[simp]
theorem isSuccLimit_of_dense [DenselyOrdered α] (a : α) : IsSuccLimit a := fun b => not_covby
#align order.is_succ_limit_of_dense Order.isSuccLimit_of_dense
-/

end LT

section Preorder

variable [Preorder α] {a : α}

/- warning: is_min.is_succ_limit -> IsMin.isSuccLimit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α}, (IsMin.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a) -> (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α}, (IsMin.{u1} α (Preorder.toLE.{u1} α _inst_1) a) -> (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align is_min.is_succ_limit IsMin.isSuccLimitₓ'. -/
protected theorem IsMin.isSuccLimit : IsMin a → IsSuccLimit a := fun h b hab =>
  not_isMin_of_lt hab.lt h
#align is_min.is_succ_limit IsMin.isSuccLimit

/- warning: order.is_succ_limit_bot -> Order.isSuccLimit_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α _inst_1)], Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α _inst_1) _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)], Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_bot Order.isSuccLimit_botₓ'. -/
theorem isSuccLimit_bot [OrderBot α] : IsSuccLimit (⊥ : α) :=
  isMin_bot.IsSuccLimit
#align order.is_succ_limit_bot Order.isSuccLimit_bot

variable [SuccOrder α]

/- warning: order.is_succ_limit.is_max -> Order.IsSuccLimit.isMax is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : SuccOrder.{u1} α _inst_1], (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) (Order.succ.{u1} α _inst_1 _inst_2 a)) -> (IsMax.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : SuccOrder.{u1} α _inst_1], (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) (Order.succ.{u1} α _inst_1 _inst_2 a)) -> (IsMax.{u1} α (Preorder.toLE.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit.is_max Order.IsSuccLimit.isMaxₓ'. -/
protected theorem IsSuccLimit.isMax (h : IsSuccLimit (succ a)) : IsMax a := by by_contra H;
  exact h a (covby_succ_of_not_is_max H)
#align order.is_succ_limit.is_max Order.IsSuccLimit.isMax

/- warning: order.not_is_succ_limit_succ_of_not_is_max -> Order.not_isSuccLimit_succ_of_not_isMax is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : SuccOrder.{u1} α _inst_1], (Not (IsMax.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a)) -> (Not (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) (Order.succ.{u1} α _inst_1 _inst_2 a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : SuccOrder.{u1} α _inst_1], (Not (IsMax.{u1} α (Preorder.toLE.{u1} α _inst_1) a)) -> (Not (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) (Order.succ.{u1} α _inst_1 _inst_2 a)))
Case conversion may be inaccurate. Consider using '#align order.not_is_succ_limit_succ_of_not_is_max Order.not_isSuccLimit_succ_of_not_isMaxₓ'. -/
theorem not_isSuccLimit_succ_of_not_isMax (ha : ¬IsMax a) : ¬IsSuccLimit (succ a) := by
  contrapose! ha; exact ha.is_max
#align order.not_is_succ_limit_succ_of_not_is_max Order.not_isSuccLimit_succ_of_not_isMax

section NoMaxOrder

variable [NoMaxOrder α]

/- warning: order.is_succ_limit.succ_ne -> Order.IsSuccLimit.succ_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : SuccOrder.{u1} α _inst_1] [_inst_3 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)], (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a) -> (forall (b : α), Ne.{succ u1} α (Order.succ.{u1} α _inst_1 _inst_2 b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : SuccOrder.{u1} α _inst_1] [_inst_3 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) a) -> (forall (b : α), Ne.{succ u1} α (Order.succ.{u1} α _inst_1 _inst_2 b) a)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit.succ_ne Order.IsSuccLimit.succ_neₓ'. -/
theorem IsSuccLimit.succ_ne (h : IsSuccLimit a) (b : α) : succ b ≠ a := by rintro rfl;
  exact not_isMax _ h.is_max
#align order.is_succ_limit.succ_ne Order.IsSuccLimit.succ_ne

/- warning: order.not_is_succ_limit_succ -> Order.not_isSuccLimit_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : SuccOrder.{u1} α _inst_1] [_inst_3 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] (a : α), Not (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) (Order.succ.{u1} α _inst_1 _inst_2 a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : SuccOrder.{u1} α _inst_1] [_inst_3 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)] (a : α), Not (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) (Order.succ.{u1} α _inst_1 _inst_2 a))
Case conversion may be inaccurate. Consider using '#align order.not_is_succ_limit_succ Order.not_isSuccLimit_succₓ'. -/
@[simp]
theorem not_isSuccLimit_succ (a : α) : ¬IsSuccLimit (succ a) := fun h => h.succ_ne _ rfl
#align order.not_is_succ_limit_succ Order.not_isSuccLimit_succ

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

/- warning: order.is_succ_limit.is_min_of_no_max -> Order.IsSuccLimit.isMin_of_noMax is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : SuccOrder.{u1} α _inst_1] [_inst_3 : IsSuccArchimedean.{u1} α _inst_1 _inst_2] [_inst_4 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)], (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a) -> (IsMin.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : SuccOrder.{u1} α _inst_1] [_inst_3 : IsSuccArchimedean.{u1} α _inst_1 _inst_2] [_inst_4 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) a) -> (IsMin.{u1} α (Preorder.toLE.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit.is_min_of_no_max Order.IsSuccLimit.isMin_of_noMaxₓ'. -/
theorem IsSuccLimit.isMin_of_noMax [NoMaxOrder α] (h : IsSuccLimit a) : IsMin a := fun b hb =>
  by
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩
  · exact le_rfl
  · rw [iterate_succ_apply'] at h
    exact (not_is_succ_limit_succ _ h).elim
#align order.is_succ_limit.is_min_of_no_max Order.IsSuccLimit.isMin_of_noMax

/- warning: order.is_succ_limit_iff_of_no_max -> Order.isSuccLimit_iff_of_noMax is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : SuccOrder.{u1} α _inst_1] [_inst_3 : IsSuccArchimedean.{u1} α _inst_1 _inst_2] [_inst_4 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)], Iff (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a) (IsMin.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : SuccOrder.{u1} α _inst_1] [_inst_3 : IsSuccArchimedean.{u1} α _inst_1 _inst_2] [_inst_4 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], Iff (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) a) (IsMin.{u1} α (Preorder.toLE.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_iff_of_no_max Order.isSuccLimit_iff_of_noMaxₓ'. -/
@[simp]
theorem isSuccLimit_iff_of_noMax [NoMaxOrder α] : IsSuccLimit a ↔ IsMin a :=
  ⟨IsSuccLimit.isMin_of_noMax, IsMin.isSuccLimit⟩
#align order.is_succ_limit_iff_of_no_max Order.isSuccLimit_iff_of_noMax

/- warning: order.not_is_succ_limit_of_no_max -> Order.not_isSuccLimit_of_noMax is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : SuccOrder.{u1} α _inst_1] [_inst_3 : IsSuccArchimedean.{u1} α _inst_1 _inst_2] [_inst_4 : NoMinOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] [_inst_5 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)], Not (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : SuccOrder.{u1} α _inst_1] [_inst_3 : IsSuccArchimedean.{u1} α _inst_1 _inst_2] [_inst_4 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)] [_inst_5 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], Not (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align order.not_is_succ_limit_of_no_max Order.not_isSuccLimit_of_noMaxₓ'. -/
theorem not_isSuccLimit_of_noMax [NoMinOrder α] [NoMaxOrder α] : ¬IsSuccLimit a := by simp
#align order.not_is_succ_limit_of_no_max Order.not_isSuccLimit_of_noMax

end IsSuccArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] [SuccOrder α] {a b : α} {C : α → Sort _}

/- warning: order.is_succ_limit_of_succ_ne -> Order.isSuccLimit_of_succ_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, (forall (b : α), Ne.{succ u1} α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) a) -> (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, (forall (b : α), Ne.{succ u1} α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) a) -> (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_of_succ_ne Order.isSuccLimit_of_succ_neₓ'. -/
theorem isSuccLimit_of_succ_ne (h : ∀ b, succ b ≠ a) : IsSuccLimit a := fun b hba => h b hba.succ_eq
#align order.is_succ_limit_of_succ_ne Order.isSuccLimit_of_succ_ne

/- warning: order.not_is_succ_limit_iff -> Order.not_isSuccLimit_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, Iff (Not (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) (Exists.{succ u1} α (fun (b : α) => And (Not (IsMax.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b)) (Eq.{succ u1} α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, Iff (Not (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) (Exists.{succ u1} α (fun (b : α) => And (Not (IsMax.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b)) (Eq.{succ u1} α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) a)))
Case conversion may be inaccurate. Consider using '#align order.not_is_succ_limit_iff Order.not_isSuccLimit_iffₓ'. -/
theorem not_isSuccLimit_iff : ¬IsSuccLimit a ↔ ∃ b, ¬IsMax b ∧ succ b = a :=
  by
  rw [not_is_succ_limit_iff_exists_covby]
  refine' exists_congr fun b => ⟨fun hba => ⟨hba.lt.not_is_max, hba.succ_eq⟩, _⟩
  rintro ⟨h, rfl⟩
  exact covby_succ_of_not_is_max h
#align order.not_is_succ_limit_iff Order.not_isSuccLimit_iff

/- warning: order.mem_range_succ_of_not_is_succ_limit -> Order.mem_range_succ_of_not_isSuccLimit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, (Not (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.range.{u1, succ u1} α α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, (Not (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Set.range.{u1, succ u1} α α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2)))
Case conversion may be inaccurate. Consider using '#align order.mem_range_succ_of_not_is_succ_limit Order.mem_range_succ_of_not_isSuccLimitₓ'. -/
/-- See `not_is_succ_limit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_succ_of_not_isSuccLimit (h : ¬IsSuccLimit a) : a ∈ range (@succ α _ _) := by
  cases' not_is_succ_limit_iff.1 h with b hb; exact ⟨b, hb.2⟩
#align order.mem_range_succ_of_not_is_succ_limit Order.mem_range_succ_of_not_isSuccLimit

/- warning: order.is_succ_limit_of_succ_lt -> Order.isSuccLimit_of_succ_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {b : α}, (forall (a : α), (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) b)) -> (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {b : α}, (forall (a : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) b)) -> (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_of_succ_lt Order.isSuccLimit_of_succ_ltₓ'. -/
theorem isSuccLimit_of_succ_lt (H : ∀ a < b, succ a < b) : IsSuccLimit b := fun a hab =>
  (H a hab.lt).Ne hab.succ_eq
#align order.is_succ_limit_of_succ_lt Order.isSuccLimit_of_succ_lt

/- warning: order.is_succ_limit.succ_lt -> Order.IsSuccLimit.succ_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} {b : α}, (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} {b : α}, (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) b)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit.succ_lt Order.IsSuccLimit.succ_ltₓ'. -/
theorem IsSuccLimit.succ_lt (hb : IsSuccLimit b) (ha : a < b) : succ a < b :=
  by
  by_cases h : IsMax a
  · rwa [h.succ_eq]
  · rw [lt_iff_le_and_ne, succ_le_iff_of_not_is_max h]
    refine' ⟨ha, fun hab => _⟩
    subst hab
    exact (h hb.is_max).elim
#align order.is_succ_limit.succ_lt Order.IsSuccLimit.succ_lt

/- warning: order.is_succ_limit.succ_lt_iff -> Order.IsSuccLimit.succ_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} {b : α}, (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) -> (Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) b) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} {b : α}, (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) -> (Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) b) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit.succ_lt_iff Order.IsSuccLimit.succ_lt_iffₓ'. -/
theorem IsSuccLimit.succ_lt_iff (hb : IsSuccLimit b) : succ a < b ↔ a < b :=
  ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩
#align order.is_succ_limit.succ_lt_iff Order.IsSuccLimit.succ_lt_iff

/- warning: order.is_succ_limit_iff_succ_lt -> Order.isSuccLimit_iff_succ_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {b : α}, Iff (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) (forall (a : α), (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {b : α}, Iff (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b) (forall (a : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) b))
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_iff_succ_lt Order.isSuccLimit_iff_succ_ltₓ'. -/
theorem isSuccLimit_iff_succ_lt : IsSuccLimit b ↔ ∀ a < b, succ a < b :=
  ⟨fun hb a => hb.succ_lt, isSuccLimit_of_succ_lt⟩
#align order.is_succ_limit_iff_succ_lt Order.isSuccLimit_iff_succ_lt

/- warning: order.is_succ_limit_rec_on -> Order.isSuccLimitRecOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {C : α -> Sort.{u2}} (b : α), (forall (a : α), (Not (IsMax.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) -> (forall (a : α), (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) -> (C b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {C : α -> Sort.{u2}} (b : α), (forall (a : α), (Not (IsMax.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) -> (forall (a : α), (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) -> (C b)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_rec_on Order.isSuccLimitRecOnₓ'. -/
/-- A value can be built by building it on successors and successor limits. -/
@[elab_as_elim]
noncomputable def isSuccLimitRecOn (b : α) (hs : ∀ a, ¬IsMax a → C (succ a))
    (hl : ∀ a, IsSuccLimit a → C a) : C b :=
  by
  by_cases hb : is_succ_limit b
  · exact hl b hb
  · have H := Classical.choose_spec (not_is_succ_limit_iff.1 hb)
    rw [← H.2]
    exact hs _ H.1
#align order.is_succ_limit_rec_on Order.isSuccLimitRecOn

/- warning: order.is_succ_limit_rec_on_limit -> Order.isSuccLimitRecOn_limit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {b : α} {C : α -> Sort.{u2}} (hs : forall (a : α), (Not (IsMax.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) (hb : Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b), Eq.{u2} (C b) (Order.isSuccLimitRecOn.{u1, u2} α _inst_1 _inst_2 C b hs hl) (hl b hb)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : SuccOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] {b : α} {C : α -> Sort.{u1}} (hs : forall (a : α), (Not (IsMax.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a)) -> (C (Order.succ.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsSuccLimit.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a) -> (C a)) (hb : Order.IsSuccLimit.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) b), Eq.{u1} (C b) (Order.isSuccLimitRecOn.{u2, u1} α _inst_1 _inst_2 C b hs hl) (hl b hb)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_rec_on_limit Order.isSuccLimitRecOn_limitₓ'. -/
theorem isSuccLimitRecOn_limit (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    (hb : IsSuccLimit b) : @isSuccLimitRecOn α _ _ C b hs hl = hl b hb := by
  classical exact dif_pos hb
#align order.is_succ_limit_rec_on_limit Order.isSuccLimitRecOn_limit

/- warning: order.is_succ_limit_rec_on_succ' -> Order.isSuccLimitRecOn_succ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {C : α -> Sort.{u2}} (hs : forall (a : α), (Not (IsMax.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) {b : α} (hb : Not (IsMax.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b)), Eq.{u2} (C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b)) (Order.isSuccLimitRecOn.{u1, u2} α _inst_1 _inst_2 C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) hs hl) (hs b hb)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : SuccOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] {C : α -> Sort.{u1}} (hs : forall (a : α), (Not (IsMax.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a)) -> (C (Order.succ.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsSuccLimit.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a) -> (C a)) {b : α} (hb : Not (IsMax.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) b)), Eq.{u1} (C (Order.succ.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 b)) (Order.isSuccLimitRecOn.{u2, u1} α _inst_1 _inst_2 C (Order.succ.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 b) hs hl) (hs b hb)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_rec_on_succ' Order.isSuccLimitRecOn_succ'ₓ'. -/
theorem isSuccLimitRecOn_succ' (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    {b : α} (hb : ¬IsMax b) : @isSuccLimitRecOn α _ _ C (succ b) hs hl = hs b hb :=
  by
  have hb' := not_is_succ_limit_succ_of_not_is_max hb
  have H := Classical.choose_spec (not_is_succ_limit_iff.1 hb')
  rw [is_succ_limit_rec_on]
  simp only [cast_eq_iff_heq, hb', not_false_iff, eq_mpr_eq_cast, dif_neg]
  congr
  · exact (succ_eq_succ_iff_of_not_is_max H.1 hb).1 H.2
  · apply proof_irrel_heq
#align order.is_succ_limit_rec_on_succ' Order.isSuccLimitRecOn_succ'

section NoMaxOrder

variable [NoMaxOrder α]

/- warning: order.is_succ_limit_rec_on_succ -> Order.isSuccLimitRecOn_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {C : α -> Sort.{u2}} [_inst_3 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] (hs : forall (a : α), (Not (IsMax.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) (b : α), Eq.{u2} (C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b)) (Order.isSuccLimitRecOn.{u1, u2} α _inst_1 _inst_2 C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) hs hl) (hs b (not_isMax.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 b))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : SuccOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] {C : α -> Sort.{u1}} [_inst_3 : NoMaxOrder.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] (hs : forall (a : α), (Not (IsMax.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a)) -> (C (Order.succ.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsSuccLimit.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a) -> (C a)) (b : α), Eq.{u1} (C (Order.succ.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 b)) (Order.isSuccLimitRecOn.{u2, u1} α _inst_1 _inst_2 C (Order.succ.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 b) hs hl) (hs b (not_isMax.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 b))
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_rec_on_succ Order.isSuccLimitRecOn_succₓ'. -/
@[simp]
theorem isSuccLimitRecOn_succ (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    (b : α) : @isSuccLimitRecOn α _ _ C (succ b) hs hl = hs b (not_isMax b) :=
  isSuccLimitRecOn_succ' _ _ _
#align order.is_succ_limit_rec_on_succ Order.isSuccLimitRecOn_succ

/- warning: order.is_succ_limit_iff_succ_ne -> Order.isSuccLimit_iff_succ_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) (forall (b : α), Ne.{succ u1} α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) (forall (b : α), Ne.{succ u1} α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) a)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_iff_succ_ne Order.isSuccLimit_iff_succ_neₓ'. -/
theorem isSuccLimit_iff_succ_ne : IsSuccLimit a ↔ ∀ b, succ b ≠ a :=
  ⟨IsSuccLimit.succ_ne, isSuccLimit_of_succ_ne⟩
#align order.is_succ_limit_iff_succ_ne Order.isSuccLimit_iff_succ_ne

/- warning: order.not_is_succ_limit_iff' -> Order.not_isSuccLimit_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (Not (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.range.{u1, succ u1} α α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (Not (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Set.range.{u1, succ u1} α α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2)))
Case conversion may be inaccurate. Consider using '#align order.not_is_succ_limit_iff' Order.not_isSuccLimit_iff'ₓ'. -/
theorem not_isSuccLimit_iff' : ¬IsSuccLimit a ↔ a ∈ range (@succ α _ _) := by
  simp_rw [is_succ_limit_iff_succ_ne, not_forall, not_ne_iff]; rfl
#align order.not_is_succ_limit_iff' Order.not_isSuccLimit_iff'

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

/- warning: order.is_succ_limit.is_min -> Order.IsSuccLimit.isMin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : IsSuccArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2], (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (IsMin.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : IsSuccArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2], (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (IsMin.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit.is_min Order.IsSuccLimit.isMinₓ'. -/
protected theorem IsSuccLimit.isMin (h : IsSuccLimit a) : IsMin a := fun b hb =>
  by
  revert h
  refine' Succ.rec (fun _ => le_rfl) (fun c hbc H hc => _) hb
  have := hc.is_max.succ_eq
  rw [this] at hc⊢
  exact H hc
#align order.is_succ_limit.is_min Order.IsSuccLimit.isMin

/- warning: order.is_succ_limit_iff -> Order.isSuccLimit_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : IsSuccArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2], Iff (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) (IsMin.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : IsSuccArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2], Iff (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) (IsMin.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_iff Order.isSuccLimit_iffₓ'. -/
@[simp]
theorem isSuccLimit_iff : IsSuccLimit a ↔ IsMin a :=
  ⟨IsSuccLimit.isMin, IsMin.isSuccLimit⟩
#align order.is_succ_limit_iff Order.isSuccLimit_iff

/- warning: order.not_is_succ_limit -> Order.not_isSuccLimit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : IsSuccArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2] [_inst_4 : NoMinOrder.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Not (Order.IsSuccLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : IsSuccArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2] [_inst_4 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Not (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align order.not_is_succ_limit Order.not_isSuccLimitₓ'. -/
theorem not_isSuccLimit [NoMinOrder α] : ¬IsSuccLimit a := by simp
#align order.not_is_succ_limit Order.not_isSuccLimit

end IsSuccArchimedean

end PartialOrder

/-! ### Predecessor limits -/


section LT

variable [LT α] {a : α}

#print Order.IsPredLimit /-
/-- A predecessor limit is a value that isn't covered by any other.

It's so named because in a predecessor order, a predecessor limit can't be the predecessor of
anything greater. -/
def IsPredLimit (a : α) : Prop :=
  ∀ b, ¬a ⋖ b
#align order.is_pred_limit Order.IsPredLimit
-/

#print Order.not_isPredLimit_iff_exists_covby /-
theorem not_isPredLimit_iff_exists_covby (a : α) : ¬IsPredLimit a ↔ ∃ b, a ⋖ b := by
  simp [is_pred_limit]
#align order.not_is_pred_limit_iff_exists_covby Order.not_isPredLimit_iff_exists_covby
-/

#print Order.isPredLimit_of_dense /-
theorem isPredLimit_of_dense [DenselyOrdered α] (a : α) : IsPredLimit a := fun b => not_covby
#align order.is_pred_limit_of_dense Order.isPredLimit_of_dense
-/

#print Order.isSuccLimit_toDual_iff /-
@[simp]
theorem isSuccLimit_toDual_iff : IsSuccLimit (toDual a) ↔ IsPredLimit a := by
  simp [is_succ_limit, is_pred_limit]
#align order.is_succ_limit_to_dual_iff Order.isSuccLimit_toDual_iff
-/

#print Order.isPredLimit_toDual_iff /-
@[simp]
theorem isPredLimit_toDual_iff : IsPredLimit (toDual a) ↔ IsSuccLimit a := by
  simp [is_succ_limit, is_pred_limit]
#align order.is_pred_limit_to_dual_iff Order.isPredLimit_toDual_iff
-/

alias is_succ_limit_to_dual_iff ↔ _ is_pred_limit.dual
#align order.is_pred_limit.dual Order.isPredLimit.dual

alias is_pred_limit_to_dual_iff ↔ _ is_succ_limit.dual
#align order.is_succ_limit.dual Order.isSuccLimit.dual

end LT

section Preorder

variable [Preorder α] {a : α}

/- warning: is_max.is_pred_limit -> IsMax.isPredLimit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α}, (IsMax.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a) -> (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α}, (IsMax.{u1} α (Preorder.toLE.{u1} α _inst_1) a) -> (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align is_max.is_pred_limit IsMax.isPredLimitₓ'. -/
protected theorem IsMax.isPredLimit : IsMax a → IsPredLimit a := fun h b hab =>
  not_isMax_of_lt hab.lt h
#align is_max.is_pred_limit IsMax.isPredLimit

/- warning: order.is_pred_limit_top -> Order.isPredLimit_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α _inst_1)], Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α _inst_1) _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)], Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit_top Order.isPredLimit_topₓ'. -/
theorem isPredLimit_top [OrderTop α] : IsPredLimit (⊤ : α) :=
  isMax_top.IsPredLimit
#align order.is_pred_limit_top Order.isPredLimit_top

variable [PredOrder α]

/- warning: order.is_pred_limit.is_min -> Order.IsPredLimit.isMin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : PredOrder.{u1} α _inst_1], (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) (Order.pred.{u1} α _inst_1 _inst_2 a)) -> (IsMin.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : PredOrder.{u1} α _inst_1], (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) (Order.pred.{u1} α _inst_1 _inst_2 a)) -> (IsMin.{u1} α (Preorder.toLE.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit.is_min Order.IsPredLimit.isMinₓ'. -/
protected theorem IsPredLimit.isMin (h : IsPredLimit (pred a)) : IsMin a := by by_contra H;
  exact h a (pred_covby_of_not_is_min H)
#align order.is_pred_limit.is_min Order.IsPredLimit.isMin

/- warning: order.not_is_pred_limit_pred_of_not_is_min -> Order.not_isPredLimit_pred_of_not_isMin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : PredOrder.{u1} α _inst_1], (Not (IsMin.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a)) -> (Not (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) (Order.pred.{u1} α _inst_1 _inst_2 a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : PredOrder.{u1} α _inst_1], (Not (IsMin.{u1} α (Preorder.toLE.{u1} α _inst_1) a)) -> (Not (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) (Order.pred.{u1} α _inst_1 _inst_2 a)))
Case conversion may be inaccurate. Consider using '#align order.not_is_pred_limit_pred_of_not_is_min Order.not_isPredLimit_pred_of_not_isMinₓ'. -/
theorem not_isPredLimit_pred_of_not_isMin (ha : ¬IsMin a) : ¬IsPredLimit (pred a) := by
  contrapose! ha; exact ha.is_min
#align order.not_is_pred_limit_pred_of_not_is_min Order.not_isPredLimit_pred_of_not_isMin

section NoMinOrder

variable [NoMinOrder α]

/- warning: order.is_pred_limit.pred_ne -> Order.IsPredLimit.pred_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : PredOrder.{u1} α _inst_1] [_inst_3 : NoMinOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)], (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a) -> (forall (b : α), Ne.{succ u1} α (Order.pred.{u1} α _inst_1 _inst_2 b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : PredOrder.{u1} α _inst_1] [_inst_3 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) a) -> (forall (b : α), Ne.{succ u1} α (Order.pred.{u1} α _inst_1 _inst_2 b) a)
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit.pred_ne Order.IsPredLimit.pred_neₓ'. -/
theorem IsPredLimit.pred_ne (h : IsPredLimit a) (b : α) : pred b ≠ a := by rintro rfl;
  exact not_isMin _ h.is_min
#align order.is_pred_limit.pred_ne Order.IsPredLimit.pred_ne

/- warning: order.not_is_pred_limit_pred -> Order.not_isPredLimit_pred is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : PredOrder.{u1} α _inst_1] [_inst_3 : NoMinOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] (a : α), Not (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) (Order.pred.{u1} α _inst_1 _inst_2 a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : PredOrder.{u1} α _inst_1] [_inst_3 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)] (a : α), Not (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) (Order.pred.{u1} α _inst_1 _inst_2 a))
Case conversion may be inaccurate. Consider using '#align order.not_is_pred_limit_pred Order.not_isPredLimit_predₓ'. -/
@[simp]
theorem not_isPredLimit_pred (a : α) : ¬IsPredLimit (pred a) := fun h => h.pred_ne _ rfl
#align order.not_is_pred_limit_pred Order.not_isPredLimit_pred

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

/- warning: order.is_pred_limit.is_max_of_no_min -> Order.IsPredLimit.isMax_of_noMin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : PredOrder.{u1} α _inst_1] [_inst_3 : IsPredArchimedean.{u1} α _inst_1 _inst_2] [_inst_4 : NoMinOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)], (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a) -> (IsMax.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : PredOrder.{u1} α _inst_1] [_inst_3 : IsPredArchimedean.{u1} α _inst_1 _inst_2] [_inst_4 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) a) -> (IsMax.{u1} α (Preorder.toLE.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit.is_max_of_no_min Order.IsPredLimit.isMax_of_noMinₓ'. -/
protected theorem IsPredLimit.isMax_of_noMin [NoMinOrder α] (h : IsPredLimit a) : IsMax a :=
  h.dual.isMin_of_noMax
#align order.is_pred_limit.is_max_of_no_min Order.IsPredLimit.isMax_of_noMin

/- warning: order.is_pred_limit_iff_of_no_min -> Order.isPredLimit_iff_of_noMin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : PredOrder.{u1} α _inst_1] [_inst_3 : IsPredArchimedean.{u1} α _inst_1 _inst_2] [_inst_4 : NoMinOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)], Iff (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a) (IsMax.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : PredOrder.{u1} α _inst_1] [_inst_3 : IsPredArchimedean.{u1} α _inst_1 _inst_2] [_inst_4 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], Iff (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) a) (IsMax.{u1} α (Preorder.toLE.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit_iff_of_no_min Order.isPredLimit_iff_of_noMinₓ'. -/
@[simp]
theorem isPredLimit_iff_of_noMin [NoMinOrder α] : IsPredLimit a ↔ IsMax a :=
  isSuccLimit_toDual_iff.symm.trans isSuccLimit_iff_of_noMax
#align order.is_pred_limit_iff_of_no_min Order.isPredLimit_iff_of_noMin

/- warning: order.not_is_pred_limit_of_no_min -> Order.not_isPredLimit_of_noMin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : PredOrder.{u1} α _inst_1] [_inst_3 : IsPredArchimedean.{u1} α _inst_1 _inst_2] [_inst_4 : NoMinOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] [_inst_5 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)], Not (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : PredOrder.{u1} α _inst_1] [_inst_3 : IsPredArchimedean.{u1} α _inst_1 _inst_2] [_inst_4 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)] [_inst_5 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], Not (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align order.not_is_pred_limit_of_no_min Order.not_isPredLimit_of_noMinₓ'. -/
theorem not_isPredLimit_of_noMin [NoMinOrder α] [NoMaxOrder α] : ¬IsPredLimit a := by simp
#align order.not_is_pred_limit_of_no_min Order.not_isPredLimit_of_noMin

end IsPredArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] [PredOrder α] {a b : α} {C : α → Sort _}

/- warning: order.is_pred_limit_of_pred_ne -> Order.isPredLimit_of_pred_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, (forall (b : α), Ne.{succ u1} α (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) a) -> (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, (forall (b : α), Ne.{succ u1} α (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) a) -> (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit_of_pred_ne Order.isPredLimit_of_pred_neₓ'. -/
theorem isPredLimit_of_pred_ne (h : ∀ b, pred b ≠ a) : IsPredLimit a := fun b hba => h b hba.pred_eq
#align order.is_pred_limit_of_pred_ne Order.isPredLimit_of_pred_ne

/- warning: order.not_is_pred_limit_iff -> Order.not_isPredLimit_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, Iff (Not (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) (Exists.{succ u1} α (fun (b : α) => And (Not (IsMin.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b)) (Eq.{succ u1} α (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, Iff (Not (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) (Exists.{succ u1} α (fun (b : α) => And (Not (IsMin.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b)) (Eq.{succ u1} α (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) a)))
Case conversion may be inaccurate. Consider using '#align order.not_is_pred_limit_iff Order.not_isPredLimit_iffₓ'. -/
theorem not_isPredLimit_iff : ¬IsPredLimit a ↔ ∃ b, ¬IsMin b ∧ pred b = a := by
  rw [← is_succ_limit_to_dual_iff]; exact not_is_succ_limit_iff
#align order.not_is_pred_limit_iff Order.not_isPredLimit_iff

/- warning: order.mem_range_pred_of_not_is_pred_limit -> Order.mem_range_pred_of_not_isPredLimit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, (Not (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.range.{u1, succ u1} α α (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, (Not (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Set.range.{u1, succ u1} α α (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2)))
Case conversion may be inaccurate. Consider using '#align order.mem_range_pred_of_not_is_pred_limit Order.mem_range_pred_of_not_isPredLimitₓ'. -/
/-- See `not_is_pred_limit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_pred_of_not_isPredLimit (h : ¬IsPredLimit a) : a ∈ range (@pred α _ _) := by
  cases' not_is_pred_limit_iff.1 h with b hb; exact ⟨b, hb.2⟩
#align order.mem_range_pred_of_not_is_pred_limit Order.mem_range_pred_of_not_isPredLimit

/- warning: order.is_pred_limit_of_pred_lt -> Order.isPredLimit_of_pred_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {b : α}, (forall (a : α), (GT.gt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) b)) -> (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {b : α}, (forall (a : α), (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) b)) -> (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b)
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit_of_pred_lt Order.isPredLimit_of_pred_ltₓ'. -/
theorem isPredLimit_of_pred_lt (H : ∀ a > b, pred a < b) : IsPredLimit b := fun a hab =>
  (H a hab.lt).Ne hab.pred_eq
#align order.is_pred_limit_of_pred_lt Order.isPredLimit_of_pred_lt

/- warning: order.is_pred_limit.lt_pred -> Order.IsPredLimit.lt_pred is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} {b : α}, (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} {b : α}, (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b))
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit.lt_pred Order.IsPredLimit.lt_predₓ'. -/
theorem IsPredLimit.lt_pred (h : IsPredLimit a) : a < b → a < pred b :=
  h.dual.succ_lt
#align order.is_pred_limit.lt_pred Order.IsPredLimit.lt_pred

/- warning: order.is_pred_limit.lt_pred_iff -> Order.IsPredLimit.lt_pred_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} {b : α}, (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} {b : α}, (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit.lt_pred_iff Order.IsPredLimit.lt_pred_iffₓ'. -/
theorem IsPredLimit.lt_pred_iff (h : IsPredLimit a) : a < pred b ↔ a < b :=
  h.dual.succ_lt_iff
#align order.is_pred_limit.lt_pred_iff Order.IsPredLimit.lt_pred_iff

/- warning: order.is_pred_limit_iff_lt_pred -> Order.isPredLimit_iff_lt_pred is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, Iff (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) (forall {{b : α}}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α}, Iff (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) (forall {{b : α}}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b)))
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit_iff_lt_pred Order.isPredLimit_iff_lt_predₓ'. -/
theorem isPredLimit_iff_lt_pred : IsPredLimit a ↔ ∀ ⦃b⦄, a < b → a < pred b :=
  isSuccLimit_toDual_iff.symm.trans isSuccLimit_iff_succ_lt
#align order.is_pred_limit_iff_lt_pred Order.isPredLimit_iff_lt_pred

/- warning: order.is_pred_limit_rec_on -> Order.isPredLimitRecOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {C : α -> Sort.{u2}} (b : α), (forall (a : α), (Not (IsMin.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) -> (forall (a : α), (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) -> (C b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {C : α -> Sort.{u2}} (b : α), (forall (a : α), (Not (IsMin.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) -> (forall (a : α), (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) -> (C b)
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit_rec_on Order.isPredLimitRecOnₓ'. -/
/-- A value can be built by building it on predecessors and predecessor limits. -/
@[elab_as_elim]
noncomputable def isPredLimitRecOn (b : α) (hs : ∀ a, ¬IsMin a → C (pred a))
    (hl : ∀ a, IsPredLimit a → C a) : C b :=
  @isSuccLimitRecOn αᵒᵈ _ _ _ _ hs fun a ha => hl _ ha.dual
#align order.is_pred_limit_rec_on Order.isPredLimitRecOn

/- warning: order.is_pred_limit_rec_on_limit -> Order.isPredLimitRecOn_limit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {b : α} {C : α -> Sort.{u2}} (hs : forall (a : α), (Not (IsMin.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) (hb : Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b), Eq.{u2} (C b) (Order.isPredLimitRecOn.{u1, u2} α _inst_1 _inst_2 C b hs hl) (hl b hb)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PredOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] {b : α} {C : α -> Sort.{u1}} (hs : forall (a : α), (Not (IsMin.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a)) -> (C (Order.pred.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsPredLimit.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a) -> (C a)) (hb : Order.IsPredLimit.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) b), Eq.{u1} (C b) (Order.isPredLimitRecOn.{u2, u1} α _inst_1 _inst_2 C b hs hl) (hl b hb)
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit_rec_on_limit Order.isPredLimitRecOn_limitₓ'. -/
theorem isPredLimitRecOn_limit (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a)
    (hb : IsPredLimit b) : @isPredLimitRecOn α _ _ C b hs hl = hl b hb :=
  isSuccLimitRecOn_limit _ _ hb.dual
#align order.is_pred_limit_rec_on_limit Order.isPredLimitRecOn_limit

/- warning: order.is_pred_limit_rec_on_pred' -> Order.isPredLimitRecOn_pred' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {C : α -> Sort.{u2}} (hs : forall (a : α), (Not (IsMin.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) {b : α} (hb : Not (IsMin.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b)), Eq.{u2} (C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b)) (Order.isPredLimitRecOn.{u1, u2} α _inst_1 _inst_2 C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) hs hl) (hs b hb)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PredOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] {C : α -> Sort.{u1}} (hs : forall (a : α), (Not (IsMin.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a)) -> (C (Order.pred.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsPredLimit.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a) -> (C a)) {b : α} (hb : Not (IsMin.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) b)), Eq.{u1} (C (Order.pred.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 b)) (Order.isPredLimitRecOn.{u2, u1} α _inst_1 _inst_2 C (Order.pred.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 b) hs hl) (hs b hb)
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit_rec_on_pred' Order.isPredLimitRecOn_pred'ₓ'. -/
theorem isPredLimitRecOn_pred' (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a)
    {b : α} (hb : ¬IsMin b) : @isPredLimitRecOn α _ _ C (pred b) hs hl = hs b hb :=
  isSuccLimitRecOn_succ' _ _ _
#align order.is_pred_limit_rec_on_pred' Order.isPredLimitRecOn_pred'

section NoMinOrder

variable [NoMinOrder α]

/- warning: order.is_pred_limit_rec_on_pred -> Order.isPredLimitRecOn_pred is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {C : α -> Sort.{u2}} [_inst_3 : NoMinOrder.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] (hs : forall (a : α), (Not (IsMin.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) (b : α), Eq.{u2} (C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b)) (Order.isPredLimitRecOn.{u1, u2} α _inst_1 _inst_2 C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) hs hl) (hs b (not_isMin.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 b))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PredOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] {C : α -> Sort.{u1}} [_inst_3 : NoMinOrder.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] (hs : forall (a : α), (Not (IsMin.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a)) -> (C (Order.pred.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsPredLimit.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a) -> (C a)) (b : α), Eq.{u1} (C (Order.pred.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 b)) (Order.isPredLimitRecOn.{u2, u1} α _inst_1 _inst_2 C (Order.pred.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 b) hs hl) (hs b (not_isMin.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 b))
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit_rec_on_pred Order.isPredLimitRecOn_predₓ'. -/
@[simp]
theorem isPredLimitRecOn_pred (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a)
    (b : α) : @isPredLimitRecOn α _ _ C (pred b) hs hl = hs b (not_isMin b) :=
  isSuccLimitRecOn_succ _ _ _
#align order.is_pred_limit_rec_on_pred Order.isPredLimitRecOn_pred

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

/- warning: order.is_pred_limit.is_max -> Order.IsPredLimit.isMax is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : IsPredArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2], (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (IsMax.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : IsPredArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2], (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (IsMax.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit.is_max Order.IsPredLimit.isMaxₓ'. -/
protected theorem IsPredLimit.isMax (h : IsPredLimit a) : IsMax a :=
  h.dual.IsMin
#align order.is_pred_limit.is_max Order.IsPredLimit.isMax

/- warning: order.is_pred_limit_iff -> Order.isPredLimit_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : IsPredArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2], Iff (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) (IsMax.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : IsPredArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2], Iff (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) (IsMax.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit_iff Order.isPredLimit_iffₓ'. -/
@[simp]
theorem isPredLimit_iff : IsPredLimit a ↔ IsMax a :=
  isSuccLimit_toDual_iff.symm.trans isSuccLimit_iff
#align order.is_pred_limit_iff Order.isPredLimit_iff

/- warning: order.not_is_pred_limit -> Order.not_isPredLimit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : IsPredArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2] [_inst_4 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Not (Order.IsPredLimit.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : IsPredArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2] [_inst_4 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Not (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align order.not_is_pred_limit Order.not_isPredLimitₓ'. -/
theorem not_isPredLimit [NoMaxOrder α] : ¬IsPredLimit a := by simp
#align order.not_is_pred_limit Order.not_isPredLimit

end IsPredArchimedean

end PartialOrder

end Order

