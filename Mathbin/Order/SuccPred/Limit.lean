/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios

! This file was ported from Lean 3 source module order.succ_pred.limit
! leanprover-community/mathlib commit 44b58b42794e5abe2bf86397c38e26b587e07e59
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.SuccPred.Basic

/-!
# Successor and predecessor limits

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

#print Order.IsMin.isSuccLimit /-
protected theorem Order.IsMin.isSuccLimit : IsMin a → IsSuccLimit a := fun h b hab =>
  not_isMin_of_lt hab.lt h
#align is_min.is_succ_limit Order.IsMin.isSuccLimit
-/

/- warning: order.is_succ_limit_bot -> Order.isSuccLimit_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)], Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)], Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_bot Order.isSuccLimit_botₓ'. -/
theorem isSuccLimit_bot [OrderBot α] : IsSuccLimit (⊥ : α) :=
  isMin_bot.IsSuccLimit
#align order.is_succ_limit_bot Order.isSuccLimit_bot

variable [SuccOrder α]

#print Order.IsSuccLimit.isMax /-
protected theorem IsSuccLimit.isMax (h : IsSuccLimit (succ a)) : IsMax a :=
  by
  by_contra H
  exact h a (covby_succ_of_not_is_max H)
#align order.is_succ_limit.is_max Order.IsSuccLimit.isMax
-/

#print Order.not_isSuccLimit_succ_of_not_isMax /-
theorem not_isSuccLimit_succ_of_not_isMax (ha : ¬IsMax a) : ¬IsSuccLimit (succ a) :=
  by
  contrapose! ha
  exact ha.is_max
#align order.not_is_succ_limit_succ_of_not_is_max Order.not_isSuccLimit_succ_of_not_isMax
-/

section NoMaxOrder

variable [NoMaxOrder α]

#print Order.IsSuccLimit.succ_ne /-
theorem IsSuccLimit.succ_ne (h : IsSuccLimit a) (b : α) : succ b ≠ a :=
  by
  rintro rfl
  exact not_isMax _ h.is_max
#align order.is_succ_limit.succ_ne Order.IsSuccLimit.succ_ne
-/

#print Order.not_isSuccLimit_succ /-
@[simp]
theorem not_isSuccLimit_succ (a : α) : ¬IsSuccLimit (succ a) := fun h => h.succ_ne _ rfl
#align order.not_is_succ_limit_succ Order.not_isSuccLimit_succ
-/

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

#print Order.IsSuccLimit.isMin_of_noMax /-
theorem IsSuccLimit.isMin_of_noMax [NoMaxOrder α] (h : IsSuccLimit a) : IsMin a := fun b hb =>
  by
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩
  · exact le_rfl
  · rw [iterate_succ_apply'] at h
    exact (not_is_succ_limit_succ _ h).elim
#align order.is_succ_limit.is_min_of_no_max Order.IsSuccLimit.isMin_of_noMax
-/

#print Order.isSuccLimit_iff_of_noMax /-
@[simp]
theorem isSuccLimit_iff_of_noMax [NoMaxOrder α] : IsSuccLimit a ↔ IsMin a :=
  ⟨IsSuccLimit.isMin_of_noMax, Order.IsMin.isSuccLimit⟩
#align order.is_succ_limit_iff_of_no_max Order.isSuccLimit_iff_of_noMax
-/

#print Order.not_isSuccLimit_of_noMax /-
theorem not_isSuccLimit_of_noMax [NoMinOrder α] [NoMaxOrder α] : ¬IsSuccLimit a := by simp
#align order.not_is_succ_limit_of_no_max Order.not_isSuccLimit_of_noMax
-/

end IsSuccArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] [SuccOrder α] {a b : α} {C : α → Sort _}

#print Order.isSuccLimit_of_succ_ne /-
theorem isSuccLimit_of_succ_ne (h : ∀ b, succ b ≠ a) : IsSuccLimit a := fun b hba => h b hba.succ_eq
#align order.is_succ_limit_of_succ_ne Order.isSuccLimit_of_succ_ne
-/

#print Order.not_isSuccLimit_iff /-
theorem not_isSuccLimit_iff : ¬IsSuccLimit a ↔ ∃ b, ¬IsMax b ∧ succ b = a :=
  by
  rw [not_is_succ_limit_iff_exists_covby]
  refine' exists_congr fun b => ⟨fun hba => ⟨hba.lt.not_is_max, hba.succ_eq⟩, _⟩
  rintro ⟨h, rfl⟩
  exact covby_succ_of_not_is_max h
#align order.not_is_succ_limit_iff Order.not_isSuccLimit_iff
-/

#print Order.mem_range_succ_of_not_isSuccLimit /-
/-- See `not_is_succ_limit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_succ_of_not_isSuccLimit (h : ¬IsSuccLimit a) : a ∈ range (@succ α _ _) :=
  by
  cases' not_is_succ_limit_iff.1 h with b hb
  exact ⟨b, hb.2⟩
#align order.mem_range_succ_of_not_is_succ_limit Order.mem_range_succ_of_not_isSuccLimit
-/

#print Order.isSuccLimit_of_succ_lt /-
theorem isSuccLimit_of_succ_lt (H : ∀ a < b, succ a < b) : IsSuccLimit b := fun a hab =>
  (H a hab.lt).Ne hab.succ_eq
#align order.is_succ_limit_of_succ_lt Order.isSuccLimit_of_succ_lt
-/

#print Order.IsSuccLimit.succ_lt /-
theorem IsSuccLimit.succ_lt (hb : IsSuccLimit b) (ha : a < b) : succ a < b :=
  by
  by_cases h : IsMax a
  · rwa [h.succ_eq]
  · rw [lt_iff_le_and_ne, succ_le_iff_of_not_is_max h]
    refine' ⟨ha, fun hab => _⟩
    subst hab
    exact (h hb.is_max).elim
#align order.is_succ_limit.succ_lt Order.IsSuccLimit.succ_lt
-/

#print Order.IsSuccLimit.succ_lt_iff /-
theorem IsSuccLimit.succ_lt_iff (hb : IsSuccLimit b) : succ a < b ↔ a < b :=
  ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩
#align order.is_succ_limit.succ_lt_iff Order.IsSuccLimit.succ_lt_iff
-/

#print Order.isSuccLimit_iff_succ_lt /-
theorem isSuccLimit_iff_succ_lt : IsSuccLimit b ↔ ∀ a < b, succ a < b :=
  ⟨fun hb a => hb.succ_lt, isSuccLimit_of_succ_lt⟩
#align order.is_succ_limit_iff_succ_lt Order.isSuccLimit_iff_succ_lt
-/

#print Order.isSuccLimitRecOn /-
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
-/

/- warning: order.is_succ_limit_rec_on_limit -> Order.isSuccLimitRecOn_limit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {b : α} {C : α -> Sort.{u2}} (hs : forall (a : α), (Not (IsMax.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) (hb : Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b), Eq.{u2} (C b) (Order.isSuccLimitRecOn.{u1, u2} α _inst_1 _inst_2 C b hs hl) (hl b hb)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : SuccOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] {b : α} {C : α -> Sort.{u1}} (hs : forall (a : α), (Not (IsMax.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a)) -> (C (Order.succ.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsSuccLimit.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a) -> (C a)) (hb : Order.IsSuccLimit.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) b), Eq.{u1} (C b) (Order.isSuccLimitRecOn.{u2, u1} α _inst_1 _inst_2 C b hs hl) (hl b hb)
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_rec_on_limit Order.isSuccLimitRecOn_limitₓ'. -/
theorem isSuccLimitRecOn_limit (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    (hb : IsSuccLimit b) : @isSuccLimitRecOn α _ _ C b hs hl = hl b hb := by
  classical exact dif_pos hb
#align order.is_succ_limit_rec_on_limit Order.isSuccLimitRecOn_limit

/- warning: order.is_succ_limit_rec_on_succ' -> Order.isSuccLimitRecOn_succ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {C : α -> Sort.{u2}} (hs : forall (a : α), (Not (IsMax.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) {b : α} (hb : Not (IsMax.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b)), Eq.{u2} (C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b)) (Order.isSuccLimitRecOn.{u1, u2} α _inst_1 _inst_2 C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) hs hl) (hs b hb)
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
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {C : α -> Sort.{u2}} [_inst_3 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] (hs : forall (a : α), (Not (IsMax.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsSuccLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) (b : α), Eq.{u2} (C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b)) (Order.isSuccLimitRecOn.{u1, u2} α _inst_1 _inst_2 C (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) hs hl) (hs b (not_isMax.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 b))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : SuccOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] {C : α -> Sort.{u1}} [_inst_3 : NoMaxOrder.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] (hs : forall (a : α), (Not (IsMax.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a)) -> (C (Order.succ.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsSuccLimit.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a) -> (C a)) (b : α), Eq.{u1} (C (Order.succ.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 b)) (Order.isSuccLimitRecOn.{u2, u1} α _inst_1 _inst_2 C (Order.succ.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 b) hs hl) (hs b (not_isMax.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 b))
Case conversion may be inaccurate. Consider using '#align order.is_succ_limit_rec_on_succ Order.isSuccLimitRecOn_succₓ'. -/
@[simp]
theorem isSuccLimitRecOn_succ (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    (b : α) : @isSuccLimitRecOn α _ _ C (succ b) hs hl = hs b (not_isMax b) :=
  isSuccLimitRecOn_succ' _ _ _
#align order.is_succ_limit_rec_on_succ Order.isSuccLimitRecOn_succ

#print Order.isSuccLimit_iff_succ_ne /-
theorem isSuccLimit_iff_succ_ne : IsSuccLimit a ↔ ∀ b, succ b ≠ a :=
  ⟨IsSuccLimit.succ_ne, isSuccLimit_of_succ_ne⟩
#align order.is_succ_limit_iff_succ_ne Order.isSuccLimit_iff_succ_ne
-/

#print Order.not_isSuccLimit_iff' /-
theorem not_isSuccLimit_iff' : ¬IsSuccLimit a ↔ a ∈ range (@succ α _ _) :=
  by
  simp_rw [is_succ_limit_iff_succ_ne, not_forall, not_ne_iff]
  rfl
#align order.not_is_succ_limit_iff' Order.not_isSuccLimit_iff'
-/

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

#print Order.IsSuccLimit.isMin /-
protected theorem IsSuccLimit.isMin (h : IsSuccLimit a) : IsMin a := fun b hb =>
  by
  revert h
  refine' Succ.rec (fun _ => le_rfl) (fun c hbc H hc => _) hb
  have := hc.is_max.succ_eq
  rw [this] at hc⊢
  exact H hc
#align order.is_succ_limit.is_min Order.IsSuccLimit.isMin
-/

#print Order.isSuccLimit_iff /-
@[simp]
theorem isSuccLimit_iff : IsSuccLimit a ↔ IsMin a :=
  ⟨IsSuccLimit.isMin, Order.IsMin.isSuccLimit⟩
#align order.is_succ_limit_iff Order.isSuccLimit_iff
-/

#print Order.not_isSuccLimit /-
theorem not_isSuccLimit [NoMinOrder α] : ¬IsSuccLimit a := by simp
#align order.not_is_succ_limit Order.not_isSuccLimit
-/

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

alias is_pred_limit_to_dual_iff ↔ _ is_succ_limit.dual

end LT

section Preorder

variable [Preorder α] {a : α}

#print Order.IsMax.isPredLimit /-
protected theorem Order.IsMax.isPredLimit : IsMax a → IsPredLimit a := fun h b hab =>
  not_isMax_of_lt hab.lt h
#align is_max.is_pred_limit Order.IsMax.isPredLimit
-/

/- warning: order.is_pred_limit_top -> Order.isPredLimit_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)], Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)], Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α _inst_1) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit_top Order.isPredLimit_topₓ'. -/
theorem isPredLimit_top [OrderTop α] : IsPredLimit (⊤ : α) :=
  isMax_top.IsPredLimit
#align order.is_pred_limit_top Order.isPredLimit_top

variable [PredOrder α]

protected theorem IsPredLimit.is_min (h : IsPredLimit (pred a)) : IsMin a :=
  by
  by_contra H
  exact h a (pred_covby_of_not_is_min H)
#align order.is_pred_limit.is_min Order.IsPredLimit.is_min

#print Order.not_isPredLimit_pred_of_not_isMin /-
theorem not_isPredLimit_pred_of_not_isMin (ha : ¬IsMin a) : ¬IsPredLimit (pred a) :=
  by
  contrapose! ha
  exact ha.is_min
#align order.not_is_pred_limit_pred_of_not_is_min Order.not_isPredLimit_pred_of_not_isMin
-/

section NoMinOrder

variable [NoMinOrder α]

#print Order.IsPredLimit.pred_ne /-
theorem IsPredLimit.pred_ne (h : IsPredLimit a) (b : α) : pred b ≠ a :=
  by
  rintro rfl
  exact not_isMin _ h.is_min
#align order.is_pred_limit.pred_ne Order.IsPredLimit.pred_ne
-/

#print Order.not_isPredLimit_pred /-
@[simp]
theorem not_isPredLimit_pred (a : α) : ¬IsPredLimit (pred a) := fun h => h.pred_ne _ rfl
#align order.not_is_pred_limit_pred Order.not_isPredLimit_pred
-/

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

#print Order.IsPredLimit.isMax_of_noMin /-
protected theorem IsPredLimit.isMax_of_noMin [NoMinOrder α] (h : IsPredLimit a) : IsMax a :=
  h.dual.is_min_of_no_max
#align order.is_pred_limit.is_max_of_no_min Order.IsPredLimit.isMax_of_noMin
-/

#print Order.isPredLimit_iff_of_noMin /-
@[simp]
theorem isPredLimit_iff_of_noMin [NoMinOrder α] : IsPredLimit a ↔ IsMax a :=
  isSuccLimit_toDual_iff.symm.trans isSuccLimit_iff_of_noMax
#align order.is_pred_limit_iff_of_no_min Order.isPredLimit_iff_of_noMin
-/

#print Order.not_isPredLimit_of_noMin /-
theorem not_isPredLimit_of_noMin [NoMinOrder α] [NoMaxOrder α] : ¬IsPredLimit a := by simp
#align order.not_is_pred_limit_of_no_min Order.not_isPredLimit_of_noMin
-/

end IsPredArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] [PredOrder α] {a b : α} {C : α → Sort _}

#print Order.isPredLimit_of_pred_ne /-
theorem isPredLimit_of_pred_ne (h : ∀ b, pred b ≠ a) : IsPredLimit a := fun b hba => h b hba.pred_eq
#align order.is_pred_limit_of_pred_ne Order.isPredLimit_of_pred_ne
-/

#print Order.not_isPredLimit_iff /-
theorem not_isPredLimit_iff : ¬IsPredLimit a ↔ ∃ b, ¬IsMin b ∧ pred b = a :=
  by
  rw [← is_succ_limit_to_dual_iff]
  exact not_is_succ_limit_iff
#align order.not_is_pred_limit_iff Order.not_isPredLimit_iff
-/

#print Order.mem_range_pred_of_not_isPredLimit /-
/-- See `not_is_pred_limit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_pred_of_not_isPredLimit (h : ¬IsPredLimit a) : a ∈ range (@pred α _ _) :=
  by
  cases' not_is_pred_limit_iff.1 h with b hb
  exact ⟨b, hb.2⟩
#align order.mem_range_pred_of_not_is_pred_limit Order.mem_range_pred_of_not_isPredLimit
-/

#print Order.isPredLimit_of_pred_lt /-
theorem isPredLimit_of_pred_lt (H : ∀ a > b, pred a < b) : IsPredLimit b := fun a hab =>
  (H a hab.lt).Ne hab.pred_eq
#align order.is_pred_limit_of_pred_lt Order.isPredLimit_of_pred_lt
-/

/- warning: order.is_pred_limit.lt_pred clashes with order.isPredLimit.lt_pred -> Order.IsPredLimit.lt_pred
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit.lt_pred Order.IsPredLimit.lt_predₓ'. -/
#print Order.IsPredLimit.lt_pred /-
theorem IsPredLimit.lt_pred (h : IsPredLimit a) : a < b → a < pred b :=
  h.dual.succ_lt
#align order.is_pred_limit.lt_pred Order.IsPredLimit.lt_pred
-/

#print Order.IsPredLimit.lt_pred_iff /-
theorem IsPredLimit.lt_pred_iff (h : IsPredLimit a) : a < pred b ↔ a < b :=
  h.dual.succ_lt_iff
#align order.is_pred_limit.lt_pred_iff Order.IsPredLimit.lt_pred_iff
-/

#print Order.isPredLimit_iff_lt_pred /-
theorem isPredLimit_iff_lt_pred : IsPredLimit a ↔ ∀ ⦃b⦄, a < b → a < pred b :=
  isSuccLimit_toDual_iff.symm.trans isSuccLimit_iff_succ_lt
#align order.is_pred_limit_iff_lt_pred Order.isPredLimit_iff_lt_pred
-/

#print Order.isPredLimitRecOn /-
/-- A value can be built by building it on predecessors and predecessor limits. -/
@[elab_as_elim]
noncomputable def isPredLimitRecOn (b : α) (hs : ∀ a, ¬IsMin a → C (pred a))
    (hl : ∀ a, IsPredLimit a → C a) : C b :=
  @isSuccLimitRecOn αᵒᵈ _ _ _ _ hs fun a ha => hl _ ha.dual
#align order.is_pred_limit_rec_on Order.isPredLimitRecOn
-/

/- warning: order.is_pred_limit_rec_on_limit -> Order.isPredLimitRecOn_limit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {b : α} {C : α -> Sort.{u2}} (hs : forall (a : α), (Not (IsMin.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) (hb : Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b), Eq.{u2} (C b) (Order.isPredLimitRecOn.{u1, u2} α _inst_1 _inst_2 C b hs hl) (hl b hb)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PredOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] {b : α} {C : α -> Sort.{u1}} (hs : forall (a : α), (Not (IsMin.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a)) -> (C (Order.pred.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsPredLimit.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) a) -> (C a)) (hb : Order.IsPredLimit.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) b), Eq.{u1} (C b) (Order.isPredLimitRecOn.{u2, u1} α _inst_1 _inst_2 C b hs hl) (hl b hb)
Case conversion may be inaccurate. Consider using '#align order.is_pred_limit_rec_on_limit Order.isPredLimitRecOn_limitₓ'. -/
theorem isPredLimitRecOn_limit (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a)
    (hb : IsPredLimit b) : @isPredLimitRecOn α _ _ C b hs hl = hl b hb :=
  isSuccLimitRecOn_limit _ _ hb.dual
#align order.is_pred_limit_rec_on_limit Order.isPredLimitRecOn_limit

/- warning: order.is_pred_limit_rec_on_pred' -> Order.isPredLimitRecOn_pred' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {C : α -> Sort.{u2}} (hs : forall (a : α), (Not (IsMin.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) {b : α} (hb : Not (IsMin.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) b)), Eq.{u2} (C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b)) (Order.isPredLimitRecOn.{u1, u2} α _inst_1 _inst_2 C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) hs hl) (hs b hb)
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
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {C : α -> Sort.{u2}} [_inst_3 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] (hs : forall (a : α), (Not (IsMin.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a)) -> (C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a))) (hl : forall (a : α), (Order.IsPredLimit.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a) -> (C a)) (b : α), Eq.{u2} (C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b)) (Order.isPredLimitRecOn.{u1, u2} α _inst_1 _inst_2 C (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 b) hs hl) (hs b (not_isMin.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 b))
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

protected theorem IsPredLimit.is_max (h : IsPredLimit a) : IsMax a :=
  h.dual.IsMin
#align order.is_pred_limit.is_max Order.IsPredLimit.is_max

#print Order.isPredLimit_iff /-
@[simp]
theorem isPredLimit_iff : IsPredLimit a ↔ IsMax a :=
  isSuccLimit_toDual_iff.symm.trans isSuccLimit_iff
#align order.is_pred_limit_iff Order.isPredLimit_iff
-/

#print Order.not_isPredLimit /-
theorem not_isPredLimit [NoMaxOrder α] : ¬IsPredLimit a := by simp
#align order.not_is_pred_limit Order.not_isPredLimit
-/

end IsPredArchimedean

end PartialOrder

end Order

