/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov, Yaël Dillies

! This file was ported from Lean 3 source module order.max
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Synonym

/-!
# Minimal/maximal and bottom/top elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines predicates for elements to be minimal/maximal or bottom/top and typeclasses
saying that there are no such elements.

## Predicates

* `is_bot`: An element is *bottom* if all elements are greater than it.
* `is_top`: An element is *top* if all elements are less than it.
* `is_min`: An element is *minimal* if no element is strictly less than it.
* `is_max`: An element is *maximal* if no element is strictly greater than it.

See also `is_bot_iff_is_min` and `is_top_iff_is_max` for the equivalences in a (co)directed order.

## Typeclasses

* `no_bot_order`: An order without bottom elements.
* `no_top_order`: An order without top elements.
* `no_min_order`: An order without minimal elements.
* `no_max_order`: An order without maximal elements.
-/


open OrderDual

variable {ι α β : Type _} {π : ι → Type _}

#print NoBotOrder /-
/-- Order without bottom elements. -/
class NoBotOrder (α : Type _) [LE α] : Prop where
  exists_not_ge (a : α) : ∃ b, ¬a ≤ b
#align no_bot_order NoBotOrder
-/

#print NoTopOrder /-
/-- Order without top elements. -/
class NoTopOrder (α : Type _) [LE α] : Prop where
  exists_not_le (a : α) : ∃ b, ¬b ≤ a
#align no_top_order NoTopOrder
-/

#print NoMinOrder /-
/-- Order without minimal elements. Sometimes called coinitial or dense. -/
class NoMinOrder (α : Type _) [LT α] : Prop where
  exists_lt (a : α) : ∃ b, b < a
#align no_min_order NoMinOrder
-/

#print NoMaxOrder /-
/-- Order without maximal elements. Sometimes called cofinal. -/
class NoMaxOrder (α : Type _) [LT α] : Prop where
  exists_gt (a : α) : ∃ b, a < b
#align no_max_order NoMaxOrder
-/

export NoBotOrder (exists_not_ge)

export NoTopOrder (exists_not_le)

export NoMinOrder (exists_lt)

export NoMaxOrder (exists_gt)

#print nonempty_lt /-
instance nonempty_lt [LT α] [NoMinOrder α] (a : α) : Nonempty { x // x < a } :=
  nonempty_subtype.2 (exists_lt a)
#align nonempty_lt nonempty_lt
-/

#print nonempty_gt /-
instance nonempty_gt [LT α] [NoMaxOrder α] (a : α) : Nonempty { x // a < x } :=
  nonempty_subtype.2 (exists_gt a)
#align nonempty_gt nonempty_gt
-/

#print OrderDual.noBotOrder /-
instance OrderDual.noBotOrder (α : Type _) [LE α] [NoTopOrder α] : NoBotOrder αᵒᵈ :=
  ⟨fun a => @exists_not_le α _ _ a⟩
#align order_dual.no_bot_order OrderDual.noBotOrder
-/

#print OrderDual.noTopOrder /-
instance OrderDual.noTopOrder (α : Type _) [LE α] [NoBotOrder α] : NoTopOrder αᵒᵈ :=
  ⟨fun a => @exists_not_ge α _ _ a⟩
#align order_dual.no_top_order OrderDual.noTopOrder
-/

#print OrderDual.noMinOrder /-
instance OrderDual.noMinOrder (α : Type _) [LT α] [NoMaxOrder α] : NoMinOrder αᵒᵈ :=
  ⟨fun a => @exists_gt α _ _ a⟩
#align order_dual.no_min_order OrderDual.noMinOrder
-/

#print OrderDual.noMaxOrder /-
instance OrderDual.noMaxOrder (α : Type _) [LT α] [NoMinOrder α] : NoMaxOrder αᵒᵈ :=
  ⟨fun a => @exists_lt α _ _ a⟩
#align order_dual.no_max_order OrderDual.noMaxOrder
-/

/- warning: no_max_order_of_left -> noMaxOrder_of_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], NoMaxOrder.{max u1 u2} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], NoMaxOrder.{max u2 u1} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.instPreorderProd.{u1, u2} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align no_max_order_of_left noMaxOrder_of_leftₓ'. -/
instance noMaxOrder_of_left [Preorder α] [Preorder β] [NoMaxOrder α] : NoMaxOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_gt a
    exact ⟨(c, b), Prod.mk_lt_mk_iff_left.2 h⟩⟩
#align no_max_order_of_left noMaxOrder_of_left

/- warning: no_max_order_of_right -> noMaxOrder_of_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : NoMaxOrder.{u2} β (Preorder.toLT.{u2} β _inst_2)], NoMaxOrder.{max u1 u2} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : NoMaxOrder.{u2} β (Preorder.toLT.{u2} β _inst_2)], NoMaxOrder.{max u2 u1} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.instPreorderProd.{u1, u2} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align no_max_order_of_right noMaxOrder_of_rightₓ'. -/
instance noMaxOrder_of_right [Preorder α] [Preorder β] [NoMaxOrder β] : NoMaxOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_gt b
    exact ⟨(a, c), Prod.mk_lt_mk_iff_right.2 h⟩⟩
#align no_max_order_of_right noMaxOrder_of_right

/- warning: no_min_order_of_left -> noMinOrder_of_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], NoMinOrder.{max u1 u2} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], NoMinOrder.{max u2 u1} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.instPreorderProd.{u1, u2} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align no_min_order_of_left noMinOrder_of_leftₓ'. -/
instance noMinOrder_of_left [Preorder α] [Preorder β] [NoMinOrder α] : NoMinOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt a
    exact ⟨(c, b), Prod.mk_lt_mk_iff_left.2 h⟩⟩
#align no_min_order_of_left noMinOrder_of_left

/- warning: no_min_order_of_right -> noMinOrder_of_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : NoMinOrder.{u2} β (Preorder.toLT.{u2} β _inst_2)], NoMinOrder.{max u1 u2} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : NoMinOrder.{u2} β (Preorder.toLT.{u2} β _inst_2)], NoMinOrder.{max u2 u1} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.instPreorderProd.{u1, u2} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align no_min_order_of_right noMinOrder_of_rightₓ'. -/
instance noMinOrder_of_right [Preorder α] [Preorder β] [NoMinOrder β] : NoMinOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt b
    exact ⟨(a, c), Prod.mk_lt_mk_iff_right.2 h⟩⟩
#align no_min_order_of_right noMinOrder_of_right

instance [Nonempty ι] [∀ i, Preorder (π i)] [∀ i, NoMaxOrder (π i)] : NoMaxOrder (∀ i, π i) :=
  ⟨fun a => by
    classical
      obtain ⟨b, hb⟩ := exists_gt (a <| Classical.arbitrary _)
      exact ⟨_, lt_update_self_iff.2 hb⟩⟩

instance [Nonempty ι] [∀ i, Preorder (π i)] [∀ i, NoMinOrder (π i)] : NoMinOrder (∀ i, π i) :=
  ⟨fun a => by
    classical
      obtain ⟨b, hb⟩ := exists_lt (a <| Classical.arbitrary _)
      exact ⟨_, update_lt_self_iff.2 hb⟩⟩

-- See note [lower instance priority]
instance (priority := 100) NoMinOrder.to_noBotOrder (α : Type _) [Preorder α] [NoMinOrder α] :
    NoBotOrder α :=
  ⟨fun a => (exists_lt a).imp fun _ => not_le_of_lt⟩
#align no_min_order.to_no_bot_order NoMinOrder.to_noBotOrder

-- See note [lower instance priority]
instance (priority := 100) NoMaxOrder.to_noTopOrder (α : Type _) [Preorder α] [NoMaxOrder α] :
    NoTopOrder α :=
  ⟨fun a => (exists_gt a).imp fun _ => not_le_of_lt⟩
#align no_max_order.to_no_top_order NoMaxOrder.to_noTopOrder

#print NoBotOrder.to_noMinOrder /-
theorem NoBotOrder.to_noMinOrder (α : Type _) [LinearOrder α] [NoBotOrder α] : NoMinOrder α :=
  {
    exists_lt := by
      convert fun a : α => exists_not_ge a
      simp_rw [not_le] }
#align no_bot_order.to_no_min_order NoBotOrder.to_noMinOrder
-/

#print NoTopOrder.to_noMaxOrder /-
theorem NoTopOrder.to_noMaxOrder (α : Type _) [LinearOrder α] [NoTopOrder α] : NoMaxOrder α :=
  {
    exists_gt := by
      convert fun a : α => exists_not_le a
      simp_rw [not_le] }
#align no_top_order.to_no_max_order NoTopOrder.to_noMaxOrder
-/

#print noBotOrder_iff_noMinOrder /-
theorem noBotOrder_iff_noMinOrder (α : Type _) [LinearOrder α] : NoBotOrder α ↔ NoMinOrder α :=
  ⟨fun h =>
    haveI := h
    NoBotOrder.to_noMinOrder α,
    fun h =>
    haveI := h
    NoMinOrder.to_noBotOrder α⟩
#align no_bot_order_iff_no_min_order noBotOrder_iff_noMinOrder
-/

#print noTopOrder_iff_noMaxOrder /-
theorem noTopOrder_iff_noMaxOrder (α : Type _) [LinearOrder α] : NoTopOrder α ↔ NoMaxOrder α :=
  ⟨fun h =>
    haveI := h
    NoTopOrder.to_noMaxOrder α,
    fun h =>
    haveI := h
    NoMaxOrder.to_noTopOrder α⟩
#align no_top_order_iff_no_max_order noTopOrder_iff_noMaxOrder
-/

#print NoMinOrder.not_acc /-
theorem NoMinOrder.not_acc [LT α] [NoMinOrder α] (a : α) : ¬Acc (· < ·) a := fun h =>
  Acc.recOn h fun x _ => (exists_lt x).recOn
#align no_min_order.not_acc NoMinOrder.not_acc
-/

#print NoMaxOrder.not_acc /-
theorem NoMaxOrder.not_acc [LT α] [NoMaxOrder α] (a : α) : ¬Acc (· > ·) a := fun h =>
  Acc.recOn h fun x _ => (exists_gt x).recOn
#align no_max_order.not_acc NoMaxOrder.not_acc
-/

section LE

variable [LE α] {a b : α}

#print IsBot /-
/-- `a : α` is a bottom element of `α` if it is less than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `order_bot`, except that a preorder may have
several bottom elements. When `α` is linear, this is useful to make a case disjunction on
`no_min_order α` within a proof. -/
def IsBot (a : α) : Prop :=
  ∀ b, a ≤ b
#align is_bot IsBot
-/

#print IsTop /-
/-- `a : α` is a top element of `α` if it is greater than or equal to any other element of `α`.
This predicate is roughly an unbundled version of `order_bot`, except that a preorder may have
several top elements. When `α` is linear, this is useful to make a case disjunction on
`no_max_order α` within a proof. -/
def IsTop (a : α) : Prop :=
  ∀ b, b ≤ a
#align is_top IsTop
-/

#print IsMin /-
/-- `a` is a minimal element of `α` if no element is strictly less than it. We spell it without `<`
to avoid having to convert between `≤` and `<`. Instead, `is_min_iff_forall_not_lt` does the
conversion. -/
def IsMin (a : α) : Prop :=
  ∀ ⦃b⦄, b ≤ a → a ≤ b
#align is_min IsMin
-/

#print IsMax /-
/-- `a` is a maximal element of `α` if no element is strictly greater than it. We spell it without
`<` to avoid having to convert between `≤` and `<`. Instead, `is_max_iff_forall_not_lt` does the
conversion. -/
def IsMax (a : α) : Prop :=
  ∀ ⦃b⦄, a ≤ b → b ≤ a
#align is_max IsMax
-/

#print not_isBot /-
@[simp]
theorem not_isBot [NoBotOrder α] (a : α) : ¬IsBot a := fun h =>
  let ⟨b, hb⟩ := exists_not_ge a
  hb <| h _
#align not_is_bot not_isBot
-/

#print not_isTop /-
@[simp]
theorem not_isTop [NoTopOrder α] (a : α) : ¬IsTop a := fun h =>
  let ⟨b, hb⟩ := exists_not_le a
  hb <| h _
#align not_is_top not_isTop
-/

#print IsBot.isMin /-
protected theorem IsBot.isMin (h : IsBot a) : IsMin a := fun b _ => h b
#align is_bot.is_min IsBot.isMin
-/

#print IsTop.isMax /-
protected theorem IsTop.isMax (h : IsTop a) : IsMax a := fun b _ => h b
#align is_top.is_max IsTop.isMax
-/

#print isBot_toDual_iff /-
@[simp]
theorem isBot_toDual_iff : IsBot (toDual a) ↔ IsTop a :=
  Iff.rfl
#align is_bot_to_dual_iff isBot_toDual_iff
-/

#print isTop_toDual_iff /-
@[simp]
theorem isTop_toDual_iff : IsTop (toDual a) ↔ IsBot a :=
  Iff.rfl
#align is_top_to_dual_iff isTop_toDual_iff
-/

#print isMin_toDual_iff /-
@[simp]
theorem isMin_toDual_iff : IsMin (toDual a) ↔ IsMax a :=
  Iff.rfl
#align is_min_to_dual_iff isMin_toDual_iff
-/

#print isMax_toDual_iff /-
@[simp]
theorem isMax_toDual_iff : IsMax (toDual a) ↔ IsMin a :=
  Iff.rfl
#align is_max_to_dual_iff isMax_toDual_iff
-/

#print isBot_ofDual_iff /-
@[simp]
theorem isBot_ofDual_iff {a : αᵒᵈ} : IsBot (ofDual a) ↔ IsTop a :=
  Iff.rfl
#align is_bot_of_dual_iff isBot_ofDual_iff
-/

#print isTop_ofDual_iff /-
@[simp]
theorem isTop_ofDual_iff {a : αᵒᵈ} : IsTop (ofDual a) ↔ IsBot a :=
  Iff.rfl
#align is_top_of_dual_iff isTop_ofDual_iff
-/

#print isMin_ofDual_iff /-
@[simp]
theorem isMin_ofDual_iff {a : αᵒᵈ} : IsMin (ofDual a) ↔ IsMax a :=
  Iff.rfl
#align is_min_of_dual_iff isMin_ofDual_iff
-/

#print isMax_ofDual_iff /-
@[simp]
theorem isMax_ofDual_iff {a : αᵒᵈ} : IsMax (ofDual a) ↔ IsMin a :=
  Iff.rfl
#align is_max_of_dual_iff isMax_ofDual_iff
-/

alias isBot_toDual_iff ↔ _ IsTop.toDual
#align is_top.to_dual IsTop.toDual

alias isTop_toDual_iff ↔ _ IsBot.toDual
#align is_bot.to_dual IsBot.toDual

alias isMin_toDual_iff ↔ _ IsMax.toDual
#align is_max.to_dual IsMax.toDual

alias isMax_toDual_iff ↔ _ IsMin.toDual
#align is_min.to_dual IsMin.toDual

alias isBot_ofDual_iff ↔ _ IsTop.ofDual
#align is_top.of_dual IsTop.ofDual

alias isTop_ofDual_iff ↔ _ IsBot.ofDual
#align is_bot.of_dual IsBot.ofDual

alias isMin_ofDual_iff ↔ _ IsMax.ofDual
#align is_max.of_dual IsMax.ofDual

alias isMax_ofDual_iff ↔ _ IsMin.ofDual
#align is_min.of_dual IsMin.ofDual

end LE

section Preorder

variable [Preorder α] {a b : α}

#print IsBot.mono /-
theorem IsBot.mono (ha : IsBot a) (h : b ≤ a) : IsBot b := fun c => h.trans <| ha _
#align is_bot.mono IsBot.mono
-/

#print IsTop.mono /-
theorem IsTop.mono (ha : IsTop a) (h : a ≤ b) : IsTop b := fun c => (ha _).trans h
#align is_top.mono IsTop.mono
-/

#print IsMin.mono /-
theorem IsMin.mono (ha : IsMin a) (h : b ≤ a) : IsMin b := fun c hc => h.trans <| ha <| hc.trans h
#align is_min.mono IsMin.mono
-/

#print IsMax.mono /-
theorem IsMax.mono (ha : IsMax a) (h : a ≤ b) : IsMax b := fun c hc => (ha <| h.trans hc).trans h
#align is_max.mono IsMax.mono
-/

#print IsMin.not_lt /-
theorem IsMin.not_lt (h : IsMin a) : ¬b < a := fun hb => hb.not_le <| h hb.le
#align is_min.not_lt IsMin.not_lt
-/

#print IsMax.not_lt /-
theorem IsMax.not_lt (h : IsMax a) : ¬a < b := fun hb => hb.not_le <| h hb.le
#align is_max.not_lt IsMax.not_lt
-/

#print not_isMin_of_lt /-
@[simp]
theorem not_isMin_of_lt (h : b < a) : ¬IsMin a := fun ha => ha.not_lt h
#align not_is_min_of_lt not_isMin_of_lt
-/

#print not_isMax_of_lt /-
@[simp]
theorem not_isMax_of_lt (h : a < b) : ¬IsMax a := fun ha => ha.not_lt h
#align not_is_max_of_lt not_isMax_of_lt
-/

alias not_isMin_of_lt ← LT.lt.not_isMin
#align has_lt.lt.not_is_min LT.lt.not_isMin

alias not_isMax_of_lt ← LT.lt.not_isMax
#align has_lt.lt.not_is_max LT.lt.not_isMax

#print isMin_iff_forall_not_lt /-
theorem isMin_iff_forall_not_lt : IsMin a ↔ ∀ b, ¬b < a :=
  ⟨fun h _ => h.not_lt, fun h b hba => of_not_not fun hab => h _ <| hba.lt_of_not_le hab⟩
#align is_min_iff_forall_not_lt isMin_iff_forall_not_lt
-/

#print isMax_iff_forall_not_lt /-
theorem isMax_iff_forall_not_lt : IsMax a ↔ ∀ b, ¬a < b :=
  ⟨fun h _ => h.not_lt, fun h b hba => of_not_not fun hab => h _ <| hba.lt_of_not_le hab⟩
#align is_max_iff_forall_not_lt isMax_iff_forall_not_lt
-/

#print not_isMin_iff /-
@[simp]
theorem not_isMin_iff : ¬IsMin a ↔ ∃ b, b < a := by
  simp_rw [lt_iff_le_not_le, IsMin, not_forall, exists_prop]
#align not_is_min_iff not_isMin_iff
-/

#print not_isMax_iff /-
@[simp]
theorem not_isMax_iff : ¬IsMax a ↔ ∃ b, a < b := by
  simp_rw [lt_iff_le_not_le, IsMax, not_forall, exists_prop]
#align not_is_max_iff not_isMax_iff
-/

#print not_isMin /-
@[simp]
theorem not_isMin [NoMinOrder α] (a : α) : ¬IsMin a :=
  not_isMin_iff.2 <| exists_lt a
#align not_is_min not_isMin
-/

#print not_isMax /-
@[simp]
theorem not_isMax [NoMaxOrder α] (a : α) : ¬IsMax a :=
  not_isMax_iff.2 <| exists_gt a
#align not_is_max not_isMax
-/

namespace Subsingleton

variable [Subsingleton α]

#print Subsingleton.isBot /-
protected theorem isBot (a : α) : IsBot a := fun _ => (Subsingleton.elim _ _).le
#align subsingleton.is_bot Subsingleton.isBot
-/

#print Subsingleton.isTop /-
protected theorem isTop (a : α) : IsTop a := fun _ => (Subsingleton.elim _ _).le
#align subsingleton.is_top Subsingleton.isTop
-/

#print Subsingleton.isMin /-
protected theorem isMin (a : α) : IsMin a :=
  (Subsingleton.isBot _).IsMin
#align subsingleton.is_min Subsingleton.isMin
-/

#print Subsingleton.isMax /-
protected theorem isMax (a : α) : IsMax a :=
  (Subsingleton.isTop _).IsMax
#align subsingleton.is_max Subsingleton.isMax
-/

end Subsingleton

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

#print IsMin.eq_of_le /-
protected theorem IsMin.eq_of_le (ha : IsMin a) (h : b ≤ a) : b = a :=
  h.antisymm <| ha h
#align is_min.eq_of_le IsMin.eq_of_le
-/

#print IsMin.eq_of_ge /-
protected theorem IsMin.eq_of_ge (ha : IsMin a) (h : b ≤ a) : a = b :=
  h.antisymm' <| ha h
#align is_min.eq_of_ge IsMin.eq_of_ge
-/

#print IsMax.eq_of_le /-
protected theorem IsMax.eq_of_le (ha : IsMax a) (h : a ≤ b) : a = b :=
  h.antisymm <| ha h
#align is_max.eq_of_le IsMax.eq_of_le
-/

#print IsMax.eq_of_ge /-
protected theorem IsMax.eq_of_ge (ha : IsMax a) (h : a ≤ b) : b = a :=
  h.antisymm' <| ha h
#align is_max.eq_of_ge IsMax.eq_of_ge
-/

end PartialOrder

section Prod

variable [Preorder α] [Preorder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

/- warning: is_bot.prod_mk -> IsBot.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {a : α} {b : β}, (IsBot.{u1} α (Preorder.toLE.{u1} α _inst_1) a) -> (IsBot.{u2} β (Preorder.toLE.{u2} β _inst_2) b) -> (IsBot.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (Prod.mk.{u1, u2} α β a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {a : α} {b : β}, (IsBot.{u2} α (Preorder.toLE.{u2} α _inst_1) a) -> (IsBot.{u1} β (Preorder.toLE.{u1} β _inst_2) b) -> (IsBot.{max u1 u2} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) (Prod.mk.{u2, u1} α β a b))
Case conversion may be inaccurate. Consider using '#align is_bot.prod_mk IsBot.prod_mkₓ'. -/
theorem IsBot.prod_mk (ha : IsBot a) (hb : IsBot b) : IsBot (a, b) := fun c => ⟨ha _, hb _⟩
#align is_bot.prod_mk IsBot.prod_mk

/- warning: is_top.prod_mk -> IsTop.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {a : α} {b : β}, (IsTop.{u1} α (Preorder.toLE.{u1} α _inst_1) a) -> (IsTop.{u2} β (Preorder.toLE.{u2} β _inst_2) b) -> (IsTop.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (Prod.mk.{u1, u2} α β a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {a : α} {b : β}, (IsTop.{u2} α (Preorder.toLE.{u2} α _inst_1) a) -> (IsTop.{u1} β (Preorder.toLE.{u1} β _inst_2) b) -> (IsTop.{max u1 u2} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) (Prod.mk.{u2, u1} α β a b))
Case conversion may be inaccurate. Consider using '#align is_top.prod_mk IsTop.prod_mkₓ'. -/
theorem IsTop.prod_mk (ha : IsTop a) (hb : IsTop b) : IsTop (a, b) := fun c => ⟨ha _, hb _⟩
#align is_top.prod_mk IsTop.prod_mk

/- warning: is_min.prod_mk -> IsMin.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {a : α} {b : β}, (IsMin.{u1} α (Preorder.toLE.{u1} α _inst_1) a) -> (IsMin.{u2} β (Preorder.toLE.{u2} β _inst_2) b) -> (IsMin.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (Prod.mk.{u1, u2} α β a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {a : α} {b : β}, (IsMin.{u2} α (Preorder.toLE.{u2} α _inst_1) a) -> (IsMin.{u1} β (Preorder.toLE.{u1} β _inst_2) b) -> (IsMin.{max u1 u2} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) (Prod.mk.{u2, u1} α β a b))
Case conversion may be inaccurate. Consider using '#align is_min.prod_mk IsMin.prod_mkₓ'. -/
theorem IsMin.prod_mk (ha : IsMin a) (hb : IsMin b) : IsMin (a, b) := fun c hc => ⟨ha hc.1, hb hc.2⟩
#align is_min.prod_mk IsMin.prod_mk

/- warning: is_max.prod_mk -> IsMax.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {a : α} {b : β}, (IsMax.{u1} α (Preorder.toLE.{u1} α _inst_1) a) -> (IsMax.{u2} β (Preorder.toLE.{u2} β _inst_2) b) -> (IsMax.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (Prod.mk.{u1, u2} α β a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {a : α} {b : β}, (IsMax.{u2} α (Preorder.toLE.{u2} α _inst_1) a) -> (IsMax.{u1} β (Preorder.toLE.{u1} β _inst_2) b) -> (IsMax.{max u1 u2} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) (Prod.mk.{u2, u1} α β a b))
Case conversion may be inaccurate. Consider using '#align is_max.prod_mk IsMax.prod_mkₓ'. -/
theorem IsMax.prod_mk (ha : IsMax a) (hb : IsMax b) : IsMax (a, b) := fun c hc => ⟨ha hc.1, hb hc.2⟩
#align is_max.prod_mk IsMax.prod_mk

/- warning: is_bot.fst -> IsBot.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {x : Prod.{u1, u2} α β}, (IsBot.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) x) -> (IsBot.{u1} α (Preorder.toLE.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {x : Prod.{u2, u1} α β}, (IsBot.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) x) -> (IsBot.{u2} α (Preorder.toLE.{u2} α _inst_1) (Prod.fst.{u2, u1} α β x))
Case conversion may be inaccurate. Consider using '#align is_bot.fst IsBot.fstₓ'. -/
theorem IsBot.fst (hx : IsBot x) : IsBot x.1 := fun c => (hx (c, x.2)).1
#align is_bot.fst IsBot.fst

/- warning: is_bot.snd -> IsBot.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {x : Prod.{u1, u2} α β}, (IsBot.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) x) -> (IsBot.{u2} β (Preorder.toLE.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {x : Prod.{u2, u1} α β}, (IsBot.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) x) -> (IsBot.{u1} β (Preorder.toLE.{u1} β _inst_2) (Prod.snd.{u2, u1} α β x))
Case conversion may be inaccurate. Consider using '#align is_bot.snd IsBot.sndₓ'. -/
theorem IsBot.snd (hx : IsBot x) : IsBot x.2 := fun c => (hx (x.1, c)).2
#align is_bot.snd IsBot.snd

/- warning: is_top.fst -> IsTop.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {x : Prod.{u1, u2} α β}, (IsTop.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) x) -> (IsTop.{u1} α (Preorder.toLE.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {x : Prod.{u2, u1} α β}, (IsTop.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) x) -> (IsTop.{u2} α (Preorder.toLE.{u2} α _inst_1) (Prod.fst.{u2, u1} α β x))
Case conversion may be inaccurate. Consider using '#align is_top.fst IsTop.fstₓ'. -/
theorem IsTop.fst (hx : IsTop x) : IsTop x.1 := fun c => (hx (c, x.2)).1
#align is_top.fst IsTop.fst

/- warning: is_top.snd -> IsTop.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {x : Prod.{u1, u2} α β}, (IsTop.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) x) -> (IsTop.{u2} β (Preorder.toLE.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {x : Prod.{u2, u1} α β}, (IsTop.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) x) -> (IsTop.{u1} β (Preorder.toLE.{u1} β _inst_2) (Prod.snd.{u2, u1} α β x))
Case conversion may be inaccurate. Consider using '#align is_top.snd IsTop.sndₓ'. -/
theorem IsTop.snd (hx : IsTop x) : IsTop x.2 := fun c => (hx (x.1, c)).2
#align is_top.snd IsTop.snd

/- warning: is_min.fst -> IsMin.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {x : Prod.{u1, u2} α β}, (IsMin.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) x) -> (IsMin.{u1} α (Preorder.toLE.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {x : Prod.{u2, u1} α β}, (IsMin.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) x) -> (IsMin.{u2} α (Preorder.toLE.{u2} α _inst_1) (Prod.fst.{u2, u1} α β x))
Case conversion may be inaccurate. Consider using '#align is_min.fst IsMin.fstₓ'. -/
theorem IsMin.fst (hx : IsMin x) : IsMin x.1 := fun c hc =>
  (hx <| show (c, x.2) ≤ x from (and_iff_left le_rfl).2 hc).1
#align is_min.fst IsMin.fst

/- warning: is_min.snd -> IsMin.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {x : Prod.{u1, u2} α β}, (IsMin.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) x) -> (IsMin.{u2} β (Preorder.toLE.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {x : Prod.{u2, u1} α β}, (IsMin.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) x) -> (IsMin.{u1} β (Preorder.toLE.{u1} β _inst_2) (Prod.snd.{u2, u1} α β x))
Case conversion may be inaccurate. Consider using '#align is_min.snd IsMin.sndₓ'. -/
theorem IsMin.snd (hx : IsMin x) : IsMin x.2 := fun c hc =>
  (hx <| show (x.1, c) ≤ x from (and_iff_right le_rfl).2 hc).2
#align is_min.snd IsMin.snd

/- warning: is_max.fst -> IsMax.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {x : Prod.{u1, u2} α β}, (IsMax.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) x) -> (IsMax.{u1} α (Preorder.toLE.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {x : Prod.{u2, u1} α β}, (IsMax.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) x) -> (IsMax.{u2} α (Preorder.toLE.{u2} α _inst_1) (Prod.fst.{u2, u1} α β x))
Case conversion may be inaccurate. Consider using '#align is_max.fst IsMax.fstₓ'. -/
theorem IsMax.fst (hx : IsMax x) : IsMax x.1 := fun c hc =>
  (hx <| show x ≤ (c, x.2) from (and_iff_left le_rfl).2 hc).1
#align is_max.fst IsMax.fst

/- warning: is_max.snd -> IsMax.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {x : Prod.{u1, u2} α β}, (IsMax.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) x) -> (IsMax.{u2} β (Preorder.toLE.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {x : Prod.{u2, u1} α β}, (IsMax.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) x) -> (IsMax.{u1} β (Preorder.toLE.{u1} β _inst_2) (Prod.snd.{u2, u1} α β x))
Case conversion may be inaccurate. Consider using '#align is_max.snd IsMax.sndₓ'. -/
theorem IsMax.snd (hx : IsMax x) : IsMax x.2 := fun c hc =>
  (hx <| show x ≤ (x.1, c) from (and_iff_right le_rfl).2 hc).2
#align is_max.snd IsMax.snd

/- warning: prod.is_bot_iff -> Prod.isBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {x : Prod.{u1, u2} α β}, Iff (IsBot.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) x) (And (IsBot.{u1} α (Preorder.toLE.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x)) (IsBot.{u2} β (Preorder.toLE.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {x : Prod.{u2, u1} α β}, Iff (IsBot.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) x) (And (IsBot.{u2} α (Preorder.toLE.{u2} α _inst_1) (Prod.fst.{u2, u1} α β x)) (IsBot.{u1} β (Preorder.toLE.{u1} β _inst_2) (Prod.snd.{u2, u1} α β x)))
Case conversion may be inaccurate. Consider using '#align prod.is_bot_iff Prod.isBot_iffₓ'. -/
theorem Prod.isBot_iff : IsBot x ↔ IsBot x.1 ∧ IsBot x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩
#align prod.is_bot_iff Prod.isBot_iff

/- warning: prod.is_top_iff -> Prod.isTop_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {x : Prod.{u1, u2} α β}, Iff (IsTop.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) x) (And (IsTop.{u1} α (Preorder.toLE.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x)) (IsTop.{u2} β (Preorder.toLE.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {x : Prod.{u2, u1} α β}, Iff (IsTop.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) x) (And (IsTop.{u2} α (Preorder.toLE.{u2} α _inst_1) (Prod.fst.{u2, u1} α β x)) (IsTop.{u1} β (Preorder.toLE.{u1} β _inst_2) (Prod.snd.{u2, u1} α β x)))
Case conversion may be inaccurate. Consider using '#align prod.is_top_iff Prod.isTop_iffₓ'. -/
theorem Prod.isTop_iff : IsTop x ↔ IsTop x.1 ∧ IsTop x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩
#align prod.is_top_iff Prod.isTop_iff

/- warning: prod.is_min_iff -> Prod.isMin_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {x : Prod.{u1, u2} α β}, Iff (IsMin.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) x) (And (IsMin.{u1} α (Preorder.toLE.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x)) (IsMin.{u2} β (Preorder.toLE.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {x : Prod.{u2, u1} α β}, Iff (IsMin.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) x) (And (IsMin.{u2} α (Preorder.toLE.{u2} α _inst_1) (Prod.fst.{u2, u1} α β x)) (IsMin.{u1} β (Preorder.toLE.{u1} β _inst_2) (Prod.snd.{u2, u1} α β x)))
Case conversion may be inaccurate. Consider using '#align prod.is_min_iff Prod.isMin_iffₓ'. -/
theorem Prod.isMin_iff : IsMin x ↔ IsMin x.1 ∧ IsMin x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩
#align prod.is_min_iff Prod.isMin_iff

/- warning: prod.is_max_iff -> Prod.isMax_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {x : Prod.{u1, u2} α β}, Iff (IsMax.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasLe.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) x) (And (IsMax.{u1} α (Preorder.toLE.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x)) (IsMax.{u2} β (Preorder.toLE.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {x : Prod.{u2, u1} α β}, Iff (IsMax.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instLEProd.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)) x) (And (IsMax.{u2} α (Preorder.toLE.{u2} α _inst_1) (Prod.fst.{u2, u1} α β x)) (IsMax.{u1} β (Preorder.toLE.{u1} β _inst_2) (Prod.snd.{u2, u1} α β x)))
Case conversion may be inaccurate. Consider using '#align prod.is_max_iff Prod.isMax_iffₓ'. -/
theorem Prod.isMax_iff : IsMax x ↔ IsMax x.1 ∧ IsMax x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩
#align prod.is_max_iff Prod.isMax_iff

end Prod

