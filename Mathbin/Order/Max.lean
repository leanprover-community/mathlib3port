/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov, Yaël Dillies
-/
import Mathbin.Order.Synonym

/-!
# Minimal/maximal and bottom/top elements

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

instance nonempty_lt [LT α] [NoMinOrder α] (a : α) : Nonempty { x // x < a } :=
  nonempty_subtype.2 (exists_lt a)
#align nonempty_lt nonempty_lt

instance nonempty_gt [LT α] [NoMaxOrder α] (a : α) : Nonempty { x // a < x } :=
  nonempty_subtype.2 (exists_gt a)
#align nonempty_gt nonempty_gt

instance OrderDual.no_bot_order (α : Type _) [LE α] [NoTopOrder α] : NoBotOrder αᵒᵈ :=
  ⟨fun a => @exists_not_le α _ _ a⟩
#align order_dual.no_bot_order OrderDual.no_bot_order

instance OrderDual.no_top_order (α : Type _) [LE α] [NoBotOrder α] : NoTopOrder αᵒᵈ :=
  ⟨fun a => @exists_not_ge α _ _ a⟩
#align order_dual.no_top_order OrderDual.no_top_order

instance OrderDual.no_min_order (α : Type _) [LT α] [NoMaxOrder α] : NoMinOrder αᵒᵈ :=
  ⟨fun a => @exists_gt α _ _ a⟩
#align order_dual.no_min_order OrderDual.no_min_order

instance OrderDual.no_max_order (α : Type _) [LT α] [NoMinOrder α] : NoMaxOrder αᵒᵈ :=
  ⟨fun a => @exists_lt α _ _ a⟩
#align order_dual.no_max_order OrderDual.no_max_order

instance no_max_order_of_left [Preorder α] [Preorder β] [NoMaxOrder α] : NoMaxOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_gt a
    exact ⟨(c, b), Prod.mk_lt_mk_iff_left.2 h⟩⟩
#align no_max_order_of_left no_max_order_of_left

instance no_max_order_of_right [Preorder α] [Preorder β] [NoMaxOrder β] : NoMaxOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_gt b
    exact ⟨(a, c), Prod.mk_lt_mk_iff_right.2 h⟩⟩
#align no_max_order_of_right no_max_order_of_right

instance no_min_order_of_left [Preorder α] [Preorder β] [NoMinOrder α] : NoMinOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt a
    exact ⟨(c, b), Prod.mk_lt_mk_iff_left.2 h⟩⟩
#align no_min_order_of_left no_min_order_of_left

instance no_min_order_of_right [Preorder α] [Preorder β] [NoMinOrder β] : NoMinOrder (α × β) :=
  ⟨fun ⟨a, b⟩ => by
    obtain ⟨c, h⟩ := exists_lt b
    exact ⟨(a, c), Prod.mk_lt_mk_iff_right.2 h⟩⟩
#align no_min_order_of_right no_min_order_of_right

instance [Nonempty ι] [∀ i, Preorder (π i)] [∀ i, NoMaxOrder (π i)] : NoMaxOrder (∀ i, π i) :=
  ⟨fun a => by classical
    obtain ⟨b, hb⟩ := exists_gt (a <| Classical.arbitrary _)
    exact ⟨_, lt_update_self_iff.2 hb⟩⟩

instance [Nonempty ι] [∀ i, Preorder (π i)] [∀ i, NoMinOrder (π i)] : NoMinOrder (∀ i, π i) :=
  ⟨fun a => by
    obtain ⟨b, hb⟩ := exists_lt (a <| Classical.arbitrary _)
    exact ⟨_, update_lt_self_iff.2 hb⟩⟩

-- See note [lower instance priority]
instance (priority := 100) NoMinOrder.to_no_bot_order (α : Type _) [Preorder α] [NoMinOrder α] : NoBotOrder α :=
  ⟨fun a => (exists_lt a).imp fun _ => not_le_of_lt⟩
#align no_min_order.to_no_bot_order NoMinOrder.to_no_bot_order

-- See note [lower instance priority]
instance (priority := 100) NoMaxOrder.to_no_top_order (α : Type _) [Preorder α] [NoMaxOrder α] : NoTopOrder α :=
  ⟨fun a => (exists_gt a).imp fun _ => not_le_of_lt⟩
#align no_max_order.to_no_top_order NoMaxOrder.to_no_top_order

#print NoBotOrder.to_noMinOrder /-
theorem NoBotOrder.to_noMinOrder (α : Type _) [LinearOrder α] [NoBotOrder α] : NoMinOrder α :=
  { exists_lt := by
      convert fun a : α => exists_not_ge a
      simp_rw [not_le] }
#align no_bot_order.to_no_min_order NoBotOrder.to_noMinOrder
-/

#print NoTopOrder.to_noMaxOrder /-
theorem NoTopOrder.to_noMaxOrder (α : Type _) [LinearOrder α] [NoTopOrder α] : NoMaxOrder α :=
  { exists_gt := by
      convert fun a : α => exists_not_le a
      simp_rw [not_le] }
#align no_top_order.to_no_max_order NoTopOrder.to_noMaxOrder
-/

#print no_bot_order_iff_no_min_order /-
theorem no_bot_order_iff_no_min_order (α : Type _) [LinearOrder α] : NoBotOrder α ↔ NoMinOrder α :=
  ⟨fun h =>
    haveI := h
    NoBotOrder.to_noMinOrder α,
    fun h =>
    haveI := h
    NoMinOrder.to_no_bot_order α⟩
#align no_bot_order_iff_no_min_order no_bot_order_iff_no_min_order
-/

#print no_top_order_iff_no_max_order /-
theorem no_top_order_iff_no_max_order (α : Type _) [LinearOrder α] : NoTopOrder α ↔ NoMaxOrder α :=
  ⟨fun h =>
    haveI := h
    NoTopOrder.to_noMaxOrder α,
    fun h =>
    haveI := h
    NoMaxOrder.to_no_top_order α⟩
#align no_top_order_iff_no_max_order no_top_order_iff_no_max_order
-/

#print NoMinOrder.not_acc /-
theorem NoMinOrder.not_acc [LT α] [NoMinOrder α] (a : α) : ¬Acc (· < ·) a := fun h =>
  (Acc.recOn h) fun x _ => (exists_lt x).recOn
#align no_min_order.not_acc NoMinOrder.not_acc
-/

#print NoMaxOrder.not_acc /-
theorem NoMaxOrder.not_acc [LT α] [NoMaxOrder α] (a : α) : ¬Acc (· > ·) a := fun h =>
  (Acc.recOn h) fun x _ => (exists_gt x).recOn
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

#print not_is_bot /-
@[simp]
theorem not_is_bot [NoBotOrder α] (a : α) : ¬IsBot a := fun h =>
  let ⟨b, hb⟩ := exists_not_ge a
  hb <| h _
#align not_is_bot not_is_bot
-/

#print not_is_top /-
@[simp]
theorem not_is_top [NoTopOrder α] (a : α) : ¬IsTop a := fun h =>
  let ⟨b, hb⟩ := exists_not_le a
  hb <| h _
#align not_is_top not_is_top
-/

#print IsBot.is_min /-
protected theorem IsBot.is_min (h : IsBot a) : IsMin a := fun b _ => h b
#align is_bot.is_min IsBot.is_min
-/

#print IsTop.is_max /-
protected theorem IsTop.is_max (h : IsTop a) : IsMax a := fun b _ => h b
#align is_top.is_max IsTop.is_max
-/

#print is_bot_to_dual_iff /-
@[simp]
theorem is_bot_to_dual_iff : IsBot (toDual a) ↔ IsTop a :=
  Iff.rfl
#align is_bot_to_dual_iff is_bot_to_dual_iff
-/

#print is_top_to_dual_iff /-
@[simp]
theorem is_top_to_dual_iff : IsTop (toDual a) ↔ IsBot a :=
  Iff.rfl
#align is_top_to_dual_iff is_top_to_dual_iff
-/

#print is_min_to_dual_iff /-
@[simp]
theorem is_min_to_dual_iff : IsMin (toDual a) ↔ IsMax a :=
  Iff.rfl
#align is_min_to_dual_iff is_min_to_dual_iff
-/

#print is_max_to_dual_iff /-
@[simp]
theorem is_max_to_dual_iff : IsMax (toDual a) ↔ IsMin a :=
  Iff.rfl
#align is_max_to_dual_iff is_max_to_dual_iff
-/

#print is_bot_of_dual_iff /-
@[simp]
theorem is_bot_of_dual_iff {a : αᵒᵈ} : IsBot (ofDual a) ↔ IsTop a :=
  Iff.rfl
#align is_bot_of_dual_iff is_bot_of_dual_iff
-/

#print is_top_of_dual_iff /-
@[simp]
theorem is_top_of_dual_iff {a : αᵒᵈ} : IsTop (ofDual a) ↔ IsBot a :=
  Iff.rfl
#align is_top_of_dual_iff is_top_of_dual_iff
-/

#print is_min_of_dual_iff /-
@[simp]
theorem is_min_of_dual_iff {a : αᵒᵈ} : IsMin (ofDual a) ↔ IsMax a :=
  Iff.rfl
#align is_min_of_dual_iff is_min_of_dual_iff
-/

#print is_max_of_dual_iff /-
@[simp]
theorem is_max_of_dual_iff {a : αᵒᵈ} : IsMax (ofDual a) ↔ IsMin a :=
  Iff.rfl
#align is_max_of_dual_iff is_max_of_dual_iff
-/

alias is_bot_to_dual_iff ↔ _ IsTop.to_dual

alias is_top_to_dual_iff ↔ _ IsBot.to_dual

alias is_min_to_dual_iff ↔ _ IsMax.to_dual

alias is_max_to_dual_iff ↔ _ IsMin.to_dual

alias is_bot_of_dual_iff ↔ _ IsTop.of_dual

alias is_top_of_dual_iff ↔ _ IsBot.of_dual

alias is_min_of_dual_iff ↔ _ IsMax.of_dual

alias is_max_of_dual_iff ↔ _ IsMin.of_dual

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

#print not_is_min_of_lt /-
@[simp]
theorem not_is_min_of_lt (h : b < a) : ¬IsMin a := fun ha => ha.not_lt h
#align not_is_min_of_lt not_is_min_of_lt
-/

#print not_is_max_of_lt /-
@[simp]
theorem not_is_max_of_lt (h : a < b) : ¬IsMax a := fun ha => ha.not_lt h
#align not_is_max_of_lt not_is_max_of_lt
-/

alias not_is_min_of_lt ← LT.lt.not_is_min

alias not_is_max_of_lt ← LT.lt.not_is_max

#print is_min_iff_forall_not_lt /-
theorem is_min_iff_forall_not_lt : IsMin a ↔ ∀ b, ¬b < a :=
  ⟨fun h _ => h.not_lt, fun h b hba => of_not_not fun hab => h _ <| hba.lt_of_not_le hab⟩
#align is_min_iff_forall_not_lt is_min_iff_forall_not_lt
-/

#print is_max_iff_forall_not_lt /-
theorem is_max_iff_forall_not_lt : IsMax a ↔ ∀ b, ¬a < b :=
  ⟨fun h _ => h.not_lt, fun h b hba => of_not_not fun hab => h _ <| hba.lt_of_not_le hab⟩
#align is_max_iff_forall_not_lt is_max_iff_forall_not_lt
-/

#print not_is_min_iff /-
@[simp]
theorem not_is_min_iff : ¬IsMin a ↔ ∃ b, b < a := by simp_rw [lt_iff_le_not_le, IsMin, not_forall, exists_prop]
#align not_is_min_iff not_is_min_iff
-/

#print not_is_max_iff /-
@[simp]
theorem not_is_max_iff : ¬IsMax a ↔ ∃ b, a < b := by simp_rw [lt_iff_le_not_le, IsMax, not_forall, exists_prop]
#align not_is_max_iff not_is_max_iff
-/

#print not_is_min /-
@[simp]
theorem not_is_min [NoMinOrder α] (a : α) : ¬IsMin a :=
  not_is_min_iff.2 <| exists_lt a
#align not_is_min not_is_min
-/

#print not_is_max /-
@[simp]
theorem not_is_max [NoMaxOrder α] (a : α) : ¬IsMax a :=
  not_is_max_iff.2 <| exists_gt a
#align not_is_max not_is_max
-/

namespace Subsingleton

variable [Subsingleton α]

#print Subsingleton.is_bot /-
protected theorem is_bot (a : α) : IsBot a := fun _ => (Subsingleton.elim _ _).le
#align subsingleton.is_bot Subsingleton.is_bot
-/

#print Subsingleton.is_top /-
protected theorem is_top (a : α) : IsTop a := fun _ => (Subsingleton.elim _ _).le
#align subsingleton.is_top Subsingleton.is_top
-/

#print Subsingleton.is_min /-
protected theorem is_min (a : α) : IsMin a :=
  (Subsingleton.is_bot _).IsMin
#align subsingleton.is_min Subsingleton.is_min
-/

#print Subsingleton.is_max /-
protected theorem is_max (a : α) : IsMax a :=
  (Subsingleton.is_top _).IsMax
#align subsingleton.is_max Subsingleton.is_max
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
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {a : α} {b : β}, (IsBot.{u_2} α (Preorder.toLE.{u_2} α _inst_1) a) -> (IsBot.{u_3} β (Preorder.toLE.{u_3} β _inst_2) b) -> (IsBot.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) (Prod.mk.{u_2 u_3} α β a b))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.1736 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.1739 : Preorder.{u_2} β] {a : α} {b : β}, (IsBot.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.1736) a) -> (IsBot.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.1739) b) -> (IsBot.{(max u_2 u_1)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.1736) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.1739)) (Prod.mk.{u_1 u_2} α β a b))
Case conversion may be inaccurate. Consider using '#align is_bot.prod_mk IsBot.prod_mkₓ'. -/
theorem IsBot.prod_mk (ha : IsBot a) (hb : IsBot b) : IsBot (a, b) := fun c => ⟨ha _, hb _⟩
#align is_bot.prod_mk IsBot.prod_mk

/- warning: is_top.prod_mk -> IsTop.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {a : α} {b : β}, (IsTop.{u_2} α (Preorder.toLE.{u_2} α _inst_1) a) -> (IsTop.{u_3} β (Preorder.toLE.{u_3} β _inst_2) b) -> (IsTop.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) (Prod.mk.{u_2 u_3} α β a b))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.1785 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.1788 : Preorder.{u_2} β] {a : α} {b : β}, (IsTop.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.1785) a) -> (IsTop.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.1788) b) -> (IsTop.{(max u_2 u_1)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.1785) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.1788)) (Prod.mk.{u_1 u_2} α β a b))
Case conversion may be inaccurate. Consider using '#align is_top.prod_mk IsTop.prod_mkₓ'. -/
theorem IsTop.prod_mk (ha : IsTop a) (hb : IsTop b) : IsTop (a, b) := fun c => ⟨ha _, hb _⟩
#align is_top.prod_mk IsTop.prod_mk

/- warning: is_min.prod_mk -> IsMin.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {a : α} {b : β}, (IsMin.{u_2} α (Preorder.toLE.{u_2} α _inst_1) a) -> (IsMin.{u_3} β (Preorder.toLE.{u_3} β _inst_2) b) -> (IsMin.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) (Prod.mk.{u_2 u_3} α β a b))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.1834 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.1837 : Preorder.{u_2} β] {a : α} {b : β}, (IsMin.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.1834) a) -> (IsMin.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.1837) b) -> (IsMin.{(max u_2 u_1)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.1834) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.1837)) (Prod.mk.{u_1 u_2} α β a b))
Case conversion may be inaccurate. Consider using '#align is_min.prod_mk IsMin.prod_mkₓ'. -/
theorem IsMin.prod_mk (ha : IsMin a) (hb : IsMin b) : IsMin (a, b) := fun c hc => ⟨ha hc.1, hb hc.2⟩
#align is_min.prod_mk IsMin.prod_mk

/- warning: is_max.prod_mk -> IsMax.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {a : α} {b : β}, (IsMax.{u_2} α (Preorder.toLE.{u_2} α _inst_1) a) -> (IsMax.{u_3} β (Preorder.toLE.{u_3} β _inst_2) b) -> (IsMax.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) (Prod.mk.{u_2 u_3} α β a b))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.1884 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.1887 : Preorder.{u_2} β] {a : α} {b : β}, (IsMax.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.1884) a) -> (IsMax.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.1887) b) -> (IsMax.{(max u_2 u_1)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.1884) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.1887)) (Prod.mk.{u_1 u_2} α β a b))
Case conversion may be inaccurate. Consider using '#align is_max.prod_mk IsMax.prod_mkₓ'. -/
theorem IsMax.prod_mk (ha : IsMax a) (hb : IsMax b) : IsMax (a, b) := fun c hc => ⟨ha hc.1, hb hc.2⟩
#align is_max.prod_mk IsMax.prod_mk

/- warning: is_bot.fst -> IsBot.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {x : Prod.{u_2 u_3} α β}, (IsBot.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) x) -> (IsBot.{u_2} α (Preorder.toLE.{u_2} α _inst_1) (Prod.fst.{u_2 u_3} α β x))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.1934 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.1937 : Preorder.{u_2} β] {x : Prod.{u_1 u_2} α β}, (IsBot.{(max u_1 u_2)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.1934) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.1937)) x) -> (IsBot.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.1934) (Prod.fst.{u_1 u_2} α β x))
Case conversion may be inaccurate. Consider using '#align is_bot.fst IsBot.fstₓ'. -/
theorem IsBot.fst (hx : IsBot x) : IsBot x.1 := fun c => (hx (c, x.2)).1
#align is_bot.fst IsBot.fst

/- warning: is_bot.snd -> IsBot.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {x : Prod.{u_2 u_3} α β}, (IsBot.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) x) -> (IsBot.{u_3} β (Preorder.toLE.{u_3} β _inst_2) (Prod.snd.{u_2 u_3} α β x))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.1979 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.1982 : Preorder.{u_2} β] {x : Prod.{u_1 u_2} α β}, (IsBot.{(max u_1 u_2)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.1979) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.1982)) x) -> (IsBot.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.1982) (Prod.snd.{u_1 u_2} α β x))
Case conversion may be inaccurate. Consider using '#align is_bot.snd IsBot.sndₓ'. -/
theorem IsBot.snd (hx : IsBot x) : IsBot x.2 := fun c => (hx (x.1, c)).2
#align is_bot.snd IsBot.snd

/- warning: is_top.fst -> IsTop.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {x : Prod.{u_2 u_3} α β}, (IsTop.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) x) -> (IsTop.{u_2} α (Preorder.toLE.{u_2} α _inst_1) (Prod.fst.{u_2 u_3} α β x))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.2024 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.2027 : Preorder.{u_2} β] {x : Prod.{u_1 u_2} α β}, (IsTop.{(max u_1 u_2)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2024) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2027)) x) -> (IsTop.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2024) (Prod.fst.{u_1 u_2} α β x))
Case conversion may be inaccurate. Consider using '#align is_top.fst IsTop.fstₓ'. -/
theorem IsTop.fst (hx : IsTop x) : IsTop x.1 := fun c => (hx (c, x.2)).1
#align is_top.fst IsTop.fst

/- warning: is_top.snd -> IsTop.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {x : Prod.{u_2 u_3} α β}, (IsTop.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) x) -> (IsTop.{u_3} β (Preorder.toLE.{u_3} β _inst_2) (Prod.snd.{u_2 u_3} α β x))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.2069 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.2072 : Preorder.{u_2} β] {x : Prod.{u_1 u_2} α β}, (IsTop.{(max u_1 u_2)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2069) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2072)) x) -> (IsTop.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2072) (Prod.snd.{u_1 u_2} α β x))
Case conversion may be inaccurate. Consider using '#align is_top.snd IsTop.sndₓ'. -/
theorem IsTop.snd (hx : IsTop x) : IsTop x.2 := fun c => (hx (x.1, c)).2
#align is_top.snd IsTop.snd

/- warning: is_min.fst -> IsMin.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {x : Prod.{u_2 u_3} α β}, (IsMin.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) x) -> (IsMin.{u_2} α (Preorder.toLE.{u_2} α _inst_1) (Prod.fst.{u_2 u_3} α β x))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.2114 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.2117 : Preorder.{u_2} β] {x : Prod.{u_1 u_2} α β}, (IsMin.{(max u_1 u_2)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2114) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2117)) x) -> (IsMin.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2114) (Prod.fst.{u_1 u_2} α β x))
Case conversion may be inaccurate. Consider using '#align is_min.fst IsMin.fstₓ'. -/
theorem IsMin.fst (hx : IsMin x) : IsMin x.1 := fun c hc => (hx <| show (c, x.2) ≤ x from (and_iff_left le_rfl).2 hc).1
#align is_min.fst IsMin.fst

/- warning: is_min.snd -> IsMin.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {x : Prod.{u_2 u_3} α β}, (IsMin.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) x) -> (IsMin.{u_3} β (Preorder.toLE.{u_3} β _inst_2) (Prod.snd.{u_2 u_3} α β x))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.2177 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.2180 : Preorder.{u_2} β] {x : Prod.{u_1 u_2} α β}, (IsMin.{(max u_1 u_2)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2177) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2180)) x) -> (IsMin.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2180) (Prod.snd.{u_1 u_2} α β x))
Case conversion may be inaccurate. Consider using '#align is_min.snd IsMin.sndₓ'. -/
theorem IsMin.snd (hx : IsMin x) : IsMin x.2 := fun c hc => (hx <| show (x.1, c) ≤ x from (and_iff_right le_rfl).2 hc).2
#align is_min.snd IsMin.snd

/- warning: is_max.fst -> IsMax.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {x : Prod.{u_2 u_3} α β}, (IsMax.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) x) -> (IsMax.{u_2} α (Preorder.toLE.{u_2} α _inst_1) (Prod.fst.{u_2 u_3} α β x))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.2240 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.2243 : Preorder.{u_2} β] {x : Prod.{u_1 u_2} α β}, (IsMax.{(max u_1 u_2)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2240) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2243)) x) -> (IsMax.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2240) (Prod.fst.{u_1 u_2} α β x))
Case conversion may be inaccurate. Consider using '#align is_max.fst IsMax.fstₓ'. -/
theorem IsMax.fst (hx : IsMax x) : IsMax x.1 := fun c hc => (hx <| show x ≤ (c, x.2) from (and_iff_left le_rfl).2 hc).1
#align is_max.fst IsMax.fst

/- warning: is_max.snd -> IsMax.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {x : Prod.{u_2 u_3} α β}, (IsMax.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) x) -> (IsMax.{u_3} β (Preorder.toLE.{u_3} β _inst_2) (Prod.snd.{u_2 u_3} α β x))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.2303 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.2306 : Preorder.{u_2} β] {x : Prod.{u_1 u_2} α β}, (IsMax.{(max u_1 u_2)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2303) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2306)) x) -> (IsMax.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2306) (Prod.snd.{u_1 u_2} α β x))
Case conversion may be inaccurate. Consider using '#align is_max.snd IsMax.sndₓ'. -/
theorem IsMax.snd (hx : IsMax x) : IsMax x.2 := fun c hc => (hx <| show x ≤ (x.1, c) from (and_iff_right le_rfl).2 hc).2
#align is_max.snd IsMax.snd

/- warning: prod.is_bot_iff -> Prod.is_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {x : Prod.{u_2 u_3} α β}, Iff (IsBot.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) x) (And (IsBot.{u_2} α (Preorder.toLE.{u_2} α _inst_1) (Prod.fst.{u_2 u_3} α β x)) (IsBot.{u_3} β (Preorder.toLE.{u_3} β _inst_2) (Prod.snd.{u_2 u_3} α β x)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.2366 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.2369 : Preorder.{u_2} β] {x : Prod.{u_1 u_2} α β}, Iff (IsBot.{(max u_1 u_2)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2366) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2369)) x) (And (IsBot.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2366) (Prod.fst.{u_1 u_2} α β x)) (IsBot.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2369) (Prod.snd.{u_1 u_2} α β x)))
Case conversion may be inaccurate. Consider using '#align prod.is_bot_iff Prod.is_bot_iffₓ'. -/
theorem Prod.is_bot_iff : IsBot x ↔ IsBot x.1 ∧ IsBot x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩
#align prod.is_bot_iff Prod.is_bot_iff

/- warning: prod.is_top_iff -> Prod.is_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {x : Prod.{u_2 u_3} α β}, Iff (IsTop.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) x) (And (IsTop.{u_2} α (Preorder.toLE.{u_2} α _inst_1) (Prod.fst.{u_2 u_3} α β x)) (IsTop.{u_3} β (Preorder.toLE.{u_3} β _inst_2) (Prod.snd.{u_2 u_3} α β x)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.2421 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.2424 : Preorder.{u_2} β] {x : Prod.{u_1 u_2} α β}, Iff (IsTop.{(max u_1 u_2)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2421) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2424)) x) (And (IsTop.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2421) (Prod.fst.{u_1 u_2} α β x)) (IsTop.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2424) (Prod.snd.{u_1 u_2} α β x)))
Case conversion may be inaccurate. Consider using '#align prod.is_top_iff Prod.is_top_iffₓ'. -/
theorem Prod.is_top_iff : IsTop x ↔ IsTop x.1 ∧ IsTop x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩
#align prod.is_top_iff Prod.is_top_iff

/- warning: prod.is_min_iff -> Prod.is_min_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {x : Prod.{u_2 u_3} α β}, Iff (IsMin.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) x) (And (IsMin.{u_2} α (Preorder.toLE.{u_2} α _inst_1) (Prod.fst.{u_2 u_3} α β x)) (IsMin.{u_3} β (Preorder.toLE.{u_3} β _inst_2) (Prod.snd.{u_2 u_3} α β x)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.2476 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.2479 : Preorder.{u_2} β] {x : Prod.{u_1 u_2} α β}, Iff (IsMin.{(max u_1 u_2)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2476) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2479)) x) (And (IsMin.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2476) (Prod.fst.{u_1 u_2} α β x)) (IsMin.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2479) (Prod.snd.{u_1 u_2} α β x)))
Case conversion may be inaccurate. Consider using '#align prod.is_min_iff Prod.is_min_iffₓ'. -/
theorem Prod.is_min_iff : IsMin x ↔ IsMin x.1 ∧ IsMin x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩
#align prod.is_min_iff Prod.is_min_iff

/- warning: prod.is_max_iff -> Prod.is_max_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : Preorder.{u_2} α] [_inst_2 : Preorder.{u_3} β] {x : Prod.{u_2 u_3} α β}, Iff (IsMax.{(max u_2 u_3)} (Prod.{u_2 u_3} α β) (Prod.hasLe.{u_2 u_3} α β (Preorder.toLE.{u_2} α _inst_1) (Preorder.toLE.{u_3} β _inst_2)) x) (And (IsMax.{u_2} α (Preorder.toLE.{u_2} α _inst_1) (Prod.fst.{u_2 u_3} α β x)) (IsMax.{u_3} β (Preorder.toLE.{u_3} β _inst_2) (Prod.snd.{u_2 u_3} α β x)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.Max._hyg.2531 : Preorder.{u_1} α] [inst._@.Mathlib.Order.Max._hyg.2534 : Preorder.{u_2} β] {x : Prod.{u_1 u_2} α β}, Iff (IsMax.{(max u_1 u_2)} (Prod.{u_1 u_2} α β) (Prod.instLEProd.{u_1 u_2} α β (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2531) (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2534)) x) (And (IsMax.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.Max._hyg.2531) (Prod.fst.{u_1 u_2} α β x)) (IsMax.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.Max._hyg.2534) (Prod.snd.{u_1 u_2} α β x)))
Case conversion may be inaccurate. Consider using '#align prod.is_max_iff Prod.is_max_iffₓ'. -/
theorem Prod.is_max_iff : IsMax x ↔ IsMax x.1 ∧ IsMax x.2 :=
  ⟨fun hx => ⟨hx.fst, hx.snd⟩, fun h => h.1.prod_mk h.2⟩
#align prod.is_max_iff Prod.is_max_iff

end Prod

