/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Order.Lattice
import Mathbin.Data.Option.Basic

/-!
# ⊤ and ⊥, bounded lattices and variants

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/697
> Any changes to this file require a corresponding PR to mathlib4.

This file defines top and bottom elements (greatest and least elements) of a type, the bounded
variants of different kinds of lattices, sets up the typeclass hierarchy between them and provides
instances for `Prop` and `fun`.

## Main declarations

* `has_<top/bot> α`: Typeclasses to declare the `⊤`/`⊥` notation.
* `order_<top/bot> α`: Order with a top/bottom element.
* `bounded_order α`: Order with a top and bottom element.

## Common lattices

* Distributive lattices with a bottom element. Notated by `[distrib_lattice α] [order_bot α]`
  It captures the properties of `disjoint` that are common to `generalized_boolean_algebra` and
  `distrib_lattice` when `order_bot`.
* Bounded and distributive lattice. Notated by `[distrib_lattice α] [bounded_order α]`.
  Typical examples include `Prop` and `set α`.
-/


open Function OrderDual

universe u v

variable {α : Type u} {β : Type v} {γ δ : Type _}

/-! ### Top, bottom element -/


#print Top /-
/-- Typeclass for the `⊤` (`\top`) notation -/
@[notation_class]
class Top (α : Type u) where
  top : α
#align has_top Top
-/

#print Bot /-
/-- Typeclass for the `⊥` (`\bot`) notation -/
@[notation_class]
class Bot (α : Type u) where
  bot : α
#align has_bot Bot
-/

-- mathport name: «expr⊤»
notation "⊤" => Top.top

-- mathport name: «expr⊥»
notation "⊥" => Bot.bot

#print top_nonempty /-
instance (priority := 100) top_nonempty (α : Type u) [Top α] : Nonempty α :=
  ⟨⊤⟩
#align has_top_nonempty top_nonempty
-/

#print bot_nonempty /-
instance (priority := 100) bot_nonempty (α : Type u) [Bot α] : Nonempty α :=
  ⟨⊥⟩
#align has_bot_nonempty bot_nonempty
-/

attribute [match_pattern] Bot.bot Top.top

#print OrderTop /-
/-- An order is an `order_top` if it has a greatest element.
We state this using a data mixin, holding the value of `⊤` and the greatest element constraint. -/
class OrderTop (α : Type u) [LE α] extends Top α where
  le_top : ∀ a : α, a ≤ ⊤
#align order_top OrderTop
-/

section OrderTop

#print topOrderOrNoTopOrder /-
/-- An order is (noncomputably) either an `order_top` or a `no_order_top`. Use as
`casesI bot_order_or_no_bot_order α`. -/
noncomputable def topOrderOrNoTopOrder (α : Type _) [LE α] : PSum (OrderTop α) (NoTopOrder α) := by
  by_cases H : ∀ a : α, ∃ b, ¬b ≤ a
  · exact PSum.inr ⟨H⟩
  · push_neg  at H
    exact PSum.inl ⟨_, Classical.choose_spec H⟩
#align top_order_or_no_top_order topOrderOrNoTopOrder
-/

section LE

variable [LE α] [OrderTop α] {a : α}

/- warning: le_top -> le_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LE.{u} α] [_inst_2 : OrderTop.{u} α _inst_1] {a : α}, LE.le.{u} α _inst_1 a (Top.top.{u} α (OrderTop.toHasTop.{u} α _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.965 : LE.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.968 : OrderTop.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.965] {a : α}, LE.le.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.965 a (Top.top.{u} α (OrderTop.toTop.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.965 inst._@.Mathlib.Order.BoundedOrder._hyg.968))
Case conversion may be inaccurate. Consider using '#align le_top le_topₓ'. -/
@[simp]
theorem le_top : a ≤ ⊤ :=
  OrderTop.le_top a
#align le_top le_top

/- warning: is_top_top -> isTop_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LE.{u} α] [_inst_2 : OrderTop.{u} α _inst_1], IsTop.{u} α _inst_1 (Top.top.{u} α (OrderTop.toHasTop.{u} α _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.988 : LE.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.991 : OrderTop.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.988], IsTop.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.988 (Top.top.{u} α (OrderTop.toTop.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.988 inst._@.Mathlib.Order.BoundedOrder._hyg.991))
Case conversion may be inaccurate. Consider using '#align is_top_top isTop_topₓ'. -/
@[simp]
theorem isTop_top : IsTop (⊤ : α) := fun _ => le_top
#align is_top_top isTop_top

end LE

section Preorder

variable [Preorder α] [OrderTop α] {a b : α}

/- warning: is_max_top -> isMax_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Preorder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α _inst_1)], IsMax.{u} α (Preorder.toLE.{u} α _inst_1) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α _inst_1) _inst_2))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1032 : Preorder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1035 : OrderTop.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1032)], IsMax.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1032) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1032) inst._@.Mathlib.Order.BoundedOrder._hyg.1035))
Case conversion may be inaccurate. Consider using '#align is_max_top isMax_topₓ'. -/
@[simp]
theorem isMax_top : IsMax (⊤ : α) :=
  isTop_top.IsMax
#align is_max_top isMax_top

/- warning: not_top_lt -> not_top_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Preorder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α _inst_1)] {a : α}, Not (LT.lt.{u} α (Preorder.toLT.{u} α _inst_1) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α _inst_1) _inst_2)) a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1054 : Preorder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1057 : OrderTop.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1054)] {a : α}, Not (LT.lt.{u} α (Preorder.toLT.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1054) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1054) inst._@.Mathlib.Order.BoundedOrder._hyg.1057)) a)
Case conversion may be inaccurate. Consider using '#align not_top_lt not_top_ltₓ'. -/
@[simp]
theorem not_top_lt : ¬⊤ < a :=
  isMax_top.not_lt
#align not_top_lt not_top_lt

/- warning: ne_top_of_lt -> ne_top_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Preorder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α _inst_1)] {a : α} {b : α}, (LT.lt.{u} α (Preorder.toLT.{u} α _inst_1) a b) -> (Ne.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α _inst_1) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1080 : Preorder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1083 : OrderTop.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1080)] {a : α} {b : α}, (LT.lt.{u} α (Preorder.toLT.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1080) a b) -> (Ne.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1080) inst._@.Mathlib.Order.BoundedOrder._hyg.1083)))
Case conversion may be inaccurate. Consider using '#align ne_top_of_lt ne_top_of_ltₓ'. -/
theorem ne_top_of_lt (h : a < b) : a ≠ ⊤ :=
  (h.trans_le le_top).Ne
#align ne_top_of_lt ne_top_of_lt

alias ne_top_of_lt ← LT.lt.ne_top

end Preorder

variable [PartialOrder α] [OrderTop α] [Preorder β] {f : α → β} {a b : α}

/- warning: is_max_iff_eq_top -> isMax_iff_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (IsMax.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a) (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1138 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1141 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1138))] {a : α}, Iff (IsMax.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1138)) a) (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1138)) inst._@.Mathlib.Order.BoundedOrder._hyg.1141)))
Case conversion may be inaccurate. Consider using '#align is_max_iff_eq_top isMax_iff_eq_topₓ'. -/
@[simp]
theorem isMax_iff_eq_top : IsMax a ↔ a = ⊤ :=
  ⟨fun h => h.eq_of_le le_top, fun h b _ => h.symm ▸ le_top⟩
#align is_max_iff_eq_top isMax_iff_eq_top

/- warning: is_top_iff_eq_top -> isTop_iff_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (IsTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a) (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1190 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1193 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1190))] {a : α}, Iff (IsTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1190)) a) (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1190)) inst._@.Mathlib.Order.BoundedOrder._hyg.1193)))
Case conversion may be inaccurate. Consider using '#align is_top_iff_eq_top isTop_iff_eq_topₓ'. -/
@[simp]
theorem isTop_iff_eq_top : IsTop a ↔ a = ⊤ :=
  ⟨fun h => h.IsMax.eq_of_le le_top, fun h b => h.symm ▸ le_top⟩
#align is_top_iff_eq_top isTop_iff_eq_top

/- warning: not_is_max_iff_ne_top -> not_isMax_iff_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (Not (IsMax.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a)) (Ne.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1240 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1243 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1240))] {a : α}, Iff (Not (IsMax.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1240)) a)) (Ne.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1240)) inst._@.Mathlib.Order.BoundedOrder._hyg.1243)))
Case conversion may be inaccurate. Consider using '#align not_is_max_iff_ne_top not_isMax_iff_ne_topₓ'. -/
theorem not_isMax_iff_ne_top : ¬IsMax a ↔ a ≠ ⊤ :=
  isMax_iff_eq_top.Not
#align not_is_max_iff_ne_top not_isMax_iff_ne_top

/- warning: not_is_top_iff_ne_top -> not_isTop_iff_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (Not (IsTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a)) (Ne.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1276 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1279 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1276))] {a : α}, Iff (Not (IsTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1276)) a)) (Ne.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1276)) inst._@.Mathlib.Order.BoundedOrder._hyg.1279)))
Case conversion may be inaccurate. Consider using '#align not_is_top_iff_ne_top not_isTop_iff_ne_topₓ'. -/
theorem not_isTop_iff_ne_top : ¬IsTop a ↔ a ≠ ⊤ :=
  isTop_iff_eq_top.Not
#align not_is_top_iff_ne_top not_isTop_iff_ne_top

alias isMax_iff_eq_top ↔ IsMax.eq_top _

alias isTop_iff_eq_top ↔ IsTop.eq_top _

/- warning: top_le_iff -> top_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)) a) (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1314 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1317 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1314))] {a : α}, Iff (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1314)) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1314)) inst._@.Mathlib.Order.BoundedOrder._hyg.1317)) a) (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1314)) inst._@.Mathlib.Order.BoundedOrder._hyg.1317)))
Case conversion may be inaccurate. Consider using '#align top_le_iff top_le_iffₓ'. -/
@[simp]
theorem top_le_iff : ⊤ ≤ a ↔ a = ⊤ :=
  le_top.le_iff_eq.trans eq_comm
#align top_le_iff top_le_iff

/- warning: top_unique -> top_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)) a) -> (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1355 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1358 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1355))] {a : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1355)) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1355)) inst._@.Mathlib.Order.BoundedOrder._hyg.1358)) a) -> (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1355)) inst._@.Mathlib.Order.BoundedOrder._hyg.1358)))
Case conversion may be inaccurate. Consider using '#align top_unique top_uniqueₓ'. -/
theorem top_unique (h : ⊤ ≤ a) : a = ⊤ :=
  le_top.antisymm h
#align top_unique top_unique

/- warning: eq_top_iff -> eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)) a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1393 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1396 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1393))] {a : α}, Iff (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1393)) inst._@.Mathlib.Order.BoundedOrder._hyg.1396))) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1393)) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1393)) inst._@.Mathlib.Order.BoundedOrder._hyg.1396)) a)
Case conversion may be inaccurate. Consider using '#align eq_top_iff eq_top_iffₓ'. -/
theorem eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
  top_le_iff.symm
#align eq_top_iff eq_top_iff

/- warning: eq_top_mono -> eq_top_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α} {b : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a b) -> (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) -> (Eq.{succ u} α b (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1433 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1436 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1433))] {a : α} {b : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1433)) a b) -> (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1433)) inst._@.Mathlib.Order.BoundedOrder._hyg.1436))) -> (Eq.{succ u} α b (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1433)) inst._@.Mathlib.Order.BoundedOrder._hyg.1436)))
Case conversion may be inaccurate. Consider using '#align eq_top_mono eq_top_monoₓ'. -/
theorem eq_top_mono (h : a ≤ b) (h₂ : a = ⊤) : b = ⊤ :=
  top_unique <| h₂ ▸ h
#align eq_top_mono eq_top_mono

/- warning: lt_top_iff_ne_top -> lt_top_iff_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (Ne.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1482 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1485 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1482))] {a : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1482)) a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1482)) inst._@.Mathlib.Order.BoundedOrder._hyg.1485))) (Ne.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1482)) inst._@.Mathlib.Order.BoundedOrder._hyg.1485)))
Case conversion may be inaccurate. Consider using '#align lt_top_iff_ne_top lt_top_iff_ne_topₓ'. -/
theorem lt_top_iff_ne_top : a < ⊤ ↔ a ≠ ⊤ :=
  le_top.lt_iff_ne
#align lt_top_iff_ne_top lt_top_iff_ne_top

/- warning: not_lt_top_iff -> not_lt_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (Not (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))) (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1521 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1524 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1521))] {a : α}, Iff (Not (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1521)) a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1521)) inst._@.Mathlib.Order.BoundedOrder._hyg.1524)))) (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1521)) inst._@.Mathlib.Order.BoundedOrder._hyg.1524)))
Case conversion may be inaccurate. Consider using '#align not_lt_top_iff not_lt_top_iffₓ'. -/
@[simp]
theorem not_lt_top_iff : ¬a < ⊤ ↔ a = ⊤ :=
  lt_top_iff_ne_top.not_left
#align not_lt_top_iff not_lt_top_iff

/- warning: eq_top_or_lt_top -> eq_top_or_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] (a : α), Or (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1564 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1567 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1564))] (a : α), Or (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1564)) inst._@.Mathlib.Order.BoundedOrder._hyg.1567))) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1564)) a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1564)) inst._@.Mathlib.Order.BoundedOrder._hyg.1567)))
Case conversion may be inaccurate. Consider using '#align eq_top_or_lt_top eq_top_or_lt_topₓ'. -/
theorem eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤ :=
  le_top.eq_or_lt
#align eq_top_or_lt_top eq_top_or_lt_top

/- warning: ne.lt_top -> Ne.lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, (Ne.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1608 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1611 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1608))] {a : α}, (Ne.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1608)) inst._@.Mathlib.Order.BoundedOrder._hyg.1611))) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1608)) a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1608)) inst._@.Mathlib.Order.BoundedOrder._hyg.1611)))
Case conversion may be inaccurate. Consider using '#align ne.lt_top Ne.lt_topₓ'. -/
theorem Ne.lt_top (h : a ≠ ⊤) : a < ⊤ :=
  lt_top_iff_ne_top.mpr h
#align ne.lt_top Ne.lt_top

/- warning: ne.lt_top' -> Ne.lt_top' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, (Ne.{succ u} α (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)) a) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1649 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1652 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1649))] {a : α}, (Ne.{succ u} α (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1649)) inst._@.Mathlib.Order.BoundedOrder._hyg.1652)) a) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1649)) a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1649)) inst._@.Mathlib.Order.BoundedOrder._hyg.1652)))
Case conversion may be inaccurate. Consider using '#align ne.lt_top' Ne.lt_top'ₓ'. -/
theorem Ne.lt_top' (h : ⊤ ≠ a) : a < ⊤ :=
  h.symm.lt_top
#align ne.lt_top' Ne.lt_top'

/- warning: ne_top_of_le_ne_top -> ne_top_of_le_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α} {b : α}, (Ne.{succ u} α b (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a b) -> (Ne.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1686 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1689 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1686))] {a : α} {b : α}, (Ne.{succ u} α b (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1686)) inst._@.Mathlib.Order.BoundedOrder._hyg.1689))) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1686)) a b) -> (Ne.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1686)) inst._@.Mathlib.Order.BoundedOrder._hyg.1689)))
Case conversion may be inaccurate. Consider using '#align ne_top_of_le_ne_top ne_top_of_le_ne_topₓ'. -/
theorem ne_top_of_le_ne_top (hb : b ≠ ⊤) (hab : a ≤ b) : a ≠ ⊤ :=
  (hab.trans_lt hb.lt_top).Ne
#align ne_top_of_le_ne_top ne_top_of_le_ne_top

/- warning: strict_mono.apply_eq_top_iff -> StrictMono.apply_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : Preorder.{v} β] {f : α -> β} {a : α}, (StrictMono.{u, v} α β (PartialOrder.toPreorder.{u} α _inst_1) _inst_3 f) -> (Iff (Eq.{succ v} β (f a) (f (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))) (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1733 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1736 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1733))] [inst._@.Mathlib.Order.BoundedOrder._hyg.1739 : Preorder.{v} β] {f : α -> β} {a : α}, (StrictMono.{u, v} α β (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1733) inst._@.Mathlib.Order.BoundedOrder._hyg.1739 f) -> (Iff (Eq.{succ v} β (f a) (f (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1733)) inst._@.Mathlib.Order.BoundedOrder._hyg.1736)))) (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1733)) inst._@.Mathlib.Order.BoundedOrder._hyg.1736))))
Case conversion may be inaccurate. Consider using '#align strict_mono.apply_eq_top_iff StrictMono.apply_eq_top_iffₓ'. -/
theorem StrictMono.apply_eq_top_iff (hf : StrictMono f) : f a = f ⊤ ↔ a = ⊤ :=
  ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).Ne h, congr_arg _⟩
#align strict_mono.apply_eq_top_iff StrictMono.apply_eq_top_iff

/- warning: strict_anti.apply_eq_top_iff -> StrictAnti.apply_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : Preorder.{v} β] {f : α -> β} {a : α}, (StrictAnti.{u, v} α β (PartialOrder.toPreorder.{u} α _inst_1) _inst_3 f) -> (Iff (Eq.{succ v} β (f a) (f (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))) (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1796 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1799 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1796))] [inst._@.Mathlib.Order.BoundedOrder._hyg.1802 : Preorder.{v} β] {f : α -> β} {a : α}, (StrictAnti.{u, v} α β (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1796) inst._@.Mathlib.Order.BoundedOrder._hyg.1802 f) -> (Iff (Eq.{succ v} β (f a) (f (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1796)) inst._@.Mathlib.Order.BoundedOrder._hyg.1799)))) (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1796)) inst._@.Mathlib.Order.BoundedOrder._hyg.1799))))
Case conversion may be inaccurate. Consider using '#align strict_anti.apply_eq_top_iff StrictAnti.apply_eq_top_iffₓ'. -/
theorem StrictAnti.apply_eq_top_iff (hf : StrictAnti f) : f a = f ⊤ ↔ a = ⊤ :=
  ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).ne' h, congr_arg _⟩
#align strict_anti.apply_eq_top_iff StrictAnti.apply_eq_top_iff

variable [Nontrivial α]

/- warning: not_is_min_top -> not_isMin_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_4 : Nontrivial.{u} α], Not (IsMin.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1879 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1882 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1879))] [inst._@.Mathlib.Order.BoundedOrder._hyg.1893 : Nontrivial.{u} α], Not (IsMin.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1879)) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1879)) inst._@.Mathlib.Order.BoundedOrder._hyg.1882)))
Case conversion may be inaccurate. Consider using '#align not_is_min_top not_isMin_topₓ'. -/
theorem not_isMin_top : ¬IsMin (⊤ : α) := fun h =>
  let ⟨a, ha⟩ := exists_ne (⊤ : α)
  ha <| top_le_iff.1 <| h le_top
#align not_is_min_top not_isMin_top

end OrderTop

/- warning: strict_mono.maximal_preimage_top -> StrictMono.maximal_preimage_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : Preorder.{v} β] [_inst_3 : OrderTop.{v} β (Preorder.toLE.{v} β _inst_2)] {f : α -> β}, (StrictMono.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))) _inst_2 f) -> (forall {a : α}, (Eq.{succ v} β (f a) (Top.top.{v} β (OrderTop.toHasTop.{v} β (Preorder.toLE.{v} β _inst_2) _inst_3))) -> (forall (x : α), LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) x a))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.BoundedOrder._hyg.1953 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.1956 : Preorder.{v} β] [inst._@.Mathlib.Order.BoundedOrder._hyg.1959 : OrderTop.{v} β (Preorder.toLE.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.1956)] {f : α -> β}, (StrictMono.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1953))))) inst._@.Mathlib.Order.BoundedOrder._hyg.1956 f) -> (forall {a : α}, (Eq.{succ v} β (f a) (Top.top.{v} β (OrderTop.toTop.{v} β (Preorder.toLE.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.1956) inst._@.Mathlib.Order.BoundedOrder._hyg.1959))) -> (forall (x : α), LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.1953)))))) x a))
Case conversion may be inaccurate. Consider using '#align strict_mono.maximal_preimage_top StrictMono.maximal_preimage_topₓ'. -/
theorem StrictMono.maximal_preimage_top [LinearOrder α] [Preorder β] [OrderTop β] {f : α → β}
    (H : StrictMono f) {a} (h_top : f a = ⊤) (x : α) : x ≤ a :=
  H.maximal_of_maximal_image
    (fun p => by 
      rw [h_top]
      exact le_top)
    x
#align strict_mono.maximal_preimage_top StrictMono.maximal_preimage_top

/- warning: order_top.ext_top -> OrderTop.ext_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {hA : PartialOrder.{u_1} α} (A : OrderTop.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hA))) {hB : PartialOrder.{u_1} α} (B : OrderTop.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hB))), (forall (x : α) (y : α), Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hA)) x y) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hB)) x y)) -> (Eq.{succ u_1} α (Top.top.{u_1} α (OrderTop.toHasTop.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hA)) A)) (Top.top.{u_1} α (OrderTop.toHasTop.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hB)) B)))
but is expected to have type
  forall {α : Type.{u_1}} {hA : PartialOrder.{u_1} α} (A : OrderTop.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hA))) {hB : PartialOrder.{u_1} α} (B : OrderTop.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hB))), (forall (x : α) (y : α), Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hA)) x y) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hB)) x y)) -> (Eq.{succ u_1} α (Top.top.{u_1} α (OrderTop.toTop.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hA)) A)) (Top.top.{u_1} α (OrderTop.toTop.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hB)) B)))
Case conversion may be inaccurate. Consider using '#align order_top.ext_top OrderTop.ext_topₓ'. -/
theorem OrderTop.ext_top {α} {hA : PartialOrder α} (A : OrderTop α) {hB : PartialOrder α}
    (B : OrderTop α)
    (H :
      ∀ x y : α,
        (haveI := hA
          x ≤ y) ↔
          x ≤ y) :
    (haveI := A
        ⊤ :
        α) =
      ⊤ :=
  top_unique <| by rw [← H] <;> apply le_top
#align order_top.ext_top OrderTop.ext_top

#print OrderTop.ext /-
theorem OrderTop.ext {α} [PartialOrder α] {A B : OrderTop α} : A = B := by
  have tt := OrderTop.ext_top A B fun _ _ => Iff.rfl
  cases' A with _ ha; cases' B with _ hb
  congr
  exact le_antisymm (hb _) (ha _)
#align order_top.ext OrderTop.ext
-/

#print OrderBot /-
/-- An order is an `order_bot` if it has a least element.
We state this using a data mixin, holding the value of `⊥` and the least element constraint. -/
class OrderBot (α : Type u) [LE α] extends Bot α where
  bot_le : ∀ a : α, ⊥ ≤ a
#align order_bot OrderBot
-/

section OrderBot

#print botOrderOrNoBotOrder /-
/-- An order is (noncomputably) either an `order_bot` or a `no_order_bot`. Use as
`casesI bot_order_or_no_bot_order α`. -/
noncomputable def botOrderOrNoBotOrder (α : Type _) [LE α] : PSum (OrderBot α) (NoBotOrder α) := by
  by_cases H : ∀ a : α, ∃ b, ¬a ≤ b
  · exact PSum.inr ⟨H⟩
  · push_neg  at H
    exact PSum.inl ⟨_, Classical.choose_spec H⟩
#align bot_order_or_no_bot_order botOrderOrNoBotOrder
-/

section LE

variable [LE α] [OrderBot α] {a : α}

/- warning: bot_le -> bot_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LE.{u} α] [_inst_2 : OrderBot.{u} α _inst_1] {a : α}, LE.le.{u} α _inst_1 (Bot.bot.{u} α (OrderBot.toHasBot.{u} α _inst_1 _inst_2)) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.2310 : LE.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.2313 : OrderBot.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2310] {a : α}, LE.le.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2310 (Bot.bot.{u} α (OrderBot.toBot.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2310 inst._@.Mathlib.Order.BoundedOrder._hyg.2313)) a
Case conversion may be inaccurate. Consider using '#align bot_le bot_leₓ'. -/
@[simp]
theorem bot_le : ⊥ ≤ a :=
  OrderBot.bot_le a
#align bot_le bot_le

/- warning: is_bot_bot -> isBot_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LE.{u} α] [_inst_2 : OrderBot.{u} α _inst_1], IsBot.{u} α _inst_1 (Bot.bot.{u} α (OrderBot.toHasBot.{u} α _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.2333 : LE.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.2336 : OrderBot.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2333], IsBot.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2333 (Bot.bot.{u} α (OrderBot.toBot.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2333 inst._@.Mathlib.Order.BoundedOrder._hyg.2336))
Case conversion may be inaccurate. Consider using '#align is_bot_bot isBot_botₓ'. -/
@[simp]
theorem isBot_bot : IsBot (⊥ : α) := fun _ => bot_le
#align is_bot_bot isBot_bot

end LE

namespace OrderDual

variable (α)

instance [Bot α] : Top αᵒᵈ :=
  ⟨(⊥ : α)⟩

instance [Top α] : Bot αᵒᵈ :=
  ⟨(⊤ : α)⟩

instance [LE α] [OrderBot α] : OrderTop αᵒᵈ :=
  { OrderDual.hasTop α with le_top := @bot_le α _ _ }

instance [LE α] [OrderTop α] : OrderBot αᵒᵈ :=
  { OrderDual.hasBot α with bot_le := @le_top α _ _ }

#print OrderDual.ofDual_bot /-
@[simp]
theorem ofDual_bot [Top α] : ofDual ⊥ = (⊤ : α) :=
  rfl
#align order_dual.of_dual_bot OrderDual.ofDual_bot
-/

#print OrderDual.ofDual_top /-
@[simp]
theorem ofDual_top [Bot α] : ofDual ⊤ = (⊥ : α) :=
  rfl
#align order_dual.of_dual_top OrderDual.ofDual_top
-/

#print OrderDual.toDual_bot /-
@[simp]
theorem toDual_bot [Bot α] : toDual (⊥ : α) = ⊤ :=
  rfl
#align order_dual.to_dual_bot OrderDual.toDual_bot
-/

#print OrderDual.toDual_top /-
@[simp]
theorem toDual_top [Top α] : toDual (⊤ : α) = ⊥ :=
  rfl
#align order_dual.to_dual_top OrderDual.toDual_top
-/

end OrderDual

section Preorder

variable [Preorder α] [OrderBot α] {a b : α}

/- warning: is_min_bot -> isMin_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Preorder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α _inst_1)], IsMin.{u} α (Preorder.toLE.{u} α _inst_1) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α _inst_1) _inst_2))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.2603 : Preorder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.2606 : OrderBot.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2603)], IsMin.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2603) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2603) inst._@.Mathlib.Order.BoundedOrder._hyg.2606))
Case conversion may be inaccurate. Consider using '#align is_min_bot isMin_botₓ'. -/
@[simp]
theorem isMin_bot : IsMin (⊥ : α) :=
  isBot_bot.IsMin
#align is_min_bot isMin_bot

/- warning: not_lt_bot -> not_lt_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Preorder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α _inst_1)] {a : α}, Not (LT.lt.{u} α (Preorder.toLT.{u} α _inst_1) a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α _inst_1) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.2625 : Preorder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.2628 : OrderBot.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2625)] {a : α}, Not (LT.lt.{u} α (Preorder.toLT.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2625) a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2625) inst._@.Mathlib.Order.BoundedOrder._hyg.2628)))
Case conversion may be inaccurate. Consider using '#align not_lt_bot not_lt_botₓ'. -/
@[simp]
theorem not_lt_bot : ¬a < ⊥ :=
  isMin_bot.not_lt
#align not_lt_bot not_lt_bot

/- warning: ne_bot_of_gt -> ne_bot_of_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Preorder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α _inst_1)] {a : α} {b : α}, (LT.lt.{u} α (Preorder.toLT.{u} α _inst_1) a b) -> (Ne.{succ u} α b (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α _inst_1) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.2651 : Preorder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.2654 : OrderBot.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2651)] {a : α} {b : α}, (LT.lt.{u} α (Preorder.toLT.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2651) a b) -> (Ne.{succ u} α b (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2651) inst._@.Mathlib.Order.BoundedOrder._hyg.2654)))
Case conversion may be inaccurate. Consider using '#align ne_bot_of_gt ne_bot_of_gtₓ'. -/
theorem ne_bot_of_gt (h : a < b) : b ≠ ⊥ :=
  (bot_le.trans_lt h).ne'
#align ne_bot_of_gt ne_bot_of_gt

alias ne_bot_of_gt ← LT.lt.ne_bot

end Preorder

variable [PartialOrder α] [OrderBot α] [Preorder β] {f : α → β} {a b : α}

/- warning: is_min_iff_eq_bot -> isMin_iff_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (IsMin.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a) (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.2709 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.2712 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2709))] {a : α}, Iff (IsMin.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2709)) a) (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2709)) inst._@.Mathlib.Order.BoundedOrder._hyg.2712)))
Case conversion may be inaccurate. Consider using '#align is_min_iff_eq_bot isMin_iff_eq_botₓ'. -/
@[simp]
theorem isMin_iff_eq_bot : IsMin a ↔ a = ⊥ :=
  ⟨fun h => h.eq_of_ge bot_le, fun h b _ => h.symm ▸ bot_le⟩
#align is_min_iff_eq_bot isMin_iff_eq_bot

/- warning: is_bot_iff_eq_bot -> isBot_iff_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (IsBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a) (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.2761 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.2764 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2761))] {a : α}, Iff (IsBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2761)) a) (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2761)) inst._@.Mathlib.Order.BoundedOrder._hyg.2764)))
Case conversion may be inaccurate. Consider using '#align is_bot_iff_eq_bot isBot_iff_eq_botₓ'. -/
@[simp]
theorem isBot_iff_eq_bot : IsBot a ↔ a = ⊥ :=
  ⟨fun h => h.IsMin.eq_of_ge bot_le, fun h b => h.symm ▸ bot_le⟩
#align is_bot_iff_eq_bot isBot_iff_eq_bot

/- warning: not_is_min_iff_ne_bot -> not_isMin_iff_ne_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (Not (IsMin.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a)) (Ne.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.2811 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.2814 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2811))] {a : α}, Iff (Not (IsMin.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2811)) a)) (Ne.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2811)) inst._@.Mathlib.Order.BoundedOrder._hyg.2814)))
Case conversion may be inaccurate. Consider using '#align not_is_min_iff_ne_bot not_isMin_iff_ne_botₓ'. -/
theorem not_isMin_iff_ne_bot : ¬IsMin a ↔ a ≠ ⊥ :=
  isMin_iff_eq_bot.Not
#align not_is_min_iff_ne_bot not_isMin_iff_ne_bot

/- warning: not_is_bot_iff_ne_bot -> not_isBot_iff_ne_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (Not (IsBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a)) (Ne.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.2847 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.2850 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2847))] {a : α}, Iff (Not (IsBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2847)) a)) (Ne.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2847)) inst._@.Mathlib.Order.BoundedOrder._hyg.2850)))
Case conversion may be inaccurate. Consider using '#align not_is_bot_iff_ne_bot not_isBot_iff_ne_botₓ'. -/
theorem not_isBot_iff_ne_bot : ¬IsBot a ↔ a ≠ ⊥ :=
  isBot_iff_eq_bot.Not
#align not_is_bot_iff_ne_bot not_isBot_iff_ne_bot

alias isMin_iff_eq_bot ↔ IsMin.eq_bot _

alias isBot_iff_eq_bot ↔ IsBot.eq_bot _

/- warning: le_bot_iff -> le_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.2885 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.2888 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2885))] {a : α}, Iff (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2885)) a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2885)) inst._@.Mathlib.Order.BoundedOrder._hyg.2888))) (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2885)) inst._@.Mathlib.Order.BoundedOrder._hyg.2888)))
Case conversion may be inaccurate. Consider using '#align le_bot_iff le_bot_iffₓ'. -/
@[simp]
theorem le_bot_iff : a ≤ ⊥ ↔ a = ⊥ :=
  bot_le.le_iff_eq
#align le_bot_iff le_bot_iff

/- warning: bot_unique -> bot_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) -> (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.2925 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.2928 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2925))] {a : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2925)) a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2925)) inst._@.Mathlib.Order.BoundedOrder._hyg.2928))) -> (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2925)) inst._@.Mathlib.Order.BoundedOrder._hyg.2928)))
Case conversion may be inaccurate. Consider using '#align bot_unique bot_uniqueₓ'. -/
theorem bot_unique (h : a ≤ ⊥) : a = ⊥ :=
  h.antisymm bot_le
#align bot_unique bot_unique

/- warning: eq_bot_iff -> eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.2963 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.2966 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2963))] {a : α}, Iff (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2963)) inst._@.Mathlib.Order.BoundedOrder._hyg.2966))) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2963)) a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.2963)) inst._@.Mathlib.Order.BoundedOrder._hyg.2966)))
Case conversion may be inaccurate. Consider using '#align eq_bot_iff eq_bot_iffₓ'. -/
theorem eq_bot_iff : a = ⊥ ↔ a ≤ ⊥ :=
  le_bot_iff.symm
#align eq_bot_iff eq_bot_iff

/- warning: eq_bot_mono -> eq_bot_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α} {b : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) a b) -> (Eq.{succ u} α b (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) -> (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3003 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3006 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3003))] {a : α} {b : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3003)) a b) -> (Eq.{succ u} α b (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3003)) inst._@.Mathlib.Order.BoundedOrder._hyg.3006))) -> (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3003)) inst._@.Mathlib.Order.BoundedOrder._hyg.3006)))
Case conversion may be inaccurate. Consider using '#align eq_bot_mono eq_bot_monoₓ'. -/
theorem eq_bot_mono (h : a ≤ b) (h₂ : b = ⊥) : a = ⊥ :=
  bot_unique <| h₂ ▸ h
#align eq_bot_mono eq_bot_mono

/- warning: bot_lt_iff_ne_bot -> bot_lt_iff_ne_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)) a) (Ne.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3052 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3055 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3052))] {a : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3052)) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3052)) inst._@.Mathlib.Order.BoundedOrder._hyg.3055)) a) (Ne.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3052)) inst._@.Mathlib.Order.BoundedOrder._hyg.3055)))
Case conversion may be inaccurate. Consider using '#align bot_lt_iff_ne_bot bot_lt_iff_ne_botₓ'. -/
theorem bot_lt_iff_ne_bot : ⊥ < a ↔ a ≠ ⊥ :=
  bot_le.lt_iff_ne.trans ne_comm
#align bot_lt_iff_ne_bot bot_lt_iff_ne_bot

/- warning: not_bot_lt_iff -> not_bot_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, Iff (Not (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)) a)) (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3092 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3095 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3092))] {a : α}, Iff (Not (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3092)) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3092)) inst._@.Mathlib.Order.BoundedOrder._hyg.3095)) a)) (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3092)) inst._@.Mathlib.Order.BoundedOrder._hyg.3095)))
Case conversion may be inaccurate. Consider using '#align not_bot_lt_iff not_bot_lt_iffₓ'. -/
@[simp]
theorem not_bot_lt_iff : ¬⊥ < a ↔ a = ⊥ :=
  bot_lt_iff_ne_bot.not_left
#align not_bot_lt_iff not_bot_lt_iff

/- warning: eq_bot_or_bot_lt -> eq_bot_or_bot_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] (a : α), Or (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)) a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3135 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3138 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3135))] (a : α), Or (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3135)) inst._@.Mathlib.Order.BoundedOrder._hyg.3138))) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3135)) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3135)) inst._@.Mathlib.Order.BoundedOrder._hyg.3138)) a)
Case conversion may be inaccurate. Consider using '#align eq_bot_or_bot_lt eq_bot_or_bot_ltₓ'. -/
theorem eq_bot_or_bot_lt (a : α) : a = ⊥ ∨ ⊥ < a :=
  bot_le.eq_or_gt
#align eq_bot_or_bot_lt eq_bot_or_bot_lt

/- warning: eq_bot_of_minimal -> eq_bot_of_minimal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, (forall (b : α), Not (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) b a)) -> (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3176 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3179 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3176))] {a : α}, (forall (b : α), Not (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3176)) b a)) -> (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3176)) inst._@.Mathlib.Order.BoundedOrder._hyg.3179)))
Case conversion may be inaccurate. Consider using '#align eq_bot_of_minimal eq_bot_of_minimalₓ'. -/
theorem eq_bot_of_minimal (h : ∀ b, ¬b < a) : a = ⊥ :=
  (eq_bot_or_bot_lt a).resolve_right (h ⊥)
#align eq_bot_of_minimal eq_bot_of_minimal

/- warning: ne.bot_lt -> Ne.bot_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, (Ne.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)) a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3229 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3232 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3229))] {a : α}, (Ne.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3229)) inst._@.Mathlib.Order.BoundedOrder._hyg.3232))) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3229)) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3229)) inst._@.Mathlib.Order.BoundedOrder._hyg.3232)) a)
Case conversion may be inaccurate. Consider using '#align ne.bot_lt Ne.bot_ltₓ'. -/
theorem Ne.bot_lt (h : a ≠ ⊥) : ⊥ < a :=
  bot_lt_iff_ne_bot.mpr h
#align ne.bot_lt Ne.bot_lt

/- warning: ne.bot_lt' -> Ne.bot_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α}, (Ne.{succ u} α (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)) a) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)) a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3270 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3273 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3270))] {a : α}, (Ne.{succ u} α (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3270)) inst._@.Mathlib.Order.BoundedOrder._hyg.3273)) a) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3270)) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3270)) inst._@.Mathlib.Order.BoundedOrder._hyg.3273)) a)
Case conversion may be inaccurate. Consider using '#align ne.bot_lt' Ne.bot_lt'ₓ'. -/
theorem Ne.bot_lt' (h : ⊥ ≠ a) : ⊥ < a :=
  h.symm.bot_lt
#align ne.bot_lt' Ne.bot_lt'

/- warning: ne_bot_of_le_ne_bot -> ne_bot_of_le_ne_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] {a : α} {b : α}, (Ne.{succ u} α b (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) b a) -> (Ne.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3307 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3310 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3307))] {a : α} {b : α}, (Ne.{succ u} α b (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3307)) inst._@.Mathlib.Order.BoundedOrder._hyg.3310))) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3307)) b a) -> (Ne.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3307)) inst._@.Mathlib.Order.BoundedOrder._hyg.3310)))
Case conversion may be inaccurate. Consider using '#align ne_bot_of_le_ne_bot ne_bot_of_le_ne_botₓ'. -/
theorem ne_bot_of_le_ne_bot (hb : b ≠ ⊥) (hab : b ≤ a) : a ≠ ⊥ :=
  (hb.bot_lt.trans_le hab).ne'
#align ne_bot_of_le_ne_bot ne_bot_of_le_ne_bot

/- warning: strict_mono.apply_eq_bot_iff -> StrictMono.apply_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : Preorder.{v} β] {f : α -> β} {a : α}, (StrictMono.{u, v} α β (PartialOrder.toPreorder.{u} α _inst_1) _inst_3 f) -> (Iff (Eq.{succ v} β (f a) (f (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))) (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3354 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3357 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3354))] [inst._@.Mathlib.Order.BoundedOrder._hyg.3360 : Preorder.{v} β] {f : α -> β} {a : α}, (StrictMono.{u, v} α β (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3354) inst._@.Mathlib.Order.BoundedOrder._hyg.3360 f) -> (Iff (Eq.{succ v} β (f a) (f (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3354)) inst._@.Mathlib.Order.BoundedOrder._hyg.3357)))) (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3354)) inst._@.Mathlib.Order.BoundedOrder._hyg.3357))))
Case conversion may be inaccurate. Consider using '#align strict_mono.apply_eq_bot_iff StrictMono.apply_eq_bot_iffₓ'. -/
theorem StrictMono.apply_eq_bot_iff (hf : StrictMono f) : f a = f ⊥ ↔ a = ⊥ :=
  hf.dual.apply_eq_top_iff
#align strict_mono.apply_eq_bot_iff StrictMono.apply_eq_bot_iff

/- warning: strict_anti.apply_eq_bot_iff -> StrictAnti.apply_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : Preorder.{v} β] {f : α -> β} {a : α}, (StrictAnti.{u, v} α β (PartialOrder.toPreorder.{u} α _inst_1) _inst_3 f) -> (Iff (Eq.{succ v} β (f a) (f (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))) (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3401 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3404 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3401))] [inst._@.Mathlib.Order.BoundedOrder._hyg.3407 : Preorder.{v} β] {f : α -> β} {a : α}, (StrictAnti.{u, v} α β (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3401) inst._@.Mathlib.Order.BoundedOrder._hyg.3407 f) -> (Iff (Eq.{succ v} β (f a) (f (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3401)) inst._@.Mathlib.Order.BoundedOrder._hyg.3404)))) (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3401)) inst._@.Mathlib.Order.BoundedOrder._hyg.3404))))
Case conversion may be inaccurate. Consider using '#align strict_anti.apply_eq_bot_iff StrictAnti.apply_eq_bot_iffₓ'. -/
theorem StrictAnti.apply_eq_bot_iff (hf : StrictAnti f) : f a = f ⊥ ↔ a = ⊥ :=
  hf.dual.apply_eq_top_iff
#align strict_anti.apply_eq_bot_iff StrictAnti.apply_eq_bot_iff

variable [Nontrivial α]

/- warning: not_is_max_bot -> not_isMax_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_4 : Nontrivial.{u} α], Not (IsMax.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3468 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3471 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3468))] [inst._@.Mathlib.Order.BoundedOrder._hyg.3482 : Nontrivial.{u} α], Not (IsMax.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3468)) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3468)) inst._@.Mathlib.Order.BoundedOrder._hyg.3471)))
Case conversion may be inaccurate. Consider using '#align not_is_max_bot not_isMax_botₓ'. -/
theorem not_isMax_bot : ¬IsMax (⊥ : α) :=
  @not_isMin_top αᵒᵈ _ _ _
#align not_is_max_bot not_isMax_bot

end OrderBot

/- warning: strict_mono.minimal_preimage_bot -> StrictMono.minimal_preimage_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : PartialOrder.{v} β] [_inst_3 : OrderBot.{v} β (Preorder.toLE.{v} β (PartialOrder.toPreorder.{v} β _inst_2))] {f : α -> β}, (StrictMono.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))) (PartialOrder.toPreorder.{v} β _inst_2) f) -> (forall {a : α}, (Eq.{succ v} β (f a) (Bot.bot.{v} β (OrderBot.toHasBot.{v} β (Preorder.toLE.{v} β (PartialOrder.toPreorder.{v} β _inst_2)) _inst_3))) -> (forall (x : α), LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a x))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3510 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3513 : PartialOrder.{v} β] [inst._@.Mathlib.Order.BoundedOrder._hyg.3516 : OrderBot.{v} β (Preorder.toLE.{v} β (PartialOrder.toPreorder.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.3513))] {f : α -> β}, (StrictMono.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3510))))) (PartialOrder.toPreorder.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.3513) f) -> (forall {a : α}, (Eq.{succ v} β (f a) (Bot.bot.{v} β (OrderBot.toBot.{v} β (Preorder.toLE.{v} β (PartialOrder.toPreorder.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.3513)) inst._@.Mathlib.Order.BoundedOrder._hyg.3516))) -> (forall (x : α), LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3510)))))) a x))
Case conversion may be inaccurate. Consider using '#align strict_mono.minimal_preimage_bot StrictMono.minimal_preimage_botₓ'. -/
theorem StrictMono.minimal_preimage_bot [LinearOrder α] [PartialOrder β] [OrderBot β] {f : α → β}
    (H : StrictMono f) {a} (h_bot : f a = ⊥) (x : α) : a ≤ x :=
  H.minimal_of_minimal_image
    (fun p => by 
      rw [h_bot]
      exact bot_le)
    x
#align strict_mono.minimal_preimage_bot StrictMono.minimal_preimage_bot

/- warning: order_bot.ext_bot -> OrderBot.ext_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {hA : PartialOrder.{u_1} α} (A : OrderBot.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hA))) {hB : PartialOrder.{u_1} α} (B : OrderBot.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hB))), (forall (x : α) (y : α), Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hA)) x y) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hB)) x y)) -> (Eq.{succ u_1} α (Bot.bot.{u_1} α (OrderBot.toHasBot.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hA)) A)) (Bot.bot.{u_1} α (OrderBot.toHasBot.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hB)) B)))
but is expected to have type
  forall {α : Type.{u_1}} {hA : PartialOrder.{u_1} α} (A : OrderBot.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hA))) {hB : PartialOrder.{u_1} α} (B : OrderBot.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hB))), (forall (x : α) (y : α), Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hA)) x y) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hB)) x y)) -> (Eq.{succ u_1} α (Bot.bot.{u_1} α (OrderBot.toBot.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hA)) A)) (Bot.bot.{u_1} α (OrderBot.toBot.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α hB)) B)))
Case conversion may be inaccurate. Consider using '#align order_bot.ext_bot OrderBot.ext_botₓ'. -/
theorem OrderBot.ext_bot {α} {hA : PartialOrder α} (A : OrderBot α) {hB : PartialOrder α}
    (B : OrderBot α)
    (H :
      ∀ x y : α,
        (haveI := hA
          x ≤ y) ↔
          x ≤ y) :
    (haveI := A
        ⊥ :
        α) =
      ⊥ :=
  bot_unique <| by rw [← H] <;> apply bot_le
#align order_bot.ext_bot OrderBot.ext_bot

#print OrderBot.ext /-
theorem OrderBot.ext {α} [PartialOrder α] {A B : OrderBot α} : A = B := by
  have tt := OrderBot.ext_bot A B fun _ _ => Iff.rfl
  cases' A with a ha; cases' B with b hb
  congr
  exact le_antisymm (ha _) (hb _)
#align order_bot.ext OrderBot.ext
-/

section SemilatticeSupTop

variable [SemilatticeSup α] [OrderTop α] {a : α}

/- warning: top_sup_eq -> top_sup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : SemilatticeSup.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1)))] {a : α}, Eq.{succ u} α (HasSup.sup.{u} α (SemilatticeSup.toHasSup.{u} α _inst_1) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1))) _inst_2)) a) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1))) _inst_2))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3734 : SemilatticeSup.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3737 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3734)))] {a : α}, Eq.{succ u} α (HasSup.sup.{u} α (SemilatticeSup.toHasSup.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3734) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3734))) inst._@.Mathlib.Order.BoundedOrder._hyg.3737)) a) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3734))) inst._@.Mathlib.Order.BoundedOrder._hyg.3737))
Case conversion may be inaccurate. Consider using '#align top_sup_eq top_sup_eqₓ'. -/
@[simp]
theorem top_sup_eq : ⊤ ⊔ a = ⊤ :=
  sup_of_le_left le_top
#align top_sup_eq top_sup_eq

/- warning: sup_top_eq -> sup_top_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : SemilatticeSup.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1)))] {a : α}, Eq.{succ u} α (HasSup.sup.{u} α (SemilatticeSup.toHasSup.{u} α _inst_1) a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1))) _inst_2))) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1))) _inst_2))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3764 : SemilatticeSup.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3767 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3764)))] {a : α}, Eq.{succ u} α (HasSup.sup.{u} α (SemilatticeSup.toHasSup.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3764) a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3764))) inst._@.Mathlib.Order.BoundedOrder._hyg.3767))) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3764))) inst._@.Mathlib.Order.BoundedOrder._hyg.3767))
Case conversion may be inaccurate. Consider using '#align sup_top_eq sup_top_eqₓ'. -/
@[simp]
theorem sup_top_eq : a ⊔ ⊤ = ⊤ :=
  sup_of_le_right le_top
#align sup_top_eq sup_top_eq

end SemilatticeSupTop

section SemilatticeSupBot

variable [SemilatticeSup α] [OrderBot α] {a b : α}

/- warning: bot_sup_eq -> bot_sup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : SemilatticeSup.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1)))] {a : α}, Eq.{succ u} α (HasSup.sup.{u} α (SemilatticeSup.toHasSup.{u} α _inst_1) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1))) _inst_2)) a) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3813 : SemilatticeSup.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3816 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3813)))] {a : α}, Eq.{succ u} α (HasSup.sup.{u} α (SemilatticeSup.toHasSup.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3813) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3813))) inst._@.Mathlib.Order.BoundedOrder._hyg.3816)) a) a
Case conversion may be inaccurate. Consider using '#align bot_sup_eq bot_sup_eqₓ'. -/
@[simp]
theorem bot_sup_eq : ⊥ ⊔ a = a :=
  sup_of_le_right bot_le
#align bot_sup_eq bot_sup_eq

/- warning: sup_bot_eq -> sup_bot_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : SemilatticeSup.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1)))] {a : α}, Eq.{succ u} α (HasSup.sup.{u} α (SemilatticeSup.toHasSup.{u} α _inst_1) a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1))) _inst_2))) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3841 : SemilatticeSup.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3844 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3841)))] {a : α}, Eq.{succ u} α (HasSup.sup.{u} α (SemilatticeSup.toHasSup.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3841) a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3841))) inst._@.Mathlib.Order.BoundedOrder._hyg.3844))) a
Case conversion may be inaccurate. Consider using '#align sup_bot_eq sup_bot_eqₓ'. -/
@[simp]
theorem sup_bot_eq : a ⊔ ⊥ = a :=
  sup_of_le_left bot_le
#align sup_bot_eq sup_bot_eq

/- warning: sup_eq_bot_iff -> sup_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : SemilatticeSup.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1)))] {a : α} {b : α}, Iff (Eq.{succ u} α (HasSup.sup.{u} α (SemilatticeSup.toHasSup.{u} α _inst_1) a b) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1))) _inst_2))) (And (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1))) _inst_2))) (Eq.{succ u} α b (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1))) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3869 : SemilatticeSup.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3872 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3869)))] {a : α} {b : α}, Iff (Eq.{succ u} α (HasSup.sup.{u} α (SemilatticeSup.toHasSup.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3869) a b) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3869))) inst._@.Mathlib.Order.BoundedOrder._hyg.3872))) (And (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3869))) inst._@.Mathlib.Order.BoundedOrder._hyg.3872))) (Eq.{succ u} α b (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3869))) inst._@.Mathlib.Order.BoundedOrder._hyg.3872))))
Case conversion may be inaccurate. Consider using '#align sup_eq_bot_iff sup_eq_bot_iffₓ'. -/
@[simp]
theorem sup_eq_bot_iff : a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := by rw [eq_bot_iff, sup_le_iff] <;> simp
#align sup_eq_bot_iff sup_eq_bot_iff

end SemilatticeSupBot

section SemilatticeInfTop

variable [SemilatticeInf α] [OrderTop α] {a b : α}

/- warning: top_inf_eq -> top_inf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : SemilatticeInf.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1)))] {a : α}, Eq.{succ u} α (HasInf.inf.{u} α (SemilatticeInf.toHasInf.{u} α _inst_1) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1))) _inst_2)) a) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3971 : SemilatticeInf.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.3974 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3971)))] {a : α}, Eq.{succ u} α (HasInf.inf.{u} α (SemilatticeInf.toHasInf.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3971) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3971))) inst._@.Mathlib.Order.BoundedOrder._hyg.3974)) a) a
Case conversion may be inaccurate. Consider using '#align top_inf_eq top_inf_eqₓ'. -/
@[simp]
theorem top_inf_eq : ⊤ ⊓ a = a :=
  inf_of_le_right le_top
#align top_inf_eq top_inf_eq

/- warning: inf_top_eq -> inf_top_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : SemilatticeInf.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1)))] {a : α}, Eq.{succ u} α (HasInf.inf.{u} α (SemilatticeInf.toHasInf.{u} α _inst_1) a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1))) _inst_2))) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.3999 : SemilatticeInf.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.4002 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3999)))] {a : α}, Eq.{succ u} α (HasInf.inf.{u} α (SemilatticeInf.toHasInf.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3999) a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.3999))) inst._@.Mathlib.Order.BoundedOrder._hyg.4002))) a
Case conversion may be inaccurate. Consider using '#align inf_top_eq inf_top_eqₓ'. -/
@[simp]
theorem inf_top_eq : a ⊓ ⊤ = a :=
  inf_of_le_left le_top
#align inf_top_eq inf_top_eq

/- warning: inf_eq_top_iff -> inf_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : SemilatticeInf.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1)))] {a : α} {b : α}, Iff (Eq.{succ u} α (HasInf.inf.{u} α (SemilatticeInf.toHasInf.{u} α _inst_1) a b) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1))) _inst_2))) (And (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1))) _inst_2))) (Eq.{succ u} α b (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1))) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4027 : SemilatticeInf.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.4030 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4027)))] {a : α} {b : α}, Iff (Eq.{succ u} α (HasInf.inf.{u} α (SemilatticeInf.toHasInf.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4027) a b) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4027))) inst._@.Mathlib.Order.BoundedOrder._hyg.4030))) (And (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4027))) inst._@.Mathlib.Order.BoundedOrder._hyg.4030))) (Eq.{succ u} α b (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4027))) inst._@.Mathlib.Order.BoundedOrder._hyg.4030))))
Case conversion may be inaccurate. Consider using '#align inf_eq_top_iff inf_eq_top_iffₓ'. -/
@[simp]
theorem inf_eq_top_iff : a ⊓ b = ⊤ ↔ a = ⊤ ∧ b = ⊤ :=
  @sup_eq_bot_iff αᵒᵈ _ _ _ _
#align inf_eq_top_iff inf_eq_top_iff

end SemilatticeInfTop

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {a : α}

/- warning: bot_inf_eq -> bot_inf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : SemilatticeInf.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1)))] {a : α}, Eq.{succ u} α (HasInf.inf.{u} α (SemilatticeInf.toHasInf.{u} α _inst_1) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1))) _inst_2)) a) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1))) _inst_2))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4100 : SemilatticeInf.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.4103 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4100)))] {a : α}, Eq.{succ u} α (HasInf.inf.{u} α (SemilatticeInf.toHasInf.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4100) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4100))) inst._@.Mathlib.Order.BoundedOrder._hyg.4103)) a) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4100))) inst._@.Mathlib.Order.BoundedOrder._hyg.4103))
Case conversion may be inaccurate. Consider using '#align bot_inf_eq bot_inf_eqₓ'. -/
@[simp]
theorem bot_inf_eq : ⊥ ⊓ a = ⊥ :=
  inf_of_le_left bot_le
#align bot_inf_eq bot_inf_eq

/- warning: inf_bot_eq -> inf_bot_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : SemilatticeInf.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1)))] {a : α}, Eq.{succ u} α (HasInf.inf.{u} α (SemilatticeInf.toHasInf.{u} α _inst_1) a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1))) _inst_2))) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1))) _inst_2))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4130 : SemilatticeInf.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.4133 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4130)))] {a : α}, Eq.{succ u} α (HasInf.inf.{u} α (SemilatticeInf.toHasInf.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4130) a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4130))) inst._@.Mathlib.Order.BoundedOrder._hyg.4133))) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4130))) inst._@.Mathlib.Order.BoundedOrder._hyg.4133))
Case conversion may be inaccurate. Consider using '#align inf_bot_eq inf_bot_eqₓ'. -/
@[simp]
theorem inf_bot_eq : a ⊓ ⊥ = ⊥ :=
  inf_of_le_right bot_le
#align inf_bot_eq inf_bot_eq

end SemilatticeInfBot

/-! ### Bounded order -/


#print BoundedOrder /-
/-- A bounded order describes an order `(≤)` with a top and bottom element,
  denoted `⊤` and `⊥` respectively. -/
class BoundedOrder (α : Type u) [LE α] extends OrderTop α, OrderBot α
#align bounded_order BoundedOrder
-/

instance (α : Type u) [LE α] [BoundedOrder α] : BoundedOrder αᵒᵈ :=
  { OrderDual.orderTop α, OrderDual.orderBot α with }

#print BoundedOrder.ext /-
theorem BoundedOrder.ext {α} [PartialOrder α] {A B : BoundedOrder α} : A = B := by
  have ht : @BoundedOrder.toOrderTop α _ A = @BoundedOrder.toOrderTop α _ B := OrderTop.ext
  have hb : @BoundedOrder.toOrderBot α _ A = @BoundedOrder.toOrderBot α _ B := OrderBot.ext
  cases A
  cases B
  injection ht with h
  injection hb with h'
  convert rfl
  · exact h.symm
  · exact h'.symm
#align bounded_order.ext BoundedOrder.ext
-/

section Logic

/-!
#### In this section we prove some properties about monotone and antitone operations on `Prop`
-/


section Preorder

variable [Preorder α]

/- warning: monotone_and -> monotone_and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Preorder.{u} α] {p : α -> Prop} {q : α -> Prop}, (Monotone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) p) -> (Monotone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) q) -> (Monotone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (fun (x : α) => And (p x) (q x)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4336 : Preorder.{u} α] {p : α -> Prop} {q : α -> Prop}, (Monotone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4336 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) p) -> (Monotone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4336 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) q) -> (Monotone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4336 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) (fun (x : α) => And (p x) (q x)))
Case conversion may be inaccurate. Consider using '#align monotone_and monotone_andₓ'. -/
theorem monotone_and {p q : α → Prop} (m_p : Monotone p) (m_q : Monotone q) :
    Monotone fun x => p x ∧ q x := fun a b h => And.imp (m_p h) (m_q h)
#align monotone_and monotone_and

/- warning: monotone_or -> monotone_or is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Preorder.{u} α] {p : α -> Prop} {q : α -> Prop}, (Monotone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) p) -> (Monotone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) q) -> (Monotone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (fun (x : α) => Or (p x) (q x)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4382 : Preorder.{u} α] {p : α -> Prop} {q : α -> Prop}, (Monotone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4382 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) p) -> (Monotone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4382 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) q) -> (Monotone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4382 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) (fun (x : α) => Or (p x) (q x)))
Case conversion may be inaccurate. Consider using '#align monotone_or monotone_orₓ'. -/
-- Note: by finish [monotone] doesn't work
theorem monotone_or {p q : α → Prop} (m_p : Monotone p) (m_q : Monotone q) :
    Monotone fun x => p x ∨ q x := fun a b h => Or.imp (m_p h) (m_q h)
#align monotone_or monotone_or

/- warning: monotone_le -> monotone_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Preorder.{u} α] {x : α}, Monotone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (LE.le.{u} α (Preorder.toLE.{u} α _inst_1) x)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4428 : Preorder.{u} α] {x : α}, Monotone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4428 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) ((fun (x._@.Mathlib.Order.BoundedOrder._hyg.4439 : α) (x._@.Mathlib.Order.BoundedOrder._hyg.4441 : α) => LE.le.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4428) x._@.Mathlib.Order.BoundedOrder._hyg.4439 x._@.Mathlib.Order.BoundedOrder._hyg.4441) x)
Case conversion may be inaccurate. Consider using '#align monotone_le monotone_leₓ'. -/
theorem monotone_le {x : α} : Monotone ((· ≤ ·) x) := fun y z h' h => h.trans h'
#align monotone_le monotone_le

/- warning: monotone_lt -> monotone_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Preorder.{u} α] {x : α}, Monotone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (LT.lt.{u} α (Preorder.toLT.{u} α _inst_1) x)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4468 : Preorder.{u} α] {x : α}, Monotone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4468 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) ((fun (x._@.Mathlib.Order.BoundedOrder._hyg.4479 : α) (x._@.Mathlib.Order.BoundedOrder._hyg.4481 : α) => LT.lt.{u} α (Preorder.toLT.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4468) x._@.Mathlib.Order.BoundedOrder._hyg.4479 x._@.Mathlib.Order.BoundedOrder._hyg.4481) x)
Case conversion may be inaccurate. Consider using '#align monotone_lt monotone_ltₓ'. -/
theorem monotone_lt {x : α} : Monotone ((· < ·) x) := fun y z h' h => h.trans_le h'
#align monotone_lt monotone_lt

/- warning: antitone_le -> antitone_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Preorder.{u} α] {x : α}, Antitone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (fun (_x : α) => LE.le.{u} α (Preorder.toLE.{u} α _inst_1) _x x)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4508 : Preorder.{u} α] {x : α}, Antitone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4508 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) (fun (x._@.Mathlib.Order.BoundedOrder._hyg.4516 : α) => LE.le.{u} α (Preorder.toLE.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4508) x._@.Mathlib.Order.BoundedOrder._hyg.4516 x)
Case conversion may be inaccurate. Consider using '#align antitone_le antitone_leₓ'. -/
theorem antitone_le {x : α} : Antitone (· ≤ x) := fun y z h' h => h'.trans h
#align antitone_le antitone_le

/- warning: antitone_lt -> antitone_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Preorder.{u} α] {x : α}, Antitone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (fun (_x : α) => LT.lt.{u} α (Preorder.toLT.{u} α _inst_1) _x x)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4541 : Preorder.{u} α] {x : α}, Antitone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4541 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) (fun (x._@.Mathlib.Order.BoundedOrder._hyg.4549 : α) => LT.lt.{u} α (Preorder.toLT.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4541) x._@.Mathlib.Order.BoundedOrder._hyg.4549 x)
Case conversion may be inaccurate. Consider using '#align antitone_lt antitone_ltₓ'. -/
theorem antitone_lt {x : α} : Antitone (· < x) := fun y z h' h => h'.trans_lt h
#align antitone_lt antitone_lt

/- warning: monotone.forall -> Monotone.forall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : Preorder.{u} α] {P : β -> α -> Prop}, (forall (x : β), Monotone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (P x)) -> (Monotone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (fun (y : α) => forall (x : β), P x y))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4577 : Preorder.{u} α] {P : β -> α -> Prop}, (forall (x : β), Monotone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4577 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) (P x)) -> (Monotone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4577 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) (fun (y : α) => forall (x : β), P x y))
Case conversion may be inaccurate. Consider using '#align monotone.forall Monotone.forallₓ'. -/
theorem Monotone.forall {P : β → α → Prop} (hP : ∀ x, Monotone (P x)) :
    Monotone fun y => ∀ x, P x y := fun y y' hy h x => hP x hy <| h x
#align monotone.forall Monotone.forall

/- warning: antitone.forall -> Antitone.forall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : Preorder.{u} α] {P : β -> α -> Prop}, (forall (x : β), Antitone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (P x)) -> (Antitone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (fun (y : α) => forall (x : β), P x y))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4629 : Preorder.{u} α] {P : β -> α -> Prop}, (forall (x : β), Antitone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4629 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) (P x)) -> (Antitone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4629 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) (fun (y : α) => forall (x : β), P x y))
Case conversion may be inaccurate. Consider using '#align antitone.forall Antitone.forallₓ'. -/
theorem Antitone.forall {P : β → α → Prop} (hP : ∀ x, Antitone (P x)) :
    Antitone fun y => ∀ x, P x y := fun y y' hy h x => hP x hy (h x)
#align antitone.forall Antitone.forall

/- warning: monotone.ball -> Monotone.ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : Preorder.{u} α] {P : β -> α -> Prop} {s : Set.{v} β}, (forall (x : β), (Membership.Mem.{v, v} β (Set.{v} β) (Set.hasMem.{v} β) x s) -> (Monotone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (P x))) -> (Monotone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (fun (y : α) => forall (x : β), (Membership.Mem.{v, v} β (Set.{v} β) (Set.hasMem.{v} β) x s) -> (P x y)))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4681 : Preorder.{u} α] {P : β -> α -> Prop} {s : Set.{v} β}, (forall (x : β), (Membership.mem.{v, v} β (Set.{v} β) (Set.instMembershipSet.{v} β) x s) -> (Monotone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4681 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) (P x))) -> (Monotone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4681 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) (fun (y : α) => forall (x : β), (Membership.mem.{v, v} β (Set.{v} β) (Set.instMembershipSet.{v} β) x s) -> (P x y)))
Case conversion may be inaccurate. Consider using '#align monotone.ball Monotone.ballₓ'. -/
theorem Monotone.ball {P : β → α → Prop} {s : Set β} (hP : ∀ x ∈ s, Monotone (P x)) :
    Monotone fun y => ∀ x ∈ s, P x y := fun y y' hy h x hx => hP x hx hy (h x hx)
#align monotone.ball Monotone.ball

/- warning: antitone.ball -> Antitone.ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : Preorder.{u} α] {P : β -> α -> Prop} {s : Set.{v} β}, (forall (x : β), (Membership.Mem.{v, v} β (Set.{v} β) (Set.hasMem.{v} β) x s) -> (Antitone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (P x))) -> (Antitone.{u, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) (fun (y : α) => forall (x : β), (Membership.Mem.{v, v} β (Set.{v} β) (Set.hasMem.{v} β) x s) -> (P x y)))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4758 : Preorder.{u} α] {P : β -> α -> Prop} {s : Set.{v} β}, (forall (x : β), (Membership.mem.{v, v} β (Set.{v} β) (Set.instMembershipSet.{v} β) x s) -> (Antitone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4758 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) (P x))) -> (Antitone.{u, 0} α Prop inst._@.Mathlib.Order.BoundedOrder._hyg.4758 (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) (fun (y : α) => forall (x : β), (Membership.mem.{v, v} β (Set.{v} β) (Set.instMembershipSet.{v} β) x s) -> (P x y)))
Case conversion may be inaccurate. Consider using '#align antitone.ball Antitone.ballₓ'. -/
theorem Antitone.ball {P : β → α → Prop} {s : Set β} (hP : ∀ x ∈ s, Antitone (P x)) :
    Antitone fun y => ∀ x ∈ s, P x y := fun y y' hy h x hx => hP x hx hy (h x hx)
#align antitone.ball Antitone.ball

end Preorder

section SemilatticeSup

variable [SemilatticeSup α]

/- warning: exists_ge_and_iff_exists -> exists_ge_and_iff_exists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : SemilatticeSup.{u} α] {P : α -> Prop} {x₀ : α}, (Monotone.{u, 0} α Prop (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1)) (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) P) -> (Iff (Exists.{succ u} α (fun (x : α) => And (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α _inst_1))) x₀ x) (P x))) (Exists.{succ u} α (fun (x : α) => P x)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4843 : SemilatticeSup.{u} α] {P : α -> Prop} {x₀ : α}, (Monotone.{u, 0} α Prop (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4843)) (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) P) -> (Iff (Exists.{succ u} α (fun (x : α) => And (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeSup.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4843))) x₀ x) (P x))) (Exists.{succ u} α (fun (x : α) => P x)))
Case conversion may be inaccurate. Consider using '#align exists_ge_and_iff_exists exists_ge_and_iff_existsₓ'. -/
theorem exists_ge_and_iff_exists {P : α → Prop} {x₀ : α} (hP : Monotone P) :
    (∃ x, x₀ ≤ x ∧ P x) ↔ ∃ x, P x :=
  ⟨fun h => h.imp fun x h => h.2, fun ⟨x, hx⟩ => ⟨x ⊔ x₀, le_sup_right, hP le_sup_left hx⟩⟩
#align exists_ge_and_iff_exists exists_ge_and_iff_exists

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α]

/- warning: exists_le_and_iff_exists -> exists_le_and_iff_exists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : SemilatticeInf.{u} α] {P : α -> Prop} {x₀ : α}, (Antitone.{u, 0} α Prop (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1)) (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder) P) -> (Iff (Exists.{succ u} α (fun (x : α) => And (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α _inst_1))) x x₀) (P x))) (Exists.{succ u} α (fun (x : α) => P x)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.4943 : SemilatticeInf.{u} α] {P : α -> Prop} {x₀ : α}, (Antitone.{u, 0} α Prop (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4943)) (PartialOrder.toPreorder.{0} Prop instPartialOrderProp) P) -> (Iff (Exists.{succ u} α (fun (x : α) => And (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.4943))) x x₀) (P x))) (Exists.{succ u} α (fun (x : α) => P x)))
Case conversion may be inaccurate. Consider using '#align exists_le_and_iff_exists exists_le_and_iff_existsₓ'. -/
theorem exists_le_and_iff_exists {P : α → Prop} {x₀ : α} (hP : Antitone P) :
    (∃ x, x ≤ x₀ ∧ P x) ↔ ∃ x, P x :=
  exists_ge_and_iff_exists hP.dual_left
#align exists_le_and_iff_exists exists_le_and_iff_exists

end SemilatticeInf

end Logic

/-! ### Function lattices -/


namespace Pi

variable {ι : Type _} {α' : ι → Type _}

instance [∀ i, Bot (α' i)] : Bot (∀ i, α' i) :=
  ⟨fun i => ⊥⟩

#print Pi.bot_apply /-
@[simp]
theorem bot_apply [∀ i, Bot (α' i)] (i : ι) : (⊥ : ∀ i, α' i) i = ⊥ :=
  rfl
#align pi.bot_apply Pi.bot_apply
-/

#print Pi.bot_def /-
theorem bot_def [∀ i, Bot (α' i)] : (⊥ : ∀ i, α' i) = fun i => ⊥ :=
  rfl
#align pi.bot_def Pi.bot_def
-/

instance [∀ i, Top (α' i)] : Top (∀ i, α' i) :=
  ⟨fun i => ⊤⟩

#print Pi.top_apply /-
@[simp]
theorem top_apply [∀ i, Top (α' i)] (i : ι) : (⊤ : ∀ i, α' i) i = ⊤ :=
  rfl
#align pi.top_apply Pi.top_apply
-/

#print Pi.top_def /-
theorem top_def [∀ i, Top (α' i)] : (⊤ : ∀ i, α' i) = fun i => ⊤ :=
  rfl
#align pi.top_def Pi.top_def
-/

instance [∀ i, LE (α' i)] [∀ i, OrderTop (α' i)] : OrderTop (∀ i, α' i) :=
  { Pi.hasTop with le_top := fun _ _ => le_top }

instance [∀ i, LE (α' i)] [∀ i, OrderBot (α' i)] : OrderBot (∀ i, α' i) :=
  { Pi.hasBot with bot_le := fun _ _ => bot_le }

instance [∀ i, LE (α' i)] [∀ i, BoundedOrder (α' i)] : BoundedOrder (∀ i, α' i) :=
  { Pi.orderTop, Pi.orderBot with }

end Pi

section Subsingleton

variable [PartialOrder α] [BoundedOrder α]

/- warning: eq_bot_of_bot_eq_top -> eq_bot_of_bot_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))], (Eq.{succ u} α (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))) -> (forall (x : α), Eq.{succ u} α x (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.5475 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.5478 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5475))], (Eq.{succ u} α (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5475)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5475)) inst._@.Mathlib.Order.BoundedOrder._hyg.5478))) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5475)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5475)) inst._@.Mathlib.Order.BoundedOrder._hyg.5478)))) -> (forall (x : α), Eq.{succ u} α x (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5475)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5475)) inst._@.Mathlib.Order.BoundedOrder._hyg.5478))))
Case conversion may be inaccurate. Consider using '#align eq_bot_of_bot_eq_top eq_bot_of_bot_eq_topₓ'. -/
theorem eq_bot_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊥ : α) :=
  eq_bot_mono le_top (Eq.symm hα)
#align eq_bot_of_bot_eq_top eq_bot_of_bot_eq_top

/- warning: eq_top_of_bot_eq_top -> eq_top_of_bot_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))], (Eq.{succ u} α (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))) -> (forall (x : α), Eq.{succ u} α x (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.5519 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.5522 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5519))], (Eq.{succ u} α (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5519)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5519)) inst._@.Mathlib.Order.BoundedOrder._hyg.5522))) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5519)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5519)) inst._@.Mathlib.Order.BoundedOrder._hyg.5522)))) -> (forall (x : α), Eq.{succ u} α x (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5519)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5519)) inst._@.Mathlib.Order.BoundedOrder._hyg.5522))))
Case conversion may be inaccurate. Consider using '#align eq_top_of_bot_eq_top eq_top_of_bot_eq_topₓ'. -/
theorem eq_top_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊤ : α) :=
  eq_top_mono bot_le hα
#align eq_top_of_bot_eq_top eq_top_of_bot_eq_top

/- warning: subsingleton_of_top_le_bot -> subsingleton_of_top_le_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))], (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))) -> (Subsingleton.{succ u} α)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.5560 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.5563 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5560))], (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5560)) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5560)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5560)) inst._@.Mathlib.Order.BoundedOrder._hyg.5563))) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5560)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5560)) inst._@.Mathlib.Order.BoundedOrder._hyg.5563)))) -> (Subsingleton.{succ u} α)
Case conversion may be inaccurate. Consider using '#align subsingleton_of_top_le_bot subsingleton_of_top_le_botₓ'. -/
theorem subsingleton_of_top_le_bot (h : (⊤ : α) ≤ (⊥ : α)) : Subsingleton α :=
  ⟨fun a b =>
    le_antisymm (le_trans le_top <| le_trans h bot_le) (le_trans le_top <| le_trans h bot_le)⟩
#align subsingleton_of_top_le_bot subsingleton_of_top_le_bot

/- warning: subsingleton_of_bot_eq_top -> subsingleton_of_bot_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))], (Eq.{succ u} α (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))) -> (Subsingleton.{succ u} α)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.5618 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.5621 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5618))], (Eq.{succ u} α (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5618)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5618)) inst._@.Mathlib.Order.BoundedOrder._hyg.5621))) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5618)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5618)) inst._@.Mathlib.Order.BoundedOrder._hyg.5621)))) -> (Subsingleton.{succ u} α)
Case conversion may be inaccurate. Consider using '#align subsingleton_of_bot_eq_top subsingleton_of_bot_eq_topₓ'. -/
theorem subsingleton_of_bot_eq_top (hα : (⊥ : α) = (⊤ : α)) : Subsingleton α :=
  subsingleton_of_top_le_bot (ge_of_eq hα)
#align subsingleton_of_bot_eq_top subsingleton_of_bot_eq_top

/- warning: subsingleton_iff_bot_eq_top -> subsingleton_iff_bot_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))], Iff (Eq.{succ u} α (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))) (Subsingleton.{succ u} α)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.5654 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.5657 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5654))], Iff (Eq.{succ u} α (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5654)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5654)) inst._@.Mathlib.Order.BoundedOrder._hyg.5657))) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5654)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5654)) inst._@.Mathlib.Order.BoundedOrder._hyg.5657)))) (Subsingleton.{succ u} α)
Case conversion may be inaccurate. Consider using '#align subsingleton_iff_bot_eq_top subsingleton_iff_bot_eq_topₓ'. -/
theorem subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ : α) ↔ Subsingleton α :=
  ⟨subsingleton_of_bot_eq_top, fun h => Subsingleton.elim ⊥ ⊤⟩
#align subsingleton_iff_bot_eq_top subsingleton_iff_bot_eq_top

end Subsingleton

section lift

/- warning: order_top.lift -> OrderTop.lift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : LE.{u} α] [_inst_2 : Top.{u} α] [_inst_3 : LE.{v} β] [_inst_4 : OrderTop.{v} β _inst_3] (f : α -> β), (forall (a : α) (b : α), (LE.le.{v} β _inst_3 (f a) (f b)) -> (LE.le.{u} α _inst_1 a b)) -> (Eq.{succ v} β (f (Top.top.{u} α _inst_2)) (Top.top.{v} β (OrderTop.toHasTop.{v} β _inst_3 _inst_4))) -> (OrderTop.{u} α _inst_1)
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.BoundedOrder._hyg.5707 : LE.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.5710 : Top.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.5713 : LE.{v} β] [inst._@.Mathlib.Order.BoundedOrder._hyg.5716 : OrderTop.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.5713] (f : α -> β), (forall (a : α) (b : α), (LE.le.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.5713 (f a) (f b)) -> (LE.le.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5707 a b)) -> (Eq.{succ v} β (f (Top.top.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5710)) (Top.top.{v} β (OrderTop.toTop.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.5713 inst._@.Mathlib.Order.BoundedOrder._hyg.5716))) -> (OrderTop.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5707)
Case conversion may be inaccurate. Consider using '#align order_top.lift OrderTop.liftₓ'. -/
-- See note [reducible non-instances]
/-- Pullback an `order_top`. -/
@[reducible]
def OrderTop.lift [LE α] [Top α] [LE β] [OrderTop β] (f : α → β) (map_le : ∀ a b, f a ≤ f b → a ≤ b)
    (map_top : f ⊤ = ⊤) : OrderTop α :=
  ⟨⊤, fun a =>
    map_le _ _ <| by 
      rw [map_top]
      exact le_top⟩
#align order_top.lift OrderTop.lift

/- warning: order_bot.lift -> OrderBot.lift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : LE.{u} α] [_inst_2 : Bot.{u} α] [_inst_3 : LE.{v} β] [_inst_4 : OrderBot.{v} β _inst_3] (f : α -> β), (forall (a : α) (b : α), (LE.le.{v} β _inst_3 (f a) (f b)) -> (LE.le.{u} α _inst_1 a b)) -> (Eq.{succ v} β (f (Bot.bot.{u} α _inst_2)) (Bot.bot.{v} β (OrderBot.toHasBot.{v} β _inst_3 _inst_4))) -> (OrderBot.{u} α _inst_1)
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.BoundedOrder._hyg.5808 : LE.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.5811 : Bot.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.5814 : LE.{v} β] [inst._@.Mathlib.Order.BoundedOrder._hyg.5817 : OrderBot.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.5814] (f : α -> β), (forall (a : α) (b : α), (LE.le.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.5814 (f a) (f b)) -> (LE.le.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5808 a b)) -> (Eq.{succ v} β (f (Bot.bot.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5811)) (Bot.bot.{v} β (OrderBot.toBot.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.5814 inst._@.Mathlib.Order.BoundedOrder._hyg.5817))) -> (OrderBot.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5808)
Case conversion may be inaccurate. Consider using '#align order_bot.lift OrderBot.liftₓ'. -/
-- See note [reducible non-instances]
/-- Pullback an `order_bot`. -/
@[reducible]
def OrderBot.lift [LE α] [Bot α] [LE β] [OrderBot β] (f : α → β) (map_le : ∀ a b, f a ≤ f b → a ≤ b)
    (map_bot : f ⊥ = ⊥) : OrderBot α :=
  ⟨⊥, fun a =>
    map_le _ _ <| by 
      rw [map_bot]
      exact bot_le⟩
#align order_bot.lift OrderBot.lift

/- warning: bounded_order.lift -> BoundedOrder.lift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : LE.{u} α] [_inst_2 : Top.{u} α] [_inst_3 : Bot.{u} α] [_inst_4 : LE.{v} β] [_inst_5 : BoundedOrder.{v} β _inst_4] (f : α -> β), (forall (a : α) (b : α), (LE.le.{v} β _inst_4 (f a) (f b)) -> (LE.le.{u} α _inst_1 a b)) -> (Eq.{succ v} β (f (Top.top.{u} α _inst_2)) (Top.top.{v} β (OrderTop.toHasTop.{v} β _inst_4 (BoundedOrder.toOrderTop.{v} β _inst_4 _inst_5)))) -> (Eq.{succ v} β (f (Bot.bot.{u} α _inst_3)) (Bot.bot.{v} β (OrderBot.toHasBot.{v} β _inst_4 (BoundedOrder.toOrderBot.{v} β _inst_4 _inst_5)))) -> (BoundedOrder.{u} α _inst_1)
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.BoundedOrder._hyg.5909 : LE.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.5912 : Top.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.5915 : Bot.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.5918 : LE.{v} β] [inst._@.Mathlib.Order.BoundedOrder._hyg.5921 : BoundedOrder.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.5918] (f : α -> β), (forall (a : α) (b : α), (LE.le.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.5918 (f a) (f b)) -> (LE.le.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5909 a b)) -> (Eq.{succ v} β (f (Top.top.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5912)) (Top.top.{v} β (OrderTop.toTop.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.5918 (BoundedOrder.toOrderTop.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.5918 inst._@.Mathlib.Order.BoundedOrder._hyg.5921)))) -> (Eq.{succ v} β (f (Bot.bot.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5915)) (Bot.bot.{v} β (OrderBot.toBot.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.5918 (BoundedOrder.toOrderBot.{v} β inst._@.Mathlib.Order.BoundedOrder._hyg.5918 inst._@.Mathlib.Order.BoundedOrder._hyg.5921)))) -> (BoundedOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.5909)
Case conversion may be inaccurate. Consider using '#align bounded_order.lift BoundedOrder.liftₓ'. -/
-- See note [reducible non-instances]
/-- Pullback a `bounded_order`. -/
@[reducible]
def BoundedOrder.lift [LE α] [Top α] [Bot α] [LE β] [BoundedOrder β] (f : α → β)
    (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : BoundedOrder α :=
  { OrderTop.lift f map_le map_top, OrderBot.lift f map_le map_bot with }
#align bounded_order.lift BoundedOrder.lift

end lift

/-! ### Subtype, order dual, product lattices -/


namespace Subtype

variable {p : α → Prop}

/- warning: subtype.order_bot -> Subtype.orderBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {p : α -> Prop} [_inst_1 : LE.{u} α] [_inst_2 : OrderBot.{u} α _inst_1], (p (Bot.bot.{u} α (OrderBot.toHasBot.{u} α _inst_1 _inst_2))) -> (OrderBot.{u} (Subtype.{succ u} α (fun (x : α) => p x)) (Subtype.hasLe.{u} α _inst_1 (fun (x : α) => p x)))
but is expected to have type
  forall {α : Type.{u}} {p : α -> Prop} [inst._@.Mathlib.Order.BoundedOrder._hyg.6016 : LE.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6019 : OrderBot.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6016], (p (Bot.bot.{u} α (OrderBot.toBot.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6016 inst._@.Mathlib.Order.BoundedOrder._hyg.6019))) -> (OrderBot.{u} (Subtype.{succ u} α (fun (x : α) => p x)) (Subtype.instLESubtype.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6016 (fun (x : α) => p x)))
Case conversion may be inaccurate. Consider using '#align subtype.order_bot Subtype.orderBotₓ'. -/
-- See note [reducible non-instances]
/-- A subtype remains a `⊥`-order if the property holds at `⊥`. -/
@[reducible]
protected def orderBot [LE α] [OrderBot α] (hbot : p ⊥) :
    OrderBot { x : α // p x } where 
  bot := ⟨⊥, hbot⟩
  bot_le _ := bot_le
#align subtype.order_bot Subtype.orderBot

/- warning: subtype.order_top -> Subtype.orderTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {p : α -> Prop} [_inst_1 : LE.{u} α] [_inst_2 : OrderTop.{u} α _inst_1], (p (Top.top.{u} α (OrderTop.toHasTop.{u} α _inst_1 _inst_2))) -> (OrderTop.{u} (Subtype.{succ u} α (fun (x : α) => p x)) (Subtype.hasLe.{u} α _inst_1 (fun (x : α) => p x)))
but is expected to have type
  forall {α : Type.{u}} {p : α -> Prop} [inst._@.Mathlib.Order.BoundedOrder._hyg.6061 : LE.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6064 : OrderTop.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6061], (p (Top.top.{u} α (OrderTop.toTop.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6061 inst._@.Mathlib.Order.BoundedOrder._hyg.6064))) -> (OrderTop.{u} (Subtype.{succ u} α (fun (x : α) => p x)) (Subtype.instLESubtype.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6061 (fun (x : α) => p x)))
Case conversion may be inaccurate. Consider using '#align subtype.order_top Subtype.orderTopₓ'. -/
-- See note [reducible non-instances]
/-- A subtype remains a `⊤`-order if the property holds at `⊤`. -/
@[reducible]
protected def orderTop [LE α] [OrderTop α] (htop : p ⊤) :
    OrderTop { x : α // p x } where 
  top := ⟨⊤, htop⟩
  le_top _ := le_top
#align subtype.order_top Subtype.orderTop

/- warning: subtype.bounded_order -> Subtype.boundedOrder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {p : α -> Prop} [_inst_1 : LE.{u} α] [_inst_2 : BoundedOrder.{u} α _inst_1], (p (Bot.bot.{u} α (OrderBot.toHasBot.{u} α _inst_1 (BoundedOrder.toOrderBot.{u} α _inst_1 _inst_2)))) -> (p (Top.top.{u} α (OrderTop.toHasTop.{u} α _inst_1 (BoundedOrder.toOrderTop.{u} α _inst_1 _inst_2)))) -> (BoundedOrder.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α _inst_1 p))
but is expected to have type
  forall {α : Type.{u}} {p : α -> Prop} [inst._@.Mathlib.Order.BoundedOrder._hyg.6106 : LE.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6109 : BoundedOrder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6106], (p (Bot.bot.{u} α (OrderBot.toBot.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6106 (BoundedOrder.toOrderBot.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6106 inst._@.Mathlib.Order.BoundedOrder._hyg.6109)))) -> (p (Top.top.{u} α (OrderTop.toTop.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6106 (BoundedOrder.toOrderTop.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6106 inst._@.Mathlib.Order.BoundedOrder._hyg.6109)))) -> (BoundedOrder.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6106 p))
Case conversion may be inaccurate. Consider using '#align subtype.bounded_order Subtype.boundedOrderₓ'. -/
-- See note [reducible non-instances]
/-- A subtype remains a bounded order if the property holds at `⊥` and `⊤`. -/
@[reducible]
protected def boundedOrder [LE α] [BoundedOrder α] (hbot : p ⊥) (htop : p ⊤) :
    BoundedOrder (Subtype p) :=
  { Subtype.orderTop htop, Subtype.orderBot hbot with }
#align subtype.bounded_order Subtype.boundedOrder

variable [PartialOrder α]

/- warning: subtype.mk_bot -> Subtype.mk_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {p : α -> Prop} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : OrderBot.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p)] (hbot : p (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))), Eq.{max 1 (succ u)} (Subtype.{succ u} α p) (Subtype.mk.{succ u} α p (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)) hbot) (Bot.bot.{u} (Subtype.{succ u} α p) (OrderBot.toHasBot.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p) _inst_3))
but is expected to have type
  forall {α : Type.{u}} {p : α -> Prop} [inst._@.Mathlib.Order.BoundedOrder._hyg.6168 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6171 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6168))] [inst._@.Mathlib.Order.BoundedOrder._hyg.6174 : OrderBot.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6168)) p)] (hbot : p (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6168)) inst._@.Mathlib.Order.BoundedOrder._hyg.6171))), Eq.{succ u} (Subtype.{succ u} α p) (Subtype.mk.{succ u} α p (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6168)) inst._@.Mathlib.Order.BoundedOrder._hyg.6171)) hbot) (Bot.bot.{u} (Subtype.{succ u} α p) (OrderBot.toBot.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6168)) p) inst._@.Mathlib.Order.BoundedOrder._hyg.6174))
Case conversion may be inaccurate. Consider using '#align subtype.mk_bot Subtype.mk_botₓ'. -/
@[simp]
theorem mk_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : mk ⊥ hbot = ⊥ :=
  le_bot_iff.1 <| coe_le_coe.1 bot_le
#align subtype.mk_bot Subtype.mk_bot

/- warning: subtype.mk_top -> Subtype.mk_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {p : α -> Prop} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : OrderTop.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p)] (htop : p (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))), Eq.{max 1 (succ u)} (Subtype.{succ u} α p) (Subtype.mk.{succ u} α p (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)) htop) (Top.top.{u} (Subtype.{succ u} α p) (OrderTop.toHasTop.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p) _inst_3))
but is expected to have type
  forall {α : Type.{u}} {p : α -> Prop} [inst._@.Mathlib.Order.BoundedOrder._hyg.6210 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6213 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6210))] [inst._@.Mathlib.Order.BoundedOrder._hyg.6216 : OrderTop.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6210)) p)] (htop : p (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6210)) inst._@.Mathlib.Order.BoundedOrder._hyg.6213))), Eq.{succ u} (Subtype.{succ u} α p) (Subtype.mk.{succ u} α p (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6210)) inst._@.Mathlib.Order.BoundedOrder._hyg.6213)) htop) (Top.top.{u} (Subtype.{succ u} α p) (OrderTop.toTop.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6210)) p) inst._@.Mathlib.Order.BoundedOrder._hyg.6216))
Case conversion may be inaccurate. Consider using '#align subtype.mk_top Subtype.mk_topₓ'. -/
@[simp]
theorem mk_top [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) : mk ⊤ htop = ⊤ :=
  top_le_iff.1 <| coe_le_coe.1 le_top
#align subtype.mk_top Subtype.mk_top

/- warning: subtype.coe_bot -> Subtype.coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {p : α -> Prop} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : OrderBot.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p)], (p (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) -> (Eq.{succ u} α ((fun (a : Sort.{max 1 (succ u)}) (b : Type.{u}) [self : HasLiftT.{max 1 (succ u), succ u} a b] => self.0) (Subtype.{succ u} α p) α (HasLiftT.mk.{max 1 (succ u), succ u} (Subtype.{succ u} α p) α (CoeTCₓ.coe.{max 1 (succ u), succ u} (Subtype.{succ u} α p) α (CoeTCₓ.mk.{max 1 (succ u), succ u} (Subtype.{succ u} α p) α (Subtype.val.{succ u} α (fun (x : α) => (fun (x : α) => p x) x))))) (Bot.bot.{u} (Subtype.{succ u} α p) (OrderBot.toHasBot.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p) _inst_3))) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} {p : α -> Prop} [inst._@.Mathlib.Order.BoundedOrder._hyg.6252 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6255 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6252))] [inst._@.Mathlib.Order.BoundedOrder._hyg.6258 : OrderBot.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6252)) p)], (p (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6252)) inst._@.Mathlib.Order.BoundedOrder._hyg.6255))) -> (Eq.{succ u} α (Subtype.val.{succ u} α p (Bot.bot.{u} (Subtype.{succ u} α p) (OrderBot.toBot.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6252)) p) inst._@.Mathlib.Order.BoundedOrder._hyg.6258))) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6252)) inst._@.Mathlib.Order.BoundedOrder._hyg.6255)))
Case conversion may be inaccurate. Consider using '#align subtype.coe_bot Subtype.coe_botₓ'. -/
theorem coe_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : ((⊥ : Subtype p) : α) = ⊥ :=
  congr_arg coe (mk_bot hbot).symm
#align subtype.coe_bot Subtype.coe_bot

/- warning: subtype.coe_top -> Subtype.coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {p : α -> Prop} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : OrderTop.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p)], (p (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) -> (Eq.{succ u} α ((fun (a : Sort.{max 1 (succ u)}) (b : Type.{u}) [self : HasLiftT.{max 1 (succ u), succ u} a b] => self.0) (Subtype.{succ u} α p) α (HasLiftT.mk.{max 1 (succ u), succ u} (Subtype.{succ u} α p) α (CoeTCₓ.coe.{max 1 (succ u), succ u} (Subtype.{succ u} α p) α (CoeTCₓ.mk.{max 1 (succ u), succ u} (Subtype.{succ u} α p) α (Subtype.val.{succ u} α (fun (x : α) => (fun (x : α) => p x) x))))) (Top.top.{u} (Subtype.{succ u} α p) (OrderTop.toHasTop.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p) _inst_3))) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} {p : α -> Prop} [inst._@.Mathlib.Order.BoundedOrder._hyg.6302 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6305 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6302))] [inst._@.Mathlib.Order.BoundedOrder._hyg.6308 : OrderTop.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6302)) p)], (p (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6302)) inst._@.Mathlib.Order.BoundedOrder._hyg.6305))) -> (Eq.{succ u} α (Subtype.val.{succ u} α p (Top.top.{u} (Subtype.{succ u} α p) (OrderTop.toTop.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6302)) p) inst._@.Mathlib.Order.BoundedOrder._hyg.6308))) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6302)) inst._@.Mathlib.Order.BoundedOrder._hyg.6305)))
Case conversion may be inaccurate. Consider using '#align subtype.coe_top Subtype.coe_topₓ'. -/
theorem coe_top [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) : ((⊤ : Subtype p) : α) = ⊤ :=
  congr_arg coe (mk_top htop).symm
#align subtype.coe_top Subtype.coe_top

/- warning: subtype.coe_eq_bot_iff -> Subtype.coe_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {p : α -> Prop} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : OrderBot.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p)], (p (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) -> (forall {x : Subtype.{succ u} α (fun (x : α) => p x)}, Iff (Eq.{succ u} α ((fun (a : Sort.{max 1 (succ u)}) (b : Type.{u}) [self : HasLiftT.{max 1 (succ u), succ u} a b] => self.0) (Subtype.{succ u} α (fun (x : α) => p x)) α (HasLiftT.mk.{max 1 (succ u), succ u} (Subtype.{succ u} α (fun (x : α) => p x)) α (CoeTCₓ.coe.{max 1 (succ u), succ u} (Subtype.{succ u} α (fun (x : α) => p x)) α (CoeTCₓ.mk.{max 1 (succ u), succ u} (Subtype.{succ u} α (fun (x : α) => p x)) α (Subtype.val.{succ u} α (fun (x : α) => (fun (x : α) => p x) x))))) x) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (Eq.{max 1 (succ u)} (Subtype.{succ u} α (fun (x : α) => p x)) x (Bot.bot.{u} (Subtype.{succ u} α (fun (x : α) => p x)) (OrderBot.toHasBot.{u} (Subtype.{succ u} α (fun (x : α) => p x)) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p) _inst_3))))
but is expected to have type
  forall {α : Type.{u}} {p : α -> Prop} [inst._@.Mathlib.Order.BoundedOrder._hyg.6352 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6355 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6352))] [inst._@.Mathlib.Order.BoundedOrder._hyg.6358 : OrderBot.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6352)) p)], (p (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6352)) inst._@.Mathlib.Order.BoundedOrder._hyg.6355))) -> (forall {x : Subtype.{succ u} α (fun (x : α) => p x)}, Iff (Eq.{succ u} α (Subtype.val.{succ u} α (fun (x : α) => p x) x) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6352)) inst._@.Mathlib.Order.BoundedOrder._hyg.6355))) (Eq.{succ u} (Subtype.{succ u} α (fun (x : α) => p x)) x (Bot.bot.{u} (Subtype.{succ u} α (fun (x : α) => p x)) (OrderBot.toBot.{u} (Subtype.{succ u} α (fun (x : α) => p x)) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6352)) (fun (x : α) => p x)) inst._@.Mathlib.Order.BoundedOrder._hyg.6358))))
Case conversion may be inaccurate. Consider using '#align subtype.coe_eq_bot_iff Subtype.coe_eq_bot_iffₓ'. -/
@[simp]
theorem coe_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : { x // p x }} :
    (x : α) = ⊥ ↔ x = ⊥ := by rw [← coe_bot hbot, ext_iff]
#align subtype.coe_eq_bot_iff Subtype.coe_eq_bot_iff

/- warning: subtype.coe_eq_top_iff -> Subtype.coe_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {p : α -> Prop} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : OrderTop.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p)], (p (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) -> (forall {x : Subtype.{succ u} α (fun (x : α) => p x)}, Iff (Eq.{succ u} α ((fun (a : Sort.{max 1 (succ u)}) (b : Type.{u}) [self : HasLiftT.{max 1 (succ u), succ u} a b] => self.0) (Subtype.{succ u} α (fun (x : α) => p x)) α (HasLiftT.mk.{max 1 (succ u), succ u} (Subtype.{succ u} α (fun (x : α) => p x)) α (CoeTCₓ.coe.{max 1 (succ u), succ u} (Subtype.{succ u} α (fun (x : α) => p x)) α (CoeTCₓ.mk.{max 1 (succ u), succ u} (Subtype.{succ u} α (fun (x : α) => p x)) α (Subtype.val.{succ u} α (fun (x : α) => (fun (x : α) => p x) x))))) x) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (Eq.{max 1 (succ u)} (Subtype.{succ u} α (fun (x : α) => p x)) x (Top.top.{u} (Subtype.{succ u} α (fun (x : α) => p x)) (OrderTop.toHasTop.{u} (Subtype.{succ u} α (fun (x : α) => p x)) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p) _inst_3))))
but is expected to have type
  forall {α : Type.{u}} {p : α -> Prop} [inst._@.Mathlib.Order.BoundedOrder._hyg.6440 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6443 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6440))] [inst._@.Mathlib.Order.BoundedOrder._hyg.6446 : OrderTop.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6440)) p)], (p (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6440)) inst._@.Mathlib.Order.BoundedOrder._hyg.6443))) -> (forall {x : Subtype.{succ u} α (fun (x : α) => p x)}, Iff (Eq.{succ u} α (Subtype.val.{succ u} α (fun (x : α) => p x) x) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6440)) inst._@.Mathlib.Order.BoundedOrder._hyg.6443))) (Eq.{succ u} (Subtype.{succ u} α (fun (x : α) => p x)) x (Top.top.{u} (Subtype.{succ u} α (fun (x : α) => p x)) (OrderTop.toTop.{u} (Subtype.{succ u} α (fun (x : α) => p x)) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6440)) (fun (x : α) => p x)) inst._@.Mathlib.Order.BoundedOrder._hyg.6446))))
Case conversion may be inaccurate. Consider using '#align subtype.coe_eq_top_iff Subtype.coe_eq_top_iffₓ'. -/
@[simp]
theorem coe_eq_top_iff [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) {x : { x // p x }} :
    (x : α) = ⊤ ↔ x = ⊤ := by rw [← coe_top htop, ext_iff]
#align subtype.coe_eq_top_iff Subtype.coe_eq_top_iff

/- warning: subtype.mk_eq_bot_iff -> Subtype.mk_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {p : α -> Prop} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : OrderBot.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p)], (p (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) -> (forall {x : α} (hx : p x), Iff (Eq.{max 1 (succ u)} (Subtype.{succ u} α p) (Subtype.mk.{succ u} α p x hx) (Bot.bot.{u} (Subtype.{succ u} α p) (OrderBot.toHasBot.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p) _inst_3))) (Eq.{succ u} α x (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} {p : α -> Prop} [inst._@.Mathlib.Order.BoundedOrder._hyg.6528 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6531 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6528))] [inst._@.Mathlib.Order.BoundedOrder._hyg.6534 : OrderBot.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6528)) p)], (p (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6528)) inst._@.Mathlib.Order.BoundedOrder._hyg.6531))) -> (forall {x : α} (hx : p x), Iff (Eq.{succ u} (Subtype.{succ u} α p) (Subtype.mk.{succ u} α p x hx) (Bot.bot.{u} (Subtype.{succ u} α p) (OrderBot.toBot.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6528)) p) inst._@.Mathlib.Order.BoundedOrder._hyg.6534))) (Eq.{succ u} α x (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6528)) inst._@.Mathlib.Order.BoundedOrder._hyg.6531))))
Case conversion may be inaccurate. Consider using '#align subtype.mk_eq_bot_iff Subtype.mk_eq_bot_iffₓ'. -/
@[simp]
theorem mk_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : α} (hx : p x) :
    (⟨x, hx⟩ : Subtype p) = ⊥ ↔ x = ⊥ :=
  (coe_eq_bot_iff hbot).symm
#align subtype.mk_eq_bot_iff Subtype.mk_eq_bot_iff

/- warning: subtype.mk_eq_top_iff -> Subtype.mk_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {p : α -> Prop} [_inst_1 : PartialOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : OrderTop.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p)], (p (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) -> (forall {x : α} (hx : p x), Iff (Eq.{max 1 (succ u)} (Subtype.{succ u} α p) (Subtype.mk.{succ u} α p x hx) (Top.top.{u} (Subtype.{succ u} α p) (OrderTop.toHasTop.{u} (Subtype.{succ u} α p) (Subtype.hasLe.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) p) _inst_3))) (Eq.{succ u} α x (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} {p : α -> Prop} [inst._@.Mathlib.Order.BoundedOrder._hyg.6588 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6591 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6588))] [inst._@.Mathlib.Order.BoundedOrder._hyg.6594 : OrderTop.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6588)) p)], (p (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6588)) inst._@.Mathlib.Order.BoundedOrder._hyg.6591))) -> (forall {x : α} (hx : p x), Iff (Eq.{succ u} (Subtype.{succ u} α p) (Subtype.mk.{succ u} α p x hx) (Top.top.{u} (Subtype.{succ u} α p) (OrderTop.toTop.{u} (Subtype.{succ u} α p) (Subtype.instLESubtype.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6588)) p) inst._@.Mathlib.Order.BoundedOrder._hyg.6594))) (Eq.{succ u} α x (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6588)) inst._@.Mathlib.Order.BoundedOrder._hyg.6591))))
Case conversion may be inaccurate. Consider using '#align subtype.mk_eq_top_iff Subtype.mk_eq_top_iffₓ'. -/
@[simp]
theorem mk_eq_top_iff [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) {x : α} (hx : p x) :
    (⟨x, hx⟩ : Subtype p) = ⊤ ↔ x = ⊤ :=
  (coe_eq_top_iff htop).symm
#align subtype.mk_eq_top_iff Subtype.mk_eq_top_iff

end Subtype

namespace Prod

variable (α β)

instance [Top α] [Top β] : Top (α × β) :=
  ⟨⟨⊤, ⊤⟩⟩

instance [Bot α] [Bot β] : Bot (α × β) :=
  ⟨⟨⊥, ⊥⟩⟩

instance [LE α] [LE β] [OrderTop α] [OrderTop β] : OrderTop (α × β) :=
  { Prod.hasTop α β with le_top := fun a => ⟨le_top, le_top⟩ }

instance [LE α] [LE β] [OrderBot α] [OrderBot β] : OrderBot (α × β) :=
  { Prod.hasBot α β with bot_le := fun a => ⟨bot_le, bot_le⟩ }

instance [LE α] [LE β] [BoundedOrder α] [BoundedOrder β] : BoundedOrder (α × β) :=
  { Prod.orderTop α β, Prod.orderBot α β with }

end Prod

section LinearOrder

variable [LinearOrder α]

/- warning: min_bot_left -> min_bot_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))] (a : α), Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2)) a) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.6906 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6909 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6906))))))] (a : α), Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6906) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6906)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.6909)) a) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6906)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.6909))
Case conversion may be inaccurate. Consider using '#align min_bot_left min_bot_leftₓ'. -/
-- `simp` can prove these, so they shouldn't be simp-lemmas.
theorem min_bot_left [OrderBot α] (a : α) : min ⊥ a = ⊥ :=
  bot_inf_eq
#align min_bot_left min_bot_left

/- warning: max_top_left -> max_top_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))] (a : α), Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2)) a) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.6932 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6935 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6932))))))] (a : α), Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6932) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6932)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.6935)) a) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6932)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.6935))
Case conversion may be inaccurate. Consider using '#align max_top_left max_top_leftₓ'. -/
theorem max_top_left [OrderTop α] (a : α) : max ⊤ a = ⊤ :=
  top_sup_eq
#align max_top_left max_top_left

/- warning: min_top_left -> min_top_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))] (a : α), Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2)) a) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.6958 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6961 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6958))))))] (a : α), Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6958) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6958)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.6961)) a) a
Case conversion may be inaccurate. Consider using '#align min_top_left min_top_leftₓ'. -/
theorem min_top_left [OrderTop α] (a : α) : min ⊤ a = a :=
  top_inf_eq
#align min_top_left min_top_left

/- warning: max_bot_left -> max_bot_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))] (a : α), Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2)) a) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.6981 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.6984 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6981))))))] (a : α), Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6981) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.6981)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.6984)) a) a
Case conversion may be inaccurate. Consider using '#align max_bot_left max_bot_leftₓ'. -/
theorem max_bot_left [OrderBot α] (a : α) : max ⊥ a = a :=
  bot_sup_eq
#align max_bot_left max_bot_left

/- warning: min_top_right -> min_top_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))] (a : α), Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.7004 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.7007 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7004))))))] (a : α), Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7004) a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7004)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7007))) a
Case conversion may be inaccurate. Consider using '#align min_top_right min_top_rightₓ'. -/
theorem min_top_right [OrderTop α] (a : α) : min a ⊤ = a :=
  inf_top_eq
#align min_top_right min_top_right

/- warning: max_bot_right -> max_bot_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))] (a : α), Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.7027 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.7030 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7027))))))] (a : α), Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7027) a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7027)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7030))) a
Case conversion may be inaccurate. Consider using '#align max_bot_right max_bot_rightₓ'. -/
theorem max_bot_right [OrderBot α] (a : α) : max a ⊥ = a :=
  sup_bot_eq
#align max_bot_right max_bot_right

/- warning: min_bot_right -> min_bot_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))] (a : α), Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.7050 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.7053 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7050))))))] (a : α), Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7050) a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7050)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7053))) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7050)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7053))
Case conversion may be inaccurate. Consider using '#align min_bot_right min_bot_rightₓ'. -/
theorem min_bot_right [OrderBot α] (a : α) : min a ⊥ = ⊥ :=
  inf_bot_eq
#align min_bot_right min_bot_right

/- warning: max_top_right -> max_top_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))] (a : α), Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.7076 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.7079 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7076))))))] (a : α), Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7076) a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7076)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7079))) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7076)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7079))
Case conversion may be inaccurate. Consider using '#align max_top_right max_top_rightₓ'. -/
theorem max_top_right [OrderTop α] (a : α) : max a ⊤ = ⊤ :=
  sup_top_eq
#align max_top_right max_top_right

/- warning: min_eq_bot -> min_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))] {a : α} {b : α}, Iff (Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))) (Or (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))) (Eq.{succ u} α b (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.7102 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.7105 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7102))))))] {a : α} {b : α}, Iff (Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7102) a b) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7102)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7105))) (Or (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7102)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7105))) (Eq.{succ u} α b (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7102)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7105))))
Case conversion may be inaccurate. Consider using '#align min_eq_bot min_eq_botₓ'. -/
@[simp]
theorem min_eq_bot [OrderBot α] {a b : α} : min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := by
  simp only [← inf_eq_min, ← le_bot_iff, inf_le_iff]
#align min_eq_bot min_eq_bot

/- warning: max_eq_top -> max_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))] {a : α} {b : α}, Iff (Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))) (Or (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))) (Eq.{succ u} α b (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.7157 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.7160 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7157))))))] {a : α} {b : α}, Iff (Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7157) a b) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7157)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7160))) (Or (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7157)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7160))) (Eq.{succ u} α b (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7157)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7160))))
Case conversion may be inaccurate. Consider using '#align max_eq_top max_eq_topₓ'. -/
@[simp]
theorem max_eq_top [OrderTop α] {a b : α} : max a b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
  @min_eq_bot αᵒᵈ _ _ a b
#align max_eq_top max_eq_top

/- warning: max_eq_bot -> max_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))] {a : α} {b : α}, Iff (Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))) (And (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))) (Eq.{succ u} α b (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.7210 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.7213 : OrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7210))))))] {a : α} {b : α}, Iff (Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7210) a b) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7210)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7213))) (And (Eq.{succ u} α a (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7210)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7213))) (Eq.{succ u} α b (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7210)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7213))))
Case conversion may be inaccurate. Consider using '#align max_eq_bot max_eq_botₓ'. -/
@[simp]
theorem max_eq_bot [OrderBot α] {a b : α} : max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥ :=
  sup_eq_bot_iff
#align max_eq_bot max_eq_bot

/- warning: min_eq_top -> min_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))))] {a : α} {b : α}, Iff (Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))) (And (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))) (Eq.{succ u} α b (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) _inst_2))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.7257 : LinearOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.7260 : OrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7257))))))] {a : α} {b : α}, Iff (Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7257) a b) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7257)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7260))) (And (Eq.{succ u} α a (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7257)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7260))) (Eq.{succ u} α b (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7257)))))) inst._@.Mathlib.Order.BoundedOrder._hyg.7260))))
Case conversion may be inaccurate. Consider using '#align min_eq_top min_eq_topₓ'. -/
@[simp]
theorem min_eq_top [OrderTop α] {a b : α} : min a b = ⊤ ↔ a = ⊤ ∧ b = ⊤ :=
  inf_eq_top_iff
#align min_eq_top min_eq_top

end LinearOrder

section Nontrivial

variable [PartialOrder α] [BoundedOrder α] [Nontrivial α]

/- warning: bot_ne_top -> bot_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : Nontrivial.{u} α], Ne.{succ u} α (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.7323 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.7326 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7323))] [inst._@.Mathlib.Order.BoundedOrder._hyg.7329 : Nontrivial.{u} α], Ne.{succ u} α (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7323)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7323)) inst._@.Mathlib.Order.BoundedOrder._hyg.7326))) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7323)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7323)) inst._@.Mathlib.Order.BoundedOrder._hyg.7326)))
Case conversion may be inaccurate. Consider using '#align bot_ne_top bot_ne_topₓ'. -/
@[simp]
theorem bot_ne_top : (⊥ : α) ≠ ⊤ := fun h => not_subsingleton _ <| subsingleton_of_bot_eq_top h
#align bot_ne_top bot_ne_top

/- warning: top_ne_bot -> top_ne_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : Nontrivial.{u} α], Ne.{succ u} α (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.7359 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.7362 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7359))] [inst._@.Mathlib.Order.BoundedOrder._hyg.7365 : Nontrivial.{u} α], Ne.{succ u} α (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7359)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7359)) inst._@.Mathlib.Order.BoundedOrder._hyg.7362))) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7359)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7359)) inst._@.Mathlib.Order.BoundedOrder._hyg.7362)))
Case conversion may be inaccurate. Consider using '#align top_ne_bot top_ne_botₓ'. -/
@[simp]
theorem top_ne_bot : (⊤ : α) ≠ ⊥ :=
  bot_ne_top.symm
#align top_ne_bot top_ne_bot

/- warning: bot_lt_top -> bot_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : PartialOrder.{u} α] [_inst_2 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1))] [_inst_3 : Nontrivial.{u} α], LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (Bot.bot.{u} α (OrderBot.toHasBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2))) (Top.top.{u} α (OrderTop.toHasTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.BoundedOrder._hyg.7387 : PartialOrder.{u} α] [inst._@.Mathlib.Order.BoundedOrder._hyg.7390 : BoundedOrder.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7387))] [inst._@.Mathlib.Order.BoundedOrder._hyg.7393 : Nontrivial.{u} α], LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7387)) (Bot.bot.{u} α (OrderBot.toBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7387)) (BoundedOrder.toOrderBot.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7387)) inst._@.Mathlib.Order.BoundedOrder._hyg.7390))) (Top.top.{u} α (OrderTop.toTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7387)) (BoundedOrder.toOrderTop.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α inst._@.Mathlib.Order.BoundedOrder._hyg.7387)) inst._@.Mathlib.Order.BoundedOrder._hyg.7390)))
Case conversion may be inaccurate. Consider using '#align bot_lt_top bot_lt_topₓ'. -/
@[simp]
theorem bot_lt_top : (⊥ : α) < ⊤ :=
  lt_top_iff_ne_top.2 bot_ne_top
#align bot_lt_top bot_lt_top

end Nontrivial

section Bool

open Bool

instance : BoundedOrder Bool where 
  top := true
  le_top x := le_true
  bot := false
  bot_le x := false_le

/- warning: top_eq_tt -> top_eq_true is a dubious translation:
lean 3 declaration is
  Eq.{1} Bool (Top.top.{0} Bool (OrderTop.toHasTop.{0} Bool (Preorder.toLE.{0} Bool (PartialOrder.toPreorder.{0} Bool (SemilatticeInf.toPartialOrder.{0} Bool (Lattice.toSemilatticeInf.{0} Bool (LinearOrder.toLattice.{0} Bool Bool.instLinearOrderBool))))) (BoundedOrder.toOrderTop.{0} Bool (Preorder.toLE.{0} Bool (PartialOrder.toPreorder.{0} Bool (SemilatticeInf.toPartialOrder.{0} Bool (Lattice.toSemilatticeInf.{0} Bool (LinearOrder.toLattice.{0} Bool Bool.instLinearOrderBool))))) Bool.boundedOrder))) Bool.true
but is expected to have type
  Eq.{1} Bool (Top.top.{0} Bool (OrderTop.toTop.{0} Bool (Preorder.toLE.{0} Bool (PartialOrder.toPreorder.{0} Bool (SemilatticeInf.toPartialOrder.{0} Bool (Lattice.toSemilatticeInf.{0} Bool (DistribLattice.toLattice.{0} Bool instDistribLatticeBool))))) (BoundedOrder.toOrderTop.{0} Bool (Preorder.toLE.{0} Bool (PartialOrder.toPreorder.{0} Bool (SemilatticeInf.toPartialOrder.{0} Bool (Lattice.toSemilatticeInf.{0} Bool (DistribLattice.toLattice.{0} Bool instDistribLatticeBool))))) instBoundedOrderBoolToLEToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeBool))) Bool.true
Case conversion may be inaccurate. Consider using '#align top_eq_tt top_eq_trueₓ'. -/
@[simp]
theorem top_eq_true : ⊤ = tt :=
  rfl
#align top_eq_tt top_eq_true

/- warning: bot_eq_ff -> bot_eq_false is a dubious translation:
lean 3 declaration is
  Eq.{1} Bool (Bot.bot.{0} Bool (OrderBot.toHasBot.{0} Bool (Preorder.toLE.{0} Bool (PartialOrder.toPreorder.{0} Bool (SemilatticeInf.toPartialOrder.{0} Bool (Lattice.toSemilatticeInf.{0} Bool (LinearOrder.toLattice.{0} Bool Bool.instLinearOrderBool))))) (BoundedOrder.toOrderBot.{0} Bool (Preorder.toLE.{0} Bool (PartialOrder.toPreorder.{0} Bool (SemilatticeInf.toPartialOrder.{0} Bool (Lattice.toSemilatticeInf.{0} Bool (LinearOrder.toLattice.{0} Bool Bool.instLinearOrderBool))))) Bool.boundedOrder))) Bool.false
but is expected to have type
  Eq.{1} Bool (Bot.bot.{0} Bool (OrderBot.toBot.{0} Bool (Preorder.toLE.{0} Bool (PartialOrder.toPreorder.{0} Bool (SemilatticeInf.toPartialOrder.{0} Bool (Lattice.toSemilatticeInf.{0} Bool (DistribLattice.toLattice.{0} Bool instDistribLatticeBool))))) (BoundedOrder.toOrderBot.{0} Bool (Preorder.toLE.{0} Bool (PartialOrder.toPreorder.{0} Bool (SemilatticeInf.toPartialOrder.{0} Bool (Lattice.toSemilatticeInf.{0} Bool (DistribLattice.toLattice.{0} Bool instDistribLatticeBool))))) instBoundedOrderBoolToLEToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeBool))) Bool.false
Case conversion may be inaccurate. Consider using '#align bot_eq_ff bot_eq_falseₓ'. -/
@[simp]
theorem bot_eq_false : ⊥ = ff :=
  rfl
#align bot_eq_ff bot_eq_false

end Bool

