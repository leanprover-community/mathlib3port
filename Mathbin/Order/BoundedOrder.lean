/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Order.Lattice
import Data.Option.Basic

#align_import order.bounded_order from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# ⊤ and ⊥, bounded lattices and variants

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
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

notation "⊤" => Top.top

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
noncomputable def topOrderOrNoTopOrder (α : Type _) [LE α] : PSum (OrderTop α) (NoTopOrder α) :=
  by
  by_cases H : ∀ a : α, ∃ b, ¬b ≤ a
  · exact PSum.inr ⟨H⟩
  · push_neg at H 
    exact PSum.inl ⟨_, Classical.choose_spec H⟩
#align top_order_or_no_top_order topOrderOrNoTopOrder
-/

section LE

variable [LE α] [OrderTop α] {a : α}

#print le_top /-
@[simp]
theorem le_top : a ≤ ⊤ :=
  OrderTop.le_top a
#align le_top le_top
-/

#print isTop_top /-
@[simp]
theorem isTop_top : IsTop (⊤ : α) := fun _ => le_top
#align is_top_top isTop_top
-/

end LE

section Preorder

variable [Preorder α] [OrderTop α] {a b : α}

#print isMax_top /-
@[simp]
theorem isMax_top : IsMax (⊤ : α) :=
  isTop_top.IsMax
#align is_max_top isMax_top
-/

#print not_top_lt /-
@[simp]
theorem not_top_lt : ¬⊤ < a :=
  isMax_top.not_lt
#align not_top_lt not_top_lt
-/

#print ne_top_of_lt /-
theorem ne_top_of_lt (h : a < b) : a ≠ ⊤ :=
  (h.trans_le le_top).Ne
#align ne_top_of_lt ne_top_of_lt
-/

alias LT.lt.ne_top := ne_top_of_lt
#align has_lt.lt.ne_top LT.lt.ne_top

end Preorder

variable [PartialOrder α] [OrderTop α] [Preorder β] {f : α → β} {a b : α}

#print isMax_iff_eq_top /-
@[simp]
theorem isMax_iff_eq_top : IsMax a ↔ a = ⊤ :=
  ⟨fun h => h.eq_of_le le_top, fun h b _ => h.symm ▸ le_top⟩
#align is_max_iff_eq_top isMax_iff_eq_top
-/

#print isTop_iff_eq_top /-
@[simp]
theorem isTop_iff_eq_top : IsTop a ↔ a = ⊤ :=
  ⟨fun h => h.IsMax.eq_of_le le_top, fun h b => h.symm ▸ le_top⟩
#align is_top_iff_eq_top isTop_iff_eq_top
-/

#print not_isMax_iff_ne_top /-
theorem not_isMax_iff_ne_top : ¬IsMax a ↔ a ≠ ⊤ :=
  isMax_iff_eq_top.Not
#align not_is_max_iff_ne_top not_isMax_iff_ne_top
-/

#print not_isTop_iff_ne_top /-
theorem not_isTop_iff_ne_top : ¬IsTop a ↔ a ≠ ⊤ :=
  isTop_iff_eq_top.Not
#align not_is_top_iff_ne_top not_isTop_iff_ne_top
-/

alias ⟨IsMax.eq_top, _⟩ := isMax_iff_eq_top
#align is_max.eq_top IsMax.eq_top

alias ⟨IsTop.eq_top, _⟩ := isTop_iff_eq_top
#align is_top.eq_top IsTop.eq_top

#print top_le_iff /-
@[simp]
theorem top_le_iff : ⊤ ≤ a ↔ a = ⊤ :=
  le_top.le_iff_eq.trans eq_comm
#align top_le_iff top_le_iff
-/

#print top_unique /-
theorem top_unique (h : ⊤ ≤ a) : a = ⊤ :=
  le_top.antisymm h
#align top_unique top_unique
-/

#print eq_top_iff /-
theorem eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
  top_le_iff.symm
#align eq_top_iff eq_top_iff
-/

#print eq_top_mono /-
theorem eq_top_mono (h : a ≤ b) (h₂ : a = ⊤) : b = ⊤ :=
  top_unique <| h₂ ▸ h
#align eq_top_mono eq_top_mono
-/

#print lt_top_iff_ne_top /-
theorem lt_top_iff_ne_top : a < ⊤ ↔ a ≠ ⊤ :=
  le_top.lt_iff_ne
#align lt_top_iff_ne_top lt_top_iff_ne_top
-/

#print not_lt_top_iff /-
@[simp]
theorem not_lt_top_iff : ¬a < ⊤ ↔ a = ⊤ :=
  lt_top_iff_ne_top.not_left
#align not_lt_top_iff not_lt_top_iff
-/

#print eq_top_or_lt_top /-
theorem eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤ :=
  le_top.eq_or_lt
#align eq_top_or_lt_top eq_top_or_lt_top
-/

#print Ne.lt_top /-
theorem Ne.lt_top (h : a ≠ ⊤) : a < ⊤ :=
  lt_top_iff_ne_top.mpr h
#align ne.lt_top Ne.lt_top
-/

#print Ne.lt_top' /-
theorem Ne.lt_top' (h : ⊤ ≠ a) : a < ⊤ :=
  h.symm.lt_top
#align ne.lt_top' Ne.lt_top'
-/

#print ne_top_of_le_ne_top /-
theorem ne_top_of_le_ne_top (hb : b ≠ ⊤) (hab : a ≤ b) : a ≠ ⊤ :=
  (hab.trans_lt hb.lt_top).Ne
#align ne_top_of_le_ne_top ne_top_of_le_ne_top
-/

#print StrictMono.apply_eq_top_iff /-
theorem StrictMono.apply_eq_top_iff (hf : StrictMono f) : f a = f ⊤ ↔ a = ⊤ :=
  ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).Ne h, congr_arg _⟩
#align strict_mono.apply_eq_top_iff StrictMono.apply_eq_top_iff
-/

#print StrictAnti.apply_eq_top_iff /-
theorem StrictAnti.apply_eq_top_iff (hf : StrictAnti f) : f a = f ⊤ ↔ a = ⊤ :=
  ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).ne' h, congr_arg _⟩
#align strict_anti.apply_eq_top_iff StrictAnti.apply_eq_top_iff
-/

variable [Nontrivial α]

#print not_isMin_top /-
theorem not_isMin_top : ¬IsMin (⊤ : α) := fun h =>
  let ⟨a, ha⟩ := exists_ne (⊤ : α)
  ha <| top_le_iff.1 <| h le_top
#align not_is_min_top not_isMin_top
-/

end OrderTop

#print StrictMono.maximal_preimage_top /-
theorem StrictMono.maximal_preimage_top [LinearOrder α] [Preorder β] [OrderTop β] {f : α → β}
    (H : StrictMono f) {a} (h_top : f a = ⊤) (x : α) : x ≤ a :=
  H.maximal_of_maximal_image (fun p => by rw [h_top]; exact le_top) x
#align strict_mono.maximal_preimage_top StrictMono.maximal_preimage_top
-/

#print OrderTop.ext_top /-
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
-/

#print OrderTop.ext /-
theorem OrderTop.ext {α} [PartialOrder α] {A B : OrderTop α} : A = B :=
  by
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
noncomputable def botOrderOrNoBotOrder (α : Type _) [LE α] : PSum (OrderBot α) (NoBotOrder α) :=
  by
  by_cases H : ∀ a : α, ∃ b, ¬a ≤ b
  · exact PSum.inr ⟨H⟩
  · push_neg at H 
    exact PSum.inl ⟨_, Classical.choose_spec H⟩
#align bot_order_or_no_bot_order botOrderOrNoBotOrder
-/

section LE

variable [LE α] [OrderBot α] {a : α}

#print bot_le /-
@[simp]
theorem bot_le : ⊥ ≤ a :=
  OrderBot.bot_le a
#align bot_le bot_le
-/

#print isBot_bot /-
@[simp]
theorem isBot_bot : IsBot (⊥ : α) := fun _ => bot_le
#align is_bot_bot isBot_bot
-/

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

#print isMin_bot /-
@[simp]
theorem isMin_bot : IsMin (⊥ : α) :=
  isBot_bot.IsMin
#align is_min_bot isMin_bot
-/

#print not_lt_bot /-
@[simp]
theorem not_lt_bot : ¬a < ⊥ :=
  isMin_bot.not_lt
#align not_lt_bot not_lt_bot
-/

#print ne_bot_of_gt /-
theorem ne_bot_of_gt (h : a < b) : b ≠ ⊥ :=
  (bot_le.trans_lt h).ne'
#align ne_bot_of_gt ne_bot_of_gt
-/

alias LT.lt.ne_bot := ne_bot_of_gt
#align has_lt.lt.ne_bot LT.lt.ne_bot

end Preorder

variable [PartialOrder α] [OrderBot α] [Preorder β] {f : α → β} {a b : α}

#print isMin_iff_eq_bot /-
@[simp]
theorem isMin_iff_eq_bot : IsMin a ↔ a = ⊥ :=
  ⟨fun h => h.eq_of_ge bot_le, fun h b _ => h.symm ▸ bot_le⟩
#align is_min_iff_eq_bot isMin_iff_eq_bot
-/

#print isBot_iff_eq_bot /-
@[simp]
theorem isBot_iff_eq_bot : IsBot a ↔ a = ⊥ :=
  ⟨fun h => h.IsMin.eq_of_ge bot_le, fun h b => h.symm ▸ bot_le⟩
#align is_bot_iff_eq_bot isBot_iff_eq_bot
-/

#print not_isMin_iff_ne_bot /-
theorem not_isMin_iff_ne_bot : ¬IsMin a ↔ a ≠ ⊥ :=
  isMin_iff_eq_bot.Not
#align not_is_min_iff_ne_bot not_isMin_iff_ne_bot
-/

#print not_isBot_iff_ne_bot /-
theorem not_isBot_iff_ne_bot : ¬IsBot a ↔ a ≠ ⊥ :=
  isBot_iff_eq_bot.Not
#align not_is_bot_iff_ne_bot not_isBot_iff_ne_bot
-/

alias ⟨IsMin.eq_bot, _⟩ := isMin_iff_eq_bot
#align is_min.eq_bot IsMin.eq_bot

alias ⟨IsBot.eq_bot, _⟩ := isBot_iff_eq_bot
#align is_bot.eq_bot IsBot.eq_bot

#print le_bot_iff /-
@[simp]
theorem le_bot_iff : a ≤ ⊥ ↔ a = ⊥ :=
  bot_le.le_iff_eq
#align le_bot_iff le_bot_iff
-/

#print bot_unique /-
theorem bot_unique (h : a ≤ ⊥) : a = ⊥ :=
  h.antisymm bot_le
#align bot_unique bot_unique
-/

#print eq_bot_iff /-
theorem eq_bot_iff : a = ⊥ ↔ a ≤ ⊥ :=
  le_bot_iff.symm
#align eq_bot_iff eq_bot_iff
-/

#print eq_bot_mono /-
theorem eq_bot_mono (h : a ≤ b) (h₂ : b = ⊥) : a = ⊥ :=
  bot_unique <| h₂ ▸ h
#align eq_bot_mono eq_bot_mono
-/

#print bot_lt_iff_ne_bot /-
theorem bot_lt_iff_ne_bot : ⊥ < a ↔ a ≠ ⊥ :=
  bot_le.lt_iff_ne.trans ne_comm
#align bot_lt_iff_ne_bot bot_lt_iff_ne_bot
-/

#print not_bot_lt_iff /-
@[simp]
theorem not_bot_lt_iff : ¬⊥ < a ↔ a = ⊥ :=
  bot_lt_iff_ne_bot.not_left
#align not_bot_lt_iff not_bot_lt_iff
-/

#print eq_bot_or_bot_lt /-
theorem eq_bot_or_bot_lt (a : α) : a = ⊥ ∨ ⊥ < a :=
  bot_le.eq_or_gt
#align eq_bot_or_bot_lt eq_bot_or_bot_lt
-/

#print eq_bot_of_minimal /-
theorem eq_bot_of_minimal (h : ∀ b, ¬b < a) : a = ⊥ :=
  (eq_bot_or_bot_lt a).resolve_right (h ⊥)
#align eq_bot_of_minimal eq_bot_of_minimal
-/

#print Ne.bot_lt /-
theorem Ne.bot_lt (h : a ≠ ⊥) : ⊥ < a :=
  bot_lt_iff_ne_bot.mpr h
#align ne.bot_lt Ne.bot_lt
-/

#print Ne.bot_lt' /-
theorem Ne.bot_lt' (h : ⊥ ≠ a) : ⊥ < a :=
  h.symm.bot_lt
#align ne.bot_lt' Ne.bot_lt'
-/

#print ne_bot_of_le_ne_bot /-
theorem ne_bot_of_le_ne_bot (hb : b ≠ ⊥) (hab : b ≤ a) : a ≠ ⊥ :=
  (hb.bot_lt.trans_le hab).ne'
#align ne_bot_of_le_ne_bot ne_bot_of_le_ne_bot
-/

#print StrictMono.apply_eq_bot_iff /-
theorem StrictMono.apply_eq_bot_iff (hf : StrictMono f) : f a = f ⊥ ↔ a = ⊥ :=
  hf.dual.apply_eq_top_iff
#align strict_mono.apply_eq_bot_iff StrictMono.apply_eq_bot_iff
-/

#print StrictAnti.apply_eq_bot_iff /-
theorem StrictAnti.apply_eq_bot_iff (hf : StrictAnti f) : f a = f ⊥ ↔ a = ⊥ :=
  hf.dual.apply_eq_top_iff
#align strict_anti.apply_eq_bot_iff StrictAnti.apply_eq_bot_iff
-/

variable [Nontrivial α]

#print not_isMax_bot /-
theorem not_isMax_bot : ¬IsMax (⊥ : α) :=
  @not_isMin_top αᵒᵈ _ _ _
#align not_is_max_bot not_isMax_bot
-/

end OrderBot

#print StrictMono.minimal_preimage_bot /-
theorem StrictMono.minimal_preimage_bot [LinearOrder α] [PartialOrder β] [OrderBot β] {f : α → β}
    (H : StrictMono f) {a} (h_bot : f a = ⊥) (x : α) : a ≤ x :=
  H.minimal_of_minimal_image (fun p => by rw [h_bot]; exact bot_le) x
#align strict_mono.minimal_preimage_bot StrictMono.minimal_preimage_bot
-/

#print OrderBot.ext_bot /-
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
-/

#print OrderBot.ext /-
theorem OrderBot.ext {α} [PartialOrder α] {A B : OrderBot α} : A = B :=
  by
  have tt := OrderBot.ext_bot A B fun _ _ => Iff.rfl
  cases' A with a ha; cases' B with b hb
  congr
  exact le_antisymm (ha _) (hb _)
#align order_bot.ext OrderBot.ext
-/

section SemilatticeSupTop

variable [SemilatticeSup α] [OrderTop α] {a : α}

#print top_sup_eq /-
@[simp]
theorem top_sup_eq : ⊤ ⊔ a = ⊤ :=
  sup_of_le_left le_top
#align top_sup_eq top_sup_eq
-/

#print sup_top_eq /-
@[simp]
theorem sup_top_eq : a ⊔ ⊤ = ⊤ :=
  sup_of_le_right le_top
#align sup_top_eq sup_top_eq
-/

end SemilatticeSupTop

section SemilatticeSupBot

variable [SemilatticeSup α] [OrderBot α] {a b : α}

#print bot_sup_eq /-
@[simp]
theorem bot_sup_eq : ⊥ ⊔ a = a :=
  sup_of_le_right bot_le
#align bot_sup_eq bot_sup_eq
-/

#print sup_bot_eq /-
@[simp]
theorem sup_bot_eq : a ⊔ ⊥ = a :=
  sup_of_le_left bot_le
#align sup_bot_eq sup_bot_eq
-/

#print sup_eq_bot_iff /-
@[simp]
theorem sup_eq_bot_iff : a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := by rw [eq_bot_iff, sup_le_iff] <;> simp
#align sup_eq_bot_iff sup_eq_bot_iff
-/

end SemilatticeSupBot

section SemilatticeInfTop

variable [SemilatticeInf α] [OrderTop α] {a b : α}

#print top_inf_eq /-
@[simp]
theorem top_inf_eq : ⊤ ⊓ a = a :=
  inf_of_le_right le_top
#align top_inf_eq top_inf_eq
-/

#print inf_top_eq /-
@[simp]
theorem inf_top_eq : a ⊓ ⊤ = a :=
  inf_of_le_left le_top
#align inf_top_eq inf_top_eq
-/

#print inf_eq_top_iff /-
@[simp]
theorem inf_eq_top_iff : a ⊓ b = ⊤ ↔ a = ⊤ ∧ b = ⊤ :=
  @sup_eq_bot_iff αᵒᵈ _ _ _ _
#align inf_eq_top_iff inf_eq_top_iff
-/

end SemilatticeInfTop

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {a : α}

#print bot_inf_eq /-
@[simp]
theorem bot_inf_eq : ⊥ ⊓ a = ⊥ :=
  inf_of_le_left bot_le
#align bot_inf_eq bot_inf_eq
-/

#print inf_bot_eq /-
@[simp]
theorem inf_bot_eq : a ⊓ ⊥ = ⊥ :=
  inf_of_le_right bot_le
#align inf_bot_eq inf_bot_eq
-/

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
theorem BoundedOrder.ext {α} [PartialOrder α] {A B : BoundedOrder α} : A = B :=
  by
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

#print monotone_and /-
theorem monotone_and {p q : α → Prop} (m_p : Monotone p) (m_q : Monotone q) :
    Monotone fun x => p x ∧ q x := fun a b h => And.imp (m_p h) (m_q h)
#align monotone_and monotone_and
-/

#print monotone_or /-
-- Note: by finish [monotone] doesn't work
theorem monotone_or {p q : α → Prop} (m_p : Monotone p) (m_q : Monotone q) :
    Monotone fun x => p x ∨ q x := fun a b h => Or.imp (m_p h) (m_q h)
#align monotone_or monotone_or
-/

#print monotone_le /-
theorem monotone_le {x : α} : Monotone ((· ≤ ·) x) := fun y z h' h => h.trans h'
#align monotone_le monotone_le
-/

#print monotone_lt /-
theorem monotone_lt {x : α} : Monotone ((· < ·) x) := fun y z h' h => h.trans_le h'
#align monotone_lt monotone_lt
-/

#print antitone_le /-
theorem antitone_le {x : α} : Antitone (· ≤ x) := fun y z h' h => h'.trans h
#align antitone_le antitone_le
-/

#print antitone_lt /-
theorem antitone_lt {x : α} : Antitone (· < x) := fun y z h' h => h'.trans_lt h
#align antitone_lt antitone_lt
-/

#print Monotone.forall /-
theorem Monotone.forall {P : β → α → Prop} (hP : ∀ x, Monotone (P x)) :
    Monotone fun y => ∀ x, P x y := fun y y' hy h x => hP x hy <| h x
#align monotone.forall Monotone.forall
-/

#print Antitone.forall /-
theorem Antitone.forall {P : β → α → Prop} (hP : ∀ x, Antitone (P x)) :
    Antitone fun y => ∀ x, P x y := fun y y' hy h x => hP x hy (h x)
#align antitone.forall Antitone.forall
-/

#print Monotone.ball /-
theorem Monotone.ball {P : β → α → Prop} {s : Set β} (hP : ∀ x ∈ s, Monotone (P x)) :
    Monotone fun y => ∀ x ∈ s, P x y := fun y y' hy h x hx => hP x hx hy (h x hx)
#align monotone.ball Monotone.ball
-/

#print Antitone.ball /-
theorem Antitone.ball {P : β → α → Prop} {s : Set β} (hP : ∀ x ∈ s, Antitone (P x)) :
    Antitone fun y => ∀ x ∈ s, P x y := fun y y' hy h x hx => hP x hx hy (h x hx)
#align antitone.ball Antitone.ball
-/

end Preorder

section SemilatticeSup

variable [SemilatticeSup α]

#print exists_ge_and_iff_exists /-
theorem exists_ge_and_iff_exists {P : α → Prop} {x₀ : α} (hP : Monotone P) :
    (∃ x, x₀ ≤ x ∧ P x) ↔ ∃ x, P x :=
  ⟨fun h => h.imp fun x h => h.2, fun ⟨x, hx⟩ => ⟨x ⊔ x₀, le_sup_right, hP le_sup_left hx⟩⟩
#align exists_ge_and_iff_exists exists_ge_and_iff_exists
-/

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α]

#print exists_le_and_iff_exists /-
theorem exists_le_and_iff_exists {P : α → Prop} {x₀ : α} (hP : Antitone P) :
    (∃ x, x ≤ x₀ ∧ P x) ↔ ∃ x, P x :=
  exists_ge_and_iff_exists hP.dual_left
#align exists_le_and_iff_exists exists_le_and_iff_exists
-/

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

#print eq_bot_of_bot_eq_top /-
theorem eq_bot_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊥ : α) :=
  eq_bot_mono le_top (Eq.symm hα)
#align eq_bot_of_bot_eq_top eq_bot_of_bot_eq_top
-/

#print eq_top_of_bot_eq_top /-
theorem eq_top_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊤ : α) :=
  eq_top_mono bot_le hα
#align eq_top_of_bot_eq_top eq_top_of_bot_eq_top
-/

#print subsingleton_of_top_le_bot /-
theorem subsingleton_of_top_le_bot (h : (⊤ : α) ≤ (⊥ : α)) : Subsingleton α :=
  ⟨fun a b =>
    le_antisymm (le_trans le_top <| le_trans h bot_le) (le_trans le_top <| le_trans h bot_le)⟩
#align subsingleton_of_top_le_bot subsingleton_of_top_le_bot
-/

#print subsingleton_of_bot_eq_top /-
theorem subsingleton_of_bot_eq_top (hα : (⊥ : α) = (⊤ : α)) : Subsingleton α :=
  subsingleton_of_top_le_bot (ge_of_eq hα)
#align subsingleton_of_bot_eq_top subsingleton_of_bot_eq_top
-/

#print subsingleton_iff_bot_eq_top /-
theorem subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ : α) ↔ Subsingleton α :=
  ⟨subsingleton_of_bot_eq_top, fun h => Subsingleton.elim ⊥ ⊤⟩
#align subsingleton_iff_bot_eq_top subsingleton_iff_bot_eq_top
-/

end Subsingleton

section lift

#print OrderTop.lift /-
-- See note [reducible non-instances]
/-- Pullback an `order_top`. -/
@[reducible]
def OrderTop.lift [LE α] [Top α] [LE β] [OrderTop β] (f : α → β) (map_le : ∀ a b, f a ≤ f b → a ≤ b)
    (map_top : f ⊤ = ⊤) : OrderTop α :=
  ⟨⊤, fun a => map_le _ _ <| by rw [map_top]; exact le_top⟩
#align order_top.lift OrderTop.lift
-/

#print OrderBot.lift /-
-- See note [reducible non-instances]
/-- Pullback an `order_bot`. -/
@[reducible]
def OrderBot.lift [LE α] [Bot α] [LE β] [OrderBot β] (f : α → β) (map_le : ∀ a b, f a ≤ f b → a ≤ b)
    (map_bot : f ⊥ = ⊥) : OrderBot α :=
  ⟨⊥, fun a => map_le _ _ <| by rw [map_bot]; exact bot_le⟩
#align order_bot.lift OrderBot.lift
-/

#print BoundedOrder.lift /-
-- See note [reducible non-instances]
/-- Pullback a `bounded_order`. -/
@[reducible]
def BoundedOrder.lift [LE α] [Top α] [Bot α] [LE β] [BoundedOrder β] (f : α → β)
    (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : BoundedOrder α :=
  { OrderTop.lift f map_le map_top, OrderBot.lift f map_le map_bot with }
#align bounded_order.lift BoundedOrder.lift
-/

end lift

/-! ### Subtype, order dual, product lattices -/


namespace Subtype

variable {p : α → Prop}

#print Subtype.orderBot /-
-- See note [reducible non-instances]
/-- A subtype remains a `⊥`-order if the property holds at `⊥`. -/
@[reducible]
protected def orderBot [LE α] [OrderBot α] (hbot : p ⊥) : OrderBot { x : α // p x }
    where
  bot := ⟨⊥, hbot⟩
  bot_le _ := bot_le
#align subtype.order_bot Subtype.orderBot
-/

#print Subtype.orderTop /-
-- See note [reducible non-instances]
/-- A subtype remains a `⊤`-order if the property holds at `⊤`. -/
@[reducible]
protected def orderTop [LE α] [OrderTop α] (htop : p ⊤) : OrderTop { x : α // p x }
    where
  top := ⟨⊤, htop⟩
  le_top _ := le_top
#align subtype.order_top Subtype.orderTop
-/

#print Subtype.boundedOrder /-
-- See note [reducible non-instances]
/-- A subtype remains a bounded order if the property holds at `⊥` and `⊤`. -/
@[reducible]
protected def boundedOrder [LE α] [BoundedOrder α] (hbot : p ⊥) (htop : p ⊤) :
    BoundedOrder (Subtype p) :=
  { Subtype.orderTop htop, Subtype.orderBot hbot with }
#align subtype.bounded_order Subtype.boundedOrder
-/

variable [PartialOrder α]

#print Subtype.mk_bot /-
@[simp]
theorem mk_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : mk ⊥ hbot = ⊥ :=
  le_bot_iff.1 <| coe_le_coe.1 bot_le
#align subtype.mk_bot Subtype.mk_bot
-/

#print Subtype.mk_top /-
@[simp]
theorem mk_top [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) : mk ⊤ htop = ⊤ :=
  top_le_iff.1 <| coe_le_coe.1 le_top
#align subtype.mk_top Subtype.mk_top
-/

#print Subtype.coe_bot /-
theorem coe_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : ((⊥ : Subtype p) : α) = ⊥ :=
  congr_arg coe (mk_bot hbot).symm
#align subtype.coe_bot Subtype.coe_bot
-/

#print Subtype.coe_top /-
theorem coe_top [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) : ((⊤ : Subtype p) : α) = ⊤ :=
  congr_arg coe (mk_top htop).symm
#align subtype.coe_top Subtype.coe_top
-/

#print Subtype.coe_eq_bot_iff /-
@[simp]
theorem coe_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : { x // p x }} :
    (x : α) = ⊥ ↔ x = ⊥ := by rw [← coe_bot hbot, ext_iff]
#align subtype.coe_eq_bot_iff Subtype.coe_eq_bot_iff
-/

#print Subtype.coe_eq_top_iff /-
@[simp]
theorem coe_eq_top_iff [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) {x : { x // p x }} :
    (x : α) = ⊤ ↔ x = ⊤ := by rw [← coe_top htop, ext_iff]
#align subtype.coe_eq_top_iff Subtype.coe_eq_top_iff
-/

#print Subtype.mk_eq_bot_iff /-
@[simp]
theorem mk_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : α} (hx : p x) :
    (⟨x, hx⟩ : Subtype p) = ⊥ ↔ x = ⊥ :=
  (coe_eq_bot_iff hbot).symm
#align subtype.mk_eq_bot_iff Subtype.mk_eq_bot_iff
-/

#print Subtype.mk_eq_top_iff /-
@[simp]
theorem mk_eq_top_iff [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) {x : α} (hx : p x) :
    (⟨x, hx⟩ : Subtype p) = ⊤ ↔ x = ⊤ :=
  (coe_eq_top_iff htop).symm
#align subtype.mk_eq_top_iff Subtype.mk_eq_top_iff
-/

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

#print min_bot_left /-
-- `simp` can prove these, so they shouldn't be simp-lemmas.
theorem min_bot_left [OrderBot α] (a : α) : min ⊥ a = ⊥ :=
  bot_inf_eq
#align min_bot_left min_bot_left
-/

#print max_top_left /-
theorem max_top_left [OrderTop α] (a : α) : max ⊤ a = ⊤ :=
  top_sup_eq
#align max_top_left max_top_left
-/

#print min_top_left /-
theorem min_top_left [OrderTop α] (a : α) : min ⊤ a = a :=
  top_inf_eq
#align min_top_left min_top_left
-/

#print max_bot_left /-
theorem max_bot_left [OrderBot α] (a : α) : max ⊥ a = a :=
  bot_sup_eq
#align max_bot_left max_bot_left
-/

#print min_top_right /-
theorem min_top_right [OrderTop α] (a : α) : min a ⊤ = a :=
  inf_top_eq
#align min_top_right min_top_right
-/

#print max_bot_right /-
theorem max_bot_right [OrderBot α] (a : α) : max a ⊥ = a :=
  sup_bot_eq
#align max_bot_right max_bot_right
-/

#print min_bot_right /-
theorem min_bot_right [OrderBot α] (a : α) : min a ⊥ = ⊥ :=
  inf_bot_eq
#align min_bot_right min_bot_right
-/

#print max_top_right /-
theorem max_top_right [OrderTop α] (a : α) : max a ⊤ = ⊤ :=
  sup_top_eq
#align max_top_right max_top_right
-/

#print min_eq_bot /-
@[simp]
theorem min_eq_bot [OrderBot α] {a b : α} : min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := by
  simp only [← inf_eq_min, ← le_bot_iff, inf_le_iff]
#align min_eq_bot min_eq_bot
-/

#print max_eq_top /-
@[simp]
theorem max_eq_top [OrderTop α] {a b : α} : max a b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
  @min_eq_bot αᵒᵈ _ _ a b
#align max_eq_top max_eq_top
-/

#print max_eq_bot /-
@[simp]
theorem max_eq_bot [OrderBot α] {a b : α} : max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥ :=
  sup_eq_bot_iff
#align max_eq_bot max_eq_bot
-/

#print min_eq_top /-
@[simp]
theorem min_eq_top [OrderTop α] {a b : α} : min a b = ⊤ ↔ a = ⊤ ∧ b = ⊤ :=
  inf_eq_top_iff
#align min_eq_top min_eq_top
-/

end LinearOrder

section Nontrivial

variable [PartialOrder α] [BoundedOrder α] [Nontrivial α]

#print bot_ne_top /-
@[simp]
theorem bot_ne_top : (⊥ : α) ≠ ⊤ := fun h => not_subsingleton _ <| subsingleton_of_bot_eq_top h
#align bot_ne_top bot_ne_top
-/

#print top_ne_bot /-
@[simp]
theorem top_ne_bot : (⊤ : α) ≠ ⊥ :=
  bot_ne_top.symm
#align top_ne_bot top_ne_bot
-/

#print bot_lt_top /-
@[simp]
theorem bot_lt_top : (⊥ : α) < ⊤ :=
  lt_top_iff_ne_top.2 bot_ne_top
#align bot_lt_top bot_lt_top
-/

end Nontrivial

section Bool

open Bool

instance : BoundedOrder Bool where
  top := true
  le_top x := le_true
  bot := false
  bot_le x := false_le

#print top_eq_true /-
@[simp]
theorem top_eq_true : ⊤ = true :=
  rfl
#align top_eq_tt top_eq_true
-/

#print bot_eq_false /-
@[simp]
theorem bot_eq_false : ⊥ = false :=
  rfl
#align bot_eq_ff bot_eq_false
-/

end Bool

