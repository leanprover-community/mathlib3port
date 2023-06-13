/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module order.with_bot
! leanprover-community/mathlib commit 0111834459f5d7400215223ea95ae38a1265a907
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.BoundedOrder
import Mathbin.Data.Option.NAry

/-!
# `with_bot`, `with_top`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Adding a `bot` or a `top` to an order.

## Main declarations

* `with_<top/bot> α`: Equips `option α` with the order on `α` plus `none` as the top/bottom element.

 -/


variable {α β γ δ : Type _}

#print WithBot /-
/-- Attach `⊥` to a type. -/
def WithBot (α : Type _) :=
  Option α
#align with_bot WithBot
-/

namespace WithBot

variable {a b : α}

unsafe instance [has_to_format α] : has_to_format (WithBot α)
    where to_format x :=
    match x with
    | none => "⊥"
    | some x => to_fmt x

instance [Repr α] : Repr (WithBot α) :=
  ⟨fun o =>
    match o with
    | none => "⊥"
    | some a => "↑" ++ repr a⟩

instance : CoeTC α (WithBot α) :=
  ⟨some⟩

instance : Bot (WithBot α) :=
  ⟨none⟩

unsafe instance {α : Type} [reflected _ α] [has_reflect α] : has_reflect (WithBot α)
  | ⊥ => q(⊥)
  | (a : α) => q((coe : α → WithBot α)).subst q(a)

instance : Inhabited (WithBot α) :=
  ⟨⊥⟩

instance [Nonempty α] : Nontrivial (WithBot α) :=
  Option.nontrivial

open Function

#print WithBot.coe_injective /-
theorem coe_injective : Injective (coe : α → WithBot α) :=
  Option.some_injective _
#align with_bot.coe_injective WithBot.coe_injective
-/

#print WithBot.coe_inj /-
@[norm_cast]
theorem coe_inj : (a : WithBot α) = b ↔ a = b :=
  Option.some_inj
#align with_bot.coe_inj WithBot.coe_inj
-/

#print WithBot.forall /-
protected theorem forall {p : WithBot α → Prop} : (∀ x, p x) ↔ p ⊥ ∧ ∀ x : α, p x :=
  Option.forall
#align with_bot.forall WithBot.forall
-/

#print WithBot.exists /-
protected theorem exists {p : WithBot α → Prop} : (∃ x, p x) ↔ p ⊥ ∨ ∃ x : α, p x :=
  Option.exists
#align with_bot.exists WithBot.exists
-/

#print WithBot.none_eq_bot /-
theorem none_eq_bot : (none : WithBot α) = (⊥ : WithBot α) :=
  rfl
#align with_bot.none_eq_bot WithBot.none_eq_bot
-/

#print WithBot.some_eq_coe /-
theorem some_eq_coe (a : α) : (some a : WithBot α) = (↑a : WithBot α) :=
  rfl
#align with_bot.some_eq_coe WithBot.some_eq_coe
-/

#print WithBot.bot_ne_coe /-
@[simp]
theorem bot_ne_coe : ⊥ ≠ (a : WithBot α) :=
  fun.
#align with_bot.bot_ne_coe WithBot.bot_ne_coe
-/

#print WithBot.coe_ne_bot /-
@[simp]
theorem coe_ne_bot : (a : WithBot α) ≠ ⊥ :=
  fun.
#align with_bot.coe_ne_bot WithBot.coe_ne_bot
-/

#print WithBot.recBotCoe /-
/-- Recursor for `with_bot` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_elim]
def recBotCoe {C : WithBot α → Sort _} (h₁ : C ⊥) (h₂ : ∀ a : α, C a) : ∀ n : WithBot α, C n :=
  Option.rec h₁ h₂
#align with_bot.rec_bot_coe WithBot.recBotCoe
-/

#print WithBot.recBotCoe_bot /-
@[simp]
theorem recBotCoe_bot {C : WithBot α → Sort _} (d : C ⊥) (f : ∀ a : α, C a) :
    @recBotCoe _ C d f ⊥ = d :=
  rfl
#align with_bot.rec_bot_coe_bot WithBot.recBotCoe_bot
-/

#print WithBot.recBotCoe_coe /-
@[simp]
theorem recBotCoe_coe {C : WithBot α → Sort _} (d : C ⊥) (f : ∀ a : α, C a) (x : α) :
    @recBotCoe _ C d f ↑x = f x :=
  rfl
#align with_bot.rec_bot_coe_coe WithBot.recBotCoe_coe
-/

#print WithBot.unbot' /-
/-- Specialization of `option.get_or_else` to values in `with_bot α` that respects API boundaries.
-/
def unbot' (d : α) (x : WithBot α) : α :=
  recBotCoe d id x
#align with_bot.unbot' WithBot.unbot'
-/

#print WithBot.unbot'_bot /-
@[simp]
theorem unbot'_bot {α} (d : α) : unbot' d ⊥ = d :=
  rfl
#align with_bot.unbot'_bot WithBot.unbot'_bot
-/

#print WithBot.unbot'_coe /-
@[simp]
theorem unbot'_coe {α} (d x : α) : unbot' d x = x :=
  rfl
#align with_bot.unbot'_coe WithBot.unbot'_coe
-/

#print WithBot.coe_eq_coe /-
@[norm_cast]
theorem coe_eq_coe : (a : WithBot α) = b ↔ a = b :=
  Option.some_inj
#align with_bot.coe_eq_coe WithBot.coe_eq_coe
-/

#print WithBot.unbot'_eq_iff /-
theorem unbot'_eq_iff {d y : α} {x : WithBot α} : unbot' d x = y ↔ x = y ∨ x = ⊥ ∧ y = d := by
  induction x using WithBot.recBotCoe <;> simp [@eq_comm _ d, coe_eq_coe]
#align with_bot.unbot'_eq_iff WithBot.unbot'_eq_iff
-/

#print WithBot.unbot'_eq_self_iff /-
@[simp]
theorem unbot'_eq_self_iff {d : α} {x : WithBot α} : unbot' d x = d ↔ x = d ∨ x = ⊥ := by
  simp [unbot'_eq_iff]
#align with_bot.unbot'_eq_self_iff WithBot.unbot'_eq_self_iff
-/

#print WithBot.unbot'_eq_unbot'_iff /-
theorem unbot'_eq_unbot'_iff {d : α} {x y : WithBot α} :
    unbot' d x = unbot' d y ↔ x = y ∨ x = d ∧ y = ⊥ ∨ x = ⊥ ∧ y = d := by
  induction y using WithBot.recBotCoe <;> simp [unbot'_eq_iff, or_comm', coe_eq_coe]
#align with_bot.unbot'_eq_unbot'_iff WithBot.unbot'_eq_unbot'_iff
-/

#print WithBot.map /-
/-- Lift a map `f : α → β` to `with_bot α → with_bot β`. Implemented using `option.map`. -/
def map (f : α → β) : WithBot α → WithBot β :=
  Option.map f
#align with_bot.map WithBot.map
-/

#print WithBot.map_bot /-
@[simp]
theorem map_bot (f : α → β) : map f ⊥ = ⊥ :=
  rfl
#align with_bot.map_bot WithBot.map_bot
-/

#print WithBot.map_coe /-
@[simp]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl
#align with_bot.map_coe WithBot.map_coe
-/

#print WithBot.map_comm /-
theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂)
    (a : α) : map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _
#align with_bot.map_comm WithBot.map_comm
-/

#print WithBot.ne_bot_iff_exists /-
theorem ne_bot_iff_exists {x : WithBot α} : x ≠ ⊥ ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists
#align with_bot.ne_bot_iff_exists WithBot.ne_bot_iff_exists
-/

#print WithBot.unbot /-
/-- Deconstruct a `x : with_bot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
def unbot : ∀ x : WithBot α, x ≠ ⊥ → α
  | ⊥, h => absurd rfl h
  | some x, h => x
#align with_bot.unbot WithBot.unbot
-/

#print WithBot.coe_unbot /-
@[simp]
theorem coe_unbot (x : WithBot α) (h : x ≠ ⊥) : (x.unbot h : WithBot α) = x := by cases x;
  simpa using h; rfl
#align with_bot.coe_unbot WithBot.coe_unbot
-/

#print WithBot.unbot_coe /-
@[simp]
theorem unbot_coe (x : α) (h : (x : WithBot α) ≠ ⊥ := coe_ne_bot) : (x : WithBot α).unbot h = x :=
  rfl
#align with_bot.unbot_coe WithBot.unbot_coe
-/

#print WithBot.canLift /-
instance canLift : CanLift (WithBot α) α coe fun r => r ≠ ⊥
    where prf x h := ⟨x.unbot h, coe_unbot _ _⟩
#align with_bot.can_lift WithBot.canLift
-/

section LE

variable [LE α]

instance (priority := 10) : LE (WithBot α) :=
  ⟨fun o₁ o₂ : Option α => ∀ a ∈ o₁, ∃ b ∈ o₂, a ≤ b⟩

#print WithBot.some_le_some /-
@[simp]
theorem some_le_some : @LE.le (WithBot α) _ (some a) (some b) ↔ a ≤ b := by simp [(· ≤ ·)]
#align with_bot.some_le_some WithBot.some_le_some
-/

#print WithBot.coe_le_coe /-
@[simp, norm_cast]
theorem coe_le_coe : (a : WithBot α) ≤ b ↔ a ≤ b :=
  some_le_some
#align with_bot.coe_le_coe WithBot.coe_le_coe
-/

#print WithBot.none_le /-
@[simp]
theorem none_le {a : WithBot α} : @LE.le (WithBot α) _ none a := fun b h => Option.noConfusion h
#align with_bot.none_le WithBot.none_le
-/

instance : OrderBot (WithBot α) :=
  { WithBot.hasBot with bot_le := fun a => none_le }

instance [OrderTop α] : OrderTop (WithBot α)
    where
  top := some ⊤
  le_top o a ha := by cases ha <;> exact ⟨_, rfl, le_top⟩

instance [OrderTop α] : BoundedOrder (WithBot α) :=
  { WithBot.orderTop, WithBot.orderBot with }

#print WithBot.not_coe_le_bot /-
theorem not_coe_le_bot (a : α) : ¬(a : WithBot α) ≤ ⊥ := fun h =>
  let ⟨b, hb, _⟩ := h _ rfl
  Option.not_mem_none _ hb
#align with_bot.not_coe_le_bot WithBot.not_coe_le_bot
-/

#print WithBot.coe_le /-
theorem coe_le : ∀ {o : Option α}, b ∈ o → ((a : WithBot α) ≤ o ↔ a ≤ b)
  | _, rfl => coe_le_coe
#align with_bot.coe_le WithBot.coe_le
-/

#print WithBot.coe_le_iff /-
theorem coe_le_iff : ∀ {x : WithBot α}, ↑a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b
  | some a => by simp [some_eq_coe, coe_eq_coe]
  | none => iff_of_false (not_coe_le_bot _) <| by simp [none_eq_bot]
#align with_bot.coe_le_iff WithBot.coe_le_iff
-/

#print WithBot.le_coe_iff /-
theorem le_coe_iff : ∀ {x : WithBot α}, x ≤ b ↔ ∀ a, x = ↑a → a ≤ b
  | some b => by simp [some_eq_coe, coe_eq_coe]
  | none => by simp [none_eq_bot]
#align with_bot.le_coe_iff WithBot.le_coe_iff
-/

#print IsMax.withBot /-
protected theorem IsMax.withBot (h : IsMax a) : IsMax (a : WithBot α)
  | none, _ => bot_le
  | some b, hb => some_le_some.2 <| h <| some_le_some.1 hb
#align is_max.with_bot IsMax.withBot
-/

end LE

section LT

variable [LT α]

instance (priority := 10) : LT (WithBot α) :=
  ⟨fun o₁ o₂ : Option α => ∃ b ∈ o₂, ∀ a ∈ o₁, a < b⟩

#print WithBot.some_lt_some /-
@[simp]
theorem some_lt_some : @LT.lt (WithBot α) _ (some a) (some b) ↔ a < b := by simp [(· < ·)]
#align with_bot.some_lt_some WithBot.some_lt_some
-/

#print WithBot.coe_lt_coe /-
@[simp, norm_cast]
theorem coe_lt_coe : (a : WithBot α) < b ↔ a < b :=
  some_lt_some
#align with_bot.coe_lt_coe WithBot.coe_lt_coe
-/

#print WithBot.none_lt_some /-
@[simp]
theorem none_lt_some (a : α) : @LT.lt (WithBot α) _ none (some a) :=
  ⟨a, rfl, fun b hb => (Option.not_mem_none _ hb).elim⟩
#align with_bot.none_lt_some WithBot.none_lt_some
-/

#print WithBot.bot_lt_coe /-
theorem bot_lt_coe (a : α) : (⊥ : WithBot α) < a :=
  none_lt_some a
#align with_bot.bot_lt_coe WithBot.bot_lt_coe
-/

#print WithBot.not_lt_none /-
@[simp]
theorem not_lt_none (a : WithBot α) : ¬@LT.lt (WithBot α) _ a none := fun ⟨_, h, _⟩ =>
  Option.not_mem_none _ h
#align with_bot.not_lt_none WithBot.not_lt_none
-/

#print WithBot.lt_iff_exists_coe /-
theorem lt_iff_exists_coe : ∀ {a b : WithBot α}, a < b ↔ ∃ p : α, b = p ∧ a < p
  | a, some b => by simp [some_eq_coe, coe_eq_coe]
  | a, none => iff_of_false (not_lt_none _) <| by simp [none_eq_bot]
#align with_bot.lt_iff_exists_coe WithBot.lt_iff_exists_coe
-/

#print WithBot.lt_coe_iff /-
theorem lt_coe_iff : ∀ {x : WithBot α}, x < b ↔ ∀ a, x = ↑a → a < b
  | some b => by simp [some_eq_coe, coe_eq_coe, coe_lt_coe]
  | none => by simp [none_eq_bot, bot_lt_coe]
#align with_bot.lt_coe_iff WithBot.lt_coe_iff
-/

#print WithBot.bot_lt_iff_ne_bot /-
/-- A version of `bot_lt_iff_ne_bot` for `with_bot` that only requires `has_lt α`, not
`partial_order α`. -/
protected theorem bot_lt_iff_ne_bot : ∀ {x : WithBot α}, ⊥ < x ↔ x ≠ ⊥
  | ⊥ => iff_of_false (WithBot.not_lt_none _) fun h => h rfl
  | (x : α) => by simp [bot_lt_coe]
#align with_bot.bot_lt_iff_ne_bot WithBot.bot_lt_iff_ne_bot
-/

end LT

instance [Preorder α] : Preorder (WithBot α)
    where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by intros;
    cases a <;> cases b <;> simp [lt_iff_le_not_le] <;> simp [(· < ·), (· ≤ ·)]
  le_refl o a ha := ⟨a, ha, le_rfl⟩
  le_trans o₁ o₂ o₃ h₁ h₂ a ha :=
    let ⟨b, hb, ab⟩ := h₁ a ha
    let ⟨c, hc, bc⟩ := h₂ b hb
    ⟨c, hc, le_trans ab bc⟩

instance [PartialOrder α] : PartialOrder (WithBot α) :=
  { WithBot.preorder with
    le_antisymm := fun o₁ o₂ h₁ h₂ => by
      cases' o₁ with a
      · cases' o₂ with b; · rfl
        rcases h₂ b rfl with ⟨_, ⟨⟩, _⟩
      · rcases h₁ a rfl with ⟨b, ⟨⟩, h₁'⟩
        rcases h₂ b rfl with ⟨_, ⟨⟩, h₂'⟩
        rw [le_antisymm h₁' h₂'] }

#print WithBot.coe_strictMono /-
theorem coe_strictMono [Preorder α] : StrictMono (coe : α → WithBot α) := fun a b => some_lt_some.2
#align with_bot.coe_strict_mono WithBot.coe_strictMono
-/

#print WithBot.coe_mono /-
theorem coe_mono [Preorder α] : Monotone (coe : α → WithBot α) := fun a b => coe_le_coe.2
#align with_bot.coe_mono WithBot.coe_mono
-/

#print WithBot.monotone_iff /-
theorem monotone_iff [Preorder α] [Preorder β] {f : WithBot α → β} :
    Monotone f ↔ Monotone (f ∘ coe : α → β) ∧ ∀ x : α, f ⊥ ≤ f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_mono, fun x => h bot_le⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨fun _ => le_rfl, fun x _ => h.2 x⟩, fun x =>
        WithBot.forall.2 ⟨fun h => (not_coe_le_bot _ h).elim, fun y hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩
#align with_bot.monotone_iff WithBot.monotone_iff
-/

#print WithBot.monotone_map_iff /-
@[simp]
theorem monotone_map_iff [Preorder α] [Preorder β] {f : α → β} :
    Monotone (WithBot.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]
#align with_bot.monotone_map_iff WithBot.monotone_map_iff
-/

alias monotone_map_iff ↔ _ _root_.monotone.with_bot_map
#align monotone.with_bot_map Monotone.withBot_map

#print WithBot.strictMono_iff /-
theorem strictMono_iff [Preorder α] [Preorder β] {f : WithBot α → β} :
    StrictMono f ↔ StrictMono (f ∘ coe : α → β) ∧ ∀ x : α, f ⊥ < f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_strictMono, fun x => h (bot_lt_coe _)⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨flip absurd (lt_irrefl _), fun x _ => h.2 x⟩, fun x =>
        WithBot.forall.2 ⟨fun h => (not_lt_bot h).elim, fun y hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩
#align with_bot.strict_mono_iff WithBot.strictMono_iff
-/

#print WithBot.strictMono_map_iff /-
@[simp]
theorem strictMono_map_iff [Preorder α] [Preorder β] {f : α → β} :
    StrictMono (WithBot.map f) ↔ StrictMono f :=
  strictMono_iff.trans <| by simp [StrictMono, bot_lt_coe]
#align with_bot.strict_mono_map_iff WithBot.strictMono_map_iff
-/

alias strict_mono_map_iff ↔ _ _root_.strict_mono.with_bot_map
#align strict_mono.with_bot_map StrictMono.withBot_map

#print WithBot.map_le_iff /-
theorem map_le_iff [Preorder α] [Preorder β] (f : α → β) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    ∀ a b : WithBot α, a.map f ≤ b.map f ↔ a ≤ b
  | ⊥, _ => by simp only [map_bot, bot_le]
  | (a : α), ⊥ => by simp only [map_coe, map_bot, coe_ne_bot, not_coe_le_bot _]
  | (a : α), (b : α) => by simpa only [map_coe, coe_le_coe] using mono_iff
#align with_bot.map_le_iff WithBot.map_le_iff
-/

#print WithBot.le_coe_unbot' /-
theorem le_coe_unbot' [Preorder α] : ∀ (a : WithBot α) (b : α), a ≤ a.unbot' b
  | (a : α), b => le_rfl
  | ⊥, b => bot_le
#align with_bot.le_coe_unbot' WithBot.le_coe_unbot'
-/

#print WithBot.unbot'_bot_le_iff /-
theorem unbot'_bot_le_iff [LE α] [OrderBot α] {a : WithBot α} {b : α} : a.unbot' ⊥ ≤ b ↔ a ≤ b := by
  cases a <;> simp [none_eq_bot, some_eq_coe]
#align with_bot.unbot'_bot_le_iff WithBot.unbot'_bot_le_iff
-/

#print WithBot.unbot'_lt_iff /-
theorem unbot'_lt_iff [LT α] {a : WithBot α} {b c : α} (ha : a ≠ ⊥) : a.unbot' b < c ↔ a < c :=
  by
  lift a to α using ha
  rw [unbot'_coe, coe_lt_coe]
#align with_bot.unbot'_lt_iff WithBot.unbot'_lt_iff
-/

instance [SemilatticeSup α] : SemilatticeSup (WithBot α) :=
  { WithBot.orderBot,
    WithBot.partialOrder with
    sup := Option.liftOrGet (· ⊔ ·)
    le_sup_left := fun o₁ o₂ a ha => by cases ha <;> cases o₂ <;> simp [Option.liftOrGet]
    le_sup_right := fun o₁ o₂ a ha => by cases ha <;> cases o₁ <;> simp [Option.liftOrGet]
    sup_le := fun o₁ o₂ o₃ h₁ h₂ a ha =>
      by
      cases' o₁ with b <;> cases' o₂ with c <;> cases ha
      · exact h₂ a rfl
      · exact h₁ a rfl
      · rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩
        simp at h₂ 
        exact ⟨d, rfl, sup_le h₁' h₂⟩ }

#print WithBot.coe_sup /-
theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithBot α) = a ⊔ b :=
  rfl
#align with_bot.coe_sup WithBot.coe_sup
-/

instance [SemilatticeInf α] : SemilatticeInf (WithBot α) :=
  { WithBot.orderBot,
    WithBot.partialOrder with
    inf := Option.map₂ (· ⊓ ·)
    inf_le_left := fun o₁ o₂ a ha =>
      by
      rcases Option.mem_map₂_iff.1 ha with ⟨a, b, rfl : _ = _, rfl : _ = _, rfl⟩
      exact ⟨_, rfl, inf_le_left⟩
    inf_le_right := fun o₁ o₂ a ha =>
      by
      rcases Option.mem_map₂_iff.1 ha with ⟨a, b, rfl : _ = _, rfl : _ = _, rfl⟩
      exact ⟨_, rfl, inf_le_right⟩
    le_inf := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases ha
      rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩
      rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩
      exact ⟨_, rfl, le_inf ab ac⟩ }

#print WithBot.coe_inf /-
theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithBot α) = a ⊓ b :=
  rfl
#align with_bot.coe_inf WithBot.coe_inf
-/

instance [Lattice α] : Lattice (WithBot α) :=
  { WithBot.semilatticeSup, WithBot.semilatticeInf with }

instance [DistribLattice α] : DistribLattice (WithBot α) :=
  { WithBot.lattice with
    le_sup_inf := fun o₁ o₂ o₃ =>
      match o₁, o₂, o₃ with
      | ⊥, ⊥, ⊥ => le_rfl
      | ⊥, ⊥, (a₁ : α) => le_rfl
      | ⊥, (a₁ : α), ⊥ => le_rfl
      | ⊥, (a₁ : α), (a₃ : α) => le_rfl
      | (a₁ : α), ⊥, ⊥ => inf_le_left
      | (a₁ : α), ⊥, (a₃ : α) => inf_le_left
      | (a₁ : α), (a₂ : α), ⊥ => inf_le_right
      | (a₁ : α), (a₂ : α), (a₃ : α) => coe_le_coe.mpr le_sup_inf }

#print WithBot.decidableLE /-
instance decidableLE [LE α] [@DecidableRel α (· ≤ ·)] : @DecidableRel (WithBot α) (· ≤ ·)
  | none, x => isTrue fun a h => Option.noConfusion h
  | some x, some y => if h : x ≤ y then isTrue (some_le_some.2 h) else isFalse <| by simp [*]
  | some x, none => isFalse fun h => by rcases h x rfl with ⟨y, ⟨_⟩, _⟩
#align with_bot.decidable_le WithBot.decidableLE
-/

#print WithBot.decidableLT /-
instance decidableLT [LT α] [@DecidableRel α (· < ·)] : @DecidableRel (WithBot α) (· < ·)
  | none, some x => isTrue <| by exists x, rfl <;> rintro _ ⟨⟩
  | some x, some y => if h : x < y then isTrue <| by simp [*] else isFalse <| by simp [*]
  | x, none => isFalse <| by rintro ⟨a, ⟨⟨⟩⟩⟩
#align with_bot.decidable_lt WithBot.decidableLT
-/

#print WithBot.isTotal_le /-
instance isTotal_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithBot α) (· ≤ ·) :=
  ⟨fun a b =>
    match a, b with
    | none, _ => Or.inl bot_le
    | _, none => Or.inr bot_le
    | some x, some y => (total_of (· ≤ ·) x y).imp some_le_some.2 some_le_some.2⟩
#align with_bot.is_total_le WithBot.isTotal_le
-/

instance [LinearOrder α] : LinearOrder (WithBot α) :=
  Lattice.toLinearOrder _

#print WithBot.coe_min /-
-- this is not marked simp because the corresponding with_top lemmas are used
@[norm_cast]
theorem coe_min [LinearOrder α] (x y : α) : ((min x y : α) : WithBot α) = min x y :=
  rfl
#align with_bot.coe_min WithBot.coe_min
-/

#print WithBot.coe_max /-
-- this is not marked simp because the corresponding with_top lemmas are used
@[norm_cast]
theorem coe_max [LinearOrder α] (x y : α) : ((max x y : α) : WithBot α) = max x y :=
  rfl
#align with_bot.coe_max WithBot.coe_max
-/

#print WithBot.wellFounded_lt /-
theorem wellFounded_lt [Preorder α] (h : @WellFounded α (· < ·)) :
    @WellFounded (WithBot α) (· < ·) :=
  have acc_bot : Acc ((· < ·) : WithBot α → WithBot α → Prop) ⊥ :=
    Acc.intro _ fun a ha => (not_le_of_gt ha bot_le).elim
  ⟨fun a =>
    Option.recOn a acc_bot fun a =>
      Acc.intro _ fun b =>
        Option.recOn b (fun _ => acc_bot) fun b =>
          WellFounded.induction h b
            (show
              ∀ b : α,
                (∀ c,
                    c < b → (c : WithBot α) < a → Acc ((· < ·) : WithBot α → WithBot α → Prop) c) →
                  (b : WithBot α) < a → Acc ((· < ·) : WithBot α → WithBot α → Prop) b
              from fun b ih hba =>
              Acc.intro _ fun c =>
                Option.recOn c (fun _ => acc_bot) fun c hc =>
                  ih _ (some_lt_some.1 hc) (lt_trans hc hba))⟩
#align with_bot.well_founded_lt WithBot.wellFounded_lt
-/

instance [LT α] [DenselyOrdered α] [NoMinOrder α] : DenselyOrdered (WithBot α) :=
  ⟨fun a b =>
    match a, b with
    | a, none => fun h : a < ⊥ => (not_lt_none _ h).elim
    | none, some b => fun h =>
      let ⟨a, ha⟩ := exists_lt b
      ⟨a, bot_lt_coe a, coe_lt_coe.2 ha⟩
    | some a, some b => fun h =>
      let ⟨a, ha₁, ha₂⟩ := exists_between (coe_lt_coe.1 h)
      ⟨a, coe_lt_coe.2 ha₁, coe_lt_coe.2 ha₂⟩⟩

#print WithBot.lt_iff_exists_coe_btwn /-
theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨y, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨x, hx⟩ => lt_trans hx.1 hx.2⟩
#align with_bot.lt_iff_exists_coe_btwn WithBot.lt_iff_exists_coe_btwn
-/

instance [LE α] [NoTopOrder α] [Nonempty α] : NoTopOrder (WithBot α) :=
  ⟨by
    apply rec_bot_coe
    · exact ‹Nonempty α›.elim fun a => ⟨a, not_coe_le_bot a⟩
    · intro a
      obtain ⟨b, h⟩ := exists_not_le a
      exact ⟨b, by rwa [coe_le_coe]⟩⟩

instance [LT α] [NoMaxOrder α] [Nonempty α] : NoMaxOrder (WithBot α) :=
  ⟨by
    apply WithBot.recBotCoe
    · apply ‹Nonempty α›.elim
      exact fun a => ⟨a, WithBot.bot_lt_coe a⟩
    · intro a
      obtain ⟨b, ha⟩ := exists_gt a
      exact ⟨b, with_bot.coe_lt_coe.mpr ha⟩⟩

end WithBot

#print WithTop /-
--TODO(Mario): Construct using order dual on with_bot
/-- Attach `⊤` to a type. -/
def WithTop (α : Type _) :=
  Option α
#align with_top WithTop
-/

namespace WithTop

variable {a b : α}

unsafe instance [has_to_format α] : has_to_format (WithTop α)
    where to_format x :=
    match x with
    | none => "⊤"
    | some x => to_fmt x

instance [Repr α] : Repr (WithTop α) :=
  ⟨fun o =>
    match o with
    | none => "⊤"
    | some a => "↑" ++ repr a⟩

instance : CoeTC α (WithTop α) :=
  ⟨some⟩

instance : Top (WithTop α) :=
  ⟨none⟩

unsafe instance {α : Type} [reflected _ α] [has_reflect α] : has_reflect (WithTop α)
  | ⊤ => q(⊤)
  | (a : α) => q((coe : α → WithTop α)).subst q(a)

instance : Inhabited (WithTop α) :=
  ⟨⊤⟩

instance [Nonempty α] : Nontrivial (WithTop α) :=
  Option.nontrivial

#print WithTop.forall /-
protected theorem forall {p : WithTop α → Prop} : (∀ x, p x) ↔ p ⊤ ∧ ∀ x : α, p x :=
  Option.forall
#align with_top.forall WithTop.forall
-/

#print WithTop.exists /-
protected theorem exists {p : WithTop α → Prop} : (∃ x, p x) ↔ p ⊤ ∨ ∃ x : α, p x :=
  Option.exists
#align with_top.exists WithTop.exists
-/

#print WithTop.none_eq_top /-
theorem none_eq_top : (none : WithTop α) = (⊤ : WithTop α) :=
  rfl
#align with_top.none_eq_top WithTop.none_eq_top
-/

#print WithTop.some_eq_coe /-
theorem some_eq_coe (a : α) : (some a : WithTop α) = (↑a : WithTop α) :=
  rfl
#align with_top.some_eq_coe WithTop.some_eq_coe
-/

#print WithTop.top_ne_coe /-
@[simp]
theorem top_ne_coe : ⊤ ≠ (a : WithTop α) :=
  fun.
#align with_top.top_ne_coe WithTop.top_ne_coe
-/

#print WithTop.coe_ne_top /-
@[simp]
theorem coe_ne_top : (a : WithTop α) ≠ ⊤ :=
  fun.
#align with_top.coe_ne_top WithTop.coe_ne_top
-/

#print WithTop.recTopCoe /-
/-- Recursor for `with_top` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_elim]
def recTopCoe {C : WithTop α → Sort _} (h₁ : C ⊤) (h₂ : ∀ a : α, C a) : ∀ n : WithTop α, C n :=
  Option.rec h₁ h₂
#align with_top.rec_top_coe WithTop.recTopCoe
-/

#print WithTop.recTopCoe_top /-
@[simp]
theorem recTopCoe_top {C : WithTop α → Sort _} (d : C ⊤) (f : ∀ a : α, C a) :
    @recTopCoe _ C d f ⊤ = d :=
  rfl
#align with_top.rec_top_coe_top WithTop.recTopCoe_top
-/

#print WithTop.recTopCoe_coe /-
@[simp]
theorem recTopCoe_coe {C : WithTop α → Sort _} (d : C ⊤) (f : ∀ a : α, C a) (x : α) :
    @recTopCoe _ C d f ↑x = f x :=
  rfl
#align with_top.rec_top_coe_coe WithTop.recTopCoe_coe
-/

#print WithTop.toDual /-
/-- `with_top.to_dual` is the equivalence sending `⊤` to `⊥` and any `a : α` to `to_dual a : αᵒᵈ`.
See `with_top.to_dual_bot_equiv` for the related order-iso.
-/
protected def toDual : WithTop α ≃ WithBot αᵒᵈ :=
  Equiv.refl _
#align with_top.to_dual WithTop.toDual
-/

#print WithTop.ofDual /-
/-- `with_top.of_dual` is the equivalence sending `⊤` to `⊥` and any `a : αᵒᵈ` to `of_dual a : α`.
See `with_top.to_dual_bot_equiv` for the related order-iso.
-/
protected def ofDual : WithTop αᵒᵈ ≃ WithBot α :=
  Equiv.refl _
#align with_top.of_dual WithTop.ofDual
-/

#print WithBot.toDual /-
/-- `with_bot.to_dual` is the equivalence sending `⊥` to `⊤` and any `a : α` to `to_dual a : αᵒᵈ`.
See `with_bot.to_dual_top_equiv` for the related order-iso.
-/
protected def WithBot.toDual : WithBot α ≃ WithTop αᵒᵈ :=
  Equiv.refl _
#align with_bot.to_dual WithBot.toDual
-/

#print WithBot.ofDual /-
/-- `with_bot.of_dual` is the equivalence sending `⊥` to `⊤` and any `a : αᵒᵈ` to `of_dual a : α`.
See `with_bot.to_dual_top_equiv` for the related order-iso.
-/
protected def WithBot.ofDual : WithBot αᵒᵈ ≃ WithTop α :=
  Equiv.refl _
#align with_bot.of_dual WithBot.ofDual
-/

#print WithTop.toDual_symm_apply /-
@[simp]
theorem toDual_symm_apply (a : WithBot αᵒᵈ) : WithTop.toDual.symm a = a.ofDual :=
  rfl
#align with_top.to_dual_symm_apply WithTop.toDual_symm_apply
-/

#print WithTop.ofDual_symm_apply /-
@[simp]
theorem ofDual_symm_apply (a : WithBot α) : WithTop.ofDual.symm a = a.toDual :=
  rfl
#align with_top.of_dual_symm_apply WithTop.ofDual_symm_apply
-/

#print WithTop.toDual_apply_top /-
@[simp]
theorem toDual_apply_top : WithTop.toDual (⊤ : WithTop α) = ⊥ :=
  rfl
#align with_top.to_dual_apply_top WithTop.toDual_apply_top
-/

#print WithTop.ofDual_apply_top /-
@[simp]
theorem ofDual_apply_top : WithTop.ofDual (⊤ : WithTop α) = ⊥ :=
  rfl
#align with_top.of_dual_apply_top WithTop.ofDual_apply_top
-/

open OrderDual

#print WithTop.toDual_apply_coe /-
@[simp]
theorem toDual_apply_coe (a : α) : WithTop.toDual (a : WithTop α) = toDual a :=
  rfl
#align with_top.to_dual_apply_coe WithTop.toDual_apply_coe
-/

#print WithTop.ofDual_apply_coe /-
@[simp]
theorem ofDual_apply_coe (a : αᵒᵈ) : WithTop.ofDual (a : WithTop αᵒᵈ) = ofDual a :=
  rfl
#align with_top.of_dual_apply_coe WithTop.ofDual_apply_coe
-/

#print WithTop.untop' /-
/-- Specialization of `option.get_or_else` to values in `with_top α` that respects API boundaries.
-/
def untop' (d : α) (x : WithTop α) : α :=
  recTopCoe d id x
#align with_top.untop' WithTop.untop'
-/

#print WithTop.untop'_top /-
@[simp]
theorem untop'_top {α} (d : α) : untop' d ⊤ = d :=
  rfl
#align with_top.untop'_top WithTop.untop'_top
-/

#print WithTop.untop'_coe /-
@[simp]
theorem untop'_coe {α} (d x : α) : untop' d x = x :=
  rfl
#align with_top.untop'_coe WithTop.untop'_coe
-/

#print WithTop.coe_eq_coe /-
@[norm_cast]
theorem coe_eq_coe : (a : WithTop α) = b ↔ a = b :=
  Option.some_inj
#align with_top.coe_eq_coe WithTop.coe_eq_coe
-/

#print WithTop.untop'_eq_iff /-
theorem untop'_eq_iff {d y : α} {x : WithTop α} : untop' d x = y ↔ x = y ∨ x = ⊤ ∧ y = d :=
  WithBot.unbot'_eq_iff
#align with_top.untop'_eq_iff WithTop.untop'_eq_iff
-/

#print WithTop.untop'_eq_self_iff /-
@[simp]
theorem untop'_eq_self_iff {d : α} {x : WithTop α} : untop' d x = d ↔ x = d ∨ x = ⊤ :=
  WithBot.unbot'_eq_self_iff
#align with_top.untop'_eq_self_iff WithTop.untop'_eq_self_iff
-/

#print WithTop.untop'_eq_untop'_iff /-
theorem untop'_eq_untop'_iff {d : α} {x y : WithTop α} :
    untop' d x = untop' d y ↔ x = y ∨ x = d ∧ y = ⊤ ∨ x = ⊤ ∧ y = d :=
  WithBot.unbot'_eq_unbot'_iff
#align with_top.untop'_eq_untop'_iff WithTop.untop'_eq_untop'_iff
-/

#print WithTop.map /-
/-- Lift a map `f : α → β` to `with_top α → with_top β`. Implemented using `option.map`. -/
def map (f : α → β) : WithTop α → WithTop β :=
  Option.map f
#align with_top.map WithTop.map
-/

#print WithTop.map_top /-
@[simp]
theorem map_top (f : α → β) : map f ⊤ = ⊤ :=
  rfl
#align with_top.map_top WithTop.map_top
-/

#print WithTop.map_coe /-
@[simp]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl
#align with_top.map_coe WithTop.map_coe
-/

#print WithTop.map_comm /-
theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂)
    (a : α) : map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _
#align with_top.map_comm WithTop.map_comm
-/

#print WithTop.map_toDual /-
theorem map_toDual (f : αᵒᵈ → βᵒᵈ) (a : WithBot α) :
    map f (WithBot.toDual a) = a.map (toDual ∘ f) :=
  rfl
#align with_top.map_to_dual WithTop.map_toDual
-/

#print WithTop.map_ofDual /-
theorem map_ofDual (f : α → β) (a : WithBot αᵒᵈ) : map f (WithBot.ofDual a) = a.map (ofDual ∘ f) :=
  rfl
#align with_top.map_of_dual WithTop.map_ofDual
-/

#print WithTop.toDual_map /-
theorem toDual_map (f : α → β) (a : WithTop α) :
    WithTop.toDual (map f a) = WithBot.map (toDual ∘ f ∘ ofDual) a.toDual :=
  rfl
#align with_top.to_dual_map WithTop.toDual_map
-/

#print WithTop.ofDual_map /-
theorem ofDual_map (f : αᵒᵈ → βᵒᵈ) (a : WithTop αᵒᵈ) :
    WithTop.ofDual (map f a) = WithBot.map (ofDual ∘ f ∘ toDual) a.ofDual :=
  rfl
#align with_top.of_dual_map WithTop.ofDual_map
-/

#print WithTop.ne_top_iff_exists /-
theorem ne_top_iff_exists {x : WithTop α} : x ≠ ⊤ ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists
#align with_top.ne_top_iff_exists WithTop.ne_top_iff_exists
-/

#print WithTop.untop /-
/-- Deconstruct a `x : with_top α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/
def untop : ∀ x : WithTop α, x ≠ ⊤ → α :=
  WithBot.unbot
#align with_top.untop WithTop.untop
-/

#print WithTop.coe_untop /-
@[simp]
theorem coe_untop (x : WithTop α) (h : x ≠ ⊤) : (x.untop h : WithTop α) = x :=
  WithBot.coe_unbot x h
#align with_top.coe_untop WithTop.coe_untop
-/

#print WithTop.untop_coe /-
@[simp]
theorem untop_coe (x : α) (h : (x : WithTop α) ≠ ⊤ := coe_ne_top) : (x : WithTop α).untop h = x :=
  rfl
#align with_top.untop_coe WithTop.untop_coe
-/

#print WithTop.canLift /-
instance canLift : CanLift (WithTop α) α coe fun r => r ≠ ⊤
    where prf x h := ⟨x.untop h, coe_untop _ _⟩
#align with_top.can_lift WithTop.canLift
-/

section LE

variable [LE α]

instance (priority := 10) : LE (WithTop α) :=
  ⟨fun o₁ o₂ : Option α => ∀ a ∈ o₂, ∃ b ∈ o₁, b ≤ a⟩

#print WithTop.toDual_le_iff /-
theorem toDual_le_iff {a : WithTop α} {b : WithBot αᵒᵈ} :
    WithTop.toDual a ≤ b ↔ WithBot.ofDual b ≤ a :=
  Iff.rfl
#align with_top.to_dual_le_iff WithTop.toDual_le_iff
-/

#print WithTop.le_toDual_iff /-
theorem le_toDual_iff {a : WithBot αᵒᵈ} {b : WithTop α} :
    a ≤ WithTop.toDual b ↔ b ≤ WithBot.ofDual a :=
  Iff.rfl
#align with_top.le_to_dual_iff WithTop.le_toDual_iff
-/

#print WithTop.toDual_le_toDual_iff /-
@[simp]
theorem toDual_le_toDual_iff {a b : WithTop α} : WithTop.toDual a ≤ WithTop.toDual b ↔ b ≤ a :=
  Iff.rfl
#align with_top.to_dual_le_to_dual_iff WithTop.toDual_le_toDual_iff
-/

#print WithTop.ofDual_le_iff /-
theorem ofDual_le_iff {a : WithTop αᵒᵈ} {b : WithBot α} :
    WithTop.ofDual a ≤ b ↔ WithBot.toDual b ≤ a :=
  Iff.rfl
#align with_top.of_dual_le_iff WithTop.ofDual_le_iff
-/

#print WithTop.le_ofDual_iff /-
theorem le_ofDual_iff {a : WithBot α} {b : WithTop αᵒᵈ} :
    a ≤ WithTop.ofDual b ↔ b ≤ WithBot.toDual a :=
  Iff.rfl
#align with_top.le_of_dual_iff WithTop.le_ofDual_iff
-/

#print WithTop.ofDual_le_ofDual_iff /-
@[simp]
theorem ofDual_le_ofDual_iff {a b : WithTop αᵒᵈ} : WithTop.ofDual a ≤ WithTop.ofDual b ↔ b ≤ a :=
  Iff.rfl
#align with_top.of_dual_le_of_dual_iff WithTop.ofDual_le_ofDual_iff
-/

#print WithTop.coe_le_coe /-
@[simp, norm_cast]
theorem coe_le_coe : (a : WithTop α) ≤ b ↔ a ≤ b := by
  simp only [← to_dual_le_to_dual_iff, to_dual_apply_coe, WithBot.coe_le_coe, to_dual_le_to_dual]
#align with_top.coe_le_coe WithTop.coe_le_coe
-/

#print WithTop.some_le_some /-
@[simp]
theorem some_le_some : @LE.le (WithTop α) _ (some a) (some b) ↔ a ≤ b :=
  coe_le_coe
#align with_top.some_le_some WithTop.some_le_some
-/

#print WithTop.le_none /-
@[simp]
theorem le_none {a : WithTop α} : @LE.le (WithTop α) _ a none :=
  toDual_le_toDual_iff.mp WithBot.none_le
#align with_top.le_none WithTop.le_none
-/

instance : OrderTop (WithTop α) :=
  { WithTop.hasTop with le_top := fun a => le_none }

instance [OrderBot α] : OrderBot (WithTop α)
    where
  bot := some ⊥
  bot_le o a ha := by cases ha <;> exact ⟨_, rfl, bot_le⟩

instance [OrderBot α] : BoundedOrder (WithTop α) :=
  { WithTop.orderTop, WithTop.orderBot with }

#print WithTop.not_top_le_coe /-
theorem not_top_le_coe (a : α) : ¬(⊤ : WithTop α) ≤ ↑a :=
  WithBot.not_coe_le_bot (toDual a)
#align with_top.not_top_le_coe WithTop.not_top_le_coe
-/

#print WithTop.le_coe /-
theorem le_coe : ∀ {o : Option α}, a ∈ o → (@LE.le (WithTop α) _ o b ↔ a ≤ b)
  | _, rfl => coe_le_coe
#align with_top.le_coe WithTop.le_coe
-/

#print WithTop.le_coe_iff /-
theorem le_coe_iff {x : WithTop α} : x ≤ b ↔ ∃ a : α, x = a ∧ a ≤ b := by
  simpa [← to_dual_le_to_dual_iff, WithBot.coe_le_iff]
#align with_top.le_coe_iff WithTop.le_coe_iff
-/

#print WithTop.coe_le_iff /-
theorem coe_le_iff {x : WithTop α} : ↑a ≤ x ↔ ∀ b, x = ↑b → a ≤ b :=
  by
  simp only [← to_dual_le_to_dual_iff, to_dual_apply_coe, WithBot.le_coe_iff, OrderDual.forall,
    to_dual_le_to_dual]
  exact forall₂_congr fun _ _ => Iff.rfl
#align with_top.coe_le_iff WithTop.coe_le_iff
-/

#print IsMin.withTop /-
protected theorem IsMin.withTop (h : IsMin a) : IsMin (a : WithTop α) :=
  by
  -- defeq to is_max_to_dual_iff.mp (is_max.with_bot _), but that breaks API boundary
  intro _ hb
  rw [← to_dual_le_to_dual_iff] at hb 
  simpa [to_dual_le_iff] using (IsMax.withBot h : IsMax (to_dual a : WithBot αᵒᵈ)) hb
#align is_min.with_top IsMin.withTop
-/

end LE

section LT

variable [LT α]

instance (priority := 10) : LT (WithTop α) :=
  ⟨fun o₁ o₂ : Option α => ∃ b ∈ o₁, ∀ a ∈ o₂, b < a⟩

#print WithTop.toDual_lt_iff /-
theorem toDual_lt_iff {a : WithTop α} {b : WithBot αᵒᵈ} :
    WithTop.toDual a < b ↔ WithBot.ofDual b < a :=
  Iff.rfl
#align with_top.to_dual_lt_iff WithTop.toDual_lt_iff
-/

#print WithTop.lt_toDual_iff /-
theorem lt_toDual_iff {a : WithBot αᵒᵈ} {b : WithTop α} :
    a < WithTop.toDual b ↔ b < WithBot.ofDual a :=
  Iff.rfl
#align with_top.lt_to_dual_iff WithTop.lt_toDual_iff
-/

#print WithTop.toDual_lt_toDual_iff /-
@[simp]
theorem toDual_lt_toDual_iff {a b : WithTop α} : WithTop.toDual a < WithTop.toDual b ↔ b < a :=
  Iff.rfl
#align with_top.to_dual_lt_to_dual_iff WithTop.toDual_lt_toDual_iff
-/

#print WithTop.ofDual_lt_iff /-
theorem ofDual_lt_iff {a : WithTop αᵒᵈ} {b : WithBot α} :
    WithTop.ofDual a < b ↔ WithBot.toDual b < a :=
  Iff.rfl
#align with_top.of_dual_lt_iff WithTop.ofDual_lt_iff
-/

#print WithTop.lt_ofDual_iff /-
theorem lt_ofDual_iff {a : WithBot α} {b : WithTop αᵒᵈ} :
    a < WithTop.ofDual b ↔ b < WithBot.toDual a :=
  Iff.rfl
#align with_top.lt_of_dual_iff WithTop.lt_ofDual_iff
-/

#print WithTop.ofDual_lt_ofDual_iff /-
@[simp]
theorem ofDual_lt_ofDual_iff {a b : WithTop αᵒᵈ} : WithTop.ofDual a < WithTop.ofDual b ↔ b < a :=
  Iff.rfl
#align with_top.of_dual_lt_of_dual_iff WithTop.ofDual_lt_ofDual_iff
-/

end LT

end WithTop

namespace WithBot

open OrderDual

#print WithBot.toDual_symm_apply /-
@[simp]
theorem toDual_symm_apply (a : WithTop αᵒᵈ) : WithBot.toDual.symm a = a.ofDual :=
  rfl
#align with_bot.to_dual_symm_apply WithBot.toDual_symm_apply
-/

#print WithBot.ofDual_symm_apply /-
@[simp]
theorem ofDual_symm_apply (a : WithTop α) : WithBot.ofDual.symm a = a.toDual :=
  rfl
#align with_bot.of_dual_symm_apply WithBot.ofDual_symm_apply
-/

#print WithBot.toDual_apply_bot /-
@[simp]
theorem toDual_apply_bot : WithBot.toDual (⊥ : WithBot α) = ⊤ :=
  rfl
#align with_bot.to_dual_apply_bot WithBot.toDual_apply_bot
-/

#print WithBot.ofDual_apply_bot /-
@[simp]
theorem ofDual_apply_bot : WithBot.ofDual (⊥ : WithBot α) = ⊤ :=
  rfl
#align with_bot.of_dual_apply_bot WithBot.ofDual_apply_bot
-/

#print WithBot.toDual_apply_coe /-
@[simp]
theorem toDual_apply_coe (a : α) : WithBot.toDual (a : WithBot α) = toDual a :=
  rfl
#align with_bot.to_dual_apply_coe WithBot.toDual_apply_coe
-/

#print WithBot.ofDual_apply_coe /-
@[simp]
theorem ofDual_apply_coe (a : αᵒᵈ) : WithBot.ofDual (a : WithBot αᵒᵈ) = ofDual a :=
  rfl
#align with_bot.of_dual_apply_coe WithBot.ofDual_apply_coe
-/

#print WithBot.map_toDual /-
theorem map_toDual (f : αᵒᵈ → βᵒᵈ) (a : WithTop α) :
    WithBot.map f (WithTop.toDual a) = a.map (toDual ∘ f) :=
  rfl
#align with_bot.map_to_dual WithBot.map_toDual
-/

#print WithBot.map_ofDual /-
theorem map_ofDual (f : α → β) (a : WithTop αᵒᵈ) :
    WithBot.map f (WithTop.ofDual a) = a.map (ofDual ∘ f) :=
  rfl
#align with_bot.map_of_dual WithBot.map_ofDual
-/

#print WithBot.toDual_map /-
theorem toDual_map (f : α → β) (a : WithBot α) :
    WithBot.toDual (WithBot.map f a) = map (toDual ∘ f ∘ ofDual) a.toDual :=
  rfl
#align with_bot.to_dual_map WithBot.toDual_map
-/

#print WithBot.ofDual_map /-
theorem ofDual_map (f : αᵒᵈ → βᵒᵈ) (a : WithBot αᵒᵈ) :
    WithBot.ofDual (WithBot.map f a) = map (ofDual ∘ f ∘ toDual) a.ofDual :=
  rfl
#align with_bot.of_dual_map WithBot.ofDual_map
-/

section LE

variable [LE α] {a b : α}

#print WithBot.toDual_le_iff /-
theorem toDual_le_iff {a : WithBot α} {b : WithTop αᵒᵈ} :
    WithBot.toDual a ≤ b ↔ WithTop.ofDual b ≤ a :=
  Iff.rfl
#align with_bot.to_dual_le_iff WithBot.toDual_le_iff
-/

#print WithBot.le_toDual_iff /-
theorem le_toDual_iff {a : WithTop αᵒᵈ} {b : WithBot α} :
    a ≤ WithBot.toDual b ↔ b ≤ WithTop.ofDual a :=
  Iff.rfl
#align with_bot.le_to_dual_iff WithBot.le_toDual_iff
-/

#print WithBot.toDual_le_toDual_iff /-
@[simp]
theorem toDual_le_toDual_iff {a b : WithBot α} : WithBot.toDual a ≤ WithBot.toDual b ↔ b ≤ a :=
  Iff.rfl
#align with_bot.to_dual_le_to_dual_iff WithBot.toDual_le_toDual_iff
-/

#print WithBot.ofDual_le_iff /-
theorem ofDual_le_iff {a : WithBot αᵒᵈ} {b : WithTop α} :
    WithBot.ofDual a ≤ b ↔ WithTop.toDual b ≤ a :=
  Iff.rfl
#align with_bot.of_dual_le_iff WithBot.ofDual_le_iff
-/

#print WithBot.le_ofDual_iff /-
theorem le_ofDual_iff {a : WithTop α} {b : WithBot αᵒᵈ} :
    a ≤ WithBot.ofDual b ↔ b ≤ WithTop.toDual a :=
  Iff.rfl
#align with_bot.le_of_dual_iff WithBot.le_ofDual_iff
-/

#print WithBot.ofDual_le_ofDual_iff /-
@[simp]
theorem ofDual_le_ofDual_iff {a b : WithBot αᵒᵈ} : WithBot.ofDual a ≤ WithBot.ofDual b ↔ b ≤ a :=
  Iff.rfl
#align with_bot.of_dual_le_of_dual_iff WithBot.ofDual_le_ofDual_iff
-/

end LE

section LT

variable [LT α] {a b : α}

#print WithBot.toDual_lt_iff /-
theorem toDual_lt_iff {a : WithBot α} {b : WithTop αᵒᵈ} :
    WithBot.toDual a < b ↔ WithTop.ofDual b < a :=
  Iff.rfl
#align with_bot.to_dual_lt_iff WithBot.toDual_lt_iff
-/

#print WithBot.lt_toDual_iff /-
theorem lt_toDual_iff {a : WithTop αᵒᵈ} {b : WithBot α} :
    a < WithBot.toDual b ↔ b < WithTop.ofDual a :=
  Iff.rfl
#align with_bot.lt_to_dual_iff WithBot.lt_toDual_iff
-/

#print WithBot.toDual_lt_toDual_iff /-
@[simp]
theorem toDual_lt_toDual_iff {a b : WithBot α} : WithBot.toDual a < WithBot.toDual b ↔ b < a :=
  Iff.rfl
#align with_bot.to_dual_lt_to_dual_iff WithBot.toDual_lt_toDual_iff
-/

#print WithBot.ofDual_lt_iff /-
theorem ofDual_lt_iff {a : WithBot αᵒᵈ} {b : WithTop α} :
    WithBot.ofDual a < b ↔ WithTop.toDual b < a :=
  Iff.rfl
#align with_bot.of_dual_lt_iff WithBot.ofDual_lt_iff
-/

#print WithBot.lt_ofDual_iff /-
theorem lt_ofDual_iff {a : WithTop α} {b : WithBot αᵒᵈ} :
    a < WithBot.ofDual b ↔ b < WithTop.toDual a :=
  Iff.rfl
#align with_bot.lt_of_dual_iff WithBot.lt_ofDual_iff
-/

#print WithBot.ofDual_lt_ofDual_iff /-
@[simp]
theorem ofDual_lt_ofDual_iff {a b : WithBot αᵒᵈ} : WithBot.ofDual a < WithBot.ofDual b ↔ b < a :=
  Iff.rfl
#align with_bot.of_dual_lt_of_dual_iff WithBot.ofDual_lt_ofDual_iff
-/

end LT

end WithBot

namespace WithTop

section LT

variable [LT α] {a b : α}

open OrderDual

#print WithTop.coe_lt_coe /-
@[simp, norm_cast]
theorem coe_lt_coe : (a : WithTop α) < b ↔ a < b := by
  simp only [← to_dual_lt_to_dual_iff, to_dual_apply_coe, WithBot.coe_lt_coe, to_dual_lt_to_dual]
#align with_top.coe_lt_coe WithTop.coe_lt_coe
-/

#print WithTop.some_lt_some /-
@[simp]
theorem some_lt_some : @LT.lt (WithTop α) _ (some a) (some b) ↔ a < b :=
  coe_lt_coe
#align with_top.some_lt_some WithTop.some_lt_some
-/

#print WithTop.coe_lt_top /-
theorem coe_lt_top (a : α) : (a : WithTop α) < ⊤ := by
  simpa [← to_dual_lt_to_dual_iff] using WithBot.bot_lt_coe _
#align with_top.coe_lt_top WithTop.coe_lt_top
-/

#print WithTop.some_lt_none /-
@[simp]
theorem some_lt_none (a : α) : @LT.lt (WithTop α) _ (some a) none :=
  coe_lt_top a
#align with_top.some_lt_none WithTop.some_lt_none
-/

#print WithTop.not_none_lt /-
@[simp]
theorem not_none_lt (a : WithTop α) : ¬@LT.lt (WithTop α) _ none a :=
  by
  rw [← to_dual_lt_to_dual_iff]
  exact WithBot.not_lt_none _
#align with_top.not_none_lt WithTop.not_none_lt
-/

#print WithTop.lt_iff_exists_coe /-
theorem lt_iff_exists_coe {a b : WithTop α} : a < b ↔ ∃ p : α, a = p ∧ ↑p < b :=
  by
  rw [← to_dual_lt_to_dual_iff, WithBot.lt_iff_exists_coe, OrderDual.exists]
  exact exists_congr fun _ => and_congr_left' Iff.rfl
#align with_top.lt_iff_exists_coe WithTop.lt_iff_exists_coe
-/

#print WithTop.coe_lt_iff /-
theorem coe_lt_iff {x : WithTop α} : ↑a < x ↔ ∀ b, x = ↑b → a < b :=
  by
  simp only [← to_dual_lt_to_dual_iff, WithBot.lt_coe_iff, to_dual_apply_coe, OrderDual.forall,
    to_dual_lt_to_dual]
  exact forall₂_congr fun _ _ => Iff.rfl
#align with_top.coe_lt_iff WithTop.coe_lt_iff
-/

#print WithTop.lt_top_iff_ne_top /-
/-- A version of `lt_top_iff_ne_top` for `with_top` that only requires `has_lt α`, not
`partial_order α`. -/
protected theorem lt_top_iff_ne_top {x : WithTop α} : x < ⊤ ↔ x ≠ ⊤ :=
  @WithBot.bot_lt_iff_ne_bot αᵒᵈ _ x
#align with_top.lt_top_iff_ne_top WithTop.lt_top_iff_ne_top
-/

end LT

instance [Preorder α] : Preorder (WithTop α)
    where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by simp [← to_dual_lt_to_dual_iff, lt_iff_le_not_le]
  le_refl _ := toDual_le_toDual_iff.mp le_rfl
  le_trans _ _ _ := by simp_rw [← to_dual_le_to_dual_iff]; exact Function.swap le_trans

instance [PartialOrder α] : PartialOrder (WithTop α) :=
  { WithTop.preorder with
    le_antisymm := fun _ _ => by simp_rw [← to_dual_le_to_dual_iff];
      exact Function.swap le_antisymm }

#print WithTop.coe_strictMono /-
theorem coe_strictMono [Preorder α] : StrictMono (coe : α → WithTop α) := fun a b => some_lt_some.2
#align with_top.coe_strict_mono WithTop.coe_strictMono
-/

#print WithTop.coe_mono /-
theorem coe_mono [Preorder α] : Monotone (coe : α → WithTop α) := fun a b => coe_le_coe.2
#align with_top.coe_mono WithTop.coe_mono
-/

#print WithTop.monotone_iff /-
theorem monotone_iff [Preorder α] [Preorder β] {f : WithTop α → β} :
    Monotone f ↔ Monotone (f ∘ coe : α → β) ∧ ∀ x : α, f x ≤ f ⊤ :=
  ⟨fun h => ⟨h.comp WithTop.coe_mono, fun x => h le_top⟩, fun h =>
    WithTop.forall.2
      ⟨WithTop.forall.2 ⟨fun _ => le_rfl, fun x h => (not_top_le_coe _ h).elim⟩, fun x =>
        WithTop.forall.2 ⟨fun _ => h.2 x, fun y hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩
#align with_top.monotone_iff WithTop.monotone_iff
-/

#print WithTop.monotone_map_iff /-
@[simp]
theorem monotone_map_iff [Preorder α] [Preorder β] {f : α → β} :
    Monotone (WithTop.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]
#align with_top.monotone_map_iff WithTop.monotone_map_iff
-/

alias monotone_map_iff ↔ _ _root_.monotone.with_top_map
#align monotone.with_top_map Monotone.withTop_map

#print WithTop.strictMono_iff /-
theorem strictMono_iff [Preorder α] [Preorder β] {f : WithTop α → β} :
    StrictMono f ↔ StrictMono (f ∘ coe : α → β) ∧ ∀ x : α, f x < f ⊤ :=
  ⟨fun h => ⟨h.comp WithTop.coe_strictMono, fun x => h (coe_lt_top _)⟩, fun h =>
    WithTop.forall.2
      ⟨WithTop.forall.2 ⟨flip absurd (lt_irrefl _), fun x h => (not_top_lt h).elim⟩, fun x =>
        WithTop.forall.2 ⟨fun _ => h.2 x, fun y hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩
#align with_top.strict_mono_iff WithTop.strictMono_iff
-/

#print WithTop.strictMono_map_iff /-
@[simp]
theorem strictMono_map_iff [Preorder α] [Preorder β] {f : α → β} :
    StrictMono (WithTop.map f) ↔ StrictMono f :=
  strictMono_iff.trans <| by simp [StrictMono, coe_lt_top]
#align with_top.strict_mono_map_iff WithTop.strictMono_map_iff
-/

alias strict_mono_map_iff ↔ _ _root_.strict_mono.with_top_map
#align strict_mono.with_top_map StrictMono.withTop_map

#print WithTop.map_le_iff /-
theorem map_le_iff [Preorder α] [Preorder β] (f : α → β) (a b : WithTop α)
    (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) : a.map f ≤ b.map f ↔ a ≤ b :=
  by
  rw [← to_dual_le_to_dual_iff, to_dual_map, to_dual_map, WithBot.map_le_iff,
    to_dual_le_to_dual_iff]
  simp [mono_iff]
#align with_top.map_le_iff WithTop.map_le_iff
-/

instance [SemilatticeInf α] : SemilatticeInf (WithTop α) :=
  { WithTop.partialOrder with
    inf := Option.liftOrGet (· ⊓ ·)
    inf_le_left := fun o₁ o₂ a ha => by cases ha <;> cases o₂ <;> simp [Option.liftOrGet]
    inf_le_right := fun o₁ o₂ a ha => by cases ha <;> cases o₁ <;> simp [Option.liftOrGet]
    le_inf := fun o₁ o₂ o₃ h₁ h₂ a ha =>
      by
      cases' o₂ with b <;> cases' o₃ with c <;> cases ha
      · exact h₂ a rfl
      · exact h₁ a rfl
      · rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩
        simp at h₂ 
        exact ⟨d, rfl, le_inf h₁' h₂⟩ }

#print WithTop.coe_inf /-
theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithTop α) = a ⊓ b :=
  rfl
#align with_top.coe_inf WithTop.coe_inf
-/

instance [SemilatticeSup α] : SemilatticeSup (WithTop α) :=
  { WithTop.partialOrder with
    sup := Option.map₂ (· ⊔ ·)
    le_sup_left := fun o₁ o₂ a ha =>
      by
      rcases Option.mem_map₂_iff.1 ha with ⟨a, b, rfl : _ = _, rfl : _ = _, rfl⟩
      exact ⟨_, rfl, le_sup_left⟩
    le_sup_right := fun o₁ o₂ a ha =>
      by
      rcases Option.mem_map₂_iff.1 ha with ⟨a, b, rfl : _ = _, rfl : _ = _, rfl⟩
      exact ⟨_, rfl, le_sup_right⟩
    sup_le := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases ha
      rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩
      rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩
      exact ⟨_, rfl, sup_le ab ac⟩ }

#print WithTop.coe_sup /-
theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithTop α) = a ⊔ b :=
  rfl
#align with_top.coe_sup WithTop.coe_sup
-/

instance [Lattice α] : Lattice (WithTop α) :=
  { WithTop.semilatticeSup, WithTop.semilatticeInf with }

instance [DistribLattice α] : DistribLattice (WithTop α) :=
  { WithTop.lattice with
    le_sup_inf := fun o₁ o₂ o₃ =>
      match o₁, o₂, o₃ with
      | ⊤, o₂, o₃ => le_rfl
      | (a₁ : α), ⊤, ⊤ => le_rfl
      | (a₁ : α), ⊤, (a₃ : α) => le_rfl
      | (a₁ : α), (a₂ : α), ⊤ => le_rfl
      | (a₁ : α), (a₂ : α), (a₃ : α) => coe_le_coe.mpr le_sup_inf }

#print WithTop.decidableLE /-
instance decidableLE [LE α] [@DecidableRel α (· ≤ ·)] : @DecidableRel (WithTop α) (· ≤ ·) :=
  fun _ _ => decidable_of_decidable_of_iff (WithBot.decidableLE _ _) toDual_le_toDual_iff
#align with_top.decidable_le WithTop.decidableLE
-/

#print WithTop.decidableLT /-
instance decidableLT [LT α] [@DecidableRel α (· < ·)] : @DecidableRel (WithTop α) (· < ·) :=
  fun _ _ => decidable_of_decidable_of_iff (WithBot.decidableLT _ _) toDual_lt_toDual_iff
#align with_top.decidable_lt WithTop.decidableLT
-/

#print WithTop.isTotal_le /-
instance isTotal_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithTop α) (· ≤ ·) :=
  ⟨fun _ _ => by simp_rw [← to_dual_le_to_dual_iff]; exact total_of _ _ _⟩
#align with_top.is_total_le WithTop.isTotal_le
-/

instance [LinearOrder α] : LinearOrder (WithTop α) :=
  Lattice.toLinearOrder _

#print WithTop.coe_min /-
@[simp, norm_cast]
theorem coe_min [LinearOrder α] (x y : α) : (↑(min x y) : WithTop α) = min x y :=
  rfl
#align with_top.coe_min WithTop.coe_min
-/

#print WithTop.coe_max /-
@[simp, norm_cast]
theorem coe_max [LinearOrder α] (x y : α) : (↑(max x y) : WithTop α) = max x y :=
  rfl
#align with_top.coe_max WithTop.coe_max
-/

#print WithTop.wellFounded_lt /-
theorem wellFounded_lt [Preorder α] (h : @WellFounded α (· < ·)) :
    @WellFounded (WithTop α) (· < ·) :=
  have acc_some : ∀ a : α, Acc ((· < ·) : WithTop α → WithTop α → Prop) (some a) := fun a =>
    Acc.intro _
      (WellFounded.induction h a
        (show
          ∀ b,
            (∀ c, c < b → ∀ d : WithTop α, d < some c → Acc (· < ·) d) →
              ∀ y : WithTop α, y < some b → Acc (· < ·) y
          from fun b ih c =>
          Option.recOn c (fun hc => (not_lt_of_ge le_top hc).elim) fun c hc =>
            Acc.intro _ (ih _ (some_lt_some.1 hc))))
  ⟨fun a =>
    Option.recOn a
      (Acc.intro _ fun y => Option.recOn y (fun h => (lt_irrefl _ h).elim) fun _ _ => acc_some _)
      acc_some⟩
#align with_top.well_founded_lt WithTop.wellFounded_lt
-/

open OrderDual

#print WithTop.wellFounded_gt /-
theorem wellFounded_gt [Preorder α] (h : @WellFounded α (· > ·)) :
    @WellFounded (WithTop α) (· > ·) :=
  ⟨fun a =>
    by
    -- ideally, use rel_hom_class.acc, but that is defined later
    have : Acc (· < ·) a.to_dual := WellFounded.apply (WithBot.wellFounded_lt h) _
    revert this
    generalize ha : a.to_dual = b; intro ac
    induction' ac with _ H IH generalizing a; subst ha
    exact ⟨_, fun a' h => IH a'.toDual (to_dual_lt_to_dual.mpr h) _ rfl⟩⟩
#align with_top.well_founded_gt WithTop.wellFounded_gt
-/

#print WithBot.wellFounded_gt /-
theorem WithBot.wellFounded_gt [Preorder α] (h : @WellFounded α (· > ·)) :
    @WellFounded (WithBot α) (· > ·) :=
  ⟨fun a =>
    by
    -- ideally, use rel_hom_class.acc, but that is defined later
    have : Acc (· < ·) a.to_dual := WellFounded.apply (WithTop.wellFounded_lt h) _
    revert this
    generalize ha : a.to_dual = b; intro ac
    induction' ac with _ H IH generalizing a; subst ha
    exact ⟨_, fun a' h => IH a'.toDual (to_dual_lt_to_dual.mpr h) _ rfl⟩⟩
#align with_bot.well_founded_gt WithBot.wellFounded_gt
-/

#print WithTop.trichotomous.lt /-
instance trichotomous.lt [Preorder α] [IsTrichotomous α (· < ·)] :
    IsTrichotomous (WithTop α) (· < ·) :=
  ⟨by
    rintro (a | _) (b | _)
    iterate 3 simp
    simpa [Option.some_inj] using @trichotomous _ (· < ·) _ a b⟩
#align with_top.trichotomous.lt WithTop.trichotomous.lt
-/

#print WithTop.IsWellOrder.lt /-
instance IsWellOrder.lt [Preorder α] [h : IsWellOrder α (· < ·)] : IsWellOrder (WithTop α) (· < ·)
    where wf := wellFounded_lt h.wf
#align with_top.is_well_order.lt WithTop.IsWellOrder.lt
-/

#print WithTop.trichotomous.gt /-
instance trichotomous.gt [Preorder α] [IsTrichotomous α (· > ·)] :
    IsTrichotomous (WithTop α) (· > ·) :=
  ⟨by
    rintro (a | _) (b | _)
    iterate 3 simp
    simpa [Option.some_inj] using @trichotomous _ (· > ·) _ a b⟩
#align with_top.trichotomous.gt WithTop.trichotomous.gt
-/

#print WithTop.IsWellOrder.gt /-
instance IsWellOrder.gt [Preorder α] [h : IsWellOrder α (· > ·)] : IsWellOrder (WithTop α) (· > ·)
    where wf := wellFounded_gt h.wf
#align with_top.is_well_order.gt WithTop.IsWellOrder.gt
-/

#print WithBot.trichotomous.lt /-
instance WithBot.trichotomous.lt [Preorder α] [h : IsTrichotomous α (· < ·)] :
    IsTrichotomous (WithBot α) (· < ·) :=
  @WithTop.trichotomous.gt αᵒᵈ _ h
#align with_bot.trichotomous.lt WithBot.trichotomous.lt
-/

#print WithBot.isWellOrder.lt /-
instance WithBot.isWellOrder.lt [Preorder α] [h : IsWellOrder α (· < ·)] :
    IsWellOrder (WithBot α) (· < ·) :=
  @WithTop.IsWellOrder.gt αᵒᵈ _ h
#align with_bot.is_well_order.lt WithBot.isWellOrder.lt
-/

#print WithBot.trichotomous.gt /-
instance WithBot.trichotomous.gt [Preorder α] [h : IsTrichotomous α (· > ·)] :
    IsTrichotomous (WithBot α) (· > ·) :=
  @WithTop.trichotomous.lt αᵒᵈ _ h
#align with_bot.trichotomous.gt WithBot.trichotomous.gt
-/

#print WithBot.isWellOrder.gt /-
instance WithBot.isWellOrder.gt [Preorder α] [h : IsWellOrder α (· > ·)] :
    IsWellOrder (WithBot α) (· > ·) :=
  @WithTop.IsWellOrder.lt αᵒᵈ _ h
#align with_bot.is_well_order.gt WithBot.isWellOrder.gt
-/

instance [LT α] [DenselyOrdered α] [NoMaxOrder α] : DenselyOrdered (WithTop α) :=
  OrderDual.denselyOrdered (WithBot αᵒᵈ)

#print WithTop.lt_iff_exists_coe_btwn /-
theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMaxOrder α] {a b : WithTop α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨y, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.2
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨x, hx⟩ => lt_trans hx.1 hx.2⟩
#align with_top.lt_iff_exists_coe_btwn WithTop.lt_iff_exists_coe_btwn
-/

instance [LE α] [NoBotOrder α] [Nonempty α] : NoBotOrder (WithTop α) :=
  OrderDual.noBotOrder (WithBot αᵒᵈ)

instance [LT α] [NoMinOrder α] [Nonempty α] : NoMinOrder (WithTop α) :=
  OrderDual.noMinOrder (WithBot αᵒᵈ)

end WithTop

