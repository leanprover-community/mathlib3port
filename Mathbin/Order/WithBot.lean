/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Order.BoundedOrder

/-!
# `with_bot`, `with_top`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/776
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

unsafe instance [has_to_format α] :
    has_to_format (WithBot α) where to_format x :=
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

/- warning: with_bot.rec_bot_coe_bot -> WithBot.rec_bot_coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {C : (WithBot.{u_1} α) -> Sort.{u_2}} (d : C (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.hasBot.{u_1} α))) (f : forall (a : α), C ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a)), Eq.{u_2} (C (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.hasBot.{u_1} α))) (WithBot.recBotCoe.{u_1, u_2} α C d f (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.hasBot.{u_1} α))) d
but is expected to have type
  forall {α : Type.{u_1}} {C : (WithBot.{u_1} α) -> Sort.{u_2}} (d : C (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.instBotWithBot.{u_1} α))) (f : forall (a : α), C (WithBot.some.{u_1} α a)), Eq.{u_2} (C (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.instBotWithBot.{u_1} α))) (WithBot.recBotCoe.{u_1, u_2} α C d f (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.instBotWithBot.{u_1} α))) d
Case conversion may be inaccurate. Consider using '#align with_bot.rec_bot_coe_bot WithBot.rec_bot_coe_botₓ'. -/
@[simp]
theorem rec_bot_coe_bot {C : WithBot α → Sort _} (d : C ⊥) (f : ∀ a : α, C a) :
    @recBotCoe _ C d f ⊥ = d :=
  rfl
#align with_bot.rec_bot_coe_bot WithBot.rec_bot_coe_bot

/- warning: with_bot.rec_bot_coe_coe -> WithBot.rec_bot_coe_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {C : (WithBot.{u_1} α) -> Sort.{u_2}} (d : C (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.hasBot.{u_1} α))) (f : forall (a : α), C ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a)) (x : α), Eq.{u_2} (C ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) x)) (WithBot.recBotCoe.{u_1, u_2} α C d f ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) x)) (f x)
but is expected to have type
  forall {α : Type.{u_1}} {C : (WithBot.{u_1} α) -> Sort.{u_2}} (d : C (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.instBotWithBot.{u_1} α))) (f : forall (a : α), C (WithBot.some.{u_1} α a)) (x : α), Eq.{u_2} (C (WithBot.some.{u_1} α x)) (WithBot.recBotCoe.{u_1, u_2} α C d f (WithBot.some.{u_1} α x)) (f x)
Case conversion may be inaccurate. Consider using '#align with_bot.rec_bot_coe_coe WithBot.rec_bot_coe_coeₓ'. -/
@[simp]
theorem rec_bot_coe_coe {C : WithBot α → Sort _} (d : C ⊥) (f : ∀ a : α, C a) (x : α) :
    @recBotCoe _ C d f ↑x = f x :=
  rfl
#align with_bot.rec_bot_coe_coe WithBot.rec_bot_coe_coe

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

/- warning: with_bot.map_comm -> WithBot.map_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ}, (Eq.{max (succ u_1) (succ u_4)} (α -> δ) (Function.comp.{succ u_1, succ u_2, succ u_4} α β δ g₁ f₁) (Function.comp.{succ u_1, succ u_3, succ u_4} α γ δ g₂ f₂)) -> (forall (a : α), Eq.{succ u_4} (WithBot.{u_4} δ) (WithBot.map.{u_2, u_4} β δ g₁ (WithBot.map.{u_1, u_2} α β f₁ ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a))) (WithBot.map.{u_3, u_4} γ δ g₂ (WithBot.map.{u_1, u_3} α γ f₂ ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a))))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_4}} {δ : Type.{u_2}} {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ}, (Eq.{max (succ u_1) (succ u_2)} (α -> δ) (Function.comp.{succ u_1, succ u_3, succ u_2} α β δ g₁ f₁) (Function.comp.{succ u_1, succ u_4, succ u_2} α γ δ g₂ f₂)) -> (forall (a : α), Eq.{succ u_2} (WithBot.{u_2} δ) (WithBot.map.{u_3, u_2} β δ g₁ (WithBot.map.{u_1, u_3} α β f₁ (WithBot.some.{u_1} α a))) (WithBot.map.{u_4, u_2} γ δ g₂ (WithBot.map.{u_1, u_4} α γ f₂ (WithBot.some.{u_1} α a))))
Case conversion may be inaccurate. Consider using '#align with_bot.map_comm WithBot.map_commₓ'. -/
theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂)
    (a : α) : map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _
#align with_bot.map_comm WithBot.map_comm

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
theorem coe_unbot (x : WithBot α) (h : x ≠ ⊥) : (x.unbot h : WithBot α) = x := by
  cases x
  simpa using h
  rfl
#align with_bot.coe_unbot WithBot.coe_unbot
-/

#print WithBot.unbot_coe /-
@[simp]
theorem unbot_coe (x : α) (h : (x : WithBot α) ≠ ⊥ := coe_ne_bot) : (x : WithBot α).unbot h = x :=
  rfl
#align with_bot.unbot_coe WithBot.unbot_coe
-/

instance canLift :
    CanLift (WithBot α) α coe fun r => r ≠ ⊥ where prf x h := ⟨x.unbot h, coe_unbot _ _⟩
#align with_bot.can_lift WithBot.canLift

section LE

variable [LE α]

instance (priority := 10) : LE (WithBot α) :=
  ⟨fun o₁ o₂ : Option α => ∀ a ∈ o₁, ∃ b ∈ o₂, a ≤ b⟩

/- warning: with_bot.some_le_some -> WithBot.some_le_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : LE.{u_1} α], Iff (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.hasLe.{u_1} α _inst_1) (Option.some.{u_1} α a) (Option.some.{u_1} α b)) (LE.le.{u_1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Order.WithBot._hyg.1043 : LE.{u_1} α], Iff (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1043) (Option.some.{u_1} α a) (Option.some.{u_1} α b)) (LE.le.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1043 a b)
Case conversion may be inaccurate. Consider using '#align with_bot.some_le_some WithBot.some_le_someₓ'. -/
@[simp]
theorem some_le_some : @LE.le (WithBot α) _ (some a) (some b) ↔ a ≤ b := by simp [(· ≤ ·)]
#align with_bot.some_le_some WithBot.some_le_some

/- warning: with_bot.coe_le_coe -> WithBot.coe_le_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : LE.{u_1} α], Iff (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.hasLe.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) b)) (LE.le.{u_1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Order.WithBot._hyg.1079 : LE.{u_1} α], Iff (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1079) (WithBot.some.{u_1} α a) (WithBot.some.{u_1} α b)) (LE.le.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1079 a b)
Case conversion may be inaccurate. Consider using '#align with_bot.coe_le_coe WithBot.coe_le_coeₓ'. -/
@[simp, norm_cast]
theorem coe_le_coe : (a : WithBot α) ≤ b ↔ a ≤ b :=
  some_le_some
#align with_bot.coe_le_coe WithBot.coe_le_coe

/- warning: with_bot.none_le -> WithBot.none_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] {a : WithBot.{u_1} α}, LE.le.{u_1} (WithBot.{u_1} α) (WithBot.hasLe.{u_1} α _inst_1) (Option.none.{u_1} α) a
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.1109 : LE.{u_1} α] {a : WithBot.{u_1} α}, LE.le.{u_1} (WithBot.{u_1} α) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1109) (Option.none.{u_1} α) a
Case conversion may be inaccurate. Consider using '#align with_bot.none_le WithBot.none_leₓ'. -/
@[simp]
theorem none_le {a : WithBot α} : @LE.le (WithBot α) _ none a := fun b h => Option.noConfusion h
#align with_bot.none_le WithBot.none_le

instance : OrderBot (WithBot α) :=
  { WithBot.hasBot with bot_le := fun a => none_le }

instance [OrderTop α] : OrderTop
      (WithBot α) where 
  top := some ⊤
  le_top o a ha := by cases ha <;> exact ⟨_, rfl, le_top⟩

instance [OrderTop α] : BoundedOrder (WithBot α) :=
  { WithBot.orderTop, WithBot.orderBot with }

/- warning: with_bot.not_coe_le_bot -> WithBot.not_coe_le_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] (a : α), Not (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.hasLe.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a) (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.hasBot.{u_1} α)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.1256 : LE.{u_1} α] (a : α), Not (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1256) (WithBot.some.{u_1} α a) (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.instBotWithBot.{u_1} α)))
Case conversion may be inaccurate. Consider using '#align with_bot.not_coe_le_bot WithBot.not_coe_le_botₓ'. -/
theorem not_coe_le_bot (a : α) : ¬(a : WithBot α) ≤ ⊥ := fun h =>
  let ⟨b, hb, _⟩ := h _ rfl
  Option.not_mem_none _ hb
#align with_bot.not_coe_le_bot WithBot.not_coe_le_bot

/- warning: with_bot.coe_le -> WithBot.coe_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : LE.{u_1} α] {o : Option.{u_1} α}, (Membership.Mem.{u_1, u_1} α (Option.{u_1} α) (Option.hasMem.{u_1} α) b o) -> (Iff (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.hasLe.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a) o) (LE.le.{u_1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Order.WithBot._hyg.1320 : LE.{u_1} α] {o : Option.{u_1} α}, (Membership.mem.{u_1, u_1} α (Option.{u_1} α) (Option.instMembershipOption.{u_1} α) b o) -> (Iff (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1320) (WithBot.some.{u_1} α a) o) (LE.le.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1320 a b))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_le WithBot.coe_leₓ'. -/
theorem coe_le : ∀ {o : Option α}, b ∈ o → ((a : WithBot α) ≤ o ↔ a ≤ b)
  | _, rfl => coe_le_coe
#align with_bot.coe_le WithBot.coe_le

/- warning: with_bot.coe_le_iff -> WithBot.coe_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} [_inst_1 : LE.{u_1} α] {x : WithBot.{u_1} α}, Iff (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.hasLe.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a) x) (Exists.{succ u_1} α (fun (b : α) => And (Eq.{succ u_1} (WithBot.{u_1} α) x ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) b)) (LE.le.{u_1} α _inst_1 a b)))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} [inst._@.Mathlib.Order.WithBot._hyg.1397 : LE.{u_1} α] {x : WithBot.{u_1} α}, Iff (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1397) (WithBot.some.{u_1} α a) x) (Exists.{succ u_1} α (fun (b : α) => And (Eq.{succ u_1} (WithBot.{u_1} α) x (WithBot.some.{u_1} α b)) (LE.le.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1397 a b)))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_le_iff WithBot.coe_le_iffₓ'. -/
theorem coe_le_iff : ∀ {x : WithBot α}, ↑a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b
  | some a => by simp [some_eq_coe, coe_eq_coe]
  | none => iff_of_false (not_coe_le_bot _) <| by simp [none_eq_bot]
#align with_bot.coe_le_iff WithBot.coe_le_iff

/- warning: with_bot.le_coe_iff -> WithBot.le_coe_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {b : α} [_inst_1 : LE.{u_1} α] {x : WithBot.{u_1} α}, Iff (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.hasLe.{u_1} α _inst_1) x ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) b)) (forall (a : α), (Eq.{succ u_1} (WithBot.{u_1} α) x ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a)) -> (LE.le.{u_1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u_1}} {b : α} [inst._@.Mathlib.Order.WithBot._hyg.1484 : LE.{u_1} α] {x : WithBot.{u_1} α}, Iff (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1484) x (WithBot.some.{u_1} α b)) (forall (a : WithBot.{u_1} α), (Eq.{succ u_1} (WithBot.{u_1} α) x a) -> (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1484) a (WithBot.some.{u_1} α b)))
Case conversion may be inaccurate. Consider using '#align with_bot.le_coe_iff WithBot.le_coe_iffₓ'. -/
theorem le_coe_iff : ∀ {x : WithBot α}, x ≤ b ↔ ∀ a, x = ↑a → a ≤ b
  | some b => by simp [some_eq_coe, coe_eq_coe]
  | none => by simp [none_eq_bot]
#align with_bot.le_coe_iff WithBot.le_coe_iff

/- warning: is_max.with_bot -> IsMax.withBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} [_inst_1 : LE.{u_1} α], (IsMax.{u_1} α _inst_1 a) -> (IsMax.{u_1} (WithBot.{u_1} α) (WithBot.hasLe.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} [inst._@.Mathlib.Order.WithBot._hyg.1555 : LE.{u_1} α], (IsMax.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1555 a) -> (IsMax.{u_1} (WithBot.{u_1} α) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1555) (WithBot.some.{u_1} α a))
Case conversion may be inaccurate. Consider using '#align is_max.with_bot IsMax.withBotₓ'. -/
protected theorem IsMax.withBot (h : IsMax a) : IsMax (a : WithBot α)
  | none, _ => bot_le
  | some b, hb => some_le_some.2 <| h <| some_le_some.1 hb
#align is_max.with_bot IsMax.withBot

end LE

section LT

variable [LT α]

instance (priority := 10) : LT (WithBot α) :=
  ⟨fun o₁ o₂ : Option α => ∃ b ∈ o₂, ∀ a ∈ o₁, a < b⟩

/- warning: with_bot.some_lt_some -> WithBot.some_lt_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : LT.{u_1} α], Iff (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) (Option.some.{u_1} α a) (Option.some.{u_1} α b)) (LT.lt.{u_1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Order.WithBot._hyg.1701 : LT.{u_1} α], Iff (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1701) (Option.some.{u_1} α a) (Option.some.{u_1} α b)) (LT.lt.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1701 a b)
Case conversion may be inaccurate. Consider using '#align with_bot.some_lt_some WithBot.some_lt_someₓ'. -/
@[simp]
theorem some_lt_some : @LT.lt (WithBot α) _ (some a) (some b) ↔ a < b := by simp [(· < ·)]
#align with_bot.some_lt_some WithBot.some_lt_some

/- warning: with_bot.coe_lt_coe -> WithBot.coe_lt_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : LT.{u_1} α], Iff (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) b)) (LT.lt.{u_1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Order.WithBot._hyg.1737 : LT.{u_1} α], Iff (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1737) (WithBot.some.{u_1} α a) (WithBot.some.{u_1} α b)) (LT.lt.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1737 a b)
Case conversion may be inaccurate. Consider using '#align with_bot.coe_lt_coe WithBot.coe_lt_coeₓ'. -/
@[simp, norm_cast]
theorem coe_lt_coe : (a : WithBot α) < b ↔ a < b :=
  some_lt_some
#align with_bot.coe_lt_coe WithBot.coe_lt_coe

/- warning: with_bot.none_lt_some -> WithBot.none_lt_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] (a : α), LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) (Option.none.{u_1} α) (Option.some.{u_1} α a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.1767 : LT.{u_1} α] (a : α), LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1767) (Option.none.{u_1} α) (WithBot.some.{u_1} α a)
Case conversion may be inaccurate. Consider using '#align with_bot.none_lt_some WithBot.none_lt_someₓ'. -/
@[simp]
theorem none_lt_some (a : α) : @LT.lt (WithBot α) _ none (some a) :=
  ⟨a, rfl, fun b hb => (Option.not_mem_none _ hb).elim⟩
#align with_bot.none_lt_some WithBot.none_lt_some

/- warning: with_bot.bot_lt_coe -> WithBot.bot_lt_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] (a : α), LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.hasBot.{u_1} α)) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.1806 : LT.{u_1} α] (a : α), LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1806) (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.instBotWithBot.{u_1} α)) (WithBot.some.{u_1} α a)
Case conversion may be inaccurate. Consider using '#align with_bot.bot_lt_coe WithBot.bot_lt_coeₓ'. -/
theorem bot_lt_coe (a : α) : (⊥ : WithBot α) < a :=
  none_lt_some a
#align with_bot.bot_lt_coe WithBot.bot_lt_coe

/- warning: with_bot.not_lt_none -> WithBot.not_lt_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] (a : WithBot.{u_1} α), Not (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) a (Option.none.{u_1} α))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.1832 : LT.{u_1} α] (a : WithBot.{u_1} α), Not (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1832) a (Option.none.{u_1} α))
Case conversion may be inaccurate. Consider using '#align with_bot.not_lt_none WithBot.not_lt_noneₓ'. -/
@[simp]
theorem not_lt_none (a : WithBot α) : ¬@LT.lt (WithBot α) _ a none := fun ⟨_, h, _⟩ =>
  Option.not_mem_none _ h
#align with_bot.not_lt_none WithBot.not_lt_none

/- warning: with_bot.lt_iff_exists_coe -> WithBot.lt_iff_exists_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithBot.{u_1} α} {b : WithBot.{u_1} α}, Iff (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) a b) (Exists.{succ u_1} α (fun (p : α) => And (Eq.{succ u_1} (WithBot.{u_1} α) b ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) p)) (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) a ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) p))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.1887 : LT.{u_1} α] {a : WithBot.{u_1} α} {b : WithBot.{u_1} α}, Iff (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1887) a b) (Exists.{succ u_1} α (fun (p : α) => And (Eq.{succ u_1} (WithBot.{u_1} α) b (WithBot.some.{u_1} α p)) (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1887) a (WithBot.some.{u_1} α p))))
Case conversion may be inaccurate. Consider using '#align with_bot.lt_iff_exists_coe WithBot.lt_iff_exists_coeₓ'. -/
theorem lt_iff_exists_coe : ∀ {a b : WithBot α}, a < b ↔ ∃ p : α, b = p ∧ a < p
  | a, some b => by simp [some_eq_coe, coe_eq_coe]
  | a, none => iff_of_false (not_lt_none _) <| by simp [none_eq_bot]
#align with_bot.lt_iff_exists_coe WithBot.lt_iff_exists_coe

/- warning: with_bot.lt_coe_iff -> WithBot.lt_coe_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {b : α} [_inst_1 : LT.{u_1} α] {x : WithBot.{u_1} α}, Iff (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) x ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) b)) (forall (a : α), (Eq.{succ u_1} (WithBot.{u_1} α) x ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a)) -> (LT.lt.{u_1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u_1}} {b : α} [inst._@.Mathlib.Order.WithBot._hyg.1988 : LT.{u_1} α] {x : WithBot.{u_1} α}, Iff (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1988) x (WithBot.some.{u_1} α b)) (forall (a : WithBot.{u_1} α), (Eq.{succ u_1} (WithBot.{u_1} α) x a) -> (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.1988) a (WithBot.some.{u_1} α b)))
Case conversion may be inaccurate. Consider using '#align with_bot.lt_coe_iff WithBot.lt_coe_iffₓ'. -/
theorem lt_coe_iff : ∀ {x : WithBot α}, x < b ↔ ∀ a, x = ↑a → a < b
  | some b => by simp [some_eq_coe, coe_eq_coe, coe_lt_coe]
  | none => by simp [none_eq_bot, bot_lt_coe]
#align with_bot.lt_coe_iff WithBot.lt_coe_iff

end LT

instance [Preorder α] : Preorder
      (WithBot α) where 
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by 
    intros
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
      · cases' o₂ with b
        · rfl
        rcases h₂ b rfl with ⟨_, ⟨⟩, _⟩
      · rcases h₁ a rfl with ⟨b, ⟨⟩, h₁'⟩
        rcases h₂ b rfl with ⟨_, ⟨⟩, h₂'⟩
        rw [le_antisymm h₁' h₂'] }

/- warning: with_bot.coe_strict_mono -> WithBot.coe_strict_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α], StrictMono.{u_1, u_1} α (WithBot.{u_1} α) _inst_1 (WithBot.preorder.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.2367 : Preorder.{u_1} α], StrictMono.{u_1, u_1} α (WithBot.{u_1} α) inst._@.Mathlib.Order.WithBot._hyg.2367 (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.2367) (fun (a : α) => WithBot.some.{u_1} α a)
Case conversion may be inaccurate. Consider using '#align with_bot.coe_strict_mono WithBot.coe_strict_monoₓ'. -/
theorem coe_strict_mono [Preorder α] : StrictMono (coe : α → WithBot α) := fun a b => some_lt_some.2
#align with_bot.coe_strict_mono WithBot.coe_strict_mono

/- warning: with_bot.coe_mono -> WithBot.coe_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α], Monotone.{u_1, u_1} α (WithBot.{u_1} α) _inst_1 (WithBot.preorder.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.2396 : Preorder.{u_1} α], Monotone.{u_1, u_1} α (WithBot.{u_1} α) inst._@.Mathlib.Order.WithBot._hyg.2396 (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.2396) (fun (a : α) => WithBot.some.{u_1} α a)
Case conversion may be inaccurate. Consider using '#align with_bot.coe_mono WithBot.coe_monoₓ'. -/
theorem coe_mono [Preorder α] : Monotone (coe : α → WithBot α) := fun a b => coe_le_coe.2
#align with_bot.coe_mono WithBot.coe_mono

/- warning: with_bot.monotone_iff -> WithBot.monotone_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : Preorder.{u_2} β] {f : (WithBot.{u_1} α) -> β}, Iff (Monotone.{u_1, u_2} (WithBot.{u_1} α) β (WithBot.preorder.{u_1} α _inst_1) _inst_2 f) (And (Monotone.{u_1, u_2} α β _inst_1 _inst_2 (Function.comp.{succ u_1, succ u_1, succ u_2} α (WithBot.{u_1} α) β f ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α)))))) (forall (x : α), LE.le.{u_2} β (Preorder.toLE.{u_2} β _inst_2) (f (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.hasBot.{u_1} α))) (f ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) x))))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.WithBot._hyg.2425 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.2428 : Preorder.{u_2} β] {f : (WithBot.{u_1} α) -> β}, Iff (Monotone.{u_1, u_2} (WithBot.{u_1} α) β (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.2425) inst._@.Mathlib.Order.WithBot._hyg.2428 f) (And (Monotone.{u_1, u_2} α β inst._@.Mathlib.Order.WithBot._hyg.2425 inst._@.Mathlib.Order.WithBot._hyg.2428 (fun (a : α) => f (WithBot.some.{u_1} α a))) (forall (x : α), LE.le.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.WithBot._hyg.2428) (f (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.instBotWithBot.{u_1} α))) (f (WithBot.some.{u_1} α x))))
Case conversion may be inaccurate. Consider using '#align with_bot.monotone_iff WithBot.monotone_iffₓ'. -/
theorem monotone_iff [Preorder α] [Preorder β] {f : WithBot α → β} :
    Monotone f ↔ Monotone (f ∘ coe : α → β) ∧ ∀ x : α, f ⊥ ≤ f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_mono, fun x => h bot_le⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨fun _ => le_rfl, fun x _ => h.2 x⟩, fun x =>
        WithBot.forall.2 ⟨fun h => (not_coe_le_bot _ h).elim, fun y hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩
#align with_bot.monotone_iff WithBot.monotone_iff

/- warning: with_bot.monotone_map_iff -> WithBot.monotone_map_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : Preorder.{u_2} β] {f : α -> β}, Iff (Monotone.{u_1, u_2} (WithBot.{u_1} α) (WithBot.{u_2} β) (WithBot.preorder.{u_1} α _inst_1) (WithBot.preorder.{u_2} β _inst_2) (WithBot.map.{u_1, u_2} α β f)) (Monotone.{u_1, u_2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.WithBot._hyg.2538 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.2541 : Preorder.{u_2} β] {f : α -> β}, Iff (Monotone.{u_1, u_2} (WithBot.{u_1} α) (WithBot.{u_2} β) (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.2538) (WithBot.instPreorderWithBot.{u_2} β inst._@.Mathlib.Order.WithBot._hyg.2541) (WithBot.map.{u_1, u_2} α β f)) (Monotone.{u_1, u_2} α β inst._@.Mathlib.Order.WithBot._hyg.2538 inst._@.Mathlib.Order.WithBot._hyg.2541 f)
Case conversion may be inaccurate. Consider using '#align with_bot.monotone_map_iff WithBot.monotone_map_iffₓ'. -/
@[simp]
theorem monotone_map_iff [Preorder α] [Preorder β] {f : α → β} :
    Monotone (WithBot.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]
#align with_bot.monotone_map_iff WithBot.monotone_map_iff

alias monotone_map_iff ↔ _ _root_.monotone.with_bot_map

/- warning: with_bot.strict_mono_iff -> WithBot.strict_mono_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : Preorder.{u_2} β] {f : (WithBot.{u_1} α) -> β}, Iff (StrictMono.{u_1, u_2} (WithBot.{u_1} α) β (WithBot.preorder.{u_1} α _inst_1) _inst_2 f) (And (StrictMono.{u_1, u_2} α β _inst_1 _inst_2 (Function.comp.{succ u_1, succ u_1, succ u_2} α (WithBot.{u_1} α) β f ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α)))))) (forall (x : α), LT.lt.{u_2} β (Preorder.toLT.{u_2} β _inst_2) (f (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.hasBot.{u_1} α))) (f ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) x))))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.WithBot._hyg.2573 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.2576 : Preorder.{u_2} β] {f : (WithBot.{u_1} α) -> β}, Iff (StrictMono.{u_1, u_2} (WithBot.{u_1} α) β (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.2573) inst._@.Mathlib.Order.WithBot._hyg.2576 f) (And (StrictMono.{u_1, u_2} α β inst._@.Mathlib.Order.WithBot._hyg.2573 inst._@.Mathlib.Order.WithBot._hyg.2576 (fun (a : α) => f (WithBot.some.{u_1} α a))) (forall (x : α), LT.lt.{u_2} β (Preorder.toLT.{u_2} β inst._@.Mathlib.Order.WithBot._hyg.2576) (f (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.instBotWithBot.{u_1} α))) (f (WithBot.some.{u_1} α x))))
Case conversion may be inaccurate. Consider using '#align with_bot.strict_mono_iff WithBot.strict_mono_iffₓ'. -/
theorem strict_mono_iff [Preorder α] [Preorder β] {f : WithBot α → β} :
    StrictMono f ↔ StrictMono (f ∘ coe : α → β) ∧ ∀ x : α, f ⊥ < f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_strict_mono, fun x => h (bot_lt_coe _)⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨flip absurd (lt_irrefl _), fun x _ => h.2 x⟩, fun x =>
        WithBot.forall.2 ⟨fun h => (not_lt_bot h).elim, fun y hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩
#align with_bot.strict_mono_iff WithBot.strict_mono_iff

/- warning: with_bot.strict_mono_map_iff -> WithBot.strict_mono_map_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : Preorder.{u_2} β] {f : α -> β}, Iff (StrictMono.{u_1, u_2} (WithBot.{u_1} α) (WithBot.{u_2} β) (WithBot.preorder.{u_1} α _inst_1) (WithBot.preorder.{u_2} β _inst_2) (WithBot.map.{u_1, u_2} α β f)) (StrictMono.{u_1, u_2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.WithBot._hyg.2689 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.2692 : Preorder.{u_2} β] {f : α -> β}, Iff (StrictMono.{u_1, u_2} (WithBot.{u_1} α) (WithBot.{u_2} β) (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.2689) (WithBot.instPreorderWithBot.{u_2} β inst._@.Mathlib.Order.WithBot._hyg.2692) (WithBot.map.{u_1, u_2} α β f)) (StrictMono.{u_1, u_2} α β inst._@.Mathlib.Order.WithBot._hyg.2689 inst._@.Mathlib.Order.WithBot._hyg.2692 f)
Case conversion may be inaccurate. Consider using '#align with_bot.strict_mono_map_iff WithBot.strict_mono_map_iffₓ'. -/
@[simp]
theorem strict_mono_map_iff [Preorder α] [Preorder β] {f : α → β} :
    StrictMono (WithBot.map f) ↔ StrictMono f :=
  strict_mono_iff.trans <| by simp [StrictMono, bot_lt_coe]
#align with_bot.strict_mono_map_iff WithBot.strict_mono_map_iff

alias strict_mono_map_iff ↔ _ _root_.strict_mono.with_bot_map

/- warning: with_bot.map_le_iff -> WithBot.map_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : Preorder.{u_2} β] (f : α -> β), (forall {a : α} {b : α}, Iff (LE.le.{u_2} β (Preorder.toLE.{u_2} β _inst_2) (f a) (f b)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_1) a b)) -> (forall (a : WithBot.{u_1} α) (b : WithBot.{u_1} α), Iff (LE.le.{u_2} (WithBot.{u_2} β) (Preorder.toLE.{u_2} (WithBot.{u_2} β) (WithBot.preorder.{u_2} β _inst_2)) (WithBot.map.{u_1, u_2} α β f a) (WithBot.map.{u_1, u_2} α β f b)) (LE.le.{u_1} (WithBot.{u_1} α) (Preorder.toLE.{u_1} (WithBot.{u_1} α) (WithBot.preorder.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.WithBot._hyg.2724 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.2727 : Preorder.{u_2} β] (f : α -> β), (forall {a : α} {b : α}, Iff (LE.le.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.WithBot._hyg.2727) (f a) (f b)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.2724) a b)) -> (forall (a : WithBot.{u_1} α) (b : WithBot.{u_1} α), Iff (LE.le.{u_2} (WithBot.{u_2} β) (Preorder.toLE.{u_2} (WithBot.{u_2} β) (WithBot.instPreorderWithBot.{u_2} β inst._@.Mathlib.Order.WithBot._hyg.2727)) (WithBot.map.{u_1, u_2} α β f a) (WithBot.map.{u_1, u_2} α β f b)) (LE.le.{u_1} (WithBot.{u_1} α) (Preorder.toLE.{u_1} (WithBot.{u_1} α) (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.2724)) a b))
Case conversion may be inaccurate. Consider using '#align with_bot.map_le_iff WithBot.map_le_iffₓ'. -/
theorem map_le_iff [Preorder α] [Preorder β] (f : α → β) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    ∀ a b : WithBot α, a.map f ≤ b.map f ↔ a ≤ b
  | ⊥, _ => by simp only [map_bot, bot_le]
  | (a : α), ⊥ => by simp only [map_coe, map_bot, coe_ne_bot, not_coe_le_bot _]
  | (a : α), (b : α) => by simpa only [map_coe, coe_le_coe] using mono_iff
#align with_bot.map_le_iff WithBot.map_le_iff

/- warning: with_bot.le_coe_unbot' -> WithBot.le_coe_unbot' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α] (a : WithBot.{u_1} α) (b : α), LE.le.{u_1} (WithBot.{u_1} α) (Preorder.toLE.{u_1} (WithBot.{u_1} α) (WithBot.preorder.{u_1} α _inst_1)) a ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) (WithBot.unbot'.{u_1} α b a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.2887 : Preorder.{u_1} α] (a : WithBot.{u_1} α) (b : α), LE.le.{u_1} (WithBot.{u_1} α) (Preorder.toLE.{u_1} (WithBot.{u_1} α) (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.2887)) a (WithBot.some.{u_1} α (WithBot.unbot'.{u_1} α b a))
Case conversion may be inaccurate. Consider using '#align with_bot.le_coe_unbot' WithBot.le_coe_unbot'ₓ'. -/
theorem le_coe_unbot' [Preorder α] : ∀ (a : WithBot α) (b : α), a ≤ a.unbot' b
  | (a : α), b => le_rfl
  | ⊥, b => bot_le
#align with_bot.le_coe_unbot' WithBot.le_coe_unbot'

/- warning: with_bot.unbot'_bot_le_iff -> WithBot.unbot'_bot_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] [_inst_2 : OrderBot.{u_1} α _inst_1] {a : WithBot.{u_1} α} {b : α}, Iff (LE.le.{u_1} α _inst_1 (WithBot.unbot'.{u_1} α (Bot.bot.{u_1} α (OrderBot.toHasBot.{u_1} α _inst_1 _inst_2)) a) b) (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.hasLe.{u_1} α _inst_1) a ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.2958 : LE.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.2961 : OrderBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.2958] {a : WithBot.{u_1} α} {b : α}, Iff (LE.le.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.2958 (WithBot.unbot'.{u_1} α (Bot.bot.{u_1} α (OrderBot.toBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.2958 inst._@.Mathlib.Order.WithBot._hyg.2961)) a) b) (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.2958) a (WithBot.some.{u_1} α b))
Case conversion may be inaccurate. Consider using '#align with_bot.unbot'_bot_le_iff WithBot.unbot'_bot_le_iffₓ'. -/
theorem unbot'_bot_le_iff [LE α] [OrderBot α] {a : WithBot α} {b : α} : a.unbot' ⊥ ≤ b ↔ a ≤ b := by
  cases a <;> simp [none_eq_bot, some_eq_coe]
#align with_bot.unbot'_bot_le_iff WithBot.unbot'_bot_le_iff

/- warning: with_bot.unbot'_lt_iff -> WithBot.unbot'_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithBot.{u_1} α} {b : α} {c : α}, (Ne.{succ u_1} (WithBot.{u_1} α) a (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.hasBot.{u_1} α))) -> (Iff (LT.lt.{u_1} α _inst_1 (WithBot.unbot'.{u_1} α b a) c) (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) a ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) c)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.3013 : LT.{u_1} α] {a : WithBot.{u_1} α} {b : α} {c : α}, (Ne.{succ u_1} (WithBot.{u_1} α) a (Bot.bot.{u_1} (WithBot.{u_1} α) (WithBot.instBotWithBot.{u_1} α))) -> (Iff (LT.lt.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.3013 (WithBot.unbot'.{u_1} α b a) c) (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.3013) a (WithBot.some.{u_1} α c)))
Case conversion may be inaccurate. Consider using '#align with_bot.unbot'_lt_iff WithBot.unbot'_lt_iffₓ'. -/
theorem unbot'_lt_iff [LT α] {a : WithBot α} {b c : α} (ha : a ≠ ⊥) : a.unbot' b < c ↔ a < c := by
  lift a to α using ha
  rw [unbot'_coe, coe_lt_coe]
#align with_bot.unbot'_lt_iff WithBot.unbot'_lt_iff

instance [SemilatticeSup α] : SemilatticeSup (WithBot α) :=
  { WithBot.orderBot, WithBot.partialOrder with sup := Option.liftOrGet (· ⊔ ·),
    le_sup_left := fun o₁ o₂ a ha => by cases ha <;> cases o₂ <;> simp [Option.liftOrGet],
    le_sup_right := fun o₁ o₂ a ha => by cases ha <;> cases o₁ <;> simp [Option.liftOrGet],
    sup_le := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases' o₁ with b <;> cases' o₂ with c <;> cases ha
      · exact h₂ a rfl
      · exact h₁ a rfl
      · rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩
        simp at h₂
        exact ⟨d, rfl, sup_le h₁' h₂⟩ }

/- warning: with_bot.coe_sup -> WithBot.coe_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : SemilatticeSup.{u_1} α] (a : α) (b : α), Eq.{succ u_1} (WithBot.{u_1} α) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) (HasSup.sup.{u_1} α (SemilatticeSup.toHasSup.{u_1} α _inst_1) a b)) (HasSup.sup.{u_1} (WithBot.{u_1} α) (SemilatticeSup.toHasSup.{u_1} (WithBot.{u_1} α) (WithBot.semilatticeSup.{u_1} α _inst_1)) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.3336 : SemilatticeSup.{u_1} α] (a : α) (b : α), Eq.{succ u_1} (WithBot.{u_1} α) (WithBot.some.{u_1} α (HasSup.sup.{u_1} α (SemilatticeSup.toHasSup.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.3336) a b)) (HasSup.sup.{u_1} (WithBot.{u_1} α) (SemilatticeSup.toHasSup.{u_1} (WithBot.{u_1} α) (WithBot.instSemilatticeSupWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.3336)) (WithBot.some.{u_1} α a) (WithBot.some.{u_1} α b))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_sup WithBot.coe_supₓ'. -/
theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithBot α) = a ⊔ b :=
  rfl
#align with_bot.coe_sup WithBot.coe_sup

instance [SemilatticeInf α] : SemilatticeInf (WithBot α) :=
  { WithBot.orderBot, WithBot.partialOrder with
    inf := fun o₁ o₂ => o₁.bind fun a => o₂.map fun b => a ⊓ b,
    inf_le_left := fun o₁ o₂ a ha => by 
      simp [map] at ha; rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, inf_le_left⟩,
    inf_le_right := fun o₁ o₂ a ha => by 
      simp [map] at ha; rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, inf_le_right⟩,
    le_inf := fun o₁ o₂ o₃ h₁ h₂ a ha => by 
      cases ha
      rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩
      rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩
      exact ⟨_, rfl, le_inf ab ac⟩ }

/- warning: with_bot.coe_inf -> WithBot.coe_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : SemilatticeInf.{u_1} α] (a : α) (b : α), Eq.{succ u_1} (WithBot.{u_1} α) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) (HasInf.inf.{u_1} α (SemilatticeInf.toHasInf.{u_1} α _inst_1) a b)) (HasInf.inf.{u_1} (WithBot.{u_1} α) (SemilatticeInf.toHasInf.{u_1} (WithBot.{u_1} α) (WithBot.semilatticeInf.{u_1} α _inst_1)) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) a) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.3539 : SemilatticeInf.{u_1} α] (a : α) (b : α), Eq.{succ u_1} (WithBot.{u_1} α) (WithBot.some.{u_1} α (HasInf.inf.{u_1} α (SemilatticeInf.toHasInf.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.3539) a b)) (HasInf.inf.{u_1} (WithBot.{u_1} α) (SemilatticeInf.toHasInf.{u_1} (WithBot.{u_1} α) (WithBot.instSemilatticeInfWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.3539)) (WithBot.some.{u_1} α a) (WithBot.some.{u_1} α b))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_inf WithBot.coe_infₓ'. -/
theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithBot α) = a ⊓ b :=
  rfl
#align with_bot.coe_inf WithBot.coe_inf

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

/- warning: with_bot.decidable_le -> WithBot.decidableLe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] [_inst_2 : DecidableRel.{succ u_1} α (LE.le.{u_1} α _inst_1)], DecidableRel.{succ u_1} (WithBot.{u_1} α) (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.hasLe.{u_1} α _inst_1))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.3814 : LE.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.3817 : DecidableRel.{succ u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.3823 : α) (x._@.Mathlib.Order.WithBot._hyg.3825 : α) => LE.le.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.3814 x._@.Mathlib.Order.WithBot._hyg.3823 x._@.Mathlib.Order.WithBot._hyg.3825)], DecidableRel.{succ u_1} (WithBot.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.3843 : WithBot.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.3845 : WithBot.{u_1} α) => LE.le.{u_1} (WithBot.{u_1} α) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.3814) x._@.Mathlib.Order.WithBot._hyg.3843 x._@.Mathlib.Order.WithBot._hyg.3845)
Case conversion may be inaccurate. Consider using '#align with_bot.decidable_le WithBot.decidableLeₓ'. -/
instance decidableLe [LE α] [@DecidableRel α (· ≤ ·)] : @DecidableRel (WithBot α) (· ≤ ·)
  | none, x => is_true fun a h => Option.noConfusion h
  | some x, some y => if h : x ≤ y then isTrue (some_le_some.2 h) else is_false <| by simp [*]
  | some x, none => is_false fun h => by rcases h x rfl with ⟨y, ⟨_⟩, _⟩
#align with_bot.decidable_le WithBot.decidableLe

/- warning: with_bot.decidable_lt -> WithBot.decidableLt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] [_inst_2 : DecidableRel.{succ u_1} α (LT.lt.{u_1} α _inst_1)], DecidableRel.{succ u_1} (WithBot.{u_1} α) (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.3976 : LT.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.3979 : DecidableRel.{succ u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.3985 : α) (x._@.Mathlib.Order.WithBot._hyg.3987 : α) => LT.lt.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.3976 x._@.Mathlib.Order.WithBot._hyg.3985 x._@.Mathlib.Order.WithBot._hyg.3987)], DecidableRel.{succ u_1} (WithBot.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.4005 : WithBot.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.4007 : WithBot.{u_1} α) => LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.3976) x._@.Mathlib.Order.WithBot._hyg.4005 x._@.Mathlib.Order.WithBot._hyg.4007)
Case conversion may be inaccurate. Consider using '#align with_bot.decidable_lt WithBot.decidableLtₓ'. -/
instance decidableLt [LT α] [@DecidableRel α (· < ·)] : @DecidableRel (WithBot α) (· < ·)
  | none, some x => is_true <| by exists x, rfl <;> rintro _ ⟨⟩
  | some x, some y => if h : x < y then is_true <| by simp [*] else is_false <| by simp [*]
  | x, none => is_false <| by rintro ⟨a, ⟨⟨⟩⟩⟩
#align with_bot.decidable_lt WithBot.decidableLt

/- warning: with_bot.is_total_le -> WithBot.is_total_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] [_inst_2 : IsTotal.{u_1} α (LE.le.{u_1} α _inst_1)], IsTotal.{u_1} (WithBot.{u_1} α) (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.hasLe.{u_1} α _inst_1))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.4175 : LE.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.4178 : IsTotal.{u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.4184 : α) (x._@.Mathlib.Order.WithBot._hyg.4186 : α) => LE.le.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.4175 x._@.Mathlib.Order.WithBot._hyg.4184 x._@.Mathlib.Order.WithBot._hyg.4186)], IsTotal.{u_1} (WithBot.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.4204 : WithBot.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.4206 : WithBot.{u_1} α) => LE.le.{u_1} (WithBot.{u_1} α) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.4175) x._@.Mathlib.Order.WithBot._hyg.4204 x._@.Mathlib.Order.WithBot._hyg.4206)
Case conversion may be inaccurate. Consider using '#align with_bot.is_total_le WithBot.is_total_leₓ'. -/
instance is_total_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithBot α) (· ≤ ·) :=
  ⟨fun a b =>
    match a, b with
    | none, _ => Or.inl bot_le
    | _, none => Or.inr bot_le
    | some x, some y => (total_of (· ≤ ·) x y).imp some_le_some.2 some_le_some.2⟩
#align with_bot.is_total_le WithBot.is_total_le

instance [LinearOrder α] : LinearOrder (WithBot α) :=
  Lattice.toLinearOrder _

/- warning: with_bot.coe_min -> WithBot.coe_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LinearOrder.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (WithBot.{u_1} α) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) (LinearOrder.min.{u_1} α _inst_1 x y)) (LinearOrder.min.{u_1} (WithBot.{u_1} α) (WithBot.linearOrder.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) x) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) y))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.4308 : LinearOrder.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (WithBot.{u_1} α) (WithBot.some.{u_1} α (Min.min.{u_1} α (LinearOrder.toMin.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.4308) x y)) (Min.min.{u_1} (WithBot.{u_1} α) (LinearOrder.toMin.{u_1} (WithBot.{u_1} α) (WithBot.instLinearOrderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.4308)) (WithBot.some.{u_1} α x) (WithBot.some.{u_1} α y))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_min WithBot.coe_minₓ'. -/
-- this is not marked simp because the corresponding with_top lemmas are used
@[norm_cast]
theorem coe_min [LinearOrder α] (x y : α) : ((min x y : α) : WithBot α) = min x y :=
  rfl
#align with_bot.coe_min WithBot.coe_min

/- warning: with_bot.coe_max -> WithBot.coe_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LinearOrder.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (WithBot.{u_1} α) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) (LinearOrder.max.{u_1} α _inst_1 x y)) (LinearOrder.max.{u_1} (WithBot.{u_1} α) (WithBot.linearOrder.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) x) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) y))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.4343 : LinearOrder.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (WithBot.{u_1} α) (WithBot.some.{u_1} α (Max.max.{u_1} α (LinearOrder.toMax.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.4343) x y)) (Max.max.{u_1} (WithBot.{u_1} α) (LinearOrder.toMax.{u_1} (WithBot.{u_1} α) (WithBot.instLinearOrderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.4343)) (WithBot.some.{u_1} α x) (WithBot.some.{u_1} α y))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_max WithBot.coe_maxₓ'. -/
-- this is not marked simp because the corresponding with_top lemmas are used
@[norm_cast]
theorem coe_max [LinearOrder α] (x y : α) : ((max x y : α) : WithBot α) = max x y :=
  rfl
#align with_bot.coe_max WithBot.coe_max

/- warning: with_bot.well_founded_lt -> WithBot.well_founded_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α], (WellFounded.{succ u_1} α (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_1))) -> (WellFounded.{succ u_1} (WithBot.{u_1} α) (LT.lt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.preorder.{u_1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.4378 : Preorder.{u_1} α], (WellFounded.{succ u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.4386 : α) (x._@.Mathlib.Order.WithBot._hyg.4388 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.4378) x._@.Mathlib.Order.WithBot._hyg.4386 x._@.Mathlib.Order.WithBot._hyg.4388)) -> (WellFounded.{succ u_1} (WithBot.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.4406 : WithBot.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.4408 : WithBot.{u_1} α) => LT.lt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.4378)) x._@.Mathlib.Order.WithBot._hyg.4406 x._@.Mathlib.Order.WithBot._hyg.4408))
Case conversion may be inaccurate. Consider using '#align with_bot.well_founded_lt WithBot.well_founded_ltₓ'. -/
theorem well_founded_lt [Preorder α] (h : @WellFounded α (· < ·)) :
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
#align with_bot.well_founded_lt WithBot.well_founded_lt

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

/- warning: with_bot.lt_iff_exists_coe_btwn -> WithBot.lt_iff_exists_coe_btwn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : DenselyOrdered.{u_1} α (Preorder.toLT.{u_1} α _inst_1)] [_inst_3 : NoMinOrder.{u_1} α (Preorder.toLT.{u_1} α _inst_1)] {a : WithBot.{u_1} α} {b : WithBot.{u_1} α}, Iff (LT.lt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.preorder.{u_1} α _inst_1)) a b) (Exists.{succ u_1} α (fun (x : α) => And (LT.lt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.preorder.{u_1} α _inst_1)) a ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) x)) (LT.lt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.preorder.{u_1} α _inst_1)) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithBot.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithBot.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithBot.{u_1} α) (WithBot.hasCoeT.{u_1} α))) x) b)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.4791 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.4794 : DenselyOrdered.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.4791)] [inst._@.Mathlib.Order.WithBot._hyg.4797 : NoMinOrder.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.4791)] {a : WithBot.{u_1} α} {b : WithBot.{u_1} α}, Iff (LT.lt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.4791)) a b) (Exists.{succ u_1} α (fun (x : α) => And (LT.lt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.4791)) a (WithBot.some.{u_1} α x)) (LT.lt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.4791)) (WithBot.some.{u_1} α x) b)))
Case conversion may be inaccurate. Consider using '#align with_bot.lt_iff_exists_coe_btwn WithBot.lt_iff_exists_coe_btwnₓ'. -/
theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨y, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨x, hx⟩ => lt_trans hx.1 hx.2⟩
#align with_bot.lt_iff_exists_coe_btwn WithBot.lt_iff_exists_coe_btwn

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

unsafe instance [has_to_format α] :
    has_to_format (WithTop α) where to_format x :=
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

/- warning: with_top.rec_top_coe_top -> WithTop.rec_top_coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {C : (WithTop.{u_1} α) -> Sort.{u_2}} (d : C (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.hasTop.{u_1} α))) (f : forall (a : α), C ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a)), Eq.{u_2} (C (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.hasTop.{u_1} α))) (WithTop.recTopCoe.{u_1, u_2} α C d f (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.hasTop.{u_1} α))) d
but is expected to have type
  forall {α : Type.{u_1}} {C : (WithTop.{u_1} α) -> Sort.{u_2}} (d : C (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.instTopWithTop.{u_1} α))) (f : forall (a : α), C (WithTop.some.{u_1} α a)), Eq.{u_2} (C (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.instTopWithTop.{u_1} α))) (WithTop.recTopCoe.{u_1, u_2} α C d f (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.instTopWithTop.{u_1} α))) d
Case conversion may be inaccurate. Consider using '#align with_top.rec_top_coe_top WithTop.rec_top_coe_topₓ'. -/
@[simp]
theorem rec_top_coe_top {C : WithTop α → Sort _} (d : C ⊤) (f : ∀ a : α, C a) :
    @recTopCoe _ C d f ⊤ = d :=
  rfl
#align with_top.rec_top_coe_top WithTop.rec_top_coe_top

/- warning: with_top.rec_top_coe_coe -> WithTop.rec_top_coe_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {C : (WithTop.{u_1} α) -> Sort.{u_2}} (d : C (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.hasTop.{u_1} α))) (f : forall (a : α), C ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a)) (x : α), Eq.{u_2} (C ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) x)) (WithTop.recTopCoe.{u_1, u_2} α C d f ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) x)) (f x)
but is expected to have type
  forall {α : Type.{u_1}} {C : (WithTop.{u_1} α) -> Sort.{u_2}} (d : C (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.instTopWithTop.{u_1} α))) (f : forall (a : α), C (WithTop.some.{u_1} α a)) (x : α), Eq.{u_2} (C (WithTop.some.{u_1} α x)) (WithTop.recTopCoe.{u_1, u_2} α C d f (WithTop.some.{u_1} α x)) (f x)
Case conversion may be inaccurate. Consider using '#align with_top.rec_top_coe_coe WithTop.rec_top_coe_coeₓ'. -/
@[simp]
theorem rec_top_coe_coe {C : WithTop α → Sort _} (d : C ⊤) (f : ∀ a : α, C a) (x : α) :
    @recTopCoe _ C d f ↑x = f x :=
  rfl
#align with_top.rec_top_coe_coe WithTop.rec_top_coe_coe

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

/- warning: with_top.map_comm -> WithTop.map_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ}, (Eq.{max (succ u_1) (succ u_4)} (α -> δ) (Function.comp.{succ u_1, succ u_2, succ u_4} α β δ g₁ f₁) (Function.comp.{succ u_1, succ u_3, succ u_4} α γ δ g₂ f₂)) -> (forall (a : α), Eq.{succ u_4} (WithTop.{u_4} δ) (WithTop.map.{u_2, u_4} β δ g₁ (WithTop.map.{u_1, u_2} α β f₁ ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a))) (WithTop.map.{u_3, u_4} γ δ g₂ (WithTop.map.{u_1, u_3} α γ f₂ ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a))))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_4}} {δ : Type.{u_2}} {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ}, (Eq.{max (succ u_1) (succ u_2)} (α -> δ) (Function.comp.{succ u_1, succ u_3, succ u_2} α β δ g₁ f₁) (Function.comp.{succ u_1, succ u_4, succ u_2} α γ δ g₂ f₂)) -> (forall (a : α), Eq.{succ u_2} (WithTop.{u_2} δ) (WithTop.map.{u_3, u_2} β δ g₁ (WithTop.map.{u_1, u_3} α β f₁ (WithTop.some.{u_1} α a))) (WithTop.map.{u_4, u_2} γ δ g₂ (WithTop.map.{u_1, u_4} α γ f₂ (WithTop.some.{u_1} α a))))
Case conversion may be inaccurate. Consider using '#align with_top.map_comm WithTop.map_commₓ'. -/
theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂)
    (a : α) : map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _
#align with_top.map_comm WithTop.map_comm

/- warning: with_top.map_to_dual -> WithTop.map_toDual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : (OrderDual.{u_1} α) -> (OrderDual.{u_2} β)) (a : WithBot.{u_1} α), Eq.{succ u_2} (WithTop.{u_2} (OrderDual.{u_2} β)) (WithTop.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) f (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) => (WithBot.{u_1} α) -> (WithTop.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.toDual.{u_1} α) a)) (WithBot.map.{u_1, u_2} α (OrderDual.{u_2} β) (Function.comp.{succ u_1, succ u_2, succ u_2} α β (OrderDual.{u_2} β) (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (fun (_x : Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) => β -> (OrderDual.{u_2} β)) (Equiv.hasCoeToFun.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (OrderDual.toDual.{u_2} β)) f) a)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : (OrderDual.{u_1} α) -> (OrderDual.{u_2} β)) (a : WithBot.{u_1} α), Eq.{succ u_2} (WithTop.{u_2} (OrderDual.{u_2} β)) (WithTop.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) f (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (fun (a : WithBot.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))))) (WithBot.toDual.{u_1} α) a)) (WithBot.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) (Function.comp.{succ u_1, succ u_2, succ u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) (OrderDual.{u_2} β) (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) (OrderDual.{u_2} (OrderDual.{u_2} β))) (OrderDual.{u_2} β) (fun (a : OrderDual.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => OrderDual.{u_2} (OrderDual.{u_2} β)) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) (OrderDual.{u_2} (OrderDual.{u_2} β))) (OrderDual.{u_2} β) (OrderDual.{u_2} (OrderDual.{u_2} β)) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) (OrderDual.{u_2} (OrderDual.{u_2} β))) (OrderDual.{u_2} β) (OrderDual.{u_2} (OrderDual.{u_2} β)) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) (OrderDual.{u_2} (OrderDual.{u_2} β))))) (OrderDual.toDual.{u_2} (OrderDual.{u_2} β))) f) a)
Case conversion may be inaccurate. Consider using '#align with_top.map_to_dual WithTop.map_toDualₓ'. -/
theorem map_toDual (f : αᵒᵈ → βᵒᵈ) (a : WithBot α) :
    map f (WithBot.toDual a) = a.map (to_dual ∘ f) :=
  rfl
#align with_top.map_to_dual WithTop.map_toDual

/- warning: with_top.map_of_dual -> WithTop.map_ofDual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β) (a : WithBot.{u_1} (OrderDual.{u_1} α)), Eq.{succ u_2} (WithTop.{u_2} β) (WithTop.map.{u_1, u_2} α β f (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) => (WithBot.{u_1} (OrderDual.{u_1} α)) -> (WithTop.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.ofDual.{u_1} α) a)) (WithBot.map.{u_1, u_2} (OrderDual.{u_1} α) β (Function.comp.{succ u_1, succ u_2, succ u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) β (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (fun (_x : Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) => (OrderDual.{u_2} β) -> β) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.ofDual.{u_2} β)) f) a)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β) (a : WithBot.{u_1} (OrderDual.{u_1} α)), Eq.{succ u_2} (WithTop.{u_2} β) (WithTop.map.{u_1, u_2} α β f (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (fun (a : WithBot.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)))) (WithBot.ofDual.{u_1} α) a)) (WithBot.map.{u_1, u_2} α β (Function.comp.{succ u_1, succ u_2, succ u_2} α (OrderDual.{u_2} β) β (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) (fun (a : OrderDual.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β))) (OrderDual.ofDual.{u_2} β)) f) a)
Case conversion may be inaccurate. Consider using '#align with_top.map_of_dual WithTop.map_ofDualₓ'. -/
theorem map_ofDual (f : α → β) (a : WithBot αᵒᵈ) : map f (WithBot.ofDual a) = a.map (of_dual ∘ f) :=
  rfl
#align with_top.map_of_dual WithTop.map_ofDual

/- warning: with_top.to_dual_map -> WithTop.toDual_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β) (a : WithTop.{u_1} α), Eq.{succ u_2} (WithBot.{u_2} (OrderDual.{u_2} β)) (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (WithTop.{u_2} β) (WithBot.{u_2} (OrderDual.{u_2} β))) (fun (_x : Equiv.{succ u_2, succ u_2} (WithTop.{u_2} β) (WithBot.{u_2} (OrderDual.{u_2} β))) => (WithTop.{u_2} β) -> (WithBot.{u_2} (OrderDual.{u_2} β))) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (WithTop.{u_2} β) (WithBot.{u_2} (OrderDual.{u_2} β))) (WithTop.toDual.{u_2} β) (WithTop.map.{u_1, u_2} α β f a)) (WithBot.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) (Function.comp.{succ u_1, succ u_2, succ u_2} (OrderDual.{u_1} α) β (OrderDual.{u_2} β) (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (fun (_x : Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) => β -> (OrderDual.{u_2} β)) (Equiv.hasCoeToFun.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (OrderDual.toDual.{u_2} β)) (Function.comp.{succ u_1, succ u_1, succ u_2} (OrderDual.{u_1} α) α β f (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (fun (_x : Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) => (OrderDual.{u_1} α) -> α) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.ofDual.{u_1} α)))) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) => (WithTop.{u_1} α) -> (WithBot.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.toDual.{u_1} α) a))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β) (a : WithTop.{u_1} α), Eq.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_2} β) => WithBot.{u_2} (OrderDual.{u_2} β)) (WithTop.map.{u_1, u_2} α β f a)) (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (WithTop.{u_2} β) (WithBot.{u_2} (OrderDual.{u_2} β))) (WithTop.{u_2} β) (fun (a : WithTop.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_2} β) => WithBot.{u_2} (OrderDual.{u_2} β)) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (WithTop.{u_2} β) (WithBot.{u_2} (OrderDual.{u_2} β))) (WithTop.{u_2} β) (WithBot.{u_2} (OrderDual.{u_2} β)) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (WithTop.{u_2} β) (WithBot.{u_2} (OrderDual.{u_2} β))) (WithTop.{u_2} β) (WithBot.{u_2} (OrderDual.{u_2} β)) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (WithTop.{u_2} β) (WithBot.{u_2} (OrderDual.{u_2} β))))) (WithTop.toDual.{u_2} β) (WithTop.map.{u_1, u_2} α β f a)) (WithBot.map.{u_1, u_2} (OrderDual.{u_1} α) β (Function.comp.{succ u_1, succ u_2, succ u_2} (OrderDual.{u_1} α) β β (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => OrderDual.{u_2} β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (OrderDual.{u_2} β) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (OrderDual.{u_2} β) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)))) (OrderDual.toDual.{u_2} β)) (Function.comp.{succ u_1, succ u_1, succ u_2} (OrderDual.{u_1} α) α β f (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) (fun (a : OrderDual.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_1} α) => α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) α (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) α (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α))) (OrderDual.ofDual.{u_1} α)))) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (fun (a : WithTop.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))))) (WithTop.toDual.{u_1} α) a))
Case conversion may be inaccurate. Consider using '#align with_top.to_dual_map WithTop.toDual_mapₓ'. -/
theorem toDual_map (f : α → β) (a : WithTop α) :
    WithTop.toDual (map f a) = WithBot.map (to_dual ∘ f ∘ of_dual) a.toDual :=
  rfl
#align with_top.to_dual_map WithTop.toDual_map

/- warning: with_top.of_dual_map -> WithTop.ofDual_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : (OrderDual.{u_1} α) -> (OrderDual.{u_2} β)) (a : WithTop.{u_1} (OrderDual.{u_1} α)), Eq.{succ u_2} (WithBot.{u_2} β) (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (WithTop.{u_2} (OrderDual.{u_2} β)) (WithBot.{u_2} β)) (fun (_x : Equiv.{succ u_2, succ u_2} (WithTop.{u_2} (OrderDual.{u_2} β)) (WithBot.{u_2} β)) => (WithTop.{u_2} (OrderDual.{u_2} β)) -> (WithBot.{u_2} β)) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (WithTop.{u_2} (OrderDual.{u_2} β)) (WithBot.{u_2} β)) (WithTop.ofDual.{u_2} β) (WithTop.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) f a)) (WithBot.map.{u_1, u_2} α β (Function.comp.{succ u_1, succ u_2, succ u_2} α (OrderDual.{u_2} β) β (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (fun (_x : Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) => (OrderDual.{u_2} β) -> β) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.ofDual.{u_2} β)) (Function.comp.{succ u_1, succ u_1, succ u_2} α (OrderDual.{u_1} α) (OrderDual.{u_2} β) f (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) => α -> (OrderDual.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) (OrderDual.toDual.{u_1} α)))) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) => (WithTop.{u_1} (OrderDual.{u_1} α)) -> (WithBot.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.ofDual.{u_1} α) a))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : (OrderDual.{u_1} α) -> (OrderDual.{u_2} β)) (a : WithTop.{u_1} (OrderDual.{u_1} α)), Eq.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_2} (OrderDual.{u_2} β)) => WithBot.{u_2} β) (WithTop.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) f a)) (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (WithTop.{u_2} (OrderDual.{u_2} β)) (WithBot.{u_2} β)) (WithTop.{u_2} (OrderDual.{u_2} β)) (fun (a : WithTop.{u_2} (OrderDual.{u_2} β)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_2} (OrderDual.{u_2} β)) => WithBot.{u_2} β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (WithTop.{u_2} (OrderDual.{u_2} β)) (WithBot.{u_2} β)) (WithTop.{u_2} (OrderDual.{u_2} β)) (WithBot.{u_2} β) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (WithTop.{u_2} (OrderDual.{u_2} β)) (WithBot.{u_2} β)) (WithTop.{u_2} (OrderDual.{u_2} β)) (WithBot.{u_2} β) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (WithTop.{u_2} (OrderDual.{u_2} β)) (WithBot.{u_2} β)))) (WithTop.ofDual.{u_2} β) (WithTop.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) f a)) (WithBot.map.{u_1, u_2} α β (Function.comp.{succ u_1, succ u_2, succ u_2} α (OrderDual.{u_2} β) β (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) (fun (a : OrderDual.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β))) (OrderDual.ofDual.{u_2} β)) (Function.comp.{succ u_1, succ u_1, succ u_2} α (OrderDual.{u_1} α) (OrderDual.{u_2} β) f (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => OrderDual.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (OrderDual.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (OrderDual.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)))) (OrderDual.toDual.{u_1} α)))) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (fun (a : WithTop.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)))) (WithTop.ofDual.{u_1} α) a))
Case conversion may be inaccurate. Consider using '#align with_top.of_dual_map WithTop.ofDual_mapₓ'. -/
theorem ofDual_map (f : αᵒᵈ → βᵒᵈ) (a : WithTop αᵒᵈ) :
    WithTop.ofDual (map f a) = WithBot.map (of_dual ∘ f ∘ to_dual) a.ofDual :=
  rfl
#align with_top.of_dual_map WithTop.ofDual_map

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

instance canLift :
    CanLift (WithTop α) α coe fun r => r ≠ ⊤ where prf x h := ⟨x.untop h, coe_untop _ _⟩
#align with_top.can_lift WithTop.canLift

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

/- warning: with_top.le_to_dual_iff -> WithTop.le_toDual_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] {a : WithBot.{u_1} (OrderDual.{u_1} α)} {b : WithTop.{u_1} α}, Iff (LE.le.{u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithBot.hasLe.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLe.{u_1} α _inst_1)) a (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) => (WithTop.{u_1} α) -> (WithBot.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.toDual.{u_1} α) b)) (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.hasLe.{u_1} α _inst_1) b (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) => (WithBot.{u_1} (OrderDual.{u_1} α)) -> (WithTop.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.ofDual.{u_1} α) a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.6398 : LE.{u_1} α] {a : WithBot.{u_1} (OrderDual.{u_1} α)} {b : WithTop.{u_1} α}, Iff (LE.le.{u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithBot.instLEWithBot.{u_1} (OrderDual.{u_1} α) (OrderDual.instLEOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6398)) a (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (fun (a : WithTop.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))))) (WithTop.toDual.{u_1} α) b)) (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.instLEWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6398) b (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (fun (a : WithBot.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)))) (WithBot.ofDual.{u_1} α) a))
Case conversion may be inaccurate. Consider using '#align with_top.le_to_dual_iff WithTop.le_toDual_iffₓ'. -/
theorem le_toDual_iff {a : WithBot αᵒᵈ} {b : WithTop α} :
    a ≤ WithTop.toDual b ↔ b ≤ WithBot.ofDual a :=
  Iff.rfl
#align with_top.le_to_dual_iff WithTop.le_toDual_iff

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

/- warning: with_top.le_of_dual_iff -> WithTop.le_ofDual_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] {a : WithBot.{u_1} α} {b : WithTop.{u_1} (OrderDual.{u_1} α)}, Iff (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.hasLe.{u_1} α _inst_1) a (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) => (WithTop.{u_1} (OrderDual.{u_1} α)) -> (WithBot.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.ofDual.{u_1} α) b)) (LE.le.{u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithTop.hasLe.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLe.{u_1} α _inst_1)) b (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) => (WithBot.{u_1} α) -> (WithTop.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.toDual.{u_1} α) a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.6497 : LE.{u_1} α] {a : WithBot.{u_1} α} {b : WithTop.{u_1} (OrderDual.{u_1} α)}, Iff (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6497) a (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (fun (a : WithTop.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)))) (WithTop.ofDual.{u_1} α) b)) (LE.le.{u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithTop.instLEWithTop.{u_1} (OrderDual.{u_1} α) (OrderDual.instLEOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6497)) b (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (fun (a : WithBot.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))))) (WithBot.toDual.{u_1} α) a))
Case conversion may be inaccurate. Consider using '#align with_top.le_of_dual_iff WithTop.le_ofDual_iffₓ'. -/
theorem le_ofDual_iff {a : WithBot α} {b : WithTop αᵒᵈ} :
    a ≤ WithTop.ofDual b ↔ b ≤ WithBot.toDual a :=
  Iff.rfl
#align with_top.le_of_dual_iff WithTop.le_ofDual_iff

#print WithTop.ofDual_le_ofDual_iff /-
@[simp]
theorem ofDual_le_ofDual_iff {a b : WithTop αᵒᵈ} : WithTop.ofDual a ≤ WithTop.ofDual b ↔ b ≤ a :=
  Iff.rfl
#align with_top.of_dual_le_of_dual_iff WithTop.ofDual_le_ofDual_iff
-/

/- warning: with_top.coe_le_coe -> WithTop.coe_le_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : LE.{u_1} α], Iff (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.hasLe.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) b)) (LE.le.{u_1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Order.WithBot._hyg.6568 : LE.{u_1} α], Iff (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.instLEWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6568) (WithTop.some.{u_1} α a) (WithTop.some.{u_1} α b)) (LE.le.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6568 a b)
Case conversion may be inaccurate. Consider using '#align with_top.coe_le_coe WithTop.coe_le_coeₓ'. -/
@[simp, norm_cast]
theorem coe_le_coe : (a : WithTop α) ≤ b ↔ a ≤ b := by
  simp only [← to_dual_le_to_dual_iff, to_dual_apply_coe, WithBot.coe_le_coe, to_dual_le_to_dual]
#align with_top.coe_le_coe WithTop.coe_le_coe

/- warning: with_top.some_le_some -> WithTop.some_le_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : LE.{u_1} α], Iff (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.hasLe.{u_1} α _inst_1) (Option.some.{u_1} α a) (Option.some.{u_1} α b)) (LE.le.{u_1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Order.WithBot._hyg.6603 : LE.{u_1} α], Iff (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.instLEWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6603) (Option.some.{u_1} α a) (Option.some.{u_1} α b)) (LE.le.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6603 a b)
Case conversion may be inaccurate. Consider using '#align with_top.some_le_some WithTop.some_le_someₓ'. -/
@[simp]
theorem some_le_some : @LE.le (WithTop α) _ (some a) (some b) ↔ a ≤ b :=
  coe_le_coe
#align with_top.some_le_some WithTop.some_le_some

/- warning: with_top.le_none -> WithTop.le_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] {a : WithTop.{u_1} α}, LE.le.{u_1} (WithTop.{u_1} α) (WithTop.hasLe.{u_1} α _inst_1) a (Option.none.{u_1} α)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.6636 : LE.{u_1} α] {a : WithTop.{u_1} α}, LE.le.{u_1} (WithTop.{u_1} α) (WithTop.instLEWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6636) a (Option.none.{u_1} α)
Case conversion may be inaccurate. Consider using '#align with_top.le_none WithTop.le_noneₓ'. -/
@[simp]
theorem le_none {a : WithTop α} : @LE.le (WithTop α) _ a none :=
  toDual_le_toDual_iff.mp WithBot.none_le
#align with_top.le_none WithTop.le_none

instance : OrderTop (WithTop α) :=
  { WithTop.hasTop with le_top := fun a => le_none }

instance [OrderBot α] : OrderBot
      (WithTop α) where 
  bot := some ⊥
  bot_le o a ha := by cases ha <;> exact ⟨_, rfl, bot_le⟩

instance [OrderBot α] : BoundedOrder (WithTop α) :=
  { WithTop.orderTop, WithTop.orderBot with }

/- warning: with_top.not_top_le_coe -> WithTop.not_top_le_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] (a : α), Not (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.hasLe.{u_1} α _inst_1) (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.hasTop.{u_1} α)) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.6785 : LE.{u_1} α] (a : α), Not (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.instLEWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6785) (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.instTopWithTop.{u_1} α)) (WithTop.some.{u_1} α a))
Case conversion may be inaccurate. Consider using '#align with_top.not_top_le_coe WithTop.not_top_le_coeₓ'. -/
theorem not_top_le_coe (a : α) : ¬(⊤ : WithTop α) ≤ ↑a :=
  WithBot.not_coe_le_bot (toDual a)
#align with_top.not_top_le_coe WithTop.not_top_le_coe

/- warning: with_top.le_coe -> WithTop.le_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : LE.{u_1} α] {o : Option.{u_1} α}, (Membership.Mem.{u_1, u_1} α (Option.{u_1} α) (Option.hasMem.{u_1} α) a o) -> (Iff (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.hasLe.{u_1} α _inst_1) o ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) b)) (LE.le.{u_1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Order.WithBot._hyg.6820 : LE.{u_1} α] {o : Option.{u_1} α}, (Membership.mem.{u_1, u_1} α (Option.{u_1} α) (Option.instMembershipOption.{u_1} α) a o) -> (Iff (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.instLEWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6820) o (WithTop.some.{u_1} α b)) (LE.le.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6820 a b))
Case conversion may be inaccurate. Consider using '#align with_top.le_coe WithTop.le_coeₓ'. -/
theorem le_coe : ∀ {o : Option α}, a ∈ o → (@LE.le (WithTop α) _ o b ↔ a ≤ b)
  | _, rfl => coe_le_coe
#align with_top.le_coe WithTop.le_coe

/- warning: with_top.le_coe_iff -> WithTop.le_coe_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {b : α} [_inst_1 : LE.{u_1} α] {x : WithTop.{u_1} α}, Iff (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.hasLe.{u_1} α _inst_1) x ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) b)) (Exists.{succ u_1} α (fun (a : α) => And (Eq.{succ u_1} (WithTop.{u_1} α) x ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a)) (LE.le.{u_1} α _inst_1 a b)))
but is expected to have type
  forall {α : Type.{u_1}} {b : α} [inst._@.Mathlib.Order.WithBot._hyg.6894 : LE.{u_1} α] {x : WithTop.{u_1} α}, Iff (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.instLEWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6894) x (WithTop.some.{u_1} α b)) (Exists.{succ u_1} α (fun (a : α) => And (Eq.{succ u_1} (WithTop.{u_1} α) x (WithTop.some.{u_1} α a)) (LE.le.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6894 a b)))
Case conversion may be inaccurate. Consider using '#align with_top.le_coe_iff WithTop.le_coe_iffₓ'. -/
theorem le_coe_iff {x : WithTop α} : x ≤ b ↔ ∃ a : α, x = a ∧ a ≤ b := by
  simpa [← to_dual_le_to_dual_iff, WithBot.coe_le_iff]
#align with_top.le_coe_iff WithTop.le_coe_iff

/- warning: with_top.coe_le_iff -> WithTop.coe_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} [_inst_1 : LE.{u_1} α] {x : WithTop.{u_1} α}, Iff (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.hasLe.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a) x) (forall (b : α), (Eq.{succ u_1} (WithTop.{u_1} α) x ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) b)) -> (LE.le.{u_1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} [inst._@.Mathlib.Order.WithBot._hyg.6948 : LE.{u_1} α] {x : WithTop.{u_1} α}, Iff (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.instLEWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6948) (WithTop.some.{u_1} α a) x) (forall (b : WithTop.{u_1} α), (Eq.{succ u_1} (WithTop.{u_1} α) x b) -> (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.instLEWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.6948) (WithTop.some.{u_1} α a) b))
Case conversion may be inaccurate. Consider using '#align with_top.coe_le_iff WithTop.coe_le_iffₓ'. -/
theorem coe_le_iff {x : WithTop α} : ↑a ≤ x ↔ ∀ b, x = ↑b → a ≤ b := by
  simp only [← to_dual_le_to_dual_iff, to_dual_apply_coe, WithBot.le_coe_iff, OrderDual.forall,
    to_dual_le_to_dual]
  exact forall₂_congr fun _ _ => Iff.rfl
#align with_top.coe_le_iff WithTop.coe_le_iff

/- warning: is_min.with_top -> IsMin.withTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} [_inst_1 : LE.{u_1} α], (IsMin.{u_1} α _inst_1 a) -> (IsMin.{u_1} (WithTop.{u_1} α) (WithTop.hasLe.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} [inst._@.Mathlib.Order.WithBot._hyg.7002 : LE.{u_1} α], (IsMin.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7002 a) -> (IsMin.{u_1} (WithTop.{u_1} α) (WithTop.instLEWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7002) (WithTop.some.{u_1} α a))
Case conversion may be inaccurate. Consider using '#align is_min.with_top IsMin.withTopₓ'. -/
protected theorem IsMin.withTop (h : IsMin a) : IsMin (a : WithTop α) :=
  by
  -- defeq to is_max_to_dual_iff.mp (is_max.with_bot _), but that breaks API boundary
  intro _ hb
  rw [← to_dual_le_to_dual_iff] at hb
  simpa [to_dual_le_iff] using (IsMax.withBot h : IsMax (to_dual a : WithBot αᵒᵈ)) hb
#align is_min.with_top IsMin.withTop

end LE

section LT

variable [LT α]

instance (priority := 10) : LT (WithTop α) :=
  ⟨fun o₁ o₂ : Option α => ∃ b ∈ o₁, ∀ a ∈ o₂, b < a⟩

/- warning: with_top.to_dual_lt_iff -> WithTop.toDual_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithTop.{u_1} α} {b : WithBot.{u_1} (OrderDual.{u_1} α)}, Iff (LT.lt.{u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithBot.hasLt.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLt.{u_1} α _inst_1)) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) => (WithTop.{u_1} α) -> (WithBot.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.toDual.{u_1} α) a) b) (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) => (WithBot.{u_1} (OrderDual.{u_1} α)) -> (WithTop.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.ofDual.{u_1} α) b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.7174 : LT.{u_1} α] {a : WithTop.{u_1} α} {b : WithBot.{u_1} (OrderDual.{u_1} α)}, Iff (LT.lt.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) a) (WithBot.instLTWithBot.{u_1} (OrderDual.{u_1} α) (OrderDual.instLTOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7174)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (fun (a : WithTop.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))))) (WithTop.toDual.{u_1} α) a) b) (LT.lt.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) b) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7174) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (fun (a : WithBot.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)))) (WithBot.ofDual.{u_1} α) b) a)
Case conversion may be inaccurate. Consider using '#align with_top.to_dual_lt_iff WithTop.toDual_lt_iffₓ'. -/
theorem toDual_lt_iff {a : WithTop α} {b : WithBot αᵒᵈ} :
    WithTop.toDual a < b ↔ WithBot.ofDual b < a :=
  Iff.rfl
#align with_top.to_dual_lt_iff WithTop.toDual_lt_iff

/- warning: with_top.lt_to_dual_iff -> WithTop.lt_toDual_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithBot.{u_1} (OrderDual.{u_1} α)} {b : WithTop.{u_1} α}, Iff (LT.lt.{u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithBot.hasLt.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLt.{u_1} α _inst_1)) a (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) => (WithTop.{u_1} α) -> (WithBot.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.toDual.{u_1} α) b)) (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) b (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) => (WithBot.{u_1} (OrderDual.{u_1} α)) -> (WithTop.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.ofDual.{u_1} α) a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.7208 : LT.{u_1} α] {a : WithBot.{u_1} (OrderDual.{u_1} α)} {b : WithTop.{u_1} α}, Iff (LT.lt.{u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithBot.instLTWithBot.{u_1} (OrderDual.{u_1} α) (OrderDual.instLTOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7208)) a (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (fun (a : WithTop.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))))) (WithTop.toDual.{u_1} α) b)) (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7208) b (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (fun (a : WithBot.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)))) (WithBot.ofDual.{u_1} α) a))
Case conversion may be inaccurate. Consider using '#align with_top.lt_to_dual_iff WithTop.lt_toDual_iffₓ'. -/
theorem lt_toDual_iff {a : WithBot αᵒᵈ} {b : WithTop α} :
    a < WithTop.toDual b ↔ b < WithBot.ofDual a :=
  Iff.rfl
#align with_top.lt_to_dual_iff WithTop.lt_toDual_iff

/- warning: with_top.to_dual_lt_to_dual_iff -> WithTop.toDual_lt_toDual_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithTop.{u_1} α} {b : WithTop.{u_1} α}, Iff (LT.lt.{u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithBot.hasLt.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLt.{u_1} α _inst_1)) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) => (WithTop.{u_1} α) -> (WithBot.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.toDual.{u_1} α) a) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) => (WithTop.{u_1} α) -> (WithBot.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.toDual.{u_1} α) b)) (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) b a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.7242 : LT.{u_1} α] {a : WithTop.{u_1} α} {b : WithTop.{u_1} α}, Iff (LT.lt.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) a) (WithBot.instLTWithBot.{u_1} (OrderDual.{u_1} α) (OrderDual.instLTOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7242)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (fun (a : WithTop.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))))) (WithTop.toDual.{u_1} α) a) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (fun (a : WithTop.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))))) (WithTop.toDual.{u_1} α) b)) (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7242) b a)
Case conversion may be inaccurate. Consider using '#align with_top.to_dual_lt_to_dual_iff WithTop.toDual_lt_toDual_iffₓ'. -/
@[simp]
theorem toDual_lt_toDual_iff {a b : WithTop α} : WithTop.toDual a < WithTop.toDual b ↔ b < a :=
  Iff.rfl
#align with_top.to_dual_lt_to_dual_iff WithTop.toDual_lt_toDual_iff

/- warning: with_top.of_dual_lt_iff -> WithTop.ofDual_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithTop.{u_1} (OrderDual.{u_1} α)} {b : WithBot.{u_1} α}, Iff (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) => (WithTop.{u_1} (OrderDual.{u_1} α)) -> (WithBot.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.ofDual.{u_1} α) a) b) (LT.lt.{u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithTop.hasLt.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLt.{u_1} α _inst_1)) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) => (WithBot.{u_1} α) -> (WithTop.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.toDual.{u_1} α) b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.7273 : LT.{u_1} α] {a : WithTop.{u_1} (OrderDual.{u_1} α)} {b : WithBot.{u_1} α}, Iff (LT.lt.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) a) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7273) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (fun (a : WithTop.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)))) (WithTop.ofDual.{u_1} α) a) b) (LT.lt.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) b) (WithTop.instLTWithTop.{u_1} (OrderDual.{u_1} α) (OrderDual.instLTOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7273)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (fun (a : WithBot.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))))) (WithBot.toDual.{u_1} α) b) a)
Case conversion may be inaccurate. Consider using '#align with_top.of_dual_lt_iff WithTop.ofDual_lt_iffₓ'. -/
theorem ofDual_lt_iff {a : WithTop αᵒᵈ} {b : WithBot α} :
    WithTop.ofDual a < b ↔ WithBot.toDual b < a :=
  Iff.rfl
#align with_top.of_dual_lt_iff WithTop.ofDual_lt_iff

/- warning: with_top.lt_of_dual_iff -> WithTop.lt_ofDual_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithBot.{u_1} α} {b : WithTop.{u_1} (OrderDual.{u_1} α)}, Iff (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) a (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) => (WithTop.{u_1} (OrderDual.{u_1} α)) -> (WithBot.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.ofDual.{u_1} α) b)) (LT.lt.{u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithTop.hasLt.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLt.{u_1} α _inst_1)) b (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) => (WithBot.{u_1} α) -> (WithTop.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.toDual.{u_1} α) a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.7307 : LT.{u_1} α] {a : WithBot.{u_1} α} {b : WithTop.{u_1} (OrderDual.{u_1} α)}, Iff (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7307) a (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (fun (a : WithTop.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)))) (WithTop.ofDual.{u_1} α) b)) (LT.lt.{u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithTop.instLTWithTop.{u_1} (OrderDual.{u_1} α) (OrderDual.instLTOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7307)) b (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (fun (a : WithBot.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))))) (WithBot.toDual.{u_1} α) a))
Case conversion may be inaccurate. Consider using '#align with_top.lt_of_dual_iff WithTop.lt_ofDual_iffₓ'. -/
theorem lt_ofDual_iff {a : WithBot α} {b : WithTop αᵒᵈ} :
    a < WithTop.ofDual b ↔ b < WithBot.toDual a :=
  Iff.rfl
#align with_top.lt_of_dual_iff WithTop.lt_ofDual_iff

/- warning: with_top.of_dual_lt_of_dual_iff -> WithTop.ofDual_lt_ofDual_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithTop.{u_1} (OrderDual.{u_1} α)} {b : WithTop.{u_1} (OrderDual.{u_1} α)}, Iff (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) => (WithTop.{u_1} (OrderDual.{u_1} α)) -> (WithBot.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.ofDual.{u_1} α) a) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) => (WithTop.{u_1} (OrderDual.{u_1} α)) -> (WithBot.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.ofDual.{u_1} α) b)) (LT.lt.{u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithTop.hasLt.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLt.{u_1} α _inst_1)) b a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.7341 : LT.{u_1} α] {a : WithTop.{u_1} (OrderDual.{u_1} α)} {b : WithTop.{u_1} (OrderDual.{u_1} α)}, Iff (LT.lt.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) a) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7341) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (fun (a : WithTop.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)))) (WithTop.ofDual.{u_1} α) a) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (fun (a : WithTop.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)))) (WithTop.ofDual.{u_1} α) b)) (LT.lt.{u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithTop.instLTWithTop.{u_1} (OrderDual.{u_1} α) (OrderDual.instLTOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7341)) b a)
Case conversion may be inaccurate. Consider using '#align with_top.of_dual_lt_of_dual_iff WithTop.ofDual_lt_ofDual_iffₓ'. -/
@[simp]
theorem ofDual_lt_ofDual_iff {a b : WithTop αᵒᵈ} : WithTop.ofDual a < WithTop.ofDual b ↔ b < a :=
  Iff.rfl
#align with_top.of_dual_lt_of_dual_iff WithTop.ofDual_lt_ofDual_iff

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

/- warning: with_bot.map_to_dual -> WithBot.map_toDual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : (OrderDual.{u_1} α) -> (OrderDual.{u_2} β)) (a : WithTop.{u_1} α), Eq.{succ u_2} (WithBot.{u_2} (OrderDual.{u_2} β)) (WithBot.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) f (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) => (WithTop.{u_1} α) -> (WithBot.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.toDual.{u_1} α) a)) (WithTop.map.{u_1, u_2} α (OrderDual.{u_2} β) (Function.comp.{succ u_1, succ u_2, succ u_2} α β (OrderDual.{u_2} β) (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (fun (_x : Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) => β -> (OrderDual.{u_2} β)) (Equiv.hasCoeToFun.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (OrderDual.toDual.{u_2} β)) f) a)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : (OrderDual.{u_1} α) -> (OrderDual.{u_2} β)) (a : WithTop.{u_1} α), Eq.{succ u_2} (WithBot.{u_2} (OrderDual.{u_2} β)) (WithBot.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) f (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (fun (a : WithTop.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))))) (WithTop.toDual.{u_1} α) a)) (WithTop.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) (Function.comp.{succ u_1, succ u_2, succ u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) (OrderDual.{u_2} β) (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) (OrderDual.{u_2} (OrderDual.{u_2} β))) (OrderDual.{u_2} β) (fun (a : OrderDual.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => OrderDual.{u_2} (OrderDual.{u_2} β)) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) (OrderDual.{u_2} (OrderDual.{u_2} β))) (OrderDual.{u_2} β) (OrderDual.{u_2} (OrderDual.{u_2} β)) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) (OrderDual.{u_2} (OrderDual.{u_2} β))) (OrderDual.{u_2} β) (OrderDual.{u_2} (OrderDual.{u_2} β)) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) (OrderDual.{u_2} (OrderDual.{u_2} β))))) (OrderDual.toDual.{u_2} (OrderDual.{u_2} β))) f) a)
Case conversion may be inaccurate. Consider using '#align with_bot.map_to_dual WithBot.map_toDualₓ'. -/
theorem map_toDual (f : αᵒᵈ → βᵒᵈ) (a : WithTop α) :
    WithBot.map f (WithTop.toDual a) = a.map (to_dual ∘ f) :=
  rfl
#align with_bot.map_to_dual WithBot.map_toDual

/- warning: with_bot.map_of_dual -> WithBot.map_ofDual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β) (a : WithTop.{u_1} (OrderDual.{u_1} α)), Eq.{succ u_2} (WithBot.{u_2} β) (WithBot.map.{u_1, u_2} α β f (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) => (WithTop.{u_1} (OrderDual.{u_1} α)) -> (WithBot.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.ofDual.{u_1} α) a)) (WithTop.map.{u_1, u_2} (OrderDual.{u_1} α) β (Function.comp.{succ u_1, succ u_2, succ u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) β (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (fun (_x : Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) => (OrderDual.{u_2} β) -> β) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.ofDual.{u_2} β)) f) a)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β) (a : WithTop.{u_1} (OrderDual.{u_1} α)), Eq.{succ u_2} (WithBot.{u_2} β) (WithBot.map.{u_1, u_2} α β f (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (fun (a : WithTop.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)))) (WithTop.ofDual.{u_1} α) a)) (WithTop.map.{u_1, u_2} α β (Function.comp.{succ u_1, succ u_2, succ u_2} α (OrderDual.{u_2} β) β (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) (fun (a : OrderDual.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β))) (OrderDual.ofDual.{u_2} β)) f) a)
Case conversion may be inaccurate. Consider using '#align with_bot.map_of_dual WithBot.map_ofDualₓ'. -/
theorem map_ofDual (f : α → β) (a : WithTop αᵒᵈ) :
    WithBot.map f (WithTop.ofDual a) = a.map (of_dual ∘ f) :=
  rfl
#align with_bot.map_of_dual WithBot.map_ofDual

/- warning: with_bot.to_dual_map -> WithBot.toDual_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β) (a : WithBot.{u_1} α), Eq.{succ u_2} (WithTop.{u_2} (OrderDual.{u_2} β)) (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (WithBot.{u_2} β) (WithTop.{u_2} (OrderDual.{u_2} β))) (fun (_x : Equiv.{succ u_2, succ u_2} (WithBot.{u_2} β) (WithTop.{u_2} (OrderDual.{u_2} β))) => (WithBot.{u_2} β) -> (WithTop.{u_2} (OrderDual.{u_2} β))) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (WithBot.{u_2} β) (WithTop.{u_2} (OrderDual.{u_2} β))) (WithBot.toDual.{u_2} β) (WithBot.map.{u_1, u_2} α β f a)) (WithBot.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) (Function.comp.{succ u_1, succ u_2, succ u_2} (OrderDual.{u_1} α) β (OrderDual.{u_2} β) (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (fun (_x : Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) => β -> (OrderDual.{u_2} β)) (Equiv.hasCoeToFun.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (OrderDual.toDual.{u_2} β)) (Function.comp.{succ u_1, succ u_1, succ u_2} (OrderDual.{u_1} α) α β f (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (fun (_x : Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) => (OrderDual.{u_1} α) -> α) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.ofDual.{u_1} α)))) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) => (WithBot.{u_1} α) -> (WithTop.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.toDual.{u_1} α) a))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : α -> β) (a : WithBot.{u_1} α), Eq.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_2} β) => WithTop.{u_2} (OrderDual.{u_2} β)) (WithBot.map.{u_1, u_2} α β f a)) (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (WithBot.{u_2} β) (WithTop.{u_2} (OrderDual.{u_2} β))) (WithBot.{u_2} β) (fun (a : WithBot.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_2} β) => WithTop.{u_2} (OrderDual.{u_2} β)) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (WithBot.{u_2} β) (WithTop.{u_2} (OrderDual.{u_2} β))) (WithBot.{u_2} β) (WithTop.{u_2} (OrderDual.{u_2} β)) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (WithBot.{u_2} β) (WithTop.{u_2} (OrderDual.{u_2} β))) (WithBot.{u_2} β) (WithTop.{u_2} (OrderDual.{u_2} β)) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (WithBot.{u_2} β) (WithTop.{u_2} (OrderDual.{u_2} β))))) (WithBot.toDual.{u_2} β) (WithBot.map.{u_1, u_2} α β f a)) (WithBot.map.{u_1, u_2} (OrderDual.{u_1} α) β (Function.comp.{succ u_1, succ u_2, succ u_2} (OrderDual.{u_1} α) β β (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => OrderDual.{u_2} β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (OrderDual.{u_2} β) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (OrderDual.{u_2} β) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)))) (OrderDual.toDual.{u_2} β)) (Function.comp.{succ u_1, succ u_1, succ u_2} (OrderDual.{u_1} α) α β f (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) (fun (a : OrderDual.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_1} α) => α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) α (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) α (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α))) (OrderDual.ofDual.{u_1} α)))) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (fun (a : WithBot.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))))) (WithBot.toDual.{u_1} α) a))
Case conversion may be inaccurate. Consider using '#align with_bot.to_dual_map WithBot.toDual_mapₓ'. -/
theorem toDual_map (f : α → β) (a : WithBot α) :
    WithBot.toDual (WithBot.map f a) = map (to_dual ∘ f ∘ of_dual) a.toDual :=
  rfl
#align with_bot.to_dual_map WithBot.toDual_map

/- warning: with_bot.of_dual_map -> WithBot.ofDual_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : (OrderDual.{u_1} α) -> (OrderDual.{u_2} β)) (a : WithBot.{u_1} (OrderDual.{u_1} α)), Eq.{succ u_2} (WithTop.{u_2} β) (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (WithBot.{u_2} (OrderDual.{u_2} β)) (WithTop.{u_2} β)) (fun (_x : Equiv.{succ u_2, succ u_2} (WithBot.{u_2} (OrderDual.{u_2} β)) (WithTop.{u_2} β)) => (WithBot.{u_2} (OrderDual.{u_2} β)) -> (WithTop.{u_2} β)) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (WithBot.{u_2} (OrderDual.{u_2} β)) (WithTop.{u_2} β)) (WithBot.ofDual.{u_2} β) (WithBot.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) f a)) (WithBot.map.{u_1, u_2} α β (Function.comp.{succ u_1, succ u_2, succ u_2} α (OrderDual.{u_2} β) β (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (fun (_x : Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) => (OrderDual.{u_2} β) -> β) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.ofDual.{u_2} β)) (Function.comp.{succ u_1, succ u_1, succ u_2} α (OrderDual.{u_1} α) (OrderDual.{u_2} β) f (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) => α -> (OrderDual.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) (OrderDual.toDual.{u_1} α)))) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) => (WithBot.{u_1} (OrderDual.{u_1} α)) -> (WithTop.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.ofDual.{u_1} α) a))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (f : (OrderDual.{u_1} α) -> (OrderDual.{u_2} β)) (a : WithBot.{u_1} (OrderDual.{u_1} α)), Eq.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_2} (OrderDual.{u_2} β)) => WithTop.{u_2} β) (WithBot.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) f a)) (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (WithBot.{u_2} (OrderDual.{u_2} β)) (WithTop.{u_2} β)) (WithBot.{u_2} (OrderDual.{u_2} β)) (fun (a : WithBot.{u_2} (OrderDual.{u_2} β)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_2} (OrderDual.{u_2} β)) => WithTop.{u_2} β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (WithBot.{u_2} (OrderDual.{u_2} β)) (WithTop.{u_2} β)) (WithBot.{u_2} (OrderDual.{u_2} β)) (WithTop.{u_2} β) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (WithBot.{u_2} (OrderDual.{u_2} β)) (WithTop.{u_2} β)) (WithBot.{u_2} (OrderDual.{u_2} β)) (WithTop.{u_2} β) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (WithBot.{u_2} (OrderDual.{u_2} β)) (WithTop.{u_2} β)))) (WithBot.ofDual.{u_2} β) (WithBot.map.{u_1, u_2} (OrderDual.{u_1} α) (OrderDual.{u_2} β) f a)) (WithBot.map.{u_1, u_2} α β (Function.comp.{succ u_1, succ u_2, succ u_2} α (OrderDual.{u_2} β) β (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) (fun (a : OrderDual.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β))) (OrderDual.ofDual.{u_2} β)) (Function.comp.{succ u_1, succ u_1, succ u_2} α (OrderDual.{u_1} α) (OrderDual.{u_2} β) f (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => OrderDual.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (OrderDual.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (OrderDual.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)))) (OrderDual.toDual.{u_1} α)))) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (fun (a : WithBot.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)))) (WithBot.ofDual.{u_1} α) a))
Case conversion may be inaccurate. Consider using '#align with_bot.of_dual_map WithBot.ofDual_mapₓ'. -/
theorem ofDual_map (f : αᵒᵈ → βᵒᵈ) (a : WithBot αᵒᵈ) :
    WithBot.ofDual (WithBot.map f a) = map (of_dual ∘ f ∘ to_dual) a.ofDual :=
  rfl
#align with_bot.of_dual_map WithBot.ofDual_map

section LE

variable [LE α] {a b : α}

/- warning: with_bot.to_dual_le_iff -> WithBot.toDual_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] {a : WithBot.{u_1} α} {b : WithTop.{u_1} (OrderDual.{u_1} α)}, Iff (LE.le.{u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithTop.hasLe.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLe.{u_1} α _inst_1)) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) => (WithBot.{u_1} α) -> (WithTop.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.toDual.{u_1} α) a) b) (LE.le.{u_1} (WithBot.{u_1} α) (WithBot.hasLe.{u_1} α _inst_1) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) => (WithTop.{u_1} (OrderDual.{u_1} α)) -> (WithBot.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.ofDual.{u_1} α) b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.7667 : LE.{u_1} α] {a : WithBot.{u_1} α} {b : WithTop.{u_1} (OrderDual.{u_1} α)}, Iff (LE.le.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) a) (WithTop.instLEWithTop.{u_1} (OrderDual.{u_1} α) (OrderDual.instLEOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7667)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (fun (a : WithBot.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))))) (WithBot.toDual.{u_1} α) a) b) (LE.le.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) b) (WithBot.instLEWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7667) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (fun (a : WithTop.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)))) (WithTop.ofDual.{u_1} α) b) a)
Case conversion may be inaccurate. Consider using '#align with_bot.to_dual_le_iff WithBot.toDual_le_iffₓ'. -/
theorem toDual_le_iff {a : WithBot α} {b : WithTop αᵒᵈ} :
    WithBot.toDual a ≤ b ↔ WithTop.ofDual b ≤ a :=
  Iff.rfl
#align with_bot.to_dual_le_iff WithBot.toDual_le_iff

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

/- warning: with_bot.of_dual_le_iff -> WithBot.ofDual_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] {a : WithBot.{u_1} (OrderDual.{u_1} α)} {b : WithTop.{u_1} α}, Iff (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.hasLe.{u_1} α _inst_1) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) => (WithBot.{u_1} (OrderDual.{u_1} α)) -> (WithTop.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.ofDual.{u_1} α) a) b) (LE.le.{u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithBot.hasLe.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLe.{u_1} α _inst_1)) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) => (WithTop.{u_1} α) -> (WithBot.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.toDual.{u_1} α) b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.7766 : LE.{u_1} α] {a : WithBot.{u_1} (OrderDual.{u_1} α)} {b : WithTop.{u_1} α}, Iff (LE.le.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) a) (WithTop.instLEWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7766) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (fun (a : WithBot.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)))) (WithBot.ofDual.{u_1} α) a) b) (LE.le.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) b) (WithBot.instLEWithBot.{u_1} (OrderDual.{u_1} α) (OrderDual.instLEOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7766)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (fun (a : WithTop.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))))) (WithTop.toDual.{u_1} α) b) a)
Case conversion may be inaccurate. Consider using '#align with_bot.of_dual_le_iff WithBot.ofDual_le_iffₓ'. -/
theorem ofDual_le_iff {a : WithBot αᵒᵈ} {b : WithTop α} :
    WithBot.ofDual a ≤ b ↔ WithTop.toDual b ≤ a :=
  Iff.rfl
#align with_bot.of_dual_le_iff WithBot.ofDual_le_iff

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

/- warning: with_bot.to_dual_lt_iff -> WithBot.toDual_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithBot.{u_1} α} {b : WithTop.{u_1} (OrderDual.{u_1} α)}, Iff (LT.lt.{u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithTop.hasLt.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLt.{u_1} α _inst_1)) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) => (WithBot.{u_1} α) -> (WithTop.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.toDual.{u_1} α) a) b) (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) => (WithTop.{u_1} (OrderDual.{u_1} α)) -> (WithBot.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.ofDual.{u_1} α) b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.7886 : LT.{u_1} α] {a : WithBot.{u_1} α} {b : WithTop.{u_1} (OrderDual.{u_1} α)}, Iff (LT.lt.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) a) (WithTop.instLTWithTop.{u_1} (OrderDual.{u_1} α) (OrderDual.instLTOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7886)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (fun (a : WithBot.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))))) (WithBot.toDual.{u_1} α) a) b) (LT.lt.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) b) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7886) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (fun (a : WithTop.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)))) (WithTop.ofDual.{u_1} α) b) a)
Case conversion may be inaccurate. Consider using '#align with_bot.to_dual_lt_iff WithBot.toDual_lt_iffₓ'. -/
theorem toDual_lt_iff {a : WithBot α} {b : WithTop αᵒᵈ} :
    WithBot.toDual a < b ↔ WithTop.ofDual b < a :=
  Iff.rfl
#align with_bot.to_dual_lt_iff WithBot.toDual_lt_iff

/- warning: with_bot.lt_to_dual_iff -> WithBot.lt_toDual_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithTop.{u_1} (OrderDual.{u_1} α)} {b : WithBot.{u_1} α}, Iff (LT.lt.{u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithTop.hasLt.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLt.{u_1} α _inst_1)) a (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) => (WithBot.{u_1} α) -> (WithTop.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.toDual.{u_1} α) b)) (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) b (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) => (WithTop.{u_1} (OrderDual.{u_1} α)) -> (WithBot.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.ofDual.{u_1} α) a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.7920 : LT.{u_1} α] {a : WithTop.{u_1} (OrderDual.{u_1} α)} {b : WithBot.{u_1} α}, Iff (LT.lt.{u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithTop.instLTWithTop.{u_1} (OrderDual.{u_1} α) (OrderDual.instLTOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7920)) a (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (fun (a : WithBot.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))))) (WithBot.toDual.{u_1} α) b)) (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7920) b (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (fun (a : WithTop.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} (OrderDual.{u_1} α)) => WithBot.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)) (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithBot.{u_1} α)))) (WithTop.ofDual.{u_1} α) a))
Case conversion may be inaccurate. Consider using '#align with_bot.lt_to_dual_iff WithBot.lt_toDual_iffₓ'. -/
theorem lt_toDual_iff {a : WithTop αᵒᵈ} {b : WithBot α} :
    a < WithBot.toDual b ↔ b < WithTop.ofDual a :=
  Iff.rfl
#align with_bot.lt_to_dual_iff WithBot.lt_toDual_iff

/- warning: with_bot.to_dual_lt_to_dual_iff -> WithBot.toDual_lt_toDual_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithBot.{u_1} α} {b : WithBot.{u_1} α}, Iff (LT.lt.{u_1} (WithTop.{u_1} (OrderDual.{u_1} α)) (WithTop.hasLt.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLt.{u_1} α _inst_1)) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) => (WithBot.{u_1} α) -> (WithTop.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.toDual.{u_1} α) a) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) => (WithBot.{u_1} α) -> (WithTop.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.toDual.{u_1} α) b)) (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.hasLt.{u_1} α _inst_1) b a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.7954 : LT.{u_1} α] {a : WithBot.{u_1} α} {b : WithBot.{u_1} α}, Iff (LT.lt.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) a) (WithTop.instLTWithTop.{u_1} (OrderDual.{u_1} α) (OrderDual.instLTOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7954)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (fun (a : WithBot.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))))) (WithBot.toDual.{u_1} α) a) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (fun (a : WithBot.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} α) => WithTop.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))) (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} α) (WithTop.{u_1} (OrderDual.{u_1} α))))) (WithBot.toDual.{u_1} α) b)) (LT.lt.{u_1} (WithBot.{u_1} α) (WithBot.instLTWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7954) b a)
Case conversion may be inaccurate. Consider using '#align with_bot.to_dual_lt_to_dual_iff WithBot.toDual_lt_toDual_iffₓ'. -/
@[simp]
theorem toDual_lt_toDual_iff {a b : WithBot α} : WithBot.toDual a < WithBot.toDual b ↔ b < a :=
  Iff.rfl
#align with_bot.to_dual_lt_to_dual_iff WithBot.toDual_lt_toDual_iff

/- warning: with_bot.of_dual_lt_iff -> WithBot.ofDual_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithBot.{u_1} (OrderDual.{u_1} α)} {b : WithTop.{u_1} α}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) => (WithBot.{u_1} (OrderDual.{u_1} α)) -> (WithTop.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.ofDual.{u_1} α) a) b) (LT.lt.{u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithBot.hasLt.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLt.{u_1} α _inst_1)) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) => (WithTop.{u_1} α) -> (WithBot.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.toDual.{u_1} α) b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.7985 : LT.{u_1} α] {a : WithBot.{u_1} (OrderDual.{u_1} α)} {b : WithTop.{u_1} α}, Iff (LT.lt.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) a) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7985) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (fun (a : WithBot.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)))) (WithBot.ofDual.{u_1} α) a) b) (LT.lt.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) b) (WithBot.instLTWithBot.{u_1} (OrderDual.{u_1} α) (OrderDual.instLTOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.7985)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (fun (a : WithTop.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))))) (WithTop.toDual.{u_1} α) b) a)
Case conversion may be inaccurate. Consider using '#align with_bot.of_dual_lt_iff WithBot.ofDual_lt_iffₓ'. -/
theorem ofDual_lt_iff {a : WithBot αᵒᵈ} {b : WithTop α} :
    WithBot.ofDual a < b ↔ WithTop.toDual b < a :=
  Iff.rfl
#align with_bot.of_dual_lt_iff WithBot.ofDual_lt_iff

/- warning: with_bot.lt_of_dual_iff -> WithBot.lt_ofDual_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithTop.{u_1} α} {b : WithBot.{u_1} (OrderDual.{u_1} α)}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) a (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) => (WithBot.{u_1} (OrderDual.{u_1} α)) -> (WithTop.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.ofDual.{u_1} α) b)) (LT.lt.{u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithBot.hasLt.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLt.{u_1} α _inst_1)) b (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (fun (_x : Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) => (WithTop.{u_1} α) -> (WithBot.{u_1} (OrderDual.{u_1} α))) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.toDual.{u_1} α) a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.8019 : LT.{u_1} α] {a : WithTop.{u_1} α} {b : WithBot.{u_1} (OrderDual.{u_1} α)}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8019) a (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (fun (a : WithBot.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)))) (WithBot.ofDual.{u_1} α) b)) (LT.lt.{u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithBot.instLTWithBot.{u_1} (OrderDual.{u_1} α) (OrderDual.instLTOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8019)) b (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (fun (a : WithTop.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithTop.{u_1} α) => WithBot.{u_1} (OrderDual.{u_1} α)) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))) (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α)) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithTop.{u_1} α) (WithBot.{u_1} (OrderDual.{u_1} α))))) (WithTop.toDual.{u_1} α) a))
Case conversion may be inaccurate. Consider using '#align with_bot.lt_of_dual_iff WithBot.lt_ofDual_iffₓ'. -/
theorem lt_ofDual_iff {a : WithTop α} {b : WithBot αᵒᵈ} :
    a < WithBot.ofDual b ↔ b < WithTop.toDual a :=
  Iff.rfl
#align with_bot.lt_of_dual_iff WithBot.lt_ofDual_iff

/- warning: with_bot.of_dual_lt_of_dual_iff -> WithBot.ofDual_lt_ofDual_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithBot.{u_1} (OrderDual.{u_1} α)} {b : WithBot.{u_1} (OrderDual.{u_1} α)}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) => (WithBot.{u_1} (OrderDual.{u_1} α)) -> (WithTop.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.ofDual.{u_1} α) a) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) => (WithBot.{u_1} (OrderDual.{u_1} α)) -> (WithTop.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.ofDual.{u_1} α) b)) (LT.lt.{u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithBot.hasLt.{u_1} (OrderDual.{u_1} α) (OrderDual.hasLt.{u_1} α _inst_1)) b a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.8053 : LT.{u_1} α] {a : WithBot.{u_1} (OrderDual.{u_1} α)} {b : WithBot.{u_1} (OrderDual.{u_1} α)}, Iff (LT.lt.{u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) a) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8053) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (fun (a : WithBot.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)))) (WithBot.ofDual.{u_1} α) a) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (fun (a : WithBot.{u_1} (OrderDual.{u_1} α)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : WithBot.{u_1} (OrderDual.{u_1} α)) => WithTop.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)) (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithTop.{u_1} α)))) (WithBot.ofDual.{u_1} α) b)) (LT.lt.{u_1} (WithBot.{u_1} (OrderDual.{u_1} α)) (WithBot.instLTWithBot.{u_1} (OrderDual.{u_1} α) (OrderDual.instLTOrderDual.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8053)) b a)
Case conversion may be inaccurate. Consider using '#align with_bot.of_dual_lt_of_dual_iff WithBot.ofDual_lt_ofDual_iffₓ'. -/
@[simp]
theorem ofDual_lt_ofDual_iff {a b : WithBot αᵒᵈ} : WithBot.ofDual a < WithBot.ofDual b ↔ b < a :=
  Iff.rfl
#align with_bot.of_dual_lt_of_dual_iff WithBot.ofDual_lt_ofDual_iff

end LT

end WithBot

namespace WithTop

section LT

variable [LT α] {a b : α}

open OrderDual

/- warning: with_top.coe_lt_coe -> WithTop.coe_lt_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : α} {b : α}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) b)) (LT.lt.{u_1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.8108 : LT.{u_1} α] {a : α} {b : α}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8108) (WithTop.some.{u_1} α a) (WithTop.some.{u_1} α b)) (LT.lt.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8108 a b)
Case conversion may be inaccurate. Consider using '#align with_top.coe_lt_coe WithTop.coe_lt_coeₓ'. -/
@[simp, norm_cast]
theorem coe_lt_coe : (a : WithTop α) < b ↔ a < b := by
  simp only [← to_dual_lt_to_dual_iff, to_dual_apply_coe, WithBot.coe_lt_coe, to_dual_lt_to_dual]
#align with_top.coe_lt_coe WithTop.coe_lt_coe

/- warning: with_top.some_lt_some -> WithTop.some_lt_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : α} {b : α}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) (Option.some.{u_1} α a) (Option.some.{u_1} α b)) (LT.lt.{u_1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.8143 : LT.{u_1} α] {a : α} {b : α}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8143) (Option.some.{u_1} α a) (Option.some.{u_1} α b)) (LT.lt.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8143 a b)
Case conversion may be inaccurate. Consider using '#align with_top.some_lt_some WithTop.some_lt_someₓ'. -/
@[simp]
theorem some_lt_some : @LT.lt (WithTop α) _ (some a) (some b) ↔ a < b :=
  coe_lt_coe
#align with_top.some_lt_some WithTop.some_lt_some

/- warning: with_top.coe_lt_top -> WithTop.coe_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] (a : α), LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a) (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.hasTop.{u_1} α))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.8176 : LT.{u_1} α] (a : α), LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8176) (WithTop.some.{u_1} α a) (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.instTopWithTop.{u_1} α))
Case conversion may be inaccurate. Consider using '#align with_top.coe_lt_top WithTop.coe_lt_topₓ'. -/
theorem coe_lt_top (a : α) : (a : WithTop α) < ⊤ := by
  simpa [← to_dual_lt_to_dual_iff] using WithBot.bot_lt_coe _
#align with_top.coe_lt_top WithTop.coe_lt_top

/- warning: with_top.some_lt_none -> WithTop.some_lt_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] (a : α), LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) (Option.some.{u_1} α a) (Option.none.{u_1} α)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.8205 : LT.{u_1} α] (a : α), LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8205) (Option.some.{u_1} α a) (Option.none.{u_1} α)
Case conversion may be inaccurate. Consider using '#align with_top.some_lt_none WithTop.some_lt_noneₓ'. -/
@[simp]
theorem some_lt_none (a : α) : @LT.lt (WithTop α) _ (some a) none :=
  coe_lt_top a
#align with_top.some_lt_none WithTop.some_lt_none

/- warning: with_top.not_none_lt -> WithTop.not_none_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] (a : WithTop.{u_1} α), Not (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) (Option.none.{u_1} α) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.8229 : LT.{u_1} α] (a : WithTop.{u_1} α), Not (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8229) (Option.none.{u_1} α) a)
Case conversion may be inaccurate. Consider using '#align with_top.not_none_lt WithTop.not_none_ltₓ'. -/
@[simp]
theorem not_none_lt (a : WithTop α) : ¬@LT.lt (WithTop α) _ none a := by
  rw [← to_dual_lt_to_dual_iff]
  exact WithBot.not_lt_none _
#align with_top.not_none_lt WithTop.not_none_lt

/- warning: with_top.lt_iff_exists_coe -> WithTop.lt_iff_exists_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : WithTop.{u_1} α} {b : WithTop.{u_1} α}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) a b) (Exists.{succ u_1} α (fun (p : α) => And (Eq.{succ u_1} (WithTop.{u_1} α) a ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) p)) (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) p) b)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.8287 : LT.{u_1} α] {a : WithTop.{u_1} α} {b : WithTop.{u_1} α}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8287) a b) (Exists.{succ u_1} α (fun (p : α) => And (Eq.{succ u_1} (WithTop.{u_1} α) a (WithTop.some.{u_1} α p)) (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8287) (WithTop.some.{u_1} α p) b)))
Case conversion may be inaccurate. Consider using '#align with_top.lt_iff_exists_coe WithTop.lt_iff_exists_coeₓ'. -/
theorem lt_iff_exists_coe {a b : WithTop α} : a < b ↔ ∃ p : α, a = p ∧ ↑p < b := by
  rw [← to_dual_lt_to_dual_iff, WithBot.lt_iff_exists_coe, OrderDual.exists]
  exact exists_congr fun _ => and_congr_left' Iff.rfl
#align with_top.lt_iff_exists_coe WithTop.lt_iff_exists_coe

/- warning: with_top.coe_lt_iff -> WithTop.coe_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] {a : α} {x : WithTop.{u_1} α}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a) x) (forall (b : α), (Eq.{succ u_1} (WithTop.{u_1} α) x ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) b)) -> (LT.lt.{u_1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.8377 : LT.{u_1} α] {a : α} {x : WithTop.{u_1} α}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8377) (WithTop.some.{u_1} α a) x) (forall (b : WithTop.{u_1} α), (Eq.{succ u_1} (WithTop.{u_1} α) x b) -> (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8377) (WithTop.some.{u_1} α a) b))
Case conversion may be inaccurate. Consider using '#align with_top.coe_lt_iff WithTop.coe_lt_iffₓ'. -/
theorem coe_lt_iff {x : WithTop α} : ↑a < x ↔ ∀ b, x = ↑b → a < b := by
  simp only [← to_dual_lt_to_dual_iff, WithBot.lt_coe_iff, to_dual_apply_coe, OrderDual.forall,
    to_dual_lt_to_dual]
  exact forall₂_congr fun _ _ => Iff.rfl
#align with_top.coe_lt_iff WithTop.coe_lt_iff

end LT

instance [Preorder α] : Preorder
      (WithTop α) where 
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by simp [← to_dual_lt_to_dual_iff, lt_iff_le_not_le]
  le_refl _ := toDual_le_toDual_iff.mp le_rfl
  le_trans _ _ _ := by 
    simp_rw [← to_dual_le_to_dual_iff]
    exact Function.swap le_trans

instance [PartialOrder α] : PartialOrder (WithTop α) :=
  { WithTop.preorder with
    le_antisymm := fun _ _ => by 
      simp_rw [← to_dual_le_to_dual_iff]
      exact Function.swap le_antisymm }

/- warning: with_top.coe_strict_mono -> WithTop.coe_strict_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α], StrictMono.{u_1, u_1} α (WithTop.{u_1} α) _inst_1 (WithTop.preorder.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.8547 : Preorder.{u_1} α], StrictMono.{u_1, u_1} α (WithTop.{u_1} α) inst._@.Mathlib.Order.WithBot._hyg.8547 (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8547) (fun (a : α) => WithTop.some.{u_1} α a)
Case conversion may be inaccurate. Consider using '#align with_top.coe_strict_mono WithTop.coe_strict_monoₓ'. -/
theorem coe_strict_mono [Preorder α] : StrictMono (coe : α → WithTop α) := fun a b => some_lt_some.2
#align with_top.coe_strict_mono WithTop.coe_strict_mono

/- warning: with_top.coe_mono -> WithTop.coe_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α], Monotone.{u_1, u_1} α (WithTop.{u_1} α) _inst_1 (WithTop.preorder.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.8576 : Preorder.{u_1} α], Monotone.{u_1, u_1} α (WithTop.{u_1} α) inst._@.Mathlib.Order.WithBot._hyg.8576 (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8576) (fun (a : α) => WithTop.some.{u_1} α a)
Case conversion may be inaccurate. Consider using '#align with_top.coe_mono WithTop.coe_monoₓ'. -/
theorem coe_mono [Preorder α] : Monotone (coe : α → WithTop α) := fun a b => coe_le_coe.2
#align with_top.coe_mono WithTop.coe_mono

/- warning: with_top.monotone_iff -> WithTop.monotone_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : Preorder.{u_2} β] {f : (WithTop.{u_1} α) -> β}, Iff (Monotone.{u_1, u_2} (WithTop.{u_1} α) β (WithTop.preorder.{u_1} α _inst_1) _inst_2 f) (And (Monotone.{u_1, u_2} α β _inst_1 _inst_2 (Function.comp.{succ u_1, succ u_1, succ u_2} α (WithTop.{u_1} α) β f ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α)))))) (forall (x : α), LE.le.{u_2} β (Preorder.toLE.{u_2} β _inst_2) (f ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) x)) (f (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.hasTop.{u_1} α)))))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.WithBot._hyg.8605 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.8608 : Preorder.{u_2} β] {f : (WithTop.{u_1} α) -> β}, Iff (Monotone.{u_1, u_2} (WithTop.{u_1} α) β (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8605) inst._@.Mathlib.Order.WithBot._hyg.8608 f) (And (Monotone.{u_1, u_2} α β inst._@.Mathlib.Order.WithBot._hyg.8605 inst._@.Mathlib.Order.WithBot._hyg.8608 (fun (a : α) => f (WithTop.some.{u_1} α a))) (forall (x : α), LE.le.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.WithBot._hyg.8608) (f (WithTop.some.{u_1} α x)) (f (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.instTopWithTop.{u_1} α)))))
Case conversion may be inaccurate. Consider using '#align with_top.monotone_iff WithTop.monotone_iffₓ'. -/
theorem monotone_iff [Preorder α] [Preorder β] {f : WithTop α → β} :
    Monotone f ↔ Monotone (f ∘ coe : α → β) ∧ ∀ x : α, f x ≤ f ⊤ :=
  ⟨fun h => ⟨h.comp WithTop.coe_mono, fun x => h le_top⟩, fun h =>
    WithTop.forall.2
      ⟨WithTop.forall.2 ⟨fun _ => le_rfl, fun x h => (not_top_le_coe _ h).elim⟩, fun x =>
        WithTop.forall.2 ⟨fun _ => h.2 x, fun y hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩
#align with_top.monotone_iff WithTop.monotone_iff

/- warning: with_top.monotone_map_iff -> WithTop.monotone_map_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : Preorder.{u_2} β] {f : α -> β}, Iff (Monotone.{u_1, u_2} (WithTop.{u_1} α) (WithTop.{u_2} β) (WithTop.preorder.{u_1} α _inst_1) (WithTop.preorder.{u_2} β _inst_2) (WithTop.map.{u_1, u_2} α β f)) (Monotone.{u_1, u_2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.WithBot._hyg.8713 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.8716 : Preorder.{u_2} β] {f : α -> β}, Iff (Monotone.{u_1, u_2} (WithTop.{u_1} α) (WithTop.{u_2} β) (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8713) (WithTop.instPreorderWithTop.{u_2} β inst._@.Mathlib.Order.WithBot._hyg.8716) (WithTop.map.{u_1, u_2} α β f)) (Monotone.{u_1, u_2} α β inst._@.Mathlib.Order.WithBot._hyg.8713 inst._@.Mathlib.Order.WithBot._hyg.8716 f)
Case conversion may be inaccurate. Consider using '#align with_top.monotone_map_iff WithTop.monotone_map_iffₓ'. -/
@[simp]
theorem monotone_map_iff [Preorder α] [Preorder β] {f : α → β} :
    Monotone (WithTop.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]
#align with_top.monotone_map_iff WithTop.monotone_map_iff

alias monotone_map_iff ↔ _ _root_.monotone.with_top_map

/- warning: with_top.strict_mono_iff -> WithTop.strict_mono_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : Preorder.{u_2} β] {f : (WithTop.{u_1} α) -> β}, Iff (StrictMono.{u_1, u_2} (WithTop.{u_1} α) β (WithTop.preorder.{u_1} α _inst_1) _inst_2 f) (And (StrictMono.{u_1, u_2} α β _inst_1 _inst_2 (Function.comp.{succ u_1, succ u_1, succ u_2} α (WithTop.{u_1} α) β f ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α)))))) (forall (x : α), LT.lt.{u_2} β (Preorder.toLT.{u_2} β _inst_2) (f ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) x)) (f (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.hasTop.{u_1} α)))))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.WithBot._hyg.8746 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.8749 : Preorder.{u_2} β] {f : (WithTop.{u_1} α) -> β}, Iff (StrictMono.{u_1, u_2} (WithTop.{u_1} α) β (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8746) inst._@.Mathlib.Order.WithBot._hyg.8749 f) (And (StrictMono.{u_1, u_2} α β inst._@.Mathlib.Order.WithBot._hyg.8746 inst._@.Mathlib.Order.WithBot._hyg.8749 (fun (a : α) => f (WithTop.some.{u_1} α a))) (forall (x : α), LT.lt.{u_2} β (Preorder.toLT.{u_2} β inst._@.Mathlib.Order.WithBot._hyg.8749) (f (WithTop.some.{u_1} α x)) (f (Top.top.{u_1} (WithTop.{u_1} α) (WithTop.instTopWithTop.{u_1} α)))))
Case conversion may be inaccurate. Consider using '#align with_top.strict_mono_iff WithTop.strict_mono_iffₓ'. -/
theorem strict_mono_iff [Preorder α] [Preorder β] {f : WithTop α → β} :
    StrictMono f ↔ StrictMono (f ∘ coe : α → β) ∧ ∀ x : α, f x < f ⊤ :=
  ⟨fun h => ⟨h.comp WithTop.coe_strict_mono, fun x => h (coe_lt_top _)⟩, fun h =>
    WithTop.forall.2
      ⟨WithTop.forall.2 ⟨flip absurd (lt_irrefl _), fun x h => (not_top_lt h).elim⟩, fun x =>
        WithTop.forall.2 ⟨fun _ => h.2 x, fun y hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩
#align with_top.strict_mono_iff WithTop.strict_mono_iff

/- warning: with_top.strict_mono_map_iff -> WithTop.strict_mono_map_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : Preorder.{u_2} β] {f : α -> β}, Iff (StrictMono.{u_1, u_2} (WithTop.{u_1} α) (WithTop.{u_2} β) (WithTop.preorder.{u_1} α _inst_1) (WithTop.preorder.{u_2} β _inst_2) (WithTop.map.{u_1, u_2} α β f)) (StrictMono.{u_1, u_2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.WithBot._hyg.8857 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.8860 : Preorder.{u_2} β] {f : α -> β}, Iff (StrictMono.{u_1, u_2} (WithTop.{u_1} α) (WithTop.{u_2} β) (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8857) (WithTop.instPreorderWithTop.{u_2} β inst._@.Mathlib.Order.WithBot._hyg.8860) (WithTop.map.{u_1, u_2} α β f)) (StrictMono.{u_1, u_2} α β inst._@.Mathlib.Order.WithBot._hyg.8857 inst._@.Mathlib.Order.WithBot._hyg.8860 f)
Case conversion may be inaccurate. Consider using '#align with_top.strict_mono_map_iff WithTop.strict_mono_map_iffₓ'. -/
@[simp]
theorem strict_mono_map_iff [Preorder α] [Preorder β] {f : α → β} :
    StrictMono (WithTop.map f) ↔ StrictMono f :=
  strict_mono_iff.trans <| by simp [StrictMono, coe_lt_top]
#align with_top.strict_mono_map_iff WithTop.strict_mono_map_iff

alias strict_mono_map_iff ↔ _ _root_.strict_mono.with_top_map

/- warning: with_top.map_le_iff -> WithTop.map_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : Preorder.{u_2} β] (f : α -> β) (a : WithTop.{u_1} α) (b : WithTop.{u_1} α), (forall {a : α} {b : α}, Iff (LE.le.{u_2} β (Preorder.toLE.{u_2} β _inst_2) (f a) (f b)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_1) a b)) -> (Iff (LE.le.{u_2} (WithTop.{u_2} β) (Preorder.toLE.{u_2} (WithTop.{u_2} β) (WithTop.preorder.{u_2} β _inst_2)) (WithTop.map.{u_1, u_2} α β f a) (WithTop.map.{u_1, u_2} α β f b)) (LE.le.{u_1} (WithTop.{u_1} α) (Preorder.toLE.{u_1} (WithTop.{u_1} α) (WithTop.preorder.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Order.WithBot._hyg.8890 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.8893 : Preorder.{u_2} β] (f : α -> β) (a : WithTop.{u_1} α) (b : WithTop.{u_1} α), (forall {a : α} {b : α}, Iff (LE.le.{u_2} β (Preorder.toLE.{u_2} β inst._@.Mathlib.Order.WithBot._hyg.8893) (f a) (f b)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8890) a b)) -> (Iff (LE.le.{u_2} (WithTop.{u_2} β) (Preorder.toLE.{u_2} (WithTop.{u_2} β) (WithTop.instPreorderWithTop.{u_2} β inst._@.Mathlib.Order.WithBot._hyg.8893)) (WithTop.map.{u_1, u_2} α β f a) (WithTop.map.{u_1, u_2} α β f b)) (LE.le.{u_1} (WithTop.{u_1} α) (Preorder.toLE.{u_1} (WithTop.{u_1} α) (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.8890)) a b))
Case conversion may be inaccurate. Consider using '#align with_top.map_le_iff WithTop.map_le_iffₓ'. -/
theorem map_le_iff [Preorder α] [Preorder β] (f : α → β) (a b : WithTop α)
    (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) : a.map f ≤ b.map f ↔ a ≤ b := by
  rw [← to_dual_le_to_dual_iff, to_dual_map, to_dual_map, WithBot.map_le_iff,
    to_dual_le_to_dual_iff]
  simp [mono_iff]
#align with_top.map_le_iff WithTop.map_le_iff

instance [SemilatticeInf α] : SemilatticeInf (WithTop α) :=
  { WithTop.partialOrder with inf := Option.liftOrGet (· ⊓ ·),
    inf_le_left := fun o₁ o₂ a ha => by cases ha <;> cases o₂ <;> simp [Option.liftOrGet],
    inf_le_right := fun o₁ o₂ a ha => by cases ha <;> cases o₁ <;> simp [Option.liftOrGet],
    le_inf := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases' o₂ with b <;> cases' o₃ with c <;> cases ha
      · exact h₂ a rfl
      · exact h₁ a rfl
      · rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩
        simp at h₂
        exact ⟨d, rfl, le_inf h₁' h₂⟩ }

/- warning: with_top.coe_inf -> WithTop.coe_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : SemilatticeInf.{u_1} α] (a : α) (b : α), Eq.{succ u_1} (WithTop.{u_1} α) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) (HasInf.inf.{u_1} α (SemilatticeInf.toHasInf.{u_1} α _inst_1) a b)) (HasInf.inf.{u_1} (WithTop.{u_1} α) (SemilatticeInf.toHasInf.{u_1} (WithTop.{u_1} α) (WithTop.semilatticeInf.{u_1} α _inst_1)) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.9219 : SemilatticeInf.{u_1} α] (a : α) (b : α), Eq.{succ u_1} (WithTop.{u_1} α) (WithTop.some.{u_1} α (HasInf.inf.{u_1} α (SemilatticeInf.toHasInf.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9219) a b)) (HasInf.inf.{u_1} (WithTop.{u_1} α) (SemilatticeInf.toHasInf.{u_1} (WithTop.{u_1} α) (WithTop.instSemilatticeInfWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9219)) (WithTop.some.{u_1} α a) (WithTop.some.{u_1} α b))
Case conversion may be inaccurate. Consider using '#align with_top.coe_inf WithTop.coe_infₓ'. -/
theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithTop α) = a ⊓ b :=
  rfl
#align with_top.coe_inf WithTop.coe_inf

instance [SemilatticeSup α] : SemilatticeSup (WithTop α) :=
  { WithTop.partialOrder with sup := fun o₁ o₂ => o₁.bind fun a => o₂.map fun b => a ⊔ b,
    le_sup_left := fun o₁ o₂ a ha => by 
      simp [map] at ha; rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, le_sup_left⟩,
    le_sup_right := fun o₁ o₂ a ha => by 
      simp [map] at ha; rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, le_sup_right⟩,
    sup_le := fun o₁ o₂ o₃ h₁ h₂ a ha => by 
      cases ha
      rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩
      rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩
      exact ⟨_, rfl, sup_le ab ac⟩ }

/- warning: with_top.coe_sup -> WithTop.coe_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : SemilatticeSup.{u_1} α] (a : α) (b : α), Eq.{succ u_1} (WithTop.{u_1} α) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) (HasSup.sup.{u_1} α (SemilatticeSup.toHasSup.{u_1} α _inst_1) a b)) (HasSup.sup.{u_1} (WithTop.{u_1} α) (SemilatticeSup.toHasSup.{u_1} (WithTop.{u_1} α) (WithTop.semilatticeSup.{u_1} α _inst_1)) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) a) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.9413 : SemilatticeSup.{u_1} α] (a : α) (b : α), Eq.{succ u_1} (WithTop.{u_1} α) (WithTop.some.{u_1} α (HasSup.sup.{u_1} α (SemilatticeSup.toHasSup.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9413) a b)) (HasSup.sup.{u_1} (WithTop.{u_1} α) (SemilatticeSup.toHasSup.{u_1} (WithTop.{u_1} α) (WithTop.instSemilatticeSupWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9413)) (WithTop.some.{u_1} α a) (WithTop.some.{u_1} α b))
Case conversion may be inaccurate. Consider using '#align with_top.coe_sup WithTop.coe_supₓ'. -/
theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithTop α) = a ⊔ b :=
  rfl
#align with_top.coe_sup WithTop.coe_sup

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

/- warning: with_top.decidable_le -> WithTop.decidableLe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] [_inst_2 : DecidableRel.{succ u_1} α (LE.le.{u_1} α _inst_1)], DecidableRel.{succ u_1} (WithTop.{u_1} α) (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.hasLe.{u_1} α _inst_1))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.9628 : LE.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.9631 : DecidableRel.{succ u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.9637 : α) (x._@.Mathlib.Order.WithBot._hyg.9639 : α) => LE.le.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9628 x._@.Mathlib.Order.WithBot._hyg.9637 x._@.Mathlib.Order.WithBot._hyg.9639)], DecidableRel.{succ u_1} (WithTop.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.9657 : WithTop.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.9659 : WithTop.{u_1} α) => LE.le.{u_1} (WithTop.{u_1} α) (WithTop.instLEWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9628) x._@.Mathlib.Order.WithBot._hyg.9657 x._@.Mathlib.Order.WithBot._hyg.9659)
Case conversion may be inaccurate. Consider using '#align with_top.decidable_le WithTop.decidableLeₓ'. -/
instance decidableLe [LE α] [@DecidableRel α (· ≤ ·)] : @DecidableRel (WithTop α) (· ≤ ·) :=
  fun _ _ => decidable_of_decidable_of_iff (WithBot.decidableLe _ _) toDual_le_toDual_iff
#align with_top.decidable_le WithTop.decidableLe

/- warning: with_top.decidable_lt -> WithTop.decidableLt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LT.{u_1} α] [_inst_2 : DecidableRel.{succ u_1} α (LT.lt.{u_1} α _inst_1)], DecidableRel.{succ u_1} (WithTop.{u_1} α) (LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.hasLt.{u_1} α _inst_1))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.9683 : LT.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.9686 : DecidableRel.{succ u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.9692 : α) (x._@.Mathlib.Order.WithBot._hyg.9694 : α) => LT.lt.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9683 x._@.Mathlib.Order.WithBot._hyg.9692 x._@.Mathlib.Order.WithBot._hyg.9694)], DecidableRel.{succ u_1} (WithTop.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.9712 : WithTop.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.9714 : WithTop.{u_1} α) => LT.lt.{u_1} (WithTop.{u_1} α) (WithTop.instLTWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9683) x._@.Mathlib.Order.WithBot._hyg.9712 x._@.Mathlib.Order.WithBot._hyg.9714)
Case conversion may be inaccurate. Consider using '#align with_top.decidable_lt WithTop.decidableLtₓ'. -/
instance decidableLt [LT α] [@DecidableRel α (· < ·)] : @DecidableRel (WithTop α) (· < ·) :=
  fun _ _ => decidable_of_decidable_of_iff (WithBot.decidableLt _ _) toDual_lt_toDual_iff
#align with_top.decidable_lt WithTop.decidableLt

/- warning: with_top.is_total_le -> WithTop.is_total_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] [_inst_2 : IsTotal.{u_1} α (LE.le.{u_1} α _inst_1)], IsTotal.{u_1} (WithTop.{u_1} α) (LE.le.{u_1} (WithTop.{u_1} α) (WithTop.hasLe.{u_1} α _inst_1))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.9738 : LE.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.9741 : IsTotal.{u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.9747 : α) (x._@.Mathlib.Order.WithBot._hyg.9749 : α) => LE.le.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9738 x._@.Mathlib.Order.WithBot._hyg.9747 x._@.Mathlib.Order.WithBot._hyg.9749)], IsTotal.{u_1} (WithTop.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.9767 : WithTop.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.9769 : WithTop.{u_1} α) => LE.le.{u_1} (WithTop.{u_1} α) (WithTop.instLEWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9738) x._@.Mathlib.Order.WithBot._hyg.9767 x._@.Mathlib.Order.WithBot._hyg.9769)
Case conversion may be inaccurate. Consider using '#align with_top.is_total_le WithTop.is_total_leₓ'. -/
instance is_total_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithTop α) (· ≤ ·) :=
  ⟨fun _ _ => by 
    simp_rw [← to_dual_le_to_dual_iff]
    exact total_of _ _ _⟩
#align with_top.is_total_le WithTop.is_total_le

instance [LinearOrder α] : LinearOrder (WithTop α) :=
  Lattice.toLinearOrder _

/- warning: with_top.coe_min -> WithTop.coe_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LinearOrder.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (WithTop.{u_1} α) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) (LinearOrder.min.{u_1} α _inst_1 x y)) (LinearOrder.min.{u_1} (WithTop.{u_1} α) (WithTop.linearOrder.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) x) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) y))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.9821 : LinearOrder.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (WithTop.{u_1} α) (WithTop.some.{u_1} α (Min.min.{u_1} α (LinearOrder.toMin.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9821) x y)) (Min.min.{u_1} (WithTop.{u_1} α) (LinearOrder.toMin.{u_1} (WithTop.{u_1} α) (WithTop.instLinearOrderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9821)) (WithTop.some.{u_1} α x) (WithTop.some.{u_1} α y))
Case conversion may be inaccurate. Consider using '#align with_top.coe_min WithTop.coe_minₓ'. -/
@[simp, norm_cast]
theorem coe_min [LinearOrder α] (x y : α) : (↑(min x y) : WithTop α) = min x y :=
  rfl
#align with_top.coe_min WithTop.coe_min

/- warning: with_top.coe_max -> WithTop.coe_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LinearOrder.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (WithTop.{u_1} α) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) (LinearOrder.max.{u_1} α _inst_1 x y)) (LinearOrder.max.{u_1} (WithTop.{u_1} α) (WithTop.linearOrder.{u_1} α _inst_1) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) x) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) y))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.9854 : LinearOrder.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (WithTop.{u_1} α) (WithTop.some.{u_1} α (Max.max.{u_1} α (LinearOrder.toMax.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9854) x y)) (Max.max.{u_1} (WithTop.{u_1} α) (LinearOrder.toMax.{u_1} (WithTop.{u_1} α) (WithTop.instLinearOrderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9854)) (WithTop.some.{u_1} α x) (WithTop.some.{u_1} α y))
Case conversion may be inaccurate. Consider using '#align with_top.coe_max WithTop.coe_maxₓ'. -/
@[simp, norm_cast]
theorem coe_max [LinearOrder α] (x y : α) : (↑(max x y) : WithTop α) = max x y :=
  rfl
#align with_top.coe_max WithTop.coe_max

/- warning: with_top.well_founded_lt -> WithTop.well_founded_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α], (WellFounded.{succ u_1} α (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_1))) -> (WellFounded.{succ u_1} (WithTop.{u_1} α) (LT.lt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.preorder.{u_1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.9887 : Preorder.{u_1} α], (WellFounded.{succ u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.9895 : α) (x._@.Mathlib.Order.WithBot._hyg.9897 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9887) x._@.Mathlib.Order.WithBot._hyg.9895 x._@.Mathlib.Order.WithBot._hyg.9897)) -> (WellFounded.{succ u_1} (WithTop.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.9915 : WithTop.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.9917 : WithTop.{u_1} α) => LT.lt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.9887)) x._@.Mathlib.Order.WithBot._hyg.9915 x._@.Mathlib.Order.WithBot._hyg.9917))
Case conversion may be inaccurate. Consider using '#align with_top.well_founded_lt WithTop.well_founded_ltₓ'. -/
theorem well_founded_lt [Preorder α] (h : @WellFounded α (· < ·)) :
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
#align with_top.well_founded_lt WithTop.well_founded_lt

open OrderDual

/- warning: with_top.well_founded_gt -> WithTop.well_founded_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α], (WellFounded.{succ u_1} α (GT.gt.{u_1} α (Preorder.toLT.{u_1} α _inst_1))) -> (WellFounded.{succ u_1} (WithTop.{u_1} α) (GT.gt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.preorder.{u_1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.10135 : Preorder.{u_1} α], (WellFounded.{succ u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.10143 : α) (x._@.Mathlib.Order.WithBot._hyg.10145 : α) => GT.gt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10135) x._@.Mathlib.Order.WithBot._hyg.10143 x._@.Mathlib.Order.WithBot._hyg.10145)) -> (WellFounded.{succ u_1} (WithTop.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.10163 : WithTop.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.10165 : WithTop.{u_1} α) => GT.gt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10135)) x._@.Mathlib.Order.WithBot._hyg.10163 x._@.Mathlib.Order.WithBot._hyg.10165))
Case conversion may be inaccurate. Consider using '#align with_top.well_founded_gt WithTop.well_founded_gtₓ'. -/
theorem well_founded_gt [Preorder α] (h : @WellFounded α (· > ·)) :
    @WellFounded (WithTop α) (· > ·) :=
  ⟨fun a =>
    by
    -- ideally, use rel_hom_class.acc, but that is defined later
    have : Acc (· < ·) a.to_dual := WellFounded.apply (WithBot.well_founded_lt h) _
    revert this
    generalize ha : a.to_dual = b; intro ac
    induction' ac with _ H IH generalizing a; subst ha
    exact ⟨_, fun a' h => IH a'.toDual (to_dual_lt_to_dual.mpr h) _ rfl⟩⟩
#align with_top.well_founded_gt WithTop.well_founded_gt

/- warning: with_bot.well_founded_gt -> WithBot.well_founded_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α], (WellFounded.{succ u_1} α (GT.gt.{u_1} α (Preorder.toLT.{u_1} α _inst_1))) -> (WellFounded.{succ u_1} (WithBot.{u_1} α) (GT.gt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.preorder.{u_1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.10271 : Preorder.{u_1} α], (WellFounded.{succ u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.10279 : α) (x._@.Mathlib.Order.WithBot._hyg.10281 : α) => GT.gt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10271) x._@.Mathlib.Order.WithBot._hyg.10279 x._@.Mathlib.Order.WithBot._hyg.10281)) -> (WellFounded.{succ u_1} (WithBot.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.10299 : WithBot.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.10301 : WithBot.{u_1} α) => GT.gt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10271)) x._@.Mathlib.Order.WithBot._hyg.10299 x._@.Mathlib.Order.WithBot._hyg.10301))
Case conversion may be inaccurate. Consider using '#align with_bot.well_founded_gt WithBot.well_founded_gtₓ'. -/
theorem WithBot.well_founded_gt [Preorder α] (h : @WellFounded α (· > ·)) :
    @WellFounded (WithBot α) (· > ·) :=
  ⟨fun a =>
    by
    -- ideally, use rel_hom_class.acc, but that is defined later
    have : Acc (· < ·) a.to_dual := WellFounded.apply (WithTop.well_founded_lt h) _
    revert this
    generalize ha : a.to_dual = b; intro ac
    induction' ac with _ H IH generalizing a; subst ha
    exact ⟨_, fun a' h => IH a'.toDual (to_dual_lt_to_dual.mpr h) _ rfl⟩⟩
#align with_bot.well_founded_gt WithBot.well_founded_gt

/- warning: with_top.trichotomous.lt -> WithTop.Trichotomous.lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : IsTrichotomous.{u_1} α (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_1))], IsTrichotomous.{u_1} (WithTop.{u_1} α) (LT.lt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.preorder.{u_1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.10410 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.10413 : IsTrichotomous.{u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.10419 : α) (x._@.Mathlib.Order.WithBot._hyg.10421 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10410) x._@.Mathlib.Order.WithBot._hyg.10419 x._@.Mathlib.Order.WithBot._hyg.10421)], IsTrichotomous.{u_1} (WithTop.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.10439 : WithTop.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.10441 : WithTop.{u_1} α) => LT.lt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10410)) x._@.Mathlib.Order.WithBot._hyg.10439 x._@.Mathlib.Order.WithBot._hyg.10441)
Case conversion may be inaccurate. Consider using '#align with_top.trichotomous.lt WithTop.Trichotomous.ltₓ'. -/
instance Trichotomous.lt [Preorder α] [IsTrichotomous α (· < ·)] :
    IsTrichotomous (WithTop α) (· < ·) :=
  ⟨by 
    rintro (a | _) (b | _)
    iterate 3 simp
    simpa [Option.some_inj] using @trichotomous _ (· < ·) _ a b⟩
#align with_top.trichotomous.lt WithTop.Trichotomous.lt

/- warning: with_top.is_well_order.lt -> WithTop.IsWellOrder.lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α] [h : IsWellOrder.{u_1} α (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_1))], IsWellOrder.{u_1} (WithTop.{u_1} α) (LT.lt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.preorder.{u_1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.10526 : Preorder.{u_1} α] [h : IsWellOrder.{u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.10534 : α) (x._@.Mathlib.Order.WithBot._hyg.10536 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10526) x._@.Mathlib.Order.WithBot._hyg.10534 x._@.Mathlib.Order.WithBot._hyg.10536)], IsWellOrder.{u_1} (WithTop.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.10554 : WithTop.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.10556 : WithTop.{u_1} α) => LT.lt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10526)) x._@.Mathlib.Order.WithBot._hyg.10554 x._@.Mathlib.Order.WithBot._hyg.10556)
Case conversion may be inaccurate. Consider using '#align with_top.is_well_order.lt WithTop.IsWellOrder.ltₓ'. -/
instance IsWellOrder.lt [Preorder α] [h : IsWellOrder α (· < ·)] :
    IsWellOrder (WithTop α) (· < ·) where wf := well_founded_lt h.wf
#align with_top.is_well_order.lt WithTop.IsWellOrder.lt

/- warning: with_top.trichotomous.gt -> WithTop.Trichotomous.gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : IsTrichotomous.{u_1} α (GT.gt.{u_1} α (Preorder.toLT.{u_1} α _inst_1))], IsTrichotomous.{u_1} (WithTop.{u_1} α) (GT.gt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.preorder.{u_1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.10582 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.10585 : IsTrichotomous.{u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.10591 : α) (x._@.Mathlib.Order.WithBot._hyg.10593 : α) => GT.gt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10582) x._@.Mathlib.Order.WithBot._hyg.10591 x._@.Mathlib.Order.WithBot._hyg.10593)], IsTrichotomous.{u_1} (WithTop.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.10611 : WithTop.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.10613 : WithTop.{u_1} α) => GT.gt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10582)) x._@.Mathlib.Order.WithBot._hyg.10611 x._@.Mathlib.Order.WithBot._hyg.10613)
Case conversion may be inaccurate. Consider using '#align with_top.trichotomous.gt WithTop.Trichotomous.gtₓ'. -/
instance Trichotomous.gt [Preorder α] [IsTrichotomous α (· > ·)] :
    IsTrichotomous (WithTop α) (· > ·) :=
  ⟨by 
    rintro (a | _) (b | _)
    iterate 3 simp
    simpa [Option.some_inj] using @trichotomous _ (· > ·) _ a b⟩
#align with_top.trichotomous.gt WithTop.Trichotomous.gt

/- warning: with_top.is_well_order.gt -> WithTop.IsWellOrder.gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α] [h : IsWellOrder.{u_1} α (GT.gt.{u_1} α (Preorder.toLT.{u_1} α _inst_1))], IsWellOrder.{u_1} (WithTop.{u_1} α) (GT.gt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.preorder.{u_1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.10698 : Preorder.{u_1} α] [h : IsWellOrder.{u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.10706 : α) (x._@.Mathlib.Order.WithBot._hyg.10708 : α) => GT.gt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10698) x._@.Mathlib.Order.WithBot._hyg.10706 x._@.Mathlib.Order.WithBot._hyg.10708)], IsWellOrder.{u_1} (WithTop.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.10726 : WithTop.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.10728 : WithTop.{u_1} α) => GT.gt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10698)) x._@.Mathlib.Order.WithBot._hyg.10726 x._@.Mathlib.Order.WithBot._hyg.10728)
Case conversion may be inaccurate. Consider using '#align with_top.is_well_order.gt WithTop.IsWellOrder.gtₓ'. -/
instance IsWellOrder.gt [Preorder α] [h : IsWellOrder α (· > ·)] :
    IsWellOrder (WithTop α) (· > ·) where wf := well_founded_gt h.wf
#align with_top.is_well_order.gt WithTop.IsWellOrder.gt

/- warning: with_bot.trichotomous.lt -> WithBot.trichotomous.lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α] [h : IsTrichotomous.{u_1} α (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_1))], IsTrichotomous.{u_1} (WithBot.{u_1} α) (LT.lt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.preorder.{u_1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.10751 : Preorder.{u_1} α] [h : IsTrichotomous.{u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.10759 : α) (x._@.Mathlib.Order.WithBot._hyg.10761 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10751) x._@.Mathlib.Order.WithBot._hyg.10759 x._@.Mathlib.Order.WithBot._hyg.10761)], IsTrichotomous.{u_1} (WithBot.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.10779 : WithBot.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.10781 : WithBot.{u_1} α) => LT.lt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10751)) x._@.Mathlib.Order.WithBot._hyg.10779 x._@.Mathlib.Order.WithBot._hyg.10781)
Case conversion may be inaccurate. Consider using '#align with_bot.trichotomous.lt WithBot.trichotomous.ltₓ'. -/
instance WithBot.trichotomous.lt [Preorder α] [h : IsTrichotomous α (· < ·)] :
    IsTrichotomous (WithBot α) (· < ·) :=
  @WithTop.Trichotomous.gt αᵒᵈ _ h
#align with_bot.trichotomous.lt WithBot.trichotomous.lt

/- warning: with_bot.is_well_order.lt -> WithBot.is_well_order.lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α] [h : IsWellOrder.{u_1} α (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_1))], IsWellOrder.{u_1} (WithBot.{u_1} α) (LT.lt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.preorder.{u_1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.10803 : Preorder.{u_1} α] [h : IsWellOrder.{u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.10811 : α) (x._@.Mathlib.Order.WithBot._hyg.10813 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10803) x._@.Mathlib.Order.WithBot._hyg.10811 x._@.Mathlib.Order.WithBot._hyg.10813)], IsWellOrder.{u_1} (WithBot.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.10831 : WithBot.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.10833 : WithBot.{u_1} α) => LT.lt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10803)) x._@.Mathlib.Order.WithBot._hyg.10831 x._@.Mathlib.Order.WithBot._hyg.10833)
Case conversion may be inaccurate. Consider using '#align with_bot.is_well_order.lt WithBot.is_well_order.ltₓ'. -/
instance WithBot.is_well_order.lt [Preorder α] [h : IsWellOrder α (· < ·)] :
    IsWellOrder (WithBot α) (· < ·) :=
  @WithTop.IsWellOrder.gt αᵒᵈ _ h
#align with_bot.is_well_order.lt WithBot.is_well_order.lt

/- warning: with_bot.trichotomous.gt -> WithBot.trichotomous.gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α] [h : IsTrichotomous.{u_1} α (GT.gt.{u_1} α (Preorder.toLT.{u_1} α _inst_1))], IsTrichotomous.{u_1} (WithBot.{u_1} α) (GT.gt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.preorder.{u_1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.10855 : Preorder.{u_1} α] [h : IsTrichotomous.{u_1} α (fun (x._@.Mathlib.Order.WithBot._hyg.10863 : α) (x._@.Mathlib.Order.WithBot._hyg.10865 : α) => GT.gt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10855) x._@.Mathlib.Order.WithBot._hyg.10863 x._@.Mathlib.Order.WithBot._hyg.10865)], IsTrichotomous.{u_1} (WithBot.{u_1} α) (fun (x._@.Mathlib.Order.WithBot._hyg.10883 : WithBot.{u_1} α) (x._@.Mathlib.Order.WithBot._hyg.10885 : WithBot.{u_1} α) => GT.gt.{u_1} (WithBot.{u_1} α) (Preorder.toLT.{u_1} (WithBot.{u_1} α) (WithBot.instPreorderWithBot.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10855)) x._@.Mathlib.Order.WithBot._hyg.10883 x._@.Mathlib.Order.WithBot._hyg.10885)
Case conversion may be inaccurate. Consider using '#align with_bot.trichotomous.gt WithBot.trichotomous.gtₓ'. -/
instance WithBot.trichotomous.gt [Preorder α] [h : IsTrichotomous α (· > ·)] :
    IsTrichotomous (WithBot α) (· > ·) :=
  @WithTop.Trichotomous.lt αᵒᵈ _ h
#align with_bot.trichotomous.gt WithBot.trichotomous.gt

instance WithBot.IsWellOrder.gt [Preorder α] [h : IsWellOrder α (· > ·)] :
    IsWellOrder (WithBot α) (· > ·) :=
  @WithTop.IsWellOrder.lt αᵒᵈ _ h
#align with_bot.is_well_order.gt WithBot.IsWellOrder.gt

instance [LT α] [DenselyOrdered α] [NoMaxOrder α] : DenselyOrdered (WithTop α) :=
  OrderDual.densely_ordered (WithBot αᵒᵈ)

/- warning: with_top.lt_iff_exists_coe_btwn -> WithTop.lt_iff_exists_coe_btwn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Preorder.{u_1} α] [_inst_2 : DenselyOrdered.{u_1} α (Preorder.toLT.{u_1} α _inst_1)] [_inst_3 : NoMaxOrder.{u_1} α (Preorder.toLT.{u_1} α _inst_1)] {a : WithTop.{u_1} α} {b : WithTop.{u_1} α}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.preorder.{u_1} α _inst_1)) a b) (Exists.{succ u_1} α (fun (x : α) => And (LT.lt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.preorder.{u_1} α _inst_1)) a ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) x)) (LT.lt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.preorder.{u_1} α _inst_1)) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) α (WithTop.{u_1} α) (HasLiftT.mk.{succ u_1, succ u_1} α (WithTop.{u_1} α) (CoeTCₓ.coe.{succ u_1, succ u_1} α (WithTop.{u_1} α) (WithTop.hasCoeT.{u_1} α))) x) b)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Order.WithBot._hyg.10986 : Preorder.{u_1} α] [inst._@.Mathlib.Order.WithBot._hyg.10989 : DenselyOrdered.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10986)] [inst._@.Mathlib.Order.WithBot._hyg.10992 : NoMaxOrder.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10986)] {a : WithTop.{u_1} α} {b : WithTop.{u_1} α}, Iff (LT.lt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10986)) a b) (Exists.{succ u_1} α (fun (x : α) => And (LT.lt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10986)) a (WithTop.some.{u_1} α x)) (LT.lt.{u_1} (WithTop.{u_1} α) (Preorder.toLT.{u_1} (WithTop.{u_1} α) (WithTop.instPreorderWithTop.{u_1} α inst._@.Mathlib.Order.WithBot._hyg.10986)) (WithTop.some.{u_1} α x) b)))
Case conversion may be inaccurate. Consider using '#align with_top.lt_iff_exists_coe_btwn WithTop.lt_iff_exists_coe_btwnₓ'. -/
theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMaxOrder α] {a b : WithTop α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨y, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.2
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨x, hx⟩ => lt_trans hx.1 hx.2⟩
#align with_top.lt_iff_exists_coe_btwn WithTop.lt_iff_exists_coe_btwn

instance [LE α] [NoBotOrder α] [Nonempty α] : NoBotOrder (WithTop α) :=
  OrderDual.no_bot_order (WithBot αᵒᵈ)

instance [LT α] [NoMinOrder α] [Nonempty α] : NoMinOrder (WithTop α) :=
  OrderDual.no_min_order (WithBot αᵒᵈ)

end WithTop

