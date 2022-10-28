/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Logic.Basic

/-!
# Nonempty types

This file proves a few extra facts about `nonempty`, which is defined in core Lean.

## Main declarations

* `nonempty.some`: Extracts a witness of nonemptiness using choice. Takes `nonempty α` explicitly.
* `classical.arbitrary`: Extracts a witness of nonemptiness using choice. Takes `nonempty α` as an
  instance.
-/


variable {α β : Type _} {γ : α → Type _}

attribute [simp] nonempty_of_inhabited

instance (priority := 20) Zero.nonempty [Zero α] : Nonempty α :=
  ⟨0⟩

instance (priority := 20) One.nonempty [One α] : Nonempty α :=
  ⟨1⟩

theorem exists_true_iff_nonempty {α : Sort _} : (∃ a : α, True) ↔ Nonempty α :=
  Iff.intro (fun ⟨a, _⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨a, trivial⟩

@[simp]
theorem nonempty_Prop {p : Prop} : Nonempty p ↔ p :=
  Iff.intro (fun ⟨h⟩ => h) fun h => ⟨h⟩

theorem not_nonempty_iff_imp_false {α : Sort _} : ¬Nonempty α ↔ α → False :=
  ⟨fun h a => h ⟨a⟩, fun h ⟨a⟩ => h a⟩

@[simp]
theorem nonempty_sigma : Nonempty (Σa : α, γ a) ↔ ∃ a : α, Nonempty (γ a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]
theorem nonempty_psigma {α} {β : α → Sort _} : Nonempty (PSigma β) ↔ ∃ a : α, Nonempty (β a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]
theorem nonempty_subtype {α} {p : α → Prop} : Nonempty (Subtype p) ↔ ∃ a : α, p a :=
  Iff.intro (fun ⟨⟨a, h⟩⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a, h⟩⟩

/- warning: nonempty_prod -> nonempty_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Iff (Nonempty.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β)) (And (Nonempty.{succ u_1} α) (Nonempty.{succ u_2} β))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Iff (Nonempty.{(max (succ u_2) (succ u_1))} (Prod.{u_1 u_2} α β)) (And (Nonempty.{succ u_1} α) (Nonempty.{succ u_2} β))
Case conversion may be inaccurate. Consider using '#align nonempty_prod nonempty_prodₓ'. -/
@[simp]
theorem nonempty_prod : Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

/- warning: nonempty_pprod -> nonempty_pprod is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, Iff (Nonempty.{(max 1 u_1 u_2)} (PProd.{u_1 u_2} α β)) (And (Nonempty.{u_1} α) (Nonempty.{u_2} β))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, Iff (Nonempty.{(max (max 1 u_2) u_1)} (PProd.{u_1 u_2} α β)) (And (Nonempty.{u_1} α) (Nonempty.{u_2} β))
Case conversion may be inaccurate. Consider using '#align nonempty_pprod nonempty_pprodₓ'. -/
@[simp]
theorem nonempty_pprod {α β} : Nonempty (PProd α β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

/- warning: nonempty_sum -> nonempty_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Iff (Nonempty.{(max (succ u_1) (succ u_2))} (Sum.{u_1 u_2} α β)) (Or (Nonempty.{succ u_1} α) (Nonempty.{succ u_2} β))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Iff (Nonempty.{(max (succ u_2) (succ u_1))} (Sum.{u_1 u_2} α β)) (Or (Nonempty.{succ u_1} α) (Nonempty.{succ u_2} β))
Case conversion may be inaccurate. Consider using '#align nonempty_sum nonempty_sumₓ'. -/
@[simp]
theorem nonempty_sum : Nonempty (Sum α β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | Sum.inl a => Or.inl ⟨a⟩
      | Sum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨Sum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨Sum.inr b⟩

/- warning: nonempty_psum -> nonempty_psum is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, Iff (Nonempty.{(max 1 u_1 u_2)} (PSum.{u_1 u_2} α β)) (Or (Nonempty.{u_1} α) (Nonempty.{u_2} β))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, Iff (Nonempty.{(max (max 1 u_2) u_1)} (PSum.{u_1 u_2} α β)) (Or (Nonempty.{u_1} α) (Nonempty.{u_2} β))
Case conversion may be inaccurate. Consider using '#align nonempty_psum nonempty_psumₓ'. -/
@[simp]
theorem nonempty_psum {α β} : Nonempty (PSum α β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | PSum.inl a => Or.inl ⟨a⟩
      | PSum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨PSum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨PSum.inr b⟩

@[simp]
theorem nonempty_empty : ¬Nonempty Empty := fun ⟨h⟩ => h.elim

/- warning: nonempty_ulift -> nonempty_ulift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}}, Iff (Nonempty.{succ (max u_1 u_2)} (ULift.{u_2 u_1} α)) (Nonempty.{succ u_1} α)
but is expected to have type
  forall {α : Type.{u_1}}, Iff (Nonempty.{(max (succ u_1) (succ u_2))} (ULift.{u_2 u_1} α)) (Nonempty.{succ u_1} α)
Case conversion may be inaccurate. Consider using '#align nonempty_ulift nonempty_uliftₓ'. -/
@[simp]
theorem nonempty_ulift : Nonempty (ULift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

@[simp]
theorem nonempty_plift {α} : Nonempty (PLift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

@[simp]
theorem Nonempty.forall {α} {p : Nonempty α → Prop} : (∀ h : Nonempty α, p h) ↔ ∀ a, p ⟨a⟩ :=
  Iff.intro (fun h a => h _) fun h ⟨a⟩ => h _

@[simp]
theorem Nonempty.exists {α} {p : Nonempty α → Prop} : (∃ h : Nonempty α, p h) ↔ ∃ a, p ⟨a⟩ :=
  Iff.intro (fun ⟨⟨a⟩, h⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a⟩, h⟩

/-- Using `classical.choice`, lifts a (`Prop`-valued) `nonempty` instance to a (`Type`-valued)
  `inhabited` instance. `classical.inhabited_of_nonempty` already exists, in
  `core/init/classical.lean`, but the assumption is not a type class argument,
  which makes it unsuitable for some applications. -/
noncomputable def Classical.inhabitedOfNonempty' {α} [h : Nonempty α] : Inhabited α :=
  ⟨Classical.choice h⟩

/-- Using `classical.choice`, extracts a term from a `nonempty` type. -/
@[reducible]
protected noncomputable def Nonempty.some {α} (h : Nonempty α) : α :=
  Classical.choice h

/-- Using `classical.choice`, extracts a term from a `nonempty` type. -/
@[reducible]
protected noncomputable def Classical.arbitrary (α) [h : Nonempty α] : α :=
  Classical.choice h

/- warning: nonempty.map -> Nonempty.map is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, (α -> β) -> (Nonempty.{u_1} α) -> (Nonempty.{u_2} β)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, (α -> β) -> (Nonempty.{u_1} α) -> (Nonempty.{u_2} β)
Case conversion may be inaccurate. Consider using '#align nonempty.map Nonempty.mapₓ'. -/
/-- Given `f : α → β`, if `α` is nonempty then `β` is also nonempty.
  `nonempty` cannot be a `functor`, because `functor` is restricted to `Type`. -/
theorem Nonempty.map {α β} (f : α → β) : Nonempty α → Nonempty β
  | ⟨h⟩ => ⟨f h⟩

/- warning: nonempty.map2 -> Nonempty.map2 is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}}, (α -> β -> γ) -> (Nonempty.{u_1} α) -> (Nonempty.{u_2} β) -> (Nonempty.{u_3} γ)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}}, (α -> β -> γ) -> (Nonempty.{u_1} α) -> (Nonempty.{u_2} β) -> (Nonempty.{u_3} γ)
Case conversion may be inaccurate. Consider using '#align nonempty.map2 Nonempty.map2ₓ'. -/
protected theorem Nonempty.map2 {α β γ : Sort _} (f : α → β → γ) : Nonempty α → Nonempty β → Nonempty γ
  | ⟨x⟩, ⟨y⟩ => ⟨f x y⟩

/- warning: nonempty.congr -> Nonempty.congr is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, (α -> β) -> (β -> α) -> (Iff (Nonempty.{u_1} α) (Nonempty.{u_2} β))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, (α -> β) -> (β -> α) -> (Iff (Nonempty.{u_1} α) (Nonempty.{u_2} β))
Case conversion may be inaccurate. Consider using '#align nonempty.congr Nonempty.congrₓ'. -/
protected theorem Nonempty.congr {α β} (f : α → β) (g : β → α) : Nonempty α ↔ Nonempty β :=
  ⟨Nonempty.map f, Nonempty.map g⟩

theorem Nonempty.elim_to_inhabited {α : Sort _} [h : Nonempty α] {p : Prop} (f : Inhabited α → p) : p :=
  h.elim <| f ∘ Inhabited.mk

instance {α β} [h : Nonempty α] [h2 : Nonempty β] : Nonempty (α × β) :=
  h.elim fun g => h2.elim fun g2 => ⟨⟨g, g2⟩⟩

instance {ι : Sort _} {α : ι → Sort _} [∀ i, Nonempty (α i)] : Nonempty (∀ i, α i) :=
  ⟨fun _ => Classical.arbitrary _⟩

theorem Classical.nonempty_pi {ι} {α : ι → Sort _} : Nonempty (∀ i, α i) ↔ ∀ i, Nonempty (α i) :=
  ⟨fun ⟨f⟩ a => ⟨f a⟩, @Pi.nonempty _ _⟩

theorem subsingleton_of_not_nonempty {α : Sort _} (h : ¬Nonempty α) : Subsingleton α :=
  ⟨fun x => False.elim <| not_nonempty_iff_imp_false.mp h x⟩

theorem Function.Surjective.nonempty [h : Nonempty β] {f : α → β} (hf : Function.Surjective f) : Nonempty α :=
  let ⟨y⟩ := h
  let ⟨x, hx⟩ := hf y
  ⟨x⟩

