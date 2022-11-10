/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Logic.Basic

/-!
# Extra facts about `pprod`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/496
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Function

variable {α β γ δ : Sort _}

namespace PProd

/- warning: pprod.mk.eta -> PProd.mk.eta is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {p : PProd.{u_1 u_2} α β}, Eq.{(max 1 u_1 u_2)} (PProd.{u_1 u_2} α β) (PProd.mk.{u_1 u_2} α β (PProd.fst.{u_1 u_2} α β p) (PProd.snd.{u_1 u_2} α β p)) p
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {p : PProd.{u_1 u_2} α β}, Eq.{(max (max 1 u_1) u_2)} (PProd.{u_1 u_2} α β) (PProd.mk.{u_1 u_2} α β (PProd.fst.{u_1 u_2} α β p) (PProd.snd.{u_1 u_2} α β p)) p
Case conversion may be inaccurate. Consider using '#align pprod.mk.eta PProd.mk.etaₓ'. -/
@[simp]
theorem mk.eta {p : PProd α β} : PProd.mk p.1 p.2 = p :=
  PProd.casesOn p fun a b => rfl

/- warning: pprod.forall -> PProd.forall is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {p : (PProd.{u_1 u_2} α β) -> Prop}, Iff (forall (x : PProd.{u_1 u_2} α β), p x) (forall (a : α) (b : β), p (PProd.mk.{u_1 u_2} α β a b))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {p : (PProd.{u_1 u_2} α β) -> Prop}, Iff (forall (x : PProd.{u_1 u_2} α β), p x) (forall (a : α) (b : β), p (PProd.mk.{u_1 u_2} α β a b))
Case conversion may be inaccurate. Consider using '#align pprod.forall PProd.forallₓ'. -/
@[simp]
theorem forall {p : PProd α β → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

/- warning: pprod.exists -> PProd.exists is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {p : (PProd.{u_1 u_2} α β) -> Prop}, Iff (Exists.{(max 1 u_1 u_2)} (PProd.{u_1 u_2} α β) (fun (x : PProd.{u_1 u_2} α β) => p x)) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} β (fun (b : β) => p (PProd.mk.{u_1 u_2} α β a b))))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {p : (PProd.{u_1 u_2} α β) -> Prop}, Iff (Exists.{(max (max 1 u_1) u_2)} (PProd.{u_1 u_2} α β) (fun (x : PProd.{u_1 u_2} α β) => p x)) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} β (fun (b : β) => p (PProd.mk.{u_1 u_2} α β a b))))
Case conversion may be inaccurate. Consider using '#align pprod.exists PProd.existsₓ'. -/
@[simp]
theorem exists {p : PProd α β → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

/- warning: pprod.forall' -> PProd.forall' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {p : α -> β -> Prop}, Iff (forall (x : PProd.{u_1 u_2} α β), p (PProd.fst.{u_1 u_2} α β x) (PProd.snd.{u_1 u_2} α β x)) (forall (a : α) (b : β), p a b)
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {p : α -> β -> Prop}, Iff (forall (x : PProd.{u_1 u_2} α β), p (PProd.fst.{u_1 u_2} α β x) (PProd.snd.{u_1 u_2} α β x)) (forall (a : α) (b : β), p a b)
Case conversion may be inaccurate. Consider using '#align pprod.forall' PProd.forall'ₓ'. -/
theorem forall' {p : α → β → Prop} : (∀ x : PProd α β, p x.1 x.2) ↔ ∀ a b, p a b :=
  PProd.forall

/- warning: pprod.exists' -> PProd.exists' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {p : α -> β -> Prop}, Iff (Exists.{(max 1 u_1 u_2)} (PProd.{u_1 u_2} α β) (fun (x : PProd.{u_1 u_2} α β) => p (PProd.fst.{u_1 u_2} α β x) (PProd.snd.{u_1 u_2} α β x))) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} β (fun (b : β) => p a b)))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {p : α -> β -> Prop}, Iff (Exists.{(max (max 1 u_1) u_2)} (PProd.{u_1 u_2} α β) (fun (x : PProd.{u_1 u_2} α β) => p (PProd.fst.{u_1 u_2} α β x) (PProd.snd.{u_1 u_2} α β x))) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} β (fun (b : β) => p a b)))
Case conversion may be inaccurate. Consider using '#align pprod.exists' PProd.exists'ₓ'. -/
theorem exists' {p : α → β → Prop} : (∃ x : PProd α β, p x.1 x.2) ↔ ∃ a b, p a b :=
  PProd.exists

end PProd

/- warning: function.injective.pprod_map -> Function.Injective.pprod_map is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}} {δ : Sort.{u_4}} {f : α -> β} {g : γ -> δ}, (Function.Injective.{u_1 u_2} α β f) -> (Function.Injective.{u_3 u_4} γ δ g) -> (Function.Injective.{(max 1 u_1 u_3) (max 1 u_2 u_4)} (PProd.{u_1 u_3} α γ) (PProd.{u_2 u_4} β δ) (fun (x : PProd.{u_1 u_3} α γ) => PProd.mk.{u_2 u_4} β δ (f (PProd.fst.{u_1 u_3} α γ x)) (g (PProd.snd.{u_1 u_3} α γ x))))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}} {δ : Sort.{u_4}} {f : α -> β} {g : γ -> δ}, (Function.Injective.{u_1 u_2} α β f) -> (Function.Injective.{u_3 u_4} γ δ g) -> (Function.Injective.{(max (max 1 u_1) u_3) (max (max 1 u_2) u_4)} (PProd.{u_1 u_3} α γ) (PProd.{u_2 u_4} β δ) (fun (x : PProd.{u_1 u_3} α γ) => PProd.mk.{u_2 u_4} β δ (f (PProd.fst.{u_1 u_3} α γ x)) (g (PProd.snd.{u_1 u_3} α γ x))))
Case conversion may be inaccurate. Consider using '#align function.injective.pprod_map Function.Injective.pprod_mapₓ'. -/
theorem Function.Injective.pprod_map {f : α → β} {g : γ → δ} (hf : Injective f) (hg : Injective g) :
    Injective (fun x => ⟨f x.1, g x.2⟩ : PProd α γ → PProd β δ) := fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h =>
  have A := congr_arg PProd.fst h
  have B := congr_arg PProd.snd h
  congr_arg₂ PProd.mk (hf A) (hg B)

