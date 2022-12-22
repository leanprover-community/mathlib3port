/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module data.prod.pprod
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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
  forall {α : Sort.{u1}} {β : Sort.{u2}} {p : PProd.{u1, u2} α β}, Eq.{max 1 u1 u2} (PProd.{u1, u2} α β) (PProd.mk.{u1, u2} α β (PProd.fst.{u1, u2} α β p) (PProd.snd.{u1, u2} α β p)) p
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {p : PProd.{u2, u1} α β}, Eq.{max (max 1 u2) u1} (PProd.{u2, u1} α β) (PProd.mk.{u2, u1} α β (PProd.fst.{u2, u1} α β p) (PProd.snd.{u2, u1} α β p)) p
Case conversion may be inaccurate. Consider using '#align pprod.mk.eta PProd.mk.etaₓ'. -/
@[simp]
theorem mk.eta {p : PProd α β} : PProd.mk p.1 p.2 = p :=
  PProd.casesOn p fun a b => rfl
#align pprod.mk.eta PProd.mk.eta

/- warning: pprod.forall -> PProd.forall is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {p : (PProd.{u1, u2} α β) -> Prop}, Iff (forall (x : PProd.{u1, u2} α β), p x) (forall (a : α) (b : β), p (PProd.mk.{u1, u2} α β a b))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {p : (PProd.{u2, u1} α β) -> Prop}, Iff (forall (x : PProd.{u2, u1} α β), p x) (forall (a : α) (b : β), p (PProd.mk.{u2, u1} α β a b))
Case conversion may be inaccurate. Consider using '#align pprod.forall PProd.forallₓ'. -/
@[simp]
theorem forall {p : PProd α β → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩
#align pprod.forall PProd.forall

/- warning: pprod.exists -> PProd.exists is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {p : (PProd.{u1, u2} α β) -> Prop}, Iff (Exists.{max 1 u1 u2} (PProd.{u1, u2} α β) (fun (x : PProd.{u1, u2} α β) => p x)) (Exists.{u1} α (fun (a : α) => Exists.{u2} β (fun (b : β) => p (PProd.mk.{u1, u2} α β a b))))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {p : (PProd.{u2, u1} α β) -> Prop}, Iff (Exists.{max (max 1 u2) u1} (PProd.{u2, u1} α β) (fun (x : PProd.{u2, u1} α β) => p x)) (Exists.{u2} α (fun (a : α) => Exists.{u1} β (fun (b : β) => p (PProd.mk.{u2, u1} α β a b))))
Case conversion may be inaccurate. Consider using '#align pprod.exists PProd.existsₓ'. -/
@[simp]
theorem exists {p : PProd α β → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩
#align pprod.exists PProd.exists

/- warning: pprod.forall' -> PProd.forall' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {p : α -> β -> Prop}, Iff (forall (x : PProd.{u1, u2} α β), p (PProd.fst.{u1, u2} α β x) (PProd.snd.{u1, u2} α β x)) (forall (a : α) (b : β), p a b)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {p : α -> β -> Prop}, Iff (forall (x : PProd.{u2, u1} α β), p (PProd.fst.{u2, u1} α β x) (PProd.snd.{u2, u1} α β x)) (forall (a : α) (b : β), p a b)
Case conversion may be inaccurate. Consider using '#align pprod.forall' PProd.forall'ₓ'. -/
theorem forall' {p : α → β → Prop} : (∀ x : PProd α β, p x.1 x.2) ↔ ∀ a b, p a b :=
  PProd.forall
#align pprod.forall' PProd.forall'

/- warning: pprod.exists' -> PProd.exists' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {p : α -> β -> Prop}, Iff (Exists.{max 1 u1 u2} (PProd.{u1, u2} α β) (fun (x : PProd.{u1, u2} α β) => p (PProd.fst.{u1, u2} α β x) (PProd.snd.{u1, u2} α β x))) (Exists.{u1} α (fun (a : α) => Exists.{u2} β (fun (b : β) => p a b)))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {p : α -> β -> Prop}, Iff (Exists.{max (max 1 u2) u1} (PProd.{u2, u1} α β) (fun (x : PProd.{u2, u1} α β) => p (PProd.fst.{u2, u1} α β x) (PProd.snd.{u2, u1} α β x))) (Exists.{u2} α (fun (a : α) => Exists.{u1} β (fun (b : β) => p a b)))
Case conversion may be inaccurate. Consider using '#align pprod.exists' PProd.exists'ₓ'. -/
theorem exists' {p : α → β → Prop} : (∃ x : PProd α β, p x.1 x.2) ↔ ∃ a b, p a b :=
  PProd.exists
#align pprod.exists' PProd.exists'

end PProd

/- warning: function.injective.pprod_map -> Function.Injective.pprod_map is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} {δ : Sort.{u4}} {f : α -> β} {g : γ -> δ}, (Function.Injective.{u1, u2} α β f) -> (Function.Injective.{u3, u4} γ δ g) -> (Function.Injective.{max 1 u1 u3, max 1 u2 u4} (PProd.{u1, u3} α γ) (PProd.{u2, u4} β δ) (fun (x : PProd.{u1, u3} α γ) => PProd.mk.{u2, u4} β δ (f (PProd.fst.{u1, u3} α γ x)) (g (PProd.snd.{u1, u3} α γ x))))
but is expected to have type
  forall {α : Sort.{u4}} {β : Sort.{u3}} {γ : Sort.{u2}} {δ : Sort.{u1}} {f : α -> β} {g : γ -> δ}, (Function.Injective.{u4, u3} α β f) -> (Function.Injective.{u2, u1} γ δ g) -> (Function.Injective.{max (max 1 u4) u2, max (max 1 u3) u1} (PProd.{u4, u2} α γ) (PProd.{u3, u1} β δ) (fun (x : PProd.{u4, u2} α γ) => PProd.mk.{u3, u1} β δ (f (PProd.fst.{u4, u2} α γ x)) (g (PProd.snd.{u4, u2} α γ x))))
Case conversion may be inaccurate. Consider using '#align function.injective.pprod_map Function.Injective.pprod_mapₓ'. -/
theorem Function.Injective.pprod_map {f : α → β} {g : γ → δ} (hf : Injective f) (hg : Injective g) :
    Injective (fun x => ⟨f x.1, g x.2⟩ : PProd α γ → PProd β δ) := fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h =>
  have A := congr_arg PProd.fst h
  have B := congr_arg PProd.snd h
  congr_arg₂ PProd.mk (hf A) (hg B)
#align function.injective.pprod_map Function.Injective.pprod_map

