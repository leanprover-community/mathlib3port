/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Tactic.Basic
import Mathbin.Logic.Function.Basic

/-!
THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
https://github.com/leanprover-community/mathlib4/pull/545
Any changes to this file require a corresponding PR to mathlib4.

# Extra facts about `prod`

This file defines `prod.swap : α × β → β × α` and proves various simple lemmas about `prod`.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

/- warning: prod_map -> Prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} (f : α -> γ) (g : β -> δ) (p : Prod.{u_1 u_2} α β), Eq.{(max (succ u_3) (succ u_4))} (Prod.{u_3 u_4} γ δ) (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g p) (Prod.mk.{u_3 u_4} γ δ (f (Prod.fst.{u_1 u_2} α β p)) (g (Prod.snd.{u_1 u_2} α β p)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} (f : α -> γ) (g : β -> δ) (p : Prod.{u_1 u_2} α β), Eq.{(max (succ u_3) (succ u_4))} (Prod.{u_3 u_4} γ δ) (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g p) (Prod.mk.{u_3 u_4} γ δ (f (Prod.fst.{u_1 u_2} α β p)) (g (Prod.snd.{u_1 u_2} α β p)))
Case conversion may be inaccurate. Consider using '#align prod_map Prod_mapₓ'. -/
@[simp]
theorem Prod_map (f : α → γ) (g : β → δ) (p : α × β) : Prod.map f g p = (f p.1, g p.2) :=
  rfl
#align prod_map Prod_map

namespace Prod

/- warning: prod.forall -> Prod.forall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : (Prod.{u_1 u_2} α β) -> Prop}, Iff (forall (x : Prod.{u_1 u_2} α β), p x) (forall (a : α) (b : β), p (Prod.mk.{u_1 u_2} α β a b))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : (Prod.{u_1 u_2} α β) -> Prop}, Iff (forall (x : Prod.{u_1 u_2} α β), p x) (forall (a : α) (b : β), p (Prod.mk.{u_1 u_2} α β a b))
Case conversion may be inaccurate. Consider using '#align prod.forall Prod.forallₓ'. -/
@[simp]
theorem forall {p : α × β → Prop} : (∀ x, p x) ↔ ∀ a b, p (a, b) :=
  ⟨fun h a b => h (a, b), fun h ⟨a, b⟩ => h a b⟩
#align prod.forall Prod.forall

/- warning: prod.exists -> Prod.exists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : (Prod.{u_1 u_2} α β) -> Prop}, Iff (Exists.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (fun (x : Prod.{u_1 u_2} α β) => p x)) (Exists.{succ u_1} α (fun (a : α) => Exists.{succ u_2} β (fun (b : β) => p (Prod.mk.{u_1 u_2} α β a b))))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : (Prod.{u_1 u_2} α β) -> Prop}, Iff (Exists.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (fun (x : Prod.{u_1 u_2} α β) => p x)) (Exists.{succ u_1} α (fun (a : α) => Exists.{succ u_2} β (fun (b : β) => p (Prod.mk.{u_1 u_2} α β a b))))
Case conversion may be inaccurate. Consider using '#align prod.exists Prod.existsₓ'. -/
@[simp]
theorem exists {p : α × β → Prop} : (∃ x, p x) ↔ ∃ a b, p (a, b) :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩
#align prod.exists Prod.exists

/- warning: prod.forall' -> Prod.forall' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : α -> β -> Prop}, Iff (forall (x : Prod.{u_1 u_2} α β), p (Prod.fst.{u_1 u_2} α β x) (Prod.snd.{u_1 u_2} α β x)) (forall (a : α) (b : β), p a b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : α -> β -> Prop}, Iff (forall (x : Prod.{u_1 u_2} α β), p (Prod.fst.{u_1 u_2} α β x) (Prod.snd.{u_1 u_2} α β x)) (forall (a : α) (b : β), p a b)
Case conversion may be inaccurate. Consider using '#align prod.forall' Prod.forall'ₓ'. -/
theorem forall' {p : α → β → Prop} : (∀ x : α × β, p x.1 x.2) ↔ ∀ a b, p a b :=
  Prod.forall
#align prod.forall' Prod.forall'

/- warning: prod.exists' -> Prod.exists' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : α -> β -> Prop}, Iff (Exists.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (fun (x : Prod.{u_1 u_2} α β) => p (Prod.fst.{u_1 u_2} α β x) (Prod.snd.{u_1 u_2} α β x))) (Exists.{succ u_1} α (fun (a : α) => Exists.{succ u_2} β (fun (b : β) => p a b)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : α -> β -> Prop}, Iff (Exists.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (fun (x : Prod.{u_1 u_2} α β) => p (Prod.fst.{u_1 u_2} α β x) (Prod.snd.{u_1 u_2} α β x))) (Exists.{succ u_1} α (fun (a : α) => Exists.{succ u_2} β (fun (b : β) => p a b)))
Case conversion may be inaccurate. Consider using '#align prod.exists' Prod.exists'ₓ'. -/
theorem exists' {p : α → β → Prop} : (∃ x : α × β, p x.1 x.2) ↔ ∃ a b, p a b :=
  Prod.exists
#align prod.exists' Prod.exists'

#print Prod.snd_comp_mk /-
@[simp]
theorem snd_comp_mk (x : α) : Prod.snd ∘ (Prod.mk x : β → α × β) = id :=
  rfl
#align prod.snd_comp_mk Prod.snd_comp_mk
-/

/- warning: prod.fst_comp_mk -> Prod.fst_comp_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (x : α), Eq.{(max (succ u_2) (succ u_1))} (β -> α) (Function.comp.{succ u_2 (max (succ u_1) (succ u_2)) succ u_1} β (Prod.{u_1 u_2} α β) α (Prod.fst.{u_1 u_2} α β) (Prod.mk.{u_1 u_2} α β x)) (Function.const.{succ u_1 succ u_2} α β x)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (x : α), Eq.{(max (succ u_1) (succ u_2))} (β -> α) (Function.comp.{succ u_2 (max (succ u_2) (succ u_1)) succ u_1} β (Prod.{u_1 u_2} α β) α (Prod.fst.{u_1 u_2} α β) (Prod.mk.{u_1 u_2} α β x)) (Function.const.{succ u_1 succ u_2} α β x)
Case conversion may be inaccurate. Consider using '#align prod.fst_comp_mk Prod.fst_comp_mkₓ'. -/
@[simp]
theorem fst_comp_mk (x : α) : Prod.fst ∘ (Prod.mk x : β → α × β) = Function.const β x :=
  rfl
#align prod.fst_comp_mk Prod.fst_comp_mk

/- warning: prod.map_mk -> Prod.map_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} (f : α -> γ) (g : β -> δ) (a : α) (b : β), Eq.{(max (succ u_3) (succ u_4))} (Prod.{u_3 u_4} γ δ) (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g (Prod.mk.{u_1 u_2} α β a b)) (Prod.mk.{u_3 u_4} γ δ (f a) (g b))
but is expected to have type
  forall {α : Type.{u_3}} {β : Type.{u_4}} {γ : Type.{u_1}} {δ : Type.{u_2}} (f : α -> γ) (g : β -> δ) (a : α) (b : β), Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} γ δ) (Prod.map.{u_3 u_1 u_4 u_2} α γ β δ f g (Prod.mk.{u_3 u_4} α β a b)) (Prod.mk.{u_1 u_2} γ δ (f a) (g b))
Case conversion may be inaccurate. Consider using '#align prod.map_mk Prod.map_mkₓ'. -/
@[simp]
theorem map_mk (f : α → γ) (g : β → δ) (a : α) (b : β) : map f g (a, b) = (f a, g b) :=
  rfl
#align prod.map_mk Prod.map_mk

/- warning: prod.map_fst -> Prod.map_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} (f : α -> γ) (g : β -> δ) (p : Prod.{u_1 u_2} α β), Eq.{succ u_3} γ (Prod.fst.{u_3 u_4} γ δ (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g p)) (f (Prod.fst.{u_1 u_2} α β p))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} (f : α -> γ) (g : β -> δ) (p : Prod.{u_1 u_2} α β), Eq.{succ u_3} γ (Prod.fst.{u_3 u_4} γ δ (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g p)) (f (Prod.fst.{u_1 u_2} α β p))
Case conversion may be inaccurate. Consider using '#align prod.map_fst Prod.map_fstₓ'. -/
theorem map_fst (f : α → γ) (g : β → δ) (p : α × β) : (map f g p).1 = f p.1 :=
  rfl
#align prod.map_fst Prod.map_fst

/- warning: prod.map_snd -> Prod.map_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} (f : α -> γ) (g : β -> δ) (p : Prod.{u_1 u_2} α β), Eq.{succ u_4} δ (Prod.snd.{u_3 u_4} γ δ (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g p)) (g (Prod.snd.{u_1 u_2} α β p))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_4}} {δ : Type.{u_3}} (f : α -> γ) (g : β -> δ) (p : Prod.{u_1 u_2} α β), Eq.{succ u_3} δ (Prod.snd.{u_4 u_3} γ δ (Prod.map.{u_1 u_4 u_2 u_3} α γ β δ f g p)) (g (Prod.snd.{u_1 u_2} α β p))
Case conversion may be inaccurate. Consider using '#align prod.map_snd Prod.map_sndₓ'. -/
theorem map_snd (f : α → γ) (g : β → δ) (p : α × β) : (map f g p).2 = g p.2 :=
  rfl
#align prod.map_snd Prod.map_snd

/- warning: prod.map_fst' -> Prod.map_fst' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} (f : α -> γ) (g : β -> δ), Eq.{(max (max (succ u_1) (succ u_2)) (succ u_3))} ((Prod.{u_1 u_2} α β) -> γ) (Function.comp.{(max (succ u_1) (succ u_2)) (max (succ u_3) (succ u_4)) succ u_3} (Prod.{u_1 u_2} α β) (Prod.{u_3 u_4} γ δ) γ (Prod.fst.{u_3 u_4} γ δ) (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g)) (Function.comp.{(max (succ u_1) (succ u_2)) succ u_1 succ u_3} (Prod.{u_1 u_2} α β) α γ f (Prod.fst.{u_1 u_2} α β))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} (f : α -> γ) (g : β -> δ), Eq.{(max (max (succ u_1) (succ u_2)) (succ u_3))} ((Prod.{u_1 u_2} α β) -> γ) (Function.comp.{(max (succ u_2) (succ u_1)) (max (succ u_4) (succ u_3)) succ u_3} (Prod.{u_1 u_2} α β) (Prod.{u_3 u_4} γ δ) γ (Prod.fst.{u_3 u_4} γ δ) (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g)) (Function.comp.{(max (succ u_2) (succ u_1)) succ u_1 succ u_3} (Prod.{u_1 u_2} α β) α γ f (Prod.fst.{u_1 u_2} α β))
Case conversion may be inaccurate. Consider using '#align prod.map_fst' Prod.map_fst'ₓ'. -/
theorem map_fst' (f : α → γ) (g : β → δ) : Prod.fst ∘ map f g = f ∘ Prod.fst :=
  funext <| map_fst f g
#align prod.map_fst' Prod.map_fst'

/- warning: prod.map_snd' -> Prod.map_snd' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} (f : α -> γ) (g : β -> δ), Eq.{(max (max (succ u_1) (succ u_2)) (succ u_4))} ((Prod.{u_1 u_2} α β) -> δ) (Function.comp.{(max (succ u_1) (succ u_2)) (max (succ u_3) (succ u_4)) succ u_4} (Prod.{u_1 u_2} α β) (Prod.{u_3 u_4} γ δ) δ (Prod.snd.{u_3 u_4} γ δ) (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g)) (Function.comp.{(max (succ u_1) (succ u_2)) succ u_2 succ u_4} (Prod.{u_1 u_2} α β) β δ g (Prod.snd.{u_1 u_2} α β))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_4}} {δ : Type.{u_3}} (f : α -> γ) (g : β -> δ), Eq.{(max (max (succ u_1) (succ u_2)) (succ u_3))} ((Prod.{u_1 u_2} α β) -> δ) (Function.comp.{(max (succ u_2) (succ u_1)) (max (succ u_3) (succ u_4)) succ u_3} (Prod.{u_1 u_2} α β) (Prod.{u_4 u_3} γ δ) δ (Prod.snd.{u_4 u_3} γ δ) (Prod.map.{u_1 u_4 u_2 u_3} α γ β δ f g)) (Function.comp.{(max (succ u_2) (succ u_1)) succ u_2 succ u_3} (Prod.{u_1 u_2} α β) β δ g (Prod.snd.{u_1 u_2} α β))
Case conversion may be inaccurate. Consider using '#align prod.map_snd' Prod.map_snd'ₓ'. -/
theorem map_snd' (f : α → γ) (g : β → δ) : Prod.snd ∘ map f g = g ∘ Prod.snd :=
  funext <| map_snd f g
#align prod.map_snd' Prod.map_snd'

/- warning: prod.map_comp_map -> Prod.map_comp_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} {ε : Type.{u_5}} {ζ : Type.{u_6}} (f : α -> β) (f' : γ -> δ) (g : β -> ε) (g' : δ -> ζ), Eq.{(max (max (succ u_1) (succ u_3)) (succ u_5) (succ u_6))} ((Prod.{u_1 u_3} α γ) -> (Prod.{u_5 u_6} ε ζ)) (Function.comp.{(max (succ u_1) (succ u_3)) (max (succ u_2) (succ u_4)) (max (succ u_5) (succ u_6))} (Prod.{u_1 u_3} α γ) (Prod.{u_2 u_4} β δ) (Prod.{u_5 u_6} ε ζ) (Prod.map.{u_2 u_5 u_4 u_6} β ε δ ζ g g') (Prod.map.{u_1 u_2 u_3 u_4} α β γ δ f f')) (Prod.map.{u_1 u_5 u_3 u_6} α ε γ ζ (Function.comp.{succ u_1 succ u_2 succ u_5} α β ε g f) (Function.comp.{succ u_3 succ u_4 succ u_6} γ δ ζ g' f'))
but is expected to have type
  forall {α : Type.{u_3}} {β : Type.{u_6}} {γ : Type.{u_4}} {δ : Type.{u_5}} {ε : Type.{u_1}} {ζ : Type.{u_2}} (f : α -> β) (f' : γ -> δ) (g : β -> ε) (g' : δ -> ζ), Eq.{(max (max (max (succ u_3) (succ u_4)) (succ u_1)) (succ u_2))} ((Prod.{u_3 u_4} α γ) -> (Prod.{u_1 u_2} ε ζ)) (Function.comp.{(max (succ u_4) (succ u_3)) (max (succ u_5) (succ u_6)) (max (succ u_2) (succ u_1))} (Prod.{u_3 u_4} α γ) (Prod.{u_6 u_5} β δ) (Prod.{u_1 u_2} ε ζ) (Prod.map.{u_6 u_1 u_5 u_2} β ε δ ζ g g') (Prod.map.{u_3 u_6 u_4 u_5} α β γ δ f f')) (Prod.map.{u_3 u_1 u_4 u_2} α ε γ ζ (Function.comp.{succ u_3 succ u_6 succ u_1} α β ε g f) (Function.comp.{succ u_4 succ u_5 succ u_2} γ δ ζ g' f'))
Case conversion may be inaccurate. Consider using '#align prod.map_comp_map Prod.map_comp_mapₓ'. -/
/-- Composing a `prod.map` with another `prod.map` is equal to
a single `prod.map` of composed functions.
-/
theorem map_comp_map {ε ζ : Type _} (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) :
    Prod.map g g' ∘ Prod.map f f' = Prod.map (g ∘ f) (g' ∘ f') :=
  rfl
#align prod.map_comp_map Prod.map_comp_map

/- warning: prod.map_map -> Prod.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} {ε : Type.{u_5}} {ζ : Type.{u_6}} (f : α -> β) (f' : γ -> δ) (g : β -> ε) (g' : δ -> ζ) (x : Prod.{u_1 u_3} α γ), Eq.{(max (succ u_5) (succ u_6))} (Prod.{u_5 u_6} ε ζ) (Prod.map.{u_2 u_5 u_4 u_6} β ε δ ζ g g' (Prod.map.{u_1 u_2 u_3 u_4} α β γ δ f f' x)) (Prod.map.{u_1 u_5 u_3 u_6} α ε γ ζ (Function.comp.{succ u_1 succ u_2 succ u_5} α β ε g f) (Function.comp.{succ u_3 succ u_4 succ u_6} γ δ ζ g' f') x)
but is expected to have type
  forall {α : Type.{u_3}} {β : Type.{u_5}} {γ : Type.{u_4}} {δ : Type.{u_6}} {ε : Type.{u_1}} {ζ : Type.{u_2}} (f : α -> β) (f' : γ -> δ) (g : β -> ε) (g' : δ -> ζ) (x : Prod.{u_3 u_4} α γ), Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} ε ζ) (Prod.map.{u_5 u_1 u_6 u_2} β ε δ ζ g g' (Prod.map.{u_3 u_5 u_4 u_6} α β γ δ f f' x)) (Prod.map.{u_3 u_1 u_4 u_2} α ε γ ζ (Function.comp.{succ u_3 succ u_5 succ u_1} α β ε g f) (Function.comp.{succ u_4 succ u_6 succ u_2} γ δ ζ g' f') x)
Case conversion may be inaccurate. Consider using '#align prod.map_map Prod.map_mapₓ'. -/
/-- Composing a `prod.map` with another `prod.map` is equal to
a single `prod.map` of composed functions, fully applied.
-/
theorem map_map {ε ζ : Type _} (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) (x : α × γ) :
    Prod.map g g' (Prod.map f f' x) = Prod.map (g ∘ f) (g' ∘ f') x :=
  rfl
#align prod.map_map Prod.map_map

/- warning: prod.mk.inj_iff -> Prod.mk.inj_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {a₁ : α} {a₂ : α} {b₁ : β} {b₂ : β}, Iff (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (Prod.mk.{u_1 u_2} α β a₁ b₁) (Prod.mk.{u_1 u_2} α β a₂ b₂)) (And (Eq.{succ u_1} α a₁ a₂) (Eq.{succ u_2} β b₁ b₂))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {a₁ : α} {a₂ : α} {b₁ : β} {b₂ : β}, Iff (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (Prod.mk.{u_1 u_2} α β a₁ b₁) (Prod.mk.{u_1 u_2} α β a₂ b₂)) (And (Eq.{succ u_1} α a₁ a₂) (Eq.{succ u_2} β b₁ b₂))
Case conversion may be inaccurate. Consider using '#align prod.mk.inj_iff Prod.mk.inj_iffₓ'. -/
@[simp]
theorem mk.inj_iff {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨Prod.mk.inj, by cc⟩
#align prod.mk.inj_iff Prod.mk.inj_iff

/- warning: prod.mk.inj_left -> Prod.mk.inj_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (a : α), Function.Injective.{succ u_2 (max (succ u_1) (succ u_2))} β (Prod.{u_1 u_2} α β) (Prod.mk.{u_1 u_2} α β a)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (a : α), Function.Injective.{succ u_2 (max (succ u_1) (succ u_2))} β (Prod.{u_1 u_2} α β) (Prod.mk.{u_1 u_2} α β a)
Case conversion may be inaccurate. Consider using '#align prod.mk.inj_left Prod.mk.inj_leftₓ'. -/
theorem mk.inj_left {α β : Type _} (a : α) : Function.Injective (Prod.mk a : β → α × β) := by
  intro b₁ b₂ h
  simpa only [true_and_iff, Prod.mk.inj_iff, eq_self_iff_true] using h
#align prod.mk.inj_left Prod.mk.inj_left

/- warning: prod.mk.inj_right -> Prod.mk.inj_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (b : β), Function.Injective.{succ u_1 (max (succ u_1) (succ u_2))} α (Prod.{u_1 u_2} α β) (fun (a : α) => Prod.mk.{u_1 u_2} α β a b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (b : β), Function.Injective.{succ u_1 (max (succ u_1) (succ u_2))} α (Prod.{u_1 u_2} α β) (fun (a : α) => Prod.mk.{u_1 u_2} α β a b)
Case conversion may be inaccurate. Consider using '#align prod.mk.inj_right Prod.mk.inj_rightₓ'. -/
theorem mk.inj_right {α β : Type _} (b : β) : Function.Injective (fun a => Prod.mk a b : α → α × β) := by
  intro b₁ b₂ h
  · simpa only [and_true_iff, eq_self_iff_true, mk.inj_iff] using h
    
#align prod.mk.inj_right Prod.mk.inj_right

/- warning: prod.ext_iff -> Prod.ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {q : Prod.{u_1 u_2} α β}, Iff (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p q) (And (Eq.{succ u_1} α (Prod.fst.{u_1 u_2} α β p) (Prod.fst.{u_1 u_2} α β q)) (Eq.{succ u_2} β (Prod.snd.{u_1 u_2} α β p) (Prod.snd.{u_1 u_2} α β q)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {q : Prod.{u_1 u_2} α β}, Iff (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p q) (And (Eq.{succ u_1} α (Prod.fst.{u_1 u_2} α β p) (Prod.fst.{u_1 u_2} α β q)) (Eq.{succ u_2} β (Prod.snd.{u_1 u_2} α β p) (Prod.snd.{u_1 u_2} α β q)))
Case conversion may be inaccurate. Consider using '#align prod.ext_iff Prod.ext_iffₓ'. -/
theorem ext_iff {p q : α × β} : p = q ↔ p.1 = q.1 ∧ p.2 = q.2 := by rw [← @mk.eta _ _ p, ← @mk.eta _ _ q, mk.inj_iff]
#align prod.ext_iff Prod.ext_iff

@[ext.1]
theorem ext {α β} {p q : α × β} (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) : p = q :=
  ext_iff.2 ⟨h₁, h₂⟩
#align prod.ext Prod.extₓ

/- warning: prod.map_def -> Prod.map_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} {f : α -> γ} {g : β -> δ}, Eq.{(max (max (succ u_1) (succ u_2)) (succ u_3) (succ u_4))} ((Prod.{u_1 u_2} α β) -> (Prod.{u_3 u_4} γ δ)) (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g) (fun (p : Prod.{u_1 u_2} α β) => Prod.mk.{u_3 u_4} γ δ (f (Prod.fst.{u_1 u_2} α β p)) (g (Prod.snd.{u_1 u_2} α β p)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} {f : α -> γ} {g : β -> δ}, Eq.{(max (max (max (succ u_1) (succ u_2)) (succ u_3)) (succ u_4))} ((Prod.{u_1 u_2} α β) -> (Prod.{u_3 u_4} γ δ)) (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g) (fun (p : Prod.{u_1 u_2} α β) => Prod.mk.{u_3 u_4} γ δ (f (Prod.fst.{u_1 u_2} α β p)) (g (Prod.snd.{u_1 u_2} α β p)))
Case conversion may be inaccurate. Consider using '#align prod.map_def Prod.map_defₓ'. -/
theorem map_def {f : α → γ} {g : β → δ} : Prod.map f g = fun p : α × β => (f p.1, g p.2) :=
  funext fun p => ext (map_fst f g p) (map_snd f g p)
#align prod.map_def Prod.map_def

/- warning: prod.id_prod -> Prod.id_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Eq.{(max (succ u_1) (succ u_2))} ((Prod.{u_1 u_2} α β) -> (Prod.{u_1 u_2} α β)) (fun (p : Prod.{u_1 u_2} α β) => Prod.mk.{u_1 u_2} α β (Prod.fst.{u_1 u_2} α β p) (Prod.snd.{u_1 u_2} α β p)) (id.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Eq.{(max (succ u_1) (succ u_2))} ((Prod.{u_1 u_2} α β) -> (Prod.{u_1 u_2} α β)) (fun (p : Prod.{u_1 u_2} α β) => Prod.mk.{u_1 u_2} α β (Prod.fst.{u_1 u_2} α β p) (Prod.snd.{u_1 u_2} α β p)) (id.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β))
Case conversion may be inaccurate. Consider using '#align prod.id_prod Prod.id_prodₓ'. -/
theorem id_prod : (fun p : α × β => (p.1, p.2)) = id :=
  funext fun ⟨a, b⟩ => rfl
#align prod.id_prod Prod.id_prod

/- warning: prod.map_id -> Prod.map_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Eq.{(max (succ u_1) (succ u_2))} ((Prod.{u_1 u_2} α β) -> (Prod.{u_1 u_2} α β)) (Prod.map.{u_1 u_1 u_2 u_2} α α β β (id.{succ u_1} α) (id.{succ u_2} β)) (id.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Eq.{(max (succ u_1) (succ u_2))} ((Prod.{u_1 u_2} α β) -> (Prod.{u_1 u_2} α β)) (Prod.map.{u_1 u_1 u_2 u_2} α α β β (id.{succ u_1} α) (id.{succ u_2} β)) (id.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β))
Case conversion may be inaccurate. Consider using '#align prod.map_id Prod.map_idₓ'. -/
theorem map_id : Prod.map (@id α) (@id β) = id :=
  id_prod
#align prod.map_id Prod.map_id

#print Prod.fst_surjective /-
theorem fst_surjective [h : Nonempty β] : Function.Surjective (@fst α β) := fun x => h.elim fun y => ⟨⟨x, y⟩, rfl⟩
#align prod.fst_surjective Prod.fst_surjective
-/

/- warning: prod.snd_surjective -> Prod.snd_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [h : Nonempty.{succ u_1} α], Function.Surjective.{(max (succ u_1) (succ u_2)) succ u_2} (Prod.{u_1 u_2} α β) β (Prod.snd.{u_1 u_2} α β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [h : Nonempty.{succ u_1} α], Function.Surjective.{(max (succ u_1) (succ u_2)) succ u_2} (Prod.{u_1 u_2} α β) β (Prod.snd.{u_1 u_2} α β)
Case conversion may be inaccurate. Consider using '#align prod.snd_surjective Prod.snd_surjectiveₓ'. -/
theorem snd_surjective [h : Nonempty α] : Function.Surjective (@snd α β) := fun y => h.elim fun x => ⟨⟨x, y⟩, rfl⟩
#align prod.snd_surjective Prod.snd_surjective

#print Prod.fst_injective /-
theorem fst_injective [Subsingleton β] : Function.Injective (@fst α β) := fun x y h => ext h (Subsingleton.elim _ _)
#align prod.fst_injective Prod.fst_injective
-/

/- warning: prod.snd_injective -> Prod.snd_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Subsingleton.{succ u_1} α], Function.Injective.{(max (succ u_1) (succ u_2)) succ u_2} (Prod.{u_1 u_2} α β) β (Prod.snd.{u_1 u_2} α β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Data.Prod.Basic._hyg.1087 : Subsingleton.{succ u_1} α], Function.Injective.{(max (succ u_1) (succ u_2)) succ u_2} (Prod.{u_1 u_2} α β) β (Prod.snd.{u_1 u_2} α β)
Case conversion may be inaccurate. Consider using '#align prod.snd_injective Prod.snd_injectiveₓ'. -/
theorem snd_injective [Subsingleton α] : Function.Injective (@snd α β) := fun x y h => ext (Subsingleton.elim _ _) h
#align prod.snd_injective Prod.snd_injective

#print Prod.swap /-
/-- Swap the factors of a product. `swap (a, b) = (b, a)` -/
def swap : α × β → β × α := fun p => (p.2, p.1)
#align prod.swap Prod.swap
-/

/- warning: prod.swap_swap -> Prod.swap_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (x : Prod.{u_1 u_2} α β), Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (Prod.swap.{u_2 u_1} β α (Prod.swap.{u_1 u_2} α β x)) x
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (x : Prod.{u_1 u_2} α β), Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (Prod.swap.{u_2 u_1} β α (Prod.swap.{u_1 u_2} α β x)) x
Case conversion may be inaccurate. Consider using '#align prod.swap_swap Prod.swap_swapₓ'. -/
@[simp]
theorem swap_swap : ∀ x : α × β, swap (swap x) = x
  | ⟨a, b⟩ => rfl
#align prod.swap_swap Prod.swap_swap

/- warning: prod.fst_swap -> Prod.fst_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β}, Eq.{succ u_2} β (Prod.fst.{u_2 u_1} β α (Prod.swap.{u_1 u_2} α β p)) (Prod.snd.{u_1 u_2} α β p)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β}, Eq.{succ u_2} β (Prod.fst.{u_2 u_1} β α (Prod.swap.{u_1 u_2} α β p)) (Prod.snd.{u_1 u_2} α β p)
Case conversion may be inaccurate. Consider using '#align prod.fst_swap Prod.fst_swapₓ'. -/
@[simp]
theorem fst_swap {p : α × β} : (swap p).1 = p.2 :=
  rfl
#align prod.fst_swap Prod.fst_swap

/- warning: prod.snd_swap -> Prod.snd_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β}, Eq.{succ u_1} α (Prod.snd.{u_2 u_1} β α (Prod.swap.{u_1 u_2} α β p)) (Prod.fst.{u_1 u_2} α β p)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β}, Eq.{succ u_1} α (Prod.snd.{u_2 u_1} β α (Prod.swap.{u_1 u_2} α β p)) (Prod.fst.{u_1 u_2} α β p)
Case conversion may be inaccurate. Consider using '#align prod.snd_swap Prod.snd_swapₓ'. -/
@[simp]
theorem snd_swap {p : α × β} : (swap p).2 = p.1 :=
  rfl
#align prod.snd_swap Prod.snd_swap

/- warning: prod.swap_prod_mk -> Prod.swap_prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {a : α} {b : β}, Eq.{(max (succ u_2) (succ u_1))} (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β (Prod.mk.{u_1 u_2} α β a b)) (Prod.mk.{u_2 u_1} β α b a)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {a : α} {b : β}, Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β (Prod.mk.{u_1 u_2} α β a b)) (Prod.mk.{u_2 u_1} β α b a)
Case conversion may be inaccurate. Consider using '#align prod.swap_prod_mk Prod.swap_prod_mkₓ'. -/
@[simp]
theorem swap_prod_mk {a : α} {b : β} : swap (a, b) = (b, a) :=
  rfl
#align prod.swap_prod_mk Prod.swap_prod_mk

/- warning: prod.swap_swap_eq -> Prod.swap_swap_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Eq.{(max (succ u_1) (succ u_2))} ((Prod.{u_1 u_2} α β) -> (Prod.{u_1 u_2} α β)) (Function.comp.{(max (succ u_1) (succ u_2)) (max (succ u_2) (succ u_1)) (max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (Prod.{u_2 u_1} β α) (Prod.{u_1 u_2} α β) (Prod.swap.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β)) (id.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Eq.{(max (succ u_1) (succ u_2))} ((Prod.{u_1 u_2} α β) -> (Prod.{u_1 u_2} α β)) (Function.comp.{(max (succ u_2) (succ u_1)) (max (succ u_1) (succ u_2)) (max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (Prod.{u_2 u_1} β α) (Prod.{u_1 u_2} α β) (Prod.swap.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β)) (id.{(max (succ u_2) (succ u_1))} (Prod.{u_1 u_2} α β))
Case conversion may be inaccurate. Consider using '#align prod.swap_swap_eq Prod.swap_swap_eqₓ'. -/
@[simp]
theorem swap_swap_eq : swap ∘ swap = @id (α × β) :=
  funext swap_swap
#align prod.swap_swap_eq Prod.swap_swap_eq

/- warning: prod.swap_left_inverse -> Prod.swap_leftInverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Function.LeftInverse.{(max (succ u_2) (succ u_1)) (max (succ u_1) (succ u_2))} (Prod.{u_2 u_1} β α) (Prod.{u_1 u_2} α β) (Prod.swap.{u_1 u_2} α β) (Prod.swap.{u_2 u_1} β α)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Function.LeftInverse.{(max (succ u_1) (succ u_2)) (max (succ u_1) (succ u_2))} (Prod.{u_2 u_1} β α) (Prod.{u_1 u_2} α β) (Prod.swap.{u_1 u_2} α β) (Prod.swap.{u_2 u_1} β α)
Case conversion may be inaccurate. Consider using '#align prod.swap_left_inverse Prod.swap_leftInverseₓ'. -/
@[simp]
theorem swap_leftInverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap
#align prod.swap_left_inverse Prod.swap_leftInverse

/- warning: prod.swap_right_inverse -> Prod.swap_rightInverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Function.RightInverse.{(max (succ u_2) (succ u_1)) (max (succ u_1) (succ u_2))} (Prod.{u_2 u_1} β α) (Prod.{u_1 u_2} α β) (Prod.swap.{u_1 u_2} α β) (Prod.swap.{u_2 u_1} β α)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Function.RightInverse.{(max (succ u_1) (succ u_2)) (max (succ u_1) (succ u_2))} (Prod.{u_2 u_1} β α) (Prod.{u_1 u_2} α β) (Prod.swap.{u_1 u_2} α β) (Prod.swap.{u_2 u_1} β α)
Case conversion may be inaccurate. Consider using '#align prod.swap_right_inverse Prod.swap_rightInverseₓ'. -/
@[simp]
theorem swap_rightInverse : Function.RightInverse (@swap α β) swap :=
  swap_swap
#align prod.swap_right_inverse Prod.swap_rightInverse

/- warning: prod.swap_injective -> Prod.swap_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Function.Injective.{(max (succ u_1) (succ u_2)) (max (succ u_2) (succ u_1))} (Prod.{u_1 u_2} α β) (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Function.Injective.{(max (succ u_1) (succ u_2)) (max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β)
Case conversion may be inaccurate. Consider using '#align prod.swap_injective Prod.swap_injectiveₓ'. -/
theorem swap_injective : Function.Injective (@swap α β) :=
  swap_leftInverse.Injective
#align prod.swap_injective Prod.swap_injective

/- warning: prod.swap_surjective -> Prod.swap_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Function.Surjective.{(max (succ u_1) (succ u_2)) (max (succ u_2) (succ u_1))} (Prod.{u_1 u_2} α β) (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Function.Surjective.{(max (succ u_1) (succ u_2)) (max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β)
Case conversion may be inaccurate. Consider using '#align prod.swap_surjective Prod.swap_surjectiveₓ'. -/
theorem swap_surjective : Function.Surjective (@swap α β) :=
  swap_leftInverse.Surjective
#align prod.swap_surjective Prod.swap_surjective

/- warning: prod.swap_bijective -> Prod.swap_bijective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Function.Bijective.{(max (succ u_1) (succ u_2)) (max (succ u_2) (succ u_1))} (Prod.{u_1 u_2} α β) (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Function.Bijective.{(max (succ u_1) (succ u_2)) (max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β)
Case conversion may be inaccurate. Consider using '#align prod.swap_bijective Prod.swap_bijectiveₓ'. -/
theorem swap_bijective : Function.Bijective (@swap α β) :=
  ⟨swap_injective, swap_surjective⟩
#align prod.swap_bijective Prod.swap_bijective

/- warning: prod.swap_inj -> Prod.swap_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {q : Prod.{u_1 u_2} α β}, Iff (Eq.{(max (succ u_2) (succ u_1))} (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β p) (Prod.swap.{u_1 u_2} α β q)) (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p q)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {q : Prod.{u_1 u_2} α β}, Iff (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_2 u_1} β α) (Prod.swap.{u_1 u_2} α β p) (Prod.swap.{u_1 u_2} α β q)) (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p q)
Case conversion may be inaccurate. Consider using '#align prod.swap_inj Prod.swap_injₓ'. -/
@[simp]
theorem swap_inj {p q : α × β} : swap p = swap q ↔ p = q :=
  swap_injective.eq_iff
#align prod.swap_inj Prod.swap_inj

/- warning: prod.eq_iff_fst_eq_snd_eq -> Prod.eq_iff_fst_eq_snd_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {q : Prod.{u_1 u_2} α β}, Iff (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p q) (And (Eq.{succ u_1} α (Prod.fst.{u_1 u_2} α β p) (Prod.fst.{u_1 u_2} α β q)) (Eq.{succ u_2} β (Prod.snd.{u_1 u_2} α β p) (Prod.snd.{u_1 u_2} α β q)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {q : Prod.{u_1 u_2} α β}, Iff (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p q) (And (Eq.{succ u_1} α (Prod.fst.{u_1 u_2} α β p) (Prod.fst.{u_1 u_2} α β q)) (Eq.{succ u_2} β (Prod.snd.{u_1 u_2} α β p) (Prod.snd.{u_1 u_2} α β q)))
Case conversion may be inaccurate. Consider using '#align prod.eq_iff_fst_eq_snd_eq Prod.eq_iff_fst_eq_snd_eqₓ'. -/
theorem eq_iff_fst_eq_snd_eq : ∀ {p q : α × β}, p = q ↔ p.1 = q.1 ∧ p.2 = q.2
  | ⟨p₁, p₂⟩, ⟨q₁, q₂⟩ => by simp
#align prod.eq_iff_fst_eq_snd_eq Prod.eq_iff_fst_eq_snd_eq

/- warning: prod.fst_eq_iff -> Prod.fst_eq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {x : α}, Iff (Eq.{succ u_1} α (Prod.fst.{u_1 u_2} α β p) x) (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p (Prod.mk.{u_1 u_2} α β x (Prod.snd.{u_1 u_2} α β p)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {x : α}, Iff (Eq.{succ u_1} α (Prod.fst.{u_1 u_2} α β p) x) (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p (Prod.mk.{u_1 u_2} α β x (Prod.snd.{u_1 u_2} α β p)))
Case conversion may be inaccurate. Consider using '#align prod.fst_eq_iff Prod.fst_eq_iffₓ'. -/
theorem fst_eq_iff : ∀ {p : α × β} {x : α}, p.1 = x ↔ p = (x, p.2)
  | ⟨a, b⟩, x => by simp
#align prod.fst_eq_iff Prod.fst_eq_iff

/- warning: prod.snd_eq_iff -> Prod.snd_eq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {x : β}, Iff (Eq.{succ u_2} β (Prod.snd.{u_1 u_2} α β p) x) (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p (Prod.mk.{u_1 u_2} α β (Prod.fst.{u_1 u_2} α β p) x))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {p : Prod.{u_1 u_2} α β} {x : β}, Iff (Eq.{succ u_2} β (Prod.snd.{u_1 u_2} α β p) x) (Eq.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) p (Prod.mk.{u_1 u_2} α β (Prod.fst.{u_1 u_2} α β p) x))
Case conversion may be inaccurate. Consider using '#align prod.snd_eq_iff Prod.snd_eq_iffₓ'. -/
theorem snd_eq_iff : ∀ {p : α × β} {x : β}, p.2 = x ↔ p = (p.1, x)
  | ⟨a, b⟩, x => by simp
#align prod.snd_eq_iff Prod.snd_eq_iff

theorem lex_def (r : α → α → Prop) (s : β → β → Prop) {p q : α × β} :
    Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2 :=
  ⟨fun h => by cases h <;> simp [*], fun h =>
    match p, q, h with
    | (a, b), (c, d), Or.inl h => Lex.left _ _ h
    | (a, b), (c, d), Or.inr ⟨e, h⟩ => by change a = c at e <;> subst e <;> exact lex.right _ h⟩
#align prod.lex_def Prod.lex_def

#print Prod.Lex.decidable /-
instance Lex.decidable [DecidableEq α] (r : α → α → Prop) (s : β → β → Prop) [DecidableRel r] [DecidableRel s] :
    DecidableRel (Prod.Lex r s) := fun p q => decidable_of_decidable_of_iff (by infer_instance) (lex_def r s).symm
#align prod.lex.decidable Prod.Lex.decidable
-/

/- warning: prod.lex.refl_left -> Prod.Lex.refl_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (r : α -> α -> Prop) (s : β -> β -> Prop) [_inst_1 : IsRefl.{u_1} α r] (x : Prod.{u_1 u_2} α β), Prod.Lex.{u_1 u_2} α β r s x x
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (r : α -> α -> Prop) (s : β -> β -> Prop) [inst._@.Mathlib.Data.Prod.Basic._hyg.1855 : IsRefl.{u_1} α r] (x : Prod.{u_1 u_2} α β), Prod.Lex.{u_1 u_2} α β r s x x
Case conversion may be inaccurate. Consider using '#align prod.lex.refl_left Prod.Lex.refl_leftₓ'. -/
@[refl]
theorem Lex.refl_left (r : α → α → Prop) (s : β → β → Prop) [IsRefl α r] : ∀ x, Prod.Lex r s x x
  | (x₁, x₂) => Lex.left _ _ (refl _)
#align prod.lex.refl_left Prod.Lex.refl_left

instance is_refl_left {r : α → α → Prop} {s : β → β → Prop} [IsRefl α r] : IsRefl (α × β) (Lex r s) :=
  ⟨Lex.refl_left _ _⟩
#align prod.is_refl_left Prod.is_refl_left

#print Prod.Lex.refl_right /-
@[refl]
theorem Lex.refl_right (r : α → α → Prop) (s : β → β → Prop) [IsRefl β s] : ∀ x, Prod.Lex r s x x
  | (x₁, x₂) => Lex.right _ (refl _)
#align prod.lex.refl_right Prod.Lex.refl_right
-/

instance is_refl_right {r : α → α → Prop} {s : β → β → Prop} [IsRefl β s] : IsRefl (α × β) (Lex r s) :=
  ⟨Lex.refl_right _ _⟩
#align prod.is_refl_right Prod.is_refl_right

/- warning: prod.lex.trans -> Prod.Lex.trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsTrans.{u_1} α r] [_inst_2 : IsTrans.{u_2} β s] {x : Prod.{u_1 u_2} α β} {y : Prod.{u_1 u_2} α β} {z : Prod.{u_1 u_2} α β}, (Prod.Lex.{u_1 u_2} α β r s x y) -> (Prod.Lex.{u_1 u_2} α β r s y z) -> (Prod.Lex.{u_1 u_2} α β r s x z)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {r : α -> α -> Prop} {s : β -> β -> Prop} [inst._@.Mathlib.Data.Prod.Basic._hyg.2060 : IsTrans.{u_1} α r] [inst._@.Mathlib.Data.Prod.Basic._hyg.2064 : IsTrans.{u_2} β s] {x : Prod.{u_1 u_2} α β} {y : Prod.{u_1 u_2} α β} {z : Prod.{u_1 u_2} α β}, (Prod.Lex.{u_1 u_2} α β r s x y) -> (Prod.Lex.{u_1 u_2} α β r s y z) -> (Prod.Lex.{u_1 u_2} α β r s x z)
Case conversion may be inaccurate. Consider using '#align prod.lex.trans Prod.Lex.transₓ'. -/
@[trans]
theorem Lex.trans {r : α → α → Prop} {s : β → β → Prop} [IsTrans α r] [IsTrans β s] :
    ∀ {x y z : α × β}, Prod.Lex r s x y → Prod.Lex r s y z → Prod.Lex r s x z
  | (x₁, x₂), (y₁, y₂), (z₁, z₂), lex.left _ _ hxy₁, lex.left _ _ hyz₁ => Lex.left _ _ (trans hxy₁ hyz₁)
  | (x₁, x₂), (y₁, y₂), (z₁, z₂), lex.left _ _ hxy₁, lex.right _ hyz₂ => Lex.left _ _ hxy₁
  | (x₁, x₂), (y₁, y₂), (z₁, z₂), lex.right _ _, lex.left _ _ hyz₁ => Lex.left _ _ hyz₁
  | (x₁, x₂), (y₁, y₂), (z₁, z₂), lex.right _ hxy₂, lex.right _ hyz₂ => Lex.right _ (trans hxy₂ hyz₂)
#align prod.lex.trans Prod.Lex.trans

instance {r : α → α → Prop} {s : β → β → Prop} [IsTrans α r] [IsTrans β s] : IsTrans (α × β) (Lex r s) :=
  ⟨fun _ _ _ => Lex.trans⟩

instance {r : α → α → Prop} {s : β → β → Prop} [IsStrictOrder α r] [IsAntisymm β s] : IsAntisymm (α × β) (Lex r s) :=
  ⟨fun x₁ x₂ h₁₂ h₂₁ =>
    match x₁, x₂, h₁₂, h₂₁ with
    | (a₁, b₁), (a₂, b₂), lex.left _ _ hr₁, lex.left _ _ hr₂ => (irrefl a₁ (trans hr₁ hr₂)).elim
    | (a₁, b₁), (a₂, b₂), lex.left _ _ hr₁, lex.right _ _ => (irrefl _ hr₁).elim
    | (a₁, b₁), (a₂, b₂), lex.right _ _, lex.left _ _ hr₂ => (irrefl _ hr₂).elim
    | (a₁, b₁), (a₂, b₂), lex.right _ hs₁, lex.right _ hs₂ => antisymm hs₁ hs₂ ▸ rfl⟩

#print Prod.is_total_left /-
instance is_total_left {r : α → α → Prop} {s : β → β → Prop} [IsTotal α r] : IsTotal (α × β) (Lex r s) :=
  ⟨fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => (IsTotal.total a₁ a₂).imp (Lex.left _ _) (Lex.left _ _)⟩
#align prod.is_total_left Prod.is_total_left
-/

#print Prod.is_total_right /-
instance is_total_right {r : α → α → Prop} {s : β → β → Prop} [IsTrichotomous α r] [IsTotal β s] :
    IsTotal (α × β) (Lex r s) :=
  ⟨fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (lex.left _ _ hij)
      
    · exact (total_of s a b).imp (lex.right _) (lex.right _)
      
    · exact Or.inr (lex.left _ _ hji)
      ⟩
#align prod.is_total_right Prod.is_total_right
-/

end Prod

open Prod

namespace Function

variable {f : α → γ} {g : β → δ} {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α} {g₂ : δ → γ}

/- warning: function.injective.prod_map -> Function.Injective.Prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} {f : α -> γ} {g : β -> δ}, (Function.Injective.{succ u_1 succ u_3} α γ f) -> (Function.Injective.{succ u_2 succ u_4} β δ g) -> (Function.Injective.{(max (succ u_1) (succ u_2)) (max (succ u_3) (succ u_4))} (Prod.{u_1 u_2} α β) (Prod.{u_3 u_4} γ δ) (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_2}} {δ : Type.{u_4}} {f : α -> γ} {g : β -> δ}, (Function.Injective.{succ u_1 succ u_2} α γ f) -> (Function.Injective.{succ u_3 succ u_4} β δ g) -> (Function.Injective.{(max (succ u_3) (succ u_1)) (max (succ u_4) (succ u_2))} (Prod.{u_1 u_3} α β) (Prod.{u_2 u_4} γ δ) (Prod.map.{u_1 u_2 u_3 u_4} α γ β δ f g))
Case conversion may be inaccurate. Consider using '#align function.injective.prod_map Function.Injective.Prod_mapₓ'. -/
theorem Injective.Prod_map (hf : Injective f) (hg : Injective g) : Injective (map f g) := fun x y h =>
  ext (hf (ext_iff.1 h).1) (hg <| (ext_iff.1 h).2)
#align function.injective.prod_map Function.Injective.Prod_map

/- warning: function.surjective.prod_map -> Function.Surjective.Prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} {f : α -> γ} {g : β -> δ}, (Function.Surjective.{succ u_1 succ u_3} α γ f) -> (Function.Surjective.{succ u_2 succ u_4} β δ g) -> (Function.Surjective.{(max (succ u_1) (succ u_2)) (max (succ u_3) (succ u_4))} (Prod.{u_1 u_2} α β) (Prod.{u_3 u_4} γ δ) (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_2}} {δ : Type.{u_4}} {f : α -> γ} {g : β -> δ}, (Function.Surjective.{succ u_1 succ u_2} α γ f) -> (Function.Surjective.{succ u_3 succ u_4} β δ g) -> (Function.Surjective.{(max (succ u_3) (succ u_1)) (max (succ u_4) (succ u_2))} (Prod.{u_1 u_3} α β) (Prod.{u_2 u_4} γ δ) (Prod.map.{u_1 u_2 u_3 u_4} α γ β δ f g))
Case conversion may be inaccurate. Consider using '#align function.surjective.prod_map Function.Surjective.Prod_mapₓ'. -/
theorem Surjective.Prod_map (hf : Surjective f) (hg : Surjective g) : Surjective (map f g) := fun p =>
  let ⟨x, hx⟩ := hf p.1
  let ⟨y, hy⟩ := hg p.2
  ⟨(x, y), Prod.ext hx hy⟩
#align function.surjective.prod_map Function.Surjective.Prod_map

/- warning: function.bijective.prod_map -> Function.Bijective.Prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} {f : α -> γ} {g : β -> δ}, (Function.Bijective.{succ u_1 succ u_3} α γ f) -> (Function.Bijective.{succ u_2 succ u_4} β δ g) -> (Function.Bijective.{(max (succ u_1) (succ u_2)) (max (succ u_3) (succ u_4))} (Prod.{u_1 u_2} α β) (Prod.{u_3 u_4} γ δ) (Prod.map.{u_1 u_3 u_2 u_4} α γ β δ f g))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_3}} {γ : Type.{u_2}} {δ : Type.{u_4}} {f : α -> γ} {g : β -> δ}, (Function.Bijective.{succ u_1 succ u_2} α γ f) -> (Function.Bijective.{succ u_3 succ u_4} β δ g) -> (Function.Bijective.{(max (succ u_3) (succ u_1)) (max (succ u_4) (succ u_2))} (Prod.{u_1 u_3} α β) (Prod.{u_2 u_4} γ δ) (Prod.map.{u_1 u_2 u_3 u_4} α γ β δ f g))
Case conversion may be inaccurate. Consider using '#align function.bijective.prod_map Function.Bijective.Prod_mapₓ'. -/
theorem Bijective.Prod_map (hf : Bijective f) (hg : Bijective g) : Bijective (map f g) :=
  ⟨hf.1.prod_map hg.1, hf.2.prod_map hg.2⟩
#align function.bijective.prod_map Function.Bijective.Prod_map

/- warning: function.left_inverse.prod_map -> Function.LeftInverse.Prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} {f₁ : α -> β} {g₁ : γ -> δ} {f₂ : β -> α} {g₂ : δ -> γ}, (Function.LeftInverse.{succ u_2 succ u_1} β α f₁ f₂) -> (Function.LeftInverse.{succ u_4 succ u_3} δ γ g₁ g₂) -> (Function.LeftInverse.{(max (succ u_2) (succ u_4)) (max (succ u_1) (succ u_3))} (Prod.{u_2 u_4} β δ) (Prod.{u_1 u_3} α γ) (Prod.map.{u_1 u_2 u_3 u_4} α β γ δ f₁ g₁) (Prod.map.{u_2 u_1 u_4 u_3} β α δ γ f₂ g₂))
but is expected to have type
  forall {α : Type.{u_2}} {β : Type.{u_1}} {γ : Type.{u_4}} {δ : Type.{u_3}} {f₁ : α -> β} {g₁ : γ -> δ} {f₂ : β -> α} {g₂ : δ -> γ}, (Function.LeftInverse.{succ u_1 succ u_2} β α f₁ f₂) -> (Function.LeftInverse.{succ u_3 succ u_4} δ γ g₁ g₂) -> (Function.LeftInverse.{(max (succ u_3) (succ u_1)) (max (succ u_4) (succ u_2))} (Prod.{u_1 u_3} β δ) (Prod.{u_2 u_4} α γ) (Prod.map.{u_2 u_1 u_4 u_3} α β γ δ f₁ g₁) (Prod.map.{u_1 u_2 u_3 u_4} β α δ γ f₂ g₂))
Case conversion may be inaccurate. Consider using '#align function.left_inverse.prod_map Function.LeftInverse.Prod_mapₓ'. -/
theorem LeftInverse.Prod_map (hf : LeftInverse f₁ f₂) (hg : LeftInverse g₁ g₂) : LeftInverse (map f₁ g₁) (map f₂ g₂) :=
  fun a => by rw [Prod.map_map, hf.comp_eq_id, hg.comp_eq_id, map_id, id]
#align function.left_inverse.prod_map Function.LeftInverse.Prod_map

/- warning: function.right_inverse.prod_map -> Function.RightInverse.Prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {γ : Type.{u_3}} {δ : Type.{u_4}} {f₁ : α -> β} {g₁ : γ -> δ} {f₂ : β -> α} {g₂ : δ -> γ}, (Function.RightInverse.{succ u_2 succ u_1} β α f₁ f₂) -> (Function.RightInverse.{succ u_4 succ u_3} δ γ g₁ g₂) -> (Function.RightInverse.{(max (succ u_2) (succ u_4)) (max (succ u_1) (succ u_3))} (Prod.{u_2 u_4} β δ) (Prod.{u_1 u_3} α γ) (Prod.map.{u_1 u_2 u_3 u_4} α β γ δ f₁ g₁) (Prod.map.{u_2 u_1 u_4 u_3} β α δ γ f₂ g₂))
but is expected to have type
  forall {α : Type.{u_2}} {β : Type.{u_1}} {γ : Type.{u_4}} {δ : Type.{u_3}} {f₁ : α -> β} {g₁ : γ -> δ} {f₂ : β -> α} {g₂ : δ -> γ}, (Function.RightInverse.{succ u_1 succ u_2} β α f₁ f₂) -> (Function.RightInverse.{succ u_3 succ u_4} δ γ g₁ g₂) -> (Function.RightInverse.{(max (succ u_3) (succ u_1)) (max (succ u_4) (succ u_2))} (Prod.{u_1 u_3} β δ) (Prod.{u_2 u_4} α γ) (Prod.map.{u_2 u_1 u_4 u_3} α β γ δ f₁ g₁) (Prod.map.{u_1 u_2 u_3 u_4} β α δ γ f₂ g₂))
Case conversion may be inaccurate. Consider using '#align function.right_inverse.prod_map Function.RightInverse.Prod_mapₓ'. -/
theorem RightInverse.Prod_map : RightInverse f₁ f₂ → RightInverse g₁ g₂ → RightInverse (map f₁ g₁) (map f₂ g₂) :=
  left_inverse.prod_map
#align function.right_inverse.prod_map Function.RightInverse.Prod_map

/- warning: function.involutive.prod_map -> Function.Involutive.Prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} {f : α -> α} {g : β -> β}, (Function.Involutive.{succ u_1} α f) -> (Function.Involutive.{succ u_2} β g) -> (Function.Involutive.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β) (Prod.map.{u_1 u_1 u_2 u_2} α α β β f g))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} {f : α -> α} {g : β -> β}, (Function.Involutive.{succ u_1} α f) -> (Function.Involutive.{succ u_2} β g) -> (Function.Involutive.{(max (succ u_2) (succ u_1))} (Prod.{u_1 u_2} α β) (Prod.map.{u_1 u_1 u_2 u_2} α α β β f g))
Case conversion may be inaccurate. Consider using '#align function.involutive.prod_map Function.Involutive.Prod_mapₓ'. -/
theorem Involutive.Prod_map {f : α → α} {g : β → β} : Involutive f → Involutive g → Involutive (map f g) :=
  left_inverse.prod_map
#align function.involutive.prod_map Function.Involutive.Prod_map

end Function

