/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.sigma.basic
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Meta.Univs
import Mathbin.Tactic.Lint.Default
import Mathbin.Tactic.Ext
import Mathbin.Logic.Function.Basic

/-!
# Sigma types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic results about sigma types.

A sigma type is a dependent pair type. Like `α × β` but where the type of the second component
depends on the first component. This can be seen as a generalization of the sum type `α ⊕ β`:
* `α ⊕ β` is made of stuff which is either of type `α` or `β`.
* Given `α : ι → Type*`, `sigma α` is made of stuff which is of type `α i` for some `i : ι`. One
  effectively recovers a type isomorphic to `α ⊕ β` by taking a `ι` with exactly two elements. See
  `equiv.sum_equiv_sigma_bool`.

`Σ x, A x` is notation for `sigma A` (note the difference with the big operator `∑`).
`Σ x y z ..., A x y z ...` is notation for `Σ x, Σ y, Σ z, ..., A x y z ...`. Here we have
`α : Type*`, `β : α → Type*`, `γ : Π a : α, β a → Type*`, ...,
`A : Π (a : α) (b : β a) (c : γ a b) ..., Type*`  with `x : α` `y : β x`, `z : γ x y`, ...

## Notes

The definition of `sigma` takes values in `Type*`. This effectively forbids `Prop`- valued sigma
types. To that effect, we have `psigma`, which takes value in `Sort*` and carries a more complicated
universe signature in consequence.
-/


section Sigma

variable {α α₁ α₂ : Type _} {β : α → Type _} {β₁ : α₁ → Type _} {β₂ : α₂ → Type _}

namespace Sigma

instance [Inhabited α] [Inhabited (β default)] : Inhabited (Sigma β) :=
  ⟨⟨default, default⟩⟩

instance [h₁ : DecidableEq α] [h₂ : ∀ a, DecidableEq (β a)] : DecidableEq (Sigma β)
  | ⟨a₁, b₁⟩, ⟨a₂, b₂⟩ =>
    match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
    | _, b₁, _, b₂, is_true (Eq.refl a) =>
      match b₁, b₂, h₂ a b₁ b₂ with
      | _, _, is_true (Eq.refl b) => isTrue rfl
      | b₁, b₂, is_false n => isFalse fun h => Sigma.noConfusion h fun e₁ e₂ => n <| eq_of_hEq e₂
    | a₁, _, a₂, _, is_false n => isFalse fun h => Sigma.noConfusion h fun e₁ e₂ => n e₁

/- warning: sigma.mk.inj_iff -> Sigma.mk.inj_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {a₁ : α} {a₂ : α} {b₁ : β a₁} {b₂ : β a₂}, Iff (Eq.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun {a₁ : α} => β a₁)) (Sigma.mk.{u1, u2} α (fun {a₁ : α} => β a₁) a₁ b₁) (Sigma.mk.{u1, u2} α (fun {a₁ : α} => β a₁) a₂ b₂)) (And (Eq.{succ u1} α a₁ a₂) (HEq.{succ u2} (β a₁) b₁ (β a₂) b₂))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} {a₁ : α} {a₂ : α} {b₁ : β a₁} {b₂ : β a₂}, Iff (Eq.{max (succ u2) (succ u1)} (Sigma.{u2, u1} α β) (Sigma.mk.{u2, u1} α β a₁ b₁) (Sigma.mk.{u2, u1} α β a₂ b₂)) (And (Eq.{succ u2} α a₁ a₂) (HEq.{succ u1} (β a₁) b₁ (β a₂) b₂))
Case conversion may be inaccurate. Consider using '#align sigma.mk.inj_iff Sigma.mk.inj_iffₓ'. -/
-- sometimes the built-in injectivity support does not work
@[simp, nolint simp_nf]
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ HEq b₁ b₂ := by simp
#align sigma.mk.inj_iff Sigma.mk.inj_iff

/- warning: sigma.eta -> Sigma.eta is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} (x : Sigma.{u1, u2} α (fun (a : α) => β a)), Eq.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α β) (Sigma.mk.{u1, u2} α β (Sigma.fst.{u1, u2} α (fun (a : α) => β a) x) (Sigma.snd.{u1, u2} α (fun (a : α) => β a) x)) x
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} (x : Sigma.{u2, u1} α (fun (a : α) => β a)), Eq.{max (succ u2) (succ u1)} (Sigma.{u2, u1} α β) (Sigma.mk.{u2, u1} α β (Sigma.fst.{u2, u1} α (fun (a : α) => β a) x) (Sigma.snd.{u2, u1} α (fun (a : α) => β a) x)) x
Case conversion may be inaccurate. Consider using '#align sigma.eta Sigma.etaₓ'. -/
@[simp]
theorem eta : ∀ x : Σa, β a, Sigma.mk x.1 x.2 = x
  | ⟨i, x⟩ => rfl
#align sigma.eta Sigma.eta

/- warning: sigma.ext -> Sigma.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {x₀ : Sigma.{u1, u2} α β} {x₁ : Sigma.{u1, u2} α β}, (Eq.{succ u1} α (Sigma.fst.{u1, u2} α β x₀) (Sigma.fst.{u1, u2} α β x₁)) -> (HEq.{succ u2} (β (Sigma.fst.{u1, u2} α β x₀)) (Sigma.snd.{u1, u2} α β x₀) (β (Sigma.fst.{u1, u2} α β x₁)) (Sigma.snd.{u1, u2} α β x₁)) -> (Eq.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α β) x₀ x₁)
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} {x₀ : Sigma.{u2, u1} α β} {x₁ : Sigma.{u2, u1} α β}, (Eq.{succ u2} α (Sigma.fst.{u2, u1} α β x₀) (Sigma.fst.{u2, u1} α β x₁)) -> (HEq.{succ u1} (β (Sigma.fst.{u2, u1} α β x₀)) (Sigma.snd.{u2, u1} α β x₀) (β (Sigma.fst.{u2, u1} α β x₁)) (Sigma.snd.{u2, u1} α β x₁)) -> (Eq.{max (succ u2) (succ u1)} (Sigma.{u2, u1} α β) x₀ x₁)
Case conversion may be inaccurate. Consider using '#align sigma.ext Sigma.extₓ'. -/
@[ext]
theorem ext {x₀ x₁ : Sigma β} (h₀ : x₀.1 = x₁.1) (h₁ : HEq x₀.2 x₁.2) : x₀ = x₁ :=
  by
  cases x₀
  cases x₁
  cases h₀
  cases h₁
  rfl
#align sigma.ext Sigma.ext

/- warning: sigma.ext_iff -> Sigma.ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {x₀ : Sigma.{u1, u2} α β} {x₁ : Sigma.{u1, u2} α β}, Iff (Eq.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α β) x₀ x₁) (And (Eq.{succ u1} α (Sigma.fst.{u1, u2} α β x₀) (Sigma.fst.{u1, u2} α β x₁)) (HEq.{succ u2} (β (Sigma.fst.{u1, u2} α β x₀)) (Sigma.snd.{u1, u2} α β x₀) (β (Sigma.fst.{u1, u2} α β x₁)) (Sigma.snd.{u1, u2} α β x₁)))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} {x₀ : Sigma.{u2, u1} α β} {x₁ : Sigma.{u2, u1} α β}, Iff (Eq.{max (succ u2) (succ u1)} (Sigma.{u2, u1} α β) x₀ x₁) (And (Eq.{succ u2} α (Sigma.fst.{u2, u1} α β x₀) (Sigma.fst.{u2, u1} α β x₁)) (HEq.{succ u1} (β (Sigma.fst.{u2, u1} α β x₀)) (Sigma.snd.{u2, u1} α β x₀) (β (Sigma.fst.{u2, u1} α β x₁)) (Sigma.snd.{u2, u1} α β x₁)))
Case conversion may be inaccurate. Consider using '#align sigma.ext_iff Sigma.ext_iffₓ'. -/
theorem ext_iff {x₀ x₁ : Sigma β} : x₀ = x₁ ↔ x₀.1 = x₁.1 ∧ HEq x₀.2 x₁.2 :=
  by
  cases x₀
  cases x₁
  exact Sigma.mk.inj_iff
#align sigma.ext_iff Sigma.ext_iff

#print Sigma.subtype_ext /-
/-- A specialized ext lemma for equality of sigma types over an indexed subtype. -/
@[ext]
theorem subtype_ext {β : Type _} {p : α → β → Prop} :
    ∀ {x₀ x₁ : Σa, Subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
  | ⟨a₀, b₀, hb₀⟩, ⟨a₁, b₁, hb₁⟩, rfl, rfl => rfl
#align sigma.subtype_ext Sigma.subtype_ext
-/

#print Sigma.subtype_ext_iff /-
theorem subtype_ext_iff {β : Type _} {p : α → β → Prop} {x₀ x₁ : Σa, Subtype (p a)} :
    x₀ = x₁ ↔ x₀.fst = x₁.fst ∧ (x₀.snd : β) = x₁.snd :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => subtype_ext h₁ h₂⟩
#align sigma.subtype_ext_iff Sigma.subtype_ext_iff
-/

/- warning: sigma.forall -> Sigma.forall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {p : (Sigma.{u1, u2} α (fun (a : α) => β a)) -> Prop}, Iff (forall (x : Sigma.{u1, u2} α (fun (a : α) => β a)), p x) (forall (a : α) (b : β a), p (Sigma.mk.{u1, u2} α (fun (a : α) => β a) a b))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} {p : (Sigma.{u2, u1} α (fun (a : α) => β a)) -> Prop}, Iff (forall (x : Sigma.{u2, u1} α (fun (a : α) => β a)), p x) (forall (a : α) (b : β a), p (Sigma.mk.{u2, u1} α (fun (a : α) => β a) a b))
Case conversion may be inaccurate. Consider using '#align sigma.forall Sigma.forallₓ'. -/
@[simp]
theorem forall {p : (Σa, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩
#align sigma.forall Sigma.forall

/- warning: sigma.exists -> Sigma.exists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {p : (Sigma.{u1, u2} α (fun (a : α) => β a)) -> Prop}, Iff (Exists.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a)) (fun (x : Sigma.{u1, u2} α (fun (a : α) => β a)) => p x)) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u2} (β a) (fun (b : β a) => p (Sigma.mk.{u1, u2} α (fun (a : α) => β a) a b))))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} {p : (Sigma.{u2, u1} α (fun (a : α) => β a)) -> Prop}, Iff (Exists.{max (succ u2) (succ u1)} (Sigma.{u2, u1} α (fun (a : α) => β a)) (fun (x : Sigma.{u2, u1} α (fun (a : α) => β a)) => p x)) (Exists.{succ u2} α (fun (a : α) => Exists.{succ u1} (β a) (fun (b : β a) => p (Sigma.mk.{u2, u1} α (fun (a : α) => β a) a b))))
Case conversion may be inaccurate. Consider using '#align sigma.exists Sigma.existsₓ'. -/
@[simp]
theorem exists {p : (Σa, β a) → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩
#align sigma.exists Sigma.exists

#print Sigma.map /-
/-- Map the left and right components of a sigma -/
def map (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) (x : Sigma β₁) : Sigma β₂ :=
  ⟨f₁ x.1, f₂ x.1 x.2⟩
#align sigma.map Sigma.map
-/

end Sigma

#print sigma_mk_injective /-
theorem sigma_mk_injective {i : α} : Function.Injective (@Sigma.mk α β i)
  | _, _, rfl => rfl
#align sigma_mk_injective sigma_mk_injective
-/

/- warning: function.injective.sigma_map -> Function.Injective.sigma_map is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : α₁ -> Type.{u3}} {β₂ : α₂ -> Type.{u4}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Injective.{succ u1, succ u2} α₁ α₂ f₁) -> (forall (a : α₁), Function.Injective.{succ u3, succ u4} (β₁ a) (β₂ (f₁ a)) (f₂ a)) -> (Function.Injective.{max (succ u1) (succ u3), max (succ u2) (succ u4)} (Sigma.{u1, u3} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u2, u4} α₂ β₂) (Sigma.map.{u1, u2, u3, u4} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂))
but is expected to have type
  forall {α₁ : Type.{u4}} {α₂ : Type.{u3}} {β₁ : α₁ -> Type.{u2}} {β₂ : α₂ -> Type.{u1}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Injective.{succ u4, succ u3} α₁ α₂ f₁) -> (forall (a : α₁), Function.Injective.{succ u2, succ u1} (β₁ a) (β₂ (f₁ a)) (f₂ a)) -> (Function.Injective.{max (succ u2) (succ u4), max (succ u1) (succ u3)} (Sigma.{u4, u2} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u3, u1} α₂ β₂) (Sigma.map.{u4, u3, u2, u1} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂))
Case conversion may be inaccurate. Consider using '#align function.injective.sigma_map Function.Injective.sigma_mapₓ'. -/
theorem Function.Injective.sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h₁ : Function.Injective f₁) (h₂ : ∀ a, Function.Injective (f₂ a)) :
    Function.Injective (Sigma.map f₁ f₂)
  | ⟨i, x⟩, ⟨j, y⟩, h => by
    obtain rfl : i = j; exact h₁ (sigma.mk.inj_iff.mp h).1
    obtain rfl : x = y; exact h₂ i (sigma_mk_injective h)
    rfl
#align function.injective.sigma_map Function.Injective.sigma_map

/- warning: function.injective.of_sigma_map -> Function.Injective.of_sigma_map is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : α₁ -> Type.{u3}} {β₂ : α₂ -> Type.{u4}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Injective.{max (succ u1) (succ u3), max (succ u2) (succ u4)} (Sigma.{u1, u3} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u2, u4} α₂ β₂) (Sigma.map.{u1, u2, u3, u4} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂)) -> (forall (a : α₁), Function.Injective.{succ u3, succ u4} (β₁ a) (β₂ (f₁ a)) (f₂ a))
but is expected to have type
  forall {α₁ : Type.{u3}} {α₂ : Type.{u1}} {β₁ : α₁ -> Type.{u4}} {β₂ : α₂ -> Type.{u2}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Injective.{max (succ u4) (succ u3), max (succ u2) (succ u1)} (Sigma.{u3, u4} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u1, u2} α₂ β₂) (Sigma.map.{u3, u1, u4, u2} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂)) -> (forall (a : α₁), Function.Injective.{succ u4, succ u2} (β₁ a) (β₂ (f₁ a)) (f₂ a))
Case conversion may be inaccurate. Consider using '#align function.injective.of_sigma_map Function.Injective.of_sigma_mapₓ'. -/
theorem Function.Injective.of_sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h : Function.Injective (Sigma.map f₁ f₂)) (a : α₁) : Function.Injective (f₂ a) :=
  fun x y hxy => sigma_mk_injective <| @h ⟨a, x⟩ ⟨a, y⟩ (Sigma.ext rfl (hEq_iff_eq.2 hxy))
#align function.injective.of_sigma_map Function.Injective.of_sigma_map

/- warning: function.injective.sigma_map_iff -> Function.Injective.sigma_map_iff is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : α₁ -> Type.{u3}} {β₂ : α₂ -> Type.{u4}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Injective.{succ u1, succ u2} α₁ α₂ f₁) -> (Iff (Function.Injective.{max (succ u1) (succ u3), max (succ u2) (succ u4)} (Sigma.{u1, u3} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u2, u4} α₂ β₂) (Sigma.map.{u1, u2, u3, u4} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂)) (forall (a : α₁), Function.Injective.{succ u3, succ u4} (β₁ a) (β₂ (f₁ a)) (f₂ a)))
but is expected to have type
  forall {α₁ : Type.{u4}} {α₂ : Type.{u3}} {β₁ : α₁ -> Type.{u2}} {β₂ : α₂ -> Type.{u1}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Injective.{succ u4, succ u3} α₁ α₂ f₁) -> (Iff (Function.Injective.{max (succ u2) (succ u4), max (succ u1) (succ u3)} (Sigma.{u4, u2} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u3, u1} α₂ β₂) (Sigma.map.{u4, u3, u2, u1} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂)) (forall (a : α₁), Function.Injective.{succ u2, succ u1} (β₁ a) (β₂ (f₁ a)) (f₂ a)))
Case conversion may be inaccurate. Consider using '#align function.injective.sigma_map_iff Function.Injective.sigma_map_iffₓ'. -/
theorem Function.Injective.sigma_map_iff {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h₁ : Function.Injective f₁) :
    Function.Injective (Sigma.map f₁ f₂) ↔ ∀ a, Function.Injective (f₂ a) :=
  ⟨fun h => h.of_sigma_map, h₁.sigma_map⟩
#align function.injective.sigma_map_iff Function.Injective.sigma_map_iff

/- warning: function.surjective.sigma_map -> Function.Surjective.sigma_map is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β₁ : α₁ -> Type.{u3}} {β₂ : α₂ -> Type.{u4}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Surjective.{succ u1, succ u2} α₁ α₂ f₁) -> (forall (a : α₁), Function.Surjective.{succ u3, succ u4} (β₁ a) (β₂ (f₁ a)) (f₂ a)) -> (Function.Surjective.{max (succ u1) (succ u3), max (succ u2) (succ u4)} (Sigma.{u1, u3} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u2, u4} α₂ β₂) (Sigma.map.{u1, u2, u3, u4} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂))
but is expected to have type
  forall {α₁ : Type.{u4}} {α₂ : Type.{u3}} {β₁ : α₁ -> Type.{u2}} {β₂ : α₂ -> Type.{u1}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Surjective.{succ u4, succ u3} α₁ α₂ f₁) -> (forall (a : α₁), Function.Surjective.{succ u2, succ u1} (β₁ a) (β₂ (f₁ a)) (f₂ a)) -> (Function.Surjective.{max (succ u2) (succ u4), max (succ u1) (succ u3)} (Sigma.{u4, u2} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u3, u1} α₂ β₂) (Sigma.map.{u4, u3, u2, u1} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂))
Case conversion may be inaccurate. Consider using '#align function.surjective.sigma_map Function.Surjective.sigma_mapₓ'. -/
theorem Function.Surjective.sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h₁ : Function.Surjective f₁) (h₂ : ∀ a, Function.Surjective (f₂ a)) :
    Function.Surjective (Sigma.map f₁ f₂) :=
  by
  simp only [Function.Surjective, Sigma.forall, h₁.forall]
  exact fun i => (h₂ _).forall.2 fun x => ⟨⟨i, x⟩, rfl⟩
#align function.surjective.sigma_map Function.Surjective.sigma_map

#print Sigma.curry /-
/-- Interpret a function on `Σ x : α, β x` as a dependent function with two arguments.

This also exists as an `equiv` as `equiv.Pi_curry γ`. -/
def Sigma.curry {γ : ∀ a, β a → Type _} (f : ∀ x : Sigma β, γ x.1 x.2) (x : α) (y : β x) : γ x y :=
  f ⟨x, y⟩
#align sigma.curry Sigma.curry
-/

#print Sigma.uncurry /-
/-- Interpret a dependent function with two arguments as a function on `Σ x : α, β x`.

This also exists as an `equiv` as `(equiv.Pi_curry γ).symm`. -/
def Sigma.uncurry {γ : ∀ a, β a → Type _} (f : ∀ (x) (y : β x), γ x y) (x : Sigma β) : γ x.1 x.2 :=
  f x.1 x.2
#align sigma.uncurry Sigma.uncurry
-/

/- warning: sigma.uncurry_curry -> Sigma.uncurry_curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {γ : forall (a : α), (β a) -> Type.{u3}} (f : forall (x : Sigma.{u1, u2} α β), γ (Sigma.fst.{u1, u2} α β x) (Sigma.snd.{u1, u2} α β x)), Eq.{max (max (succ u1) (succ u2)) (succ u3)} (forall (x : Sigma.{u1, u2} α (fun (x : α) => β x)), γ (Sigma.fst.{u1, u2} α (fun (x : α) => β x) x) (Sigma.snd.{u1, u2} α (fun (x : α) => β x) x)) (Sigma.uncurry.{u1, u2, u3} α (fun (x : α) => β x) (fun (x : α) (y : β x) => γ x y) (Sigma.curry.{u1, u2, u3} α β γ f)) f
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} {γ : forall (a : α), (β a) -> Type.{u3}} (f : forall (x : Sigma.{u2, u1} α β), γ (Sigma.fst.{u2, u1} α β x) (Sigma.snd.{u2, u1} α β x)), Eq.{max (max (succ u2) (succ u1)) (succ u3)} (forall (x : Sigma.{u2, u1} α (fun (x : α) => β x)), γ (Sigma.fst.{u2, u1} α (fun (x : α) => β x) x) (Sigma.snd.{u2, u1} α (fun (x : α) => β x) x)) (Sigma.uncurry.{u2, u1, u3} α (fun (x : α) => β x) (fun (x : α) (y : β x) => γ x y) (Sigma.curry.{u2, u1, u3} α β γ f)) f
Case conversion may be inaccurate. Consider using '#align sigma.uncurry_curry Sigma.uncurry_curryₓ'. -/
@[simp]
theorem Sigma.uncurry_curry {γ : ∀ a, β a → Type _} (f : ∀ x : Sigma β, γ x.1 x.2) :
    Sigma.uncurry (Sigma.curry f) = f :=
  funext fun ⟨i, j⟩ => rfl
#align sigma.uncurry_curry Sigma.uncurry_curry

/- warning: sigma.curry_uncurry -> Sigma.curry_uncurry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {γ : forall (a : α), (β a) -> Type.{u3}} (f : forall (x : α) (y : β x), γ x y), Eq.{max (succ u1) (succ u2) (succ u3)} (forall (x : α) (y : β x), γ x y) (Sigma.curry.{u1, u2, u3} α (fun (x : α) => β x) (fun (x : α) (y : β x) => γ x y) (Sigma.uncurry.{u1, u2, u3} α (fun (x : α) => β x) (fun (x : α) (y : β x) => γ x y) f)) f
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} {γ : forall (a : α), (β a) -> Type.{u3}} (f : forall (x : α) (y : β x), γ x y), Eq.{max (max (succ u2) (succ u1)) (succ u3)} (forall (x : α) (y : β x), γ x y) (Sigma.curry.{u2, u1, u3} α (fun (x : α) => β x) (fun (x : α) (y : β x) => γ x y) (Sigma.uncurry.{u2, u1, u3} α (fun (x : α) => β x) (fun (x : α) (y : β x) => γ x y) f)) f
Case conversion may be inaccurate. Consider using '#align sigma.curry_uncurry Sigma.curry_uncurryₓ'. -/
@[simp]
theorem Sigma.curry_uncurry {γ : ∀ a, β a → Type _} (f : ∀ (x) (y : β x), γ x y) :
    Sigma.curry (Sigma.uncurry f) = f :=
  rfl
#align sigma.curry_uncurry Sigma.curry_uncurry

#print Prod.toSigma /-
/-- Convert a product type to a Σ-type. -/
def Prod.toSigma {α β} (p : α × β) : Σ_ : α, β :=
  ⟨p.1, p.2⟩
#align prod.to_sigma Prod.toSigma
-/

/- warning: prod.fst_comp_to_sigma -> Prod.fst_comp_toSigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{max (succ u1) (succ u2)} ((Prod.{u1, u2} α β) -> α) (Function.comp.{max (succ u1) (succ u2), max (succ u1) (succ u2), succ u1} (Prod.{u1, u2} α β) (Sigma.{u1, u2} α (fun (_x : α) => β)) α (Sigma.fst.{u1, u2} α (fun (_x : α) => β)) (Prod.toSigma.{u1, u2} α β)) (Prod.fst.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u1) (succ u2)} ((Prod.{u2, u1} α β) -> α) (Function.comp.{max (succ u1) (succ u2), max (succ u1) (succ u2), succ u2} (Prod.{u2, u1} α β) (Sigma.{u2, u1} α (fun (_x : α) => β)) α (Sigma.fst.{u2, u1} α (fun (_x : α) => β)) (Prod.toSigma.{u2, u1} α β)) (Prod.fst.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align prod.fst_comp_to_sigma Prod.fst_comp_toSigmaₓ'. -/
@[simp]
theorem Prod.fst_comp_toSigma {α β} : Sigma.fst ∘ @Prod.toSigma α β = Prod.fst :=
  rfl
#align prod.fst_comp_to_sigma Prod.fst_comp_toSigma

/- warning: prod.fst_to_sigma -> Prod.fst_toSigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (x : Prod.{u1, u2} α β), Eq.{succ u1} α (Sigma.fst.{u1, u2} α (fun (_x : α) => β) (Prod.toSigma.{u1, u2} α β x)) (Prod.fst.{u1, u2} α β x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (x : Prod.{u2, u1} α β), Eq.{succ u2} α (Sigma.fst.{u2, u1} α (fun (_x : α) => β) (Prod.toSigma.{u2, u1} α β x)) (Prod.fst.{u2, u1} α β x)
Case conversion may be inaccurate. Consider using '#align prod.fst_to_sigma Prod.fst_toSigmaₓ'. -/
@[simp]
theorem Prod.fst_toSigma {α β} (x : α × β) : (Prod.toSigma x).fst = x.fst :=
  rfl
#align prod.fst_to_sigma Prod.fst_toSigma

/- warning: prod.snd_to_sigma -> Prod.snd_toSigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (x : Prod.{u1, u2} α β), Eq.{succ u2} β (Sigma.snd.{u1, u2} α (fun (_x : α) => β) (Prod.toSigma.{u1, u2} α β x)) (Prod.snd.{u1, u2} α β x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (x : Prod.{u2, u1} α β), Eq.{succ u1} β (Sigma.snd.{u2, u1} α (fun (_x : α) => β) (Prod.toSigma.{u2, u1} α β x)) (Prod.snd.{u2, u1} α β x)
Case conversion may be inaccurate. Consider using '#align prod.snd_to_sigma Prod.snd_toSigmaₓ'. -/
@[simp]
theorem Prod.snd_toSigma {α β} (x : α × β) : (Prod.toSigma x).snd = x.snd :=
  rfl
#align prod.snd_to_sigma Prod.snd_toSigma

/- warning: prod.to_sigma_mk -> Prod.toSigma_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (x : α) (y : β), Eq.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (_x : α) => β)) (Prod.toSigma.{u1, u2} α β (Prod.mk.{u1, u2} α β x y)) (Sigma.mk.{u1, u2} α (fun (_x : α) => β) x y)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (x : α) (y : β), Eq.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (_x : α) => β)) (Prod.toSigma.{u2, u1} α β (Prod.mk.{u2, u1} α β x y)) (Sigma.mk.{u2, u1} α (fun (_x : α) => β) x y)
Case conversion may be inaccurate. Consider using '#align prod.to_sigma_mk Prod.toSigma_mkₓ'. -/
@[simp]
theorem Prod.toSigma_mk {α β} (x : α) (y : β) : (x, y).toSigma = ⟨x, y⟩ :=
  rfl
#align prod.to_sigma_mk Prod.toSigma_mk

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[] -/
-- we generate this manually as `@[derive has_reflect]` fails
@[instance]
protected unsafe def sigma.reflect.{u, v} [reflected_univ.{u}] [reflected_univ.{v}] {α : Type u}
    (β : α → Type v) [reflected _ α] [reflected _ β] [hα : has_reflect α]
    [hβ : ∀ i, has_reflect (β i)] : has_reflect (Σa, β a) := fun ⟨a, b⟩ =>
  (by
        trace
          "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[]" :
        reflected _ @Sigma.mk.{u, v}).subst₄
    q(α) q(β) q(a) q(b)
#align sigma.reflect sigma.reflect

end Sigma

section PSigma

variable {α : Sort _} {β : α → Sort _}

namespace PSigma

#print PSigma.elim /-
/-- Nondependent eliminator for `psigma`. -/
def elim {γ} (f : ∀ a, β a → γ) (a : PSigma β) : γ :=
  PSigma.casesOn a f
#align psigma.elim PSigma.elim
-/

/- warning: psigma.elim_val -> PSigma.elim_val is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : α -> Sort.{u2}} {γ : Sort.{u3}} (f : forall (a : α), (β a) -> γ) (a : α) (b : β a), Eq.{u3} γ (PSigma.elim.{u1, u2, u3} α (fun (a : α) => β a) γ f (PSigma.mk.{u1, u2} α (fun (a : α) => β a) a b)) (f a b)
but is expected to have type
  forall {α : Sort.{u2}} {β : α -> Sort.{u1}} {γ : Sort.{u3}} (f : forall (a : α), (β a) -> γ) (a : α) (b : β a), Eq.{u3} γ (PSigma.elim.{u2, u1, u3} α (fun (a : α) => β a) γ f (PSigma.mk.{u2, u1} α (fun (a : α) => β a) a b)) (f a b)
Case conversion may be inaccurate. Consider using '#align psigma.elim_val PSigma.elim_valₓ'. -/
@[simp]
theorem elim_val {γ} (f : ∀ a, β a → γ) (a b) : PSigma.elim f ⟨a, b⟩ = f a b :=
  rfl
#align psigma.elim_val PSigma.elim_val

instance [Inhabited α] [Inhabited (β default)] : Inhabited (PSigma β) :=
  ⟨⟨default, default⟩⟩

instance [h₁ : DecidableEq α] [h₂ : ∀ a, DecidableEq (β a)] : DecidableEq (PSigma β)
  | ⟨a₁, b₁⟩, ⟨a₂, b₂⟩ =>
    match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
    | _, b₁, _, b₂, is_true (Eq.refl a) =>
      match b₁, b₂, h₂ a b₁ b₂ with
      | _, _, is_true (Eq.refl b) => isTrue rfl
      | b₁, b₂, is_false n => isFalse fun h => PSigma.noConfusion h fun e₁ e₂ => n <| eq_of_hEq e₂
    | a₁, _, a₂, _, is_false n => isFalse fun h => PSigma.noConfusion h fun e₁ e₂ => n e₁

/- warning: psigma.mk.inj_iff -> PSigma.mk.inj_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : α -> Sort.{u2}} {a₁ : α} {a₂ : α} {b₁ : β a₁} {b₂ : β a₂}, Iff (Eq.{max 1 u1 u2} (PSigma.{u1, u2} α β) (PSigma.mk.{u1, u2} α β a₁ b₁) (PSigma.mk.{u1, u2} α β a₂ b₂)) (And (Eq.{u1} α a₁ a₂) (HEq.{u2} (β a₁) b₁ (β a₂) b₂))
but is expected to have type
  forall {α : Sort.{u2}} {β : α -> Sort.{u1}} {a₁ : α} {a₂ : α} {b₁ : β a₁} {b₂ : β a₂}, Iff (Eq.{max (max 1 u2) u1} (PSigma.{u2, u1} α β) (PSigma.mk.{u2, u1} α β a₁ b₁) (PSigma.mk.{u2, u1} α β a₂ b₂)) (And (Eq.{u2} α a₁ a₂) (HEq.{u1} (β a₁) b₁ (β a₂) b₂))
Case conversion may be inaccurate. Consider using '#align psigma.mk.inj_iff PSigma.mk.inj_iffₓ'. -/
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    @PSigma.mk α β a₁ b₁ = @PSigma.mk α β a₂ b₂ ↔ a₁ = a₂ ∧ HEq b₁ b₂ :=
  Iff.intro PSigma.mk.inj fun ⟨h₁, h₂⟩ =>
    match a₁, a₂, b₁, b₂, h₁, h₂ with
    | _, _, _, _, Eq.refl a, HEq.refl b => rfl
#align psigma.mk.inj_iff PSigma.mk.inj_iff

/- warning: psigma.ext -> PSigma.ext is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : α -> Sort.{u2}} {x₀ : PSigma.{u1, u2} α β} {x₁ : PSigma.{u1, u2} α β}, (Eq.{u1} α (PSigma.fst.{u1, u2} α β x₀) (PSigma.fst.{u1, u2} α β x₁)) -> (HEq.{u2} (β (PSigma.fst.{u1, u2} α β x₀)) (PSigma.snd.{u1, u2} α β x₀) (β (PSigma.fst.{u1, u2} α β x₁)) (PSigma.snd.{u1, u2} α β x₁)) -> (Eq.{max 1 u1 u2} (PSigma.{u1, u2} α β) x₀ x₁)
but is expected to have type
  forall {α : Sort.{u2}} {β : α -> Sort.{u1}} {x₀ : PSigma.{u2, u1} α β} {x₁ : PSigma.{u2, u1} α β}, (Eq.{u2} α (PSigma.fst.{u2, u1} α β x₀) (PSigma.fst.{u2, u1} α β x₁)) -> (HEq.{u1} (β (PSigma.fst.{u2, u1} α β x₀)) (PSigma.snd.{u2, u1} α β x₀) (β (PSigma.fst.{u2, u1} α β x₁)) (PSigma.snd.{u2, u1} α β x₁)) -> (Eq.{max (max 1 u2) u1} (PSigma.{u2, u1} α β) x₀ x₁)
Case conversion may be inaccurate. Consider using '#align psigma.ext PSigma.extₓ'. -/
@[ext]
theorem ext {x₀ x₁ : PSigma β} (h₀ : x₀.1 = x₁.1) (h₁ : HEq x₀.2 x₁.2) : x₀ = x₁ :=
  by
  cases x₀
  cases x₁
  cases h₀
  cases h₁
  rfl
#align psigma.ext PSigma.ext

/- warning: psigma.ext_iff -> PSigma.ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : α -> Sort.{u2}} {x₀ : PSigma.{u1, u2} α β} {x₁ : PSigma.{u1, u2} α β}, Iff (Eq.{max 1 u1 u2} (PSigma.{u1, u2} α β) x₀ x₁) (And (Eq.{u1} α (PSigma.fst.{u1, u2} α β x₀) (PSigma.fst.{u1, u2} α β x₁)) (HEq.{u2} (β (PSigma.fst.{u1, u2} α β x₀)) (PSigma.snd.{u1, u2} α β x₀) (β (PSigma.fst.{u1, u2} α β x₁)) (PSigma.snd.{u1, u2} α β x₁)))
but is expected to have type
  forall {α : Sort.{u2}} {β : α -> Sort.{u1}} {x₀ : PSigma.{u2, u1} α β} {x₁ : PSigma.{u2, u1} α β}, Iff (Eq.{max (max 1 u2) u1} (PSigma.{u2, u1} α β) x₀ x₁) (And (Eq.{u2} α (PSigma.fst.{u2, u1} α β x₀) (PSigma.fst.{u2, u1} α β x₁)) (HEq.{u1} (β (PSigma.fst.{u2, u1} α β x₀)) (PSigma.snd.{u2, u1} α β x₀) (β (PSigma.fst.{u2, u1} α β x₁)) (PSigma.snd.{u2, u1} α β x₁)))
Case conversion may be inaccurate. Consider using '#align psigma.ext_iff PSigma.ext_iffₓ'. -/
theorem ext_iff {x₀ x₁ : PSigma β} : x₀ = x₁ ↔ x₀.1 = x₁.1 ∧ HEq x₀.2 x₁.2 :=
  by
  cases x₀
  cases x₁
  exact PSigma.mk.inj_iff
#align psigma.ext_iff PSigma.ext_iff

/- warning: psigma.forall -> PSigma.forall is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : α -> Sort.{u2}} {p : (PSigma.{u1, u2} α (fun (a : α) => β a)) -> Prop}, Iff (forall (x : PSigma.{u1, u2} α (fun (a : α) => β a)), p x) (forall (a : α) (b : β a), p (PSigma.mk.{u1, u2} α (fun (a : α) => β a) a b))
but is expected to have type
  forall {α : Sort.{u2}} {β : α -> Sort.{u1}} {p : (PSigma.{u2, u1} α (fun (a : α) => β a)) -> Prop}, Iff (forall (x : PSigma.{u2, u1} α (fun (a : α) => β a)), p x) (forall (a : α) (b : β a), p (PSigma.mk.{u2, u1} α (fun (a : α) => β a) a b))
Case conversion may be inaccurate. Consider using '#align psigma.forall PSigma.forallₓ'. -/
@[simp]
theorem forall {p : (Σ'a, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩
#align psigma.forall PSigma.forall

/- warning: psigma.exists -> PSigma.exists is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : α -> Sort.{u2}} {p : (PSigma.{u1, u2} α (fun (a : α) => β a)) -> Prop}, Iff (Exists.{max 1 u1 u2} (PSigma.{u1, u2} α (fun (a : α) => β a)) (fun (x : PSigma.{u1, u2} α (fun (a : α) => β a)) => p x)) (Exists.{u1} α (fun (a : α) => Exists.{u2} (β a) (fun (b : β a) => p (PSigma.mk.{u1, u2} α (fun (a : α) => β a) a b))))
but is expected to have type
  forall {α : Sort.{u2}} {β : α -> Sort.{u1}} {p : (PSigma.{u2, u1} α (fun (a : α) => β a)) -> Prop}, Iff (Exists.{max (max 1 u2) u1} (PSigma.{u2, u1} α (fun (a : α) => β a)) (fun (x : PSigma.{u2, u1} α (fun (a : α) => β a)) => p x)) (Exists.{u2} α (fun (a : α) => Exists.{u1} (β a) (fun (b : β a) => p (PSigma.mk.{u2, u1} α (fun (a : α) => β a) a b))))
Case conversion may be inaccurate. Consider using '#align psigma.exists PSigma.existsₓ'. -/
@[simp]
theorem exists {p : (Σ'a, β a) → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩
#align psigma.exists PSigma.exists

#print PSigma.subtype_ext /-
/-- A specialized ext lemma for equality of psigma types over an indexed subtype. -/
@[ext]
theorem subtype_ext {β : Sort _} {p : α → β → Prop} :
    ∀ {x₀ x₁ : Σ'a, Subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
  | ⟨a₀, b₀, hb₀⟩, ⟨a₁, b₁, hb₁⟩, rfl, rfl => rfl
#align psigma.subtype_ext PSigma.subtype_ext
-/

#print PSigma.subtype_ext_iff /-
theorem subtype_ext_iff {β : Sort _} {p : α → β → Prop} {x₀ x₁ : Σ'a, Subtype (p a)} :
    x₀ = x₁ ↔ x₀.fst = x₁.fst ∧ (x₀.snd : β) = x₁.snd :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => subtype_ext h₁ h₂⟩
#align psigma.subtype_ext_iff PSigma.subtype_ext_iff
-/

variable {α₁ : Sort _} {α₂ : Sort _} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _}

#print PSigma.map /-
/-- Map the left and right components of a sigma -/
def map (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) : PSigma β₁ → PSigma β₂
  | ⟨a, b⟩ => ⟨f₁ a, f₂ a b⟩
#align psigma.map PSigma.map
-/

end PSigma

end PSigma

