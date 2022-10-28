/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Meta.Univs
import Mathbin.Tactic.Lint.Default
import Mathbin.Tactic.Ext

/-!
THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
https://github.com/leanprover-community/mathlib4/pull/449
Any changes to this file require a corresponding PR to mathlib4.

# Sigma types

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
      | b₁, b₂, is_false n => isFalse fun h => Sigma.noConfusion h fun e₁ e₂ => n <| eq_of_heq e₂
    | a₁, _, a₂, _, is_false n => isFalse fun h => Sigma.noConfusion h fun e₁ e₂ => n e₁

/- warning: sigma.mk.inj_iff -> Sigma.mk.inj_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : α -> Type.{u_4}} {a₁ : α} {a₂ : α} {b₁ : β a₁} {b₂ : β a₂}, Iff (Eq.{(max (succ u_1) (succ u_4))} (Sigma.{u_1 u_4} α (fun {a₁ : α} => β a₁)) (Sigma.mk.{u_1 u_4} α (fun {a₁ : α} => β a₁) a₁ b₁) (Sigma.mk.{u_1 u_4} α (fun {a₁ : α} => β a₁) a₂ b₂)) (And (Eq.{succ u_1} α a₁ a₂) (HEq.{succ u_4} (β a₁) b₁ (β a₂) b₂))
but is expected to have type
  forall {α : Type.{u_1}} {β : α -> Type.{u_2}} {a₁ : α} {a₂ : α} {b₁ : β a₁} {b₂ : β a₂}, Iff (Eq.{(max (succ u_1) (succ u_2))} (Sigma.{u_1 u_2} α β) (Sigma.mk.{u_1 u_2} α β a₁ b₁) (Sigma.mk.{u_1 u_2} α β a₂ b₂)) (And (Eq.{succ u_1} α a₁ a₂) (HEq.{succ u_2} (β a₁) b₁ (β a₂) b₂))
Case conversion may be inaccurate. Consider using '#align sigma.mk.inj_iff Sigma.mk.inj_iffₓ'. -/
-- sometimes the built-in injectivity support does not work
@[simp, nolint simp_nf]
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} : Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ HEq b₁ b₂ := by simp

/- warning: sigma.eta -> Sigma.eta is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : α -> Type.{u_4}} (x : Sigma.{u_1 u_4} α (fun (a : α) => β a)), Eq.{(max (succ u_1) (succ u_4))} (Sigma.{u_1 u_4} α β) (Sigma.mk.{u_1 u_4} α β (Sigma.fst.{u_1 u_4} α (fun (a : α) => β a) x) (Sigma.snd.{u_1 u_4} α (fun (a : α) => β a) x)) x
but is expected to have type
  forall {α : Type.{u_1}} {β : α -> Type.{u_2}} (x : Sigma.{u_1 u_2} α (fun (a : α) => β a)), Eq.{(max (succ u_1) (succ u_2))} (Sigma.{u_1 u_2} α β) (Sigma.mk.{u_1 u_2} α β (Sigma.fst.{u_1 u_2} α (fun (a : α) => β a) x) (Sigma.snd.{u_1 u_2} α (fun (a : α) => β a) x)) x
Case conversion may be inaccurate. Consider using '#align sigma.eta Sigma.etaₓ'. -/
@[simp]
theorem eta : ∀ x : Σa, β a, Sigma.mk x.1 x.2 = x
  | ⟨i, x⟩ => rfl

/- warning: sigma.ext -> Sigma.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : α -> Type.{u_4}} {x₀ : Sigma.{u_1 u_4} α β} {x₁ : Sigma.{u_1 u_4} α β}, (Eq.{succ u_1} α (Sigma.fst.{u_1 u_4} α β x₀) (Sigma.fst.{u_1 u_4} α β x₁)) -> (HEq.{succ u_4} (β (Sigma.fst.{u_1 u_4} α β x₀)) (Sigma.snd.{u_1 u_4} α β x₀) (β (Sigma.fst.{u_1 u_4} α β x₁)) (Sigma.snd.{u_1 u_4} α β x₁)) -> (Eq.{(max (succ u_1) (succ u_4))} (Sigma.{u_1 u_4} α β) x₀ x₁)
but is expected to have type
  forall {α : Type.{u_1}} {β : α -> Type.{u_2}} {x₀ : Sigma.{u_1 u_2} α β} {x₁ : Sigma.{u_1 u_2} α β}, (Eq.{succ u_1} α (Sigma.fst.{u_1 u_2} α β x₀) (Sigma.fst.{u_1 u_2} α β x₁)) -> (HEq.{succ u_2} (β (Sigma.fst.{u_1 u_2} α β x₀)) (Sigma.snd.{u_1 u_2} α β x₀) (β (Sigma.fst.{u_1 u_2} α β x₁)) (Sigma.snd.{u_1 u_2} α β x₁)) -> (Eq.{(max (succ u_1) (succ u_2))} (Sigma.{u_1 u_2} α β) x₀ x₁)
Case conversion may be inaccurate. Consider using '#align sigma.ext Sigma.extₓ'. -/
@[ext]
theorem ext {x₀ x₁ : Sigma β} (h₀ : x₀.1 = x₁.1) (h₁ : HEq x₀.2 x₁.2) : x₀ = x₁ := by
  cases x₀
  cases x₁
  cases h₀
  cases h₁
  rfl

/- warning: sigma.ext_iff -> Sigma.ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : α -> Type.{u_4}} {x₀ : Sigma.{u_1 u_4} α β} {x₁ : Sigma.{u_1 u_4} α β}, Iff (Eq.{(max (succ u_1) (succ u_4))} (Sigma.{u_1 u_4} α β) x₀ x₁) (And (Eq.{succ u_1} α (Sigma.fst.{u_1 u_4} α β x₀) (Sigma.fst.{u_1 u_4} α β x₁)) (HEq.{succ u_4} (β (Sigma.fst.{u_1 u_4} α β x₀)) (Sigma.snd.{u_1 u_4} α β x₀) (β (Sigma.fst.{u_1 u_4} α β x₁)) (Sigma.snd.{u_1 u_4} α β x₁)))
but is expected to have type
  forall {α : Type.{u_1}} {β : α -> Type.{u_2}} {x₀ : Sigma.{u_1 u_2} α β} {x₁ : Sigma.{u_1 u_2} α β}, Iff (Eq.{(max (succ u_1) (succ u_2))} (Sigma.{u_1 u_2} α β) x₀ x₁) (And (Eq.{succ u_1} α (Sigma.fst.{u_1 u_2} α β x₀) (Sigma.fst.{u_1 u_2} α β x₁)) (HEq.{succ u_2} (β (Sigma.fst.{u_1 u_2} α β x₀)) (Sigma.snd.{u_1 u_2} α β x₀) (β (Sigma.fst.{u_1 u_2} α β x₁)) (Sigma.snd.{u_1 u_2} α β x₁)))
Case conversion may be inaccurate. Consider using '#align sigma.ext_iff Sigma.ext_iffₓ'. -/
theorem ext_iff {x₀ x₁ : Sigma β} : x₀ = x₁ ↔ x₀.1 = x₁.1 ∧ HEq x₀.2 x₁.2 := by
  cases x₀
  cases x₁
  exact Sigma.mk.inj_iff

/-- A specialized ext lemma for equality of sigma types over an indexed subtype. -/
@[ext]
theorem subtype_ext {β : Type _} {p : α → β → Prop} :
    ∀ {x₀ x₁ : Σa, Subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
  | ⟨a₀, b₀, hb₀⟩, ⟨a₁, b₁, hb₁⟩, rfl, rfl => rfl

theorem subtype_ext_iff {β : Type _} {p : α → β → Prop} {x₀ x₁ : Σa, Subtype (p a)} :
    x₀ = x₁ ↔ x₀.fst = x₁.fst ∧ (x₀.snd : β) = x₁.snd :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => subtype_ext h₁ h₂⟩

/- warning: sigma.forall -> Sigma.forall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : α -> Type.{u_4}} {p : (Sigma.{u_1 u_4} α (fun (a : α) => β a)) -> Prop}, Iff (forall (x : Sigma.{u_1 u_4} α (fun (a : α) => β a)), p x) (forall (a : α) (b : β a), p (Sigma.mk.{u_1 u_4} α (fun (a : α) => β a) a b))
but is expected to have type
  forall {α : Type.{u_1}} {β : α -> Type.{u_2}} {p : (Sigma.{u_1 u_2} α (fun (a : α) => β a)) -> Prop}, Iff (forall (x : Sigma.{u_1 u_2} α (fun (a : α) => β a)), p x) (forall (a : α) (b : β a), p (Sigma.mk.{u_1 u_2} α (fun (a : α) => β a) a b))
Case conversion may be inaccurate. Consider using '#align sigma.forall Sigma.forallₓ'. -/
@[simp]
theorem forall {p : (Σa, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

/- warning: sigma.exists -> Sigma.exists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : α -> Type.{u_4}} {p : (Sigma.{u_1 u_4} α (fun (a : α) => β a)) -> Prop}, Iff (Exists.{(max (succ u_1) (succ u_4))} (Sigma.{u_1 u_4} α (fun (a : α) => β a)) (fun (x : Sigma.{u_1 u_4} α (fun (a : α) => β a)) => p x)) (Exists.{succ u_1} α (fun (a : α) => Exists.{succ u_4} (β a) (fun (b : β a) => p (Sigma.mk.{u_1 u_4} α (fun (a : α) => β a) a b))))
but is expected to have type
  forall {α : Type.{u_1}} {β : α -> Type.{u_2}} {p : (Sigma.{u_1 u_2} α (fun (a : α) => β a)) -> Prop}, Iff (Exists.{(max (succ u_1) (succ u_2))} (Sigma.{u_1 u_2} α (fun (a : α) => β a)) (fun (x : Sigma.{u_1 u_2} α (fun (a : α) => β a)) => p x)) (Exists.{succ u_1} α (fun (a : α) => Exists.{succ u_2} (β a) (fun (b : β a) => p (Sigma.mk.{u_1 u_2} α (fun (a : α) => β a) a b))))
Case conversion may be inaccurate. Consider using '#align sigma.exists Sigma.existsₓ'. -/
@[simp]
theorem exists {p : (Σa, β a) → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

/-- Map the left and right components of a sigma -/
def map (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) (x : Sigma β₁) : Sigma β₂ :=
  ⟨f₁ x.1, f₂ x.1 x.2⟩

end Sigma

theorem sigma_mk_injective {i : α} : Function.Injective (@Sigma.mk α β i)
  | _, _, rfl => rfl

/- warning: function.injective.sigma_map -> Function.Injective.sigma_map is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u_2}} {α₂ : Type.{u_3}} {β₁ : α₁ -> Type.{u_5}} {β₂ : α₂ -> Type.{u_6}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Injective.{succ u_2 succ u_3} α₁ α₂ f₁) -> (forall (a : α₁), Function.Injective.{succ u_5 succ u_6} (β₁ a) (β₂ (f₁ a)) (f₂ a)) -> (Function.Injective.{(max (succ u_2) (succ u_5)) (max (succ u_3) (succ u_6))} (Sigma.{u_2 u_5} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u_3 u_6} α₂ β₂) (Sigma.map.{u_2 u_3 u_5 u_6} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂))
but is expected to have type
  forall {α₁ : Type.{u_1}} {α₂ : Type.{u_2}} {β₁ : α₁ -> Type.{u_3}} {β₂ : α₂ -> Type.{u_4}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Injective.{succ u_1 succ u_2} α₁ α₂ f₁) -> (forall (a : α₁), Function.Injective.{succ u_3 succ u_4} (β₁ a) (β₂ (f₁ a)) (f₂ a)) -> (Function.Injective.{(max (succ u_3) (succ u_1)) (max (succ u_4) (succ u_2))} (Sigma.{u_1 u_3} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u_2 u_4} α₂ β₂) (Sigma.map.{u_1 u_2 u_3 u_4} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂))
Case conversion may be inaccurate. Consider using '#align function.injective.sigma_map Function.Injective.sigma_mapₓ'. -/
theorem Function.Injective.sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)} (h₁ : Function.Injective f₁)
    (h₂ : ∀ a, Function.Injective (f₂ a)) : Function.Injective (Sigma.map f₁ f₂)
  | ⟨i, x⟩, ⟨j, y⟩, h => by
    obtain rfl : i = j
    exact h₁ (sigma.mk.inj_iff.mp h).1
    obtain rfl : x = y
    exact h₂ i (sigma_mk_injective h)
    rfl

/- warning: function.injective.of_sigma_map -> Function.Injective.of_sigma_map is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u_2}} {α₂ : Type.{u_3}} {β₁ : α₁ -> Type.{u_5}} {β₂ : α₂ -> Type.{u_6}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Injective.{(max (succ u_2) (succ u_5)) (max (succ u_3) (succ u_6))} (Sigma.{u_2 u_5} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u_3 u_6} α₂ β₂) (Sigma.map.{u_2 u_3 u_5 u_6} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂)) -> (forall (a : α₁), Function.Injective.{succ u_5 succ u_6} (β₁ a) (β₂ (f₁ a)) (f₂ a))
but is expected to have type
  forall {α₁ : Type.{u_2}} {α₂ : Type.{u_4}} {β₁ : α₁ -> Type.{u_1}} {β₂ : α₂ -> Type.{u_3}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Injective.{(max (succ u_1) (succ u_2)) (max (succ u_3) (succ u_4))} (Sigma.{u_2 u_1} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u_4 u_3} α₂ β₂) (Sigma.map.{u_2 u_4 u_1 u_3} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂)) -> (forall (a : α₁), Function.Injective.{succ u_1 succ u_3} (β₁ a) (β₂ (f₁ a)) (f₂ a))
Case conversion may be inaccurate. Consider using '#align function.injective.of_sigma_map Function.Injective.of_sigma_mapₓ'. -/
theorem Function.Injective.of_sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h : Function.Injective (Sigma.map f₁ f₂)) (a : α₁) : Function.Injective (f₂ a) := fun x y hxy =>
  sigma_mk_injective <| @h ⟨a, x⟩ ⟨a, y⟩ (Sigma.ext rfl (heq_iff_eq.2 hxy))

/- warning: function.injective.sigma_map_iff -> Function.Injective.sigma_map_iff is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u_2}} {α₂ : Type.{u_3}} {β₁ : α₁ -> Type.{u_5}} {β₂ : α₂ -> Type.{u_6}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Injective.{succ u_2 succ u_3} α₁ α₂ f₁) -> (Iff (Function.Injective.{(max (succ u_2) (succ u_5)) (max (succ u_3) (succ u_6))} (Sigma.{u_2 u_5} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u_3 u_6} α₂ β₂) (Sigma.map.{u_2 u_3 u_5 u_6} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂)) (forall (a : α₁), Function.Injective.{succ u_5 succ u_6} (β₁ a) (β₂ (f₁ a)) (f₂ a)))
but is expected to have type
  forall {α₁ : Type.{u_1}} {α₂ : Type.{u_2}} {β₁ : α₁ -> Type.{u_3}} {β₂ : α₂ -> Type.{u_4}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Injective.{succ u_1 succ u_2} α₁ α₂ f₁) -> (Iff (Function.Injective.{(max (succ u_3) (succ u_1)) (max (succ u_4) (succ u_2))} (Sigma.{u_1 u_3} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u_2 u_4} α₂ β₂) (Sigma.map.{u_1 u_2 u_3 u_4} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂)) (forall (a : α₁), Function.Injective.{succ u_3 succ u_4} (β₁ a) (β₂ (f₁ a)) (f₂ a)))
Case conversion may be inaccurate. Consider using '#align function.injective.sigma_map_iff Function.Injective.sigma_map_iffₓ'. -/
theorem Function.Injective.sigma_map_iff {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)} (h₁ : Function.Injective f₁) :
    Function.Injective (Sigma.map f₁ f₂) ↔ ∀ a, Function.Injective (f₂ a) :=
  ⟨fun h => h.of_sigma_map, h₁.sigma_map⟩

/- warning: function.surjective.sigma_map -> Function.Surjective.sigma_map is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u_2}} {α₂ : Type.{u_3}} {β₁ : α₁ -> Type.{u_5}} {β₂ : α₂ -> Type.{u_6}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Surjective.{succ u_2 succ u_3} α₁ α₂ f₁) -> (forall (a : α₁), Function.Surjective.{succ u_5 succ u_6} (β₁ a) (β₂ (f₁ a)) (f₂ a)) -> (Function.Surjective.{(max (succ u_2) (succ u_5)) (max (succ u_3) (succ u_6))} (Sigma.{u_2 u_5} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u_3 u_6} α₂ β₂) (Sigma.map.{u_2 u_3 u_5 u_6} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂))
but is expected to have type
  forall {α₁ : Type.{u_1}} {α₂ : Type.{u_2}} {β₁ : α₁ -> Type.{u_3}} {β₂ : α₂ -> Type.{u_4}} {f₁ : α₁ -> α₂} {f₂ : forall (a : α₁), (β₁ a) -> (β₂ (f₁ a))}, (Function.Surjective.{succ u_1 succ u_2} α₁ α₂ f₁) -> (forall (a : α₁), Function.Surjective.{succ u_3 succ u_4} (β₁ a) (β₂ (f₁ a)) (f₂ a)) -> (Function.Surjective.{(max (succ u_3) (succ u_1)) (max (succ u_4) (succ u_2))} (Sigma.{u_1 u_3} α₁ (fun (a : α₁) => β₁ a)) (Sigma.{u_2 u_4} α₂ β₂) (Sigma.map.{u_1 u_2 u_3 u_4} α₁ α₂ (fun (a : α₁) => β₁ a) β₂ f₁ f₂))
Case conversion may be inaccurate. Consider using '#align function.surjective.sigma_map Function.Surjective.sigma_mapₓ'. -/
theorem Function.Surjective.sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)} (h₁ : Function.Surjective f₁)
    (h₂ : ∀ a, Function.Surjective (f₂ a)) : Function.Surjective (Sigma.map f₁ f₂) := by
  simp only [Function.Surjective, Sigma.forall, h₁.forall]
  exact fun i => (h₂ _).forall.2 fun x => ⟨⟨i, x⟩, rfl⟩

/-- Interpret a function on `Σ x : α, β x` as a dependent function with two arguments.

This also exists as an `equiv` as `equiv.Pi_curry γ`. -/
def Sigma.curry {γ : ∀ a, β a → Type _} (f : ∀ x : Sigma β, γ x.1 x.2) (x : α) (y : β x) : γ x y :=
  f ⟨x, y⟩

/-- Interpret a dependent function with two arguments as a function on `Σ x : α, β x`.

This also exists as an `equiv` as `(equiv.Pi_curry γ).symm`. -/
def Sigma.uncurry {γ : ∀ a, β a → Type _} (f : ∀ (x) (y : β x), γ x y) (x : Sigma β) : γ x.1 x.2 :=
  f x.1 x.2

/- warning: sigma.uncurry_curry -> Sigma.uncurry_curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : α -> Type.{u_4}} {γ : forall (a : α), (β a) -> Type.{u_2}} (f : forall (x : Sigma.{u_1 u_4} α β), γ (Sigma.fst.{u_1 u_4} α β x) (Sigma.snd.{u_1 u_4} α β x)), Eq.{(max (max (succ u_1) (succ u_4)) (succ u_2))} (forall (x : Sigma.{u_1 u_4} α (fun (x : α) => β x)), γ (Sigma.fst.{u_1 u_4} α (fun (x : α) => β x) x) (Sigma.snd.{u_1 u_4} α (fun (x : α) => β x) x)) (Sigma.uncurry.{u_1 u_4 u_2} α (fun (x : α) => β x) (fun (x : α) (y : β x) => γ x y) (Sigma.curry.{u_1 u_4 u_2} α β γ f)) f
but is expected to have type
  forall {α : Type.{u_2}} {β : α -> Type.{u_3}} {γ : forall (a : α), (β a) -> Type.{u_1}} (f : forall (x : Sigma.{u_2 u_3} α β), γ (Sigma.fst.{u_2 u_3} α β x) (Sigma.snd.{u_2 u_3} α β x)), Eq.{(max (max (succ u_2) (succ u_3)) (succ u_1))} (forall (x : Sigma.{u_2 u_3} α (fun (x : α) => β x)), γ (Sigma.fst.{u_2 u_3} α (fun (x : α) => β x) x) (Sigma.snd.{u_2 u_3} α (fun (x : α) => β x) x)) (Sigma.uncurry.{u_2 u_3 u_1} α (fun (x : α) => β x) (fun (x : α) (y : β x) => γ x y) (Sigma.curry.{u_2 u_3 u_1} α β γ f)) f
Case conversion may be inaccurate. Consider using '#align sigma.uncurry_curry Sigma.uncurry_curryₓ'. -/
@[simp]
theorem Sigma.uncurry_curry {γ : ∀ a, β a → Type _} (f : ∀ x : Sigma β, γ x.1 x.2) :
    Sigma.uncurry (Sigma.curry f) = f :=
  funext fun ⟨i, j⟩ => rfl

/- warning: sigma.curry_uncurry -> Sigma.curry_uncurry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : α -> Type.{u_4}} {γ : forall (a : α), (β a) -> Type.{u_2}} (f : forall (x : α) (y : β x), γ x y), Eq.{(max (succ u_1) (succ u_4) (succ u_2))} (forall (x : α) (y : β x), γ x y) (Sigma.curry.{u_1 u_4 u_2} α (fun (x : α) => β x) (fun (x : α) (y : β x) => γ x y) (Sigma.uncurry.{u_1 u_4 u_2} α (fun (x : α) => β x) (fun (x : α) (y : β x) => γ x y) f)) f
but is expected to have type
  forall {α : Type.{u_2}} {β : α -> Type.{u_3}} {γ : forall (a : α), (β a) -> Type.{u_1}} (f : forall (x : α) (y : β x), γ x y), Eq.{(max (max (succ u_2) (succ u_3)) (succ u_1))} (forall (x : α) (y : β x), γ x y) (Sigma.curry.{u_2 u_3 u_1} α (fun (x : α) => β x) (fun (x : α) (y : β x) => γ x y) (Sigma.uncurry.{u_2 u_3 u_1} α (fun (x : α) => β x) (fun (x : α) (y : β x) => γ x y) f)) f
Case conversion may be inaccurate. Consider using '#align sigma.curry_uncurry Sigma.curry_uncurryₓ'. -/
@[simp]
theorem Sigma.curry_uncurry {γ : ∀ a, β a → Type _} (f : ∀ (x) (y : β x), γ x y) : Sigma.curry (Sigma.uncurry f) = f :=
  rfl

/-- Convert a product type to a Σ-type. -/
def Prod.toSigma {α β} (p : α × β) : Σ_ : α, β :=
  ⟨p.1, p.2⟩

/- warning: prod.fst_comp_to_sigma -> Prod.fst_comp_to_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Eq.{(max (succ u_1) (succ u_2))} ((Prod.{u_1 u_2} α β) -> α) (Function.comp.{(max (succ u_1) (succ u_2)) (max (succ u_1) (succ u_2)) succ u_1} (Prod.{u_1 u_2} α β) (Sigma.{u_1 u_2} α (fun (_x : α) => β)) α (Sigma.fst.{u_1 u_2} α (fun (_x : α) => β)) (Prod.toSigma.{u_1 u_2} α β)) (Prod.fst.{u_1 u_2} α β)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Eq.{(max (succ u_2) (succ u_1))} ((Prod.{u_1 u_2} α β) -> α) (Function.comp.{(max (succ u_2) (succ u_1)) (max (succ u_2) (succ u_1)) succ u_1} (Prod.{u_1 u_2} α β) (Sigma.{u_1 u_2} α (fun (x._@.Mathlib.Data.Sigma.Basic._hyg.1762 : α) => β)) α (Sigma.fst.{u_1 u_2} α (fun (x._@.Mathlib.Data.Sigma.Basic._hyg.1762 : α) => β)) (Prod.toSigma.{u_1 u_2} α β)) (Prod.fst.{u_1 u_2} α β)
Case conversion may be inaccurate. Consider using '#align prod.fst_comp_to_sigma Prod.fst_comp_to_sigmaₓ'. -/
@[simp]
theorem Prod.fst_comp_to_sigma {α β} : Sigma.fst ∘ @Prod.toSigma α β = Prod.fst :=
  rfl

/- warning: prod.fst_to_sigma -> Prod.fst_to_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (x : Prod.{u_1 u_2} α β), Eq.{succ u_1} α (Sigma.fst.{u_1 u_2} α (fun (_x : α) => β) (Prod.toSigma.{u_1 u_2} α β x)) (Prod.fst.{u_1 u_2} α β x)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (x : Prod.{u_1 u_2} α β), Eq.{succ u_1} α (Sigma.fst.{u_1 u_2} α (fun (x._@.Mathlib.Data.Sigma.Basic._hyg.1762 : α) => β) (Prod.toSigma.{u_1 u_2} α β x)) (Prod.fst.{u_1 u_2} α β x)
Case conversion may be inaccurate. Consider using '#align prod.fst_to_sigma Prod.fst_to_sigmaₓ'. -/
@[simp]
theorem Prod.fst_to_sigma {α β} (x : α × β) : (Prod.toSigma x).fst = x.fst :=
  rfl

/- warning: prod.snd_to_sigma -> Prod.snd_to_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (x : Prod.{u_1 u_2} α β), Eq.{succ u_2} β (Sigma.snd.{u_1 u_2} α (fun (_x : α) => β) (Prod.toSigma.{u_1 u_2} α β x)) (Prod.snd.{u_1 u_2} α β x)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (x : Prod.{u_1 u_2} α β), Eq.{succ u_2} β (Sigma.snd.{u_1 u_2} α (fun (x._@.Mathlib.Data.Sigma.Basic._hyg.1762 : α) => β) (Prod.toSigma.{u_1 u_2} α β x)) (Prod.snd.{u_1 u_2} α β x)
Case conversion may be inaccurate. Consider using '#align prod.snd_to_sigma Prod.snd_to_sigmaₓ'. -/
@[simp]
theorem Prod.snd_to_sigma {α β} (x : α × β) : (Prod.toSigma x).snd = x.snd :=
  rfl

/- warning: prod.to_sigma_mk -> Prod.to_sigma_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} (x : α) (y : β), Eq.{(max (succ u_1) (succ u_2))} (Sigma.{u_1 u_2} α (fun (_x : α) => β)) (Prod.toSigma.{u_1 u_2} α β (Prod.mk.{u_1 u_2} α β x y)) (Sigma.mk.{u_1 u_2} α (fun (_x : α) => β) x y)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} (x : α) (y : β), Eq.{(max (succ u_2) (succ u_1))} (Sigma.{u_1 u_2} α (fun (x._@.Mathlib.Data.Sigma.Basic._hyg.1762 : α) => β)) (Prod.toSigma.{u_1 u_2} α β (Prod.mk.{u_1 u_2} α β x y)) (Sigma.mk.{u_1 u_2} α (fun (x._@.Mathlib.Data.Sigma.Basic._hyg.1762 : α) => β) x y)
Case conversion may be inaccurate. Consider using '#align prod.to_sigma_mk Prod.to_sigma_mkₓ'. -/
@[simp]
theorem Prod.to_sigma_mk {α β} (x : α) (y : β) : (x, y).toSigma = ⟨x, y⟩ :=
  rfl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:66:14: unsupported tactic `reflect_name #[] -/
-- we generate this manually as `@[derive has_reflect]` fails
@[instance]
protected unsafe def sigma.reflect.{u, v} [reflected_univ.{u}] [reflected_univ.{v}] {α : Type u} (β : α → Type v)
    [reflected _ α] [reflected _ β] [hα : has_reflect α] [hβ : ∀ i, has_reflect (β i)] : has_reflect (Σa, β a) :=
  fun ⟨a, b⟩ =>
  (by trace "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:66:14: unsupported tactic `reflect_name #[]" :
        reflected _ @Sigma.mk.{u, v}).subst₄
    (quote.1 α) (quote.1 β) (quote.1 a) (quote.1 b)

end Sigma

section PSigma

variable {α : Sort _} {β : α → Sort _}

namespace PSigma

/-- Nondependent eliminator for `psigma`. -/
def elim {γ} (f : ∀ a, β a → γ) (a : PSigma β) : γ :=
  PSigma.casesOn a f

/- warning: psigma.elim_val -> PSigma.elim_val is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {γ : Sort.{u_3}} (f : forall (a : α), (β a) -> γ) (a : α) (b : β a), Eq.{u_3} γ (PSigma.elim.{u_1 u_2 u_3} α (fun (a : α) => β a) γ f (PSigma.mk.{u_1 u_2} α (fun (a : α) => β a) a b)) (f a b)
but is expected to have type
  forall {α : Sort.{u_2}} {β : α -> Sort.{u_3}} {γ : Sort.{u_1}} (f : forall (a : α), (β a) -> γ) (a : α) (b : β a), Eq.{u_1} γ (PSigma.elim.{u_2 u_3 u_1} α (fun (a : α) => β a) γ f (PSigma.mk.{u_2 u_3} α (fun (a : α) => β a) a b)) (f a b)
Case conversion may be inaccurate. Consider using '#align psigma.elim_val PSigma.elim_valₓ'. -/
@[simp]
theorem elim_val {γ} (f : ∀ a, β a → γ) (a b) : PSigma.elim f ⟨a, b⟩ = f a b :=
  rfl

instance [Inhabited α] [Inhabited (β default)] : Inhabited (PSigma β) :=
  ⟨⟨default, default⟩⟩

instance [h₁ : DecidableEq α] [h₂ : ∀ a, DecidableEq (β a)] : DecidableEq (PSigma β)
  | ⟨a₁, b₁⟩, ⟨a₂, b₂⟩ =>
    match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
    | _, b₁, _, b₂, is_true (Eq.refl a) =>
      match b₁, b₂, h₂ a b₁ b₂ with
      | _, _, is_true (Eq.refl b) => isTrue rfl
      | b₁, b₂, is_false n => isFalse fun h => PSigma.noConfusion h fun e₁ e₂ => n <| eq_of_heq e₂
    | a₁, _, a₂, _, is_false n => isFalse fun h => PSigma.noConfusion h fun e₁ e₂ => n e₁

/- warning: psigma.mk.inj_iff -> PSigma.mk.inj_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {a₁ : α} {a₂ : α} {b₁ : β a₁} {b₂ : β a₂}, Iff (Eq.{(max 1 u_1 u_2)} (PSigma.{u_1 u_2} α β) (PSigma.mk.{u_1 u_2} α β a₁ b₁) (PSigma.mk.{u_1 u_2} α β a₂ b₂)) (And (Eq.{u_1} α a₁ a₂) (HEq.{u_2} (β a₁) b₁ (β a₂) b₂))
but is expected to have type
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {a₁ : α} {a₂ : α} {b₁ : β a₁} {b₂ : β a₂}, Iff (Eq.{(max (max 1 u_1) u_2)} (PSigma.{u_1 u_2} α β) (PSigma.mk.{u_1 u_2} α β a₁ b₁) (PSigma.mk.{u_1 u_2} α β a₂ b₂)) (And (Eq.{u_1} α a₁ a₂) (HEq.{u_2} (β a₁) b₁ (β a₂) b₂))
Case conversion may be inaccurate. Consider using '#align psigma.mk.inj_iff PSigma.mk.inj_iffₓ'. -/
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    @PSigma.mk α β a₁ b₁ = @PSigma.mk α β a₂ b₂ ↔ a₁ = a₂ ∧ HEq b₁ b₂ :=
  (Iff.intro PSigma.mk.inj) fun ⟨h₁, h₂⟩ =>
    match a₁, a₂, b₁, b₂, h₁, h₂ with
    | _, _, _, _, Eq.refl a, HEq.refl b => rfl

/- warning: psigma.ext -> PSigma.ext is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {x₀ : PSigma.{u_1 u_2} α β} {x₁ : PSigma.{u_1 u_2} α β}, (Eq.{u_1} α (PSigma.fst.{u_1 u_2} α β x₀) (PSigma.fst.{u_1 u_2} α β x₁)) -> (HEq.{u_2} (β (PSigma.fst.{u_1 u_2} α β x₀)) (PSigma.snd.{u_1 u_2} α β x₀) (β (PSigma.fst.{u_1 u_2} α β x₁)) (PSigma.snd.{u_1 u_2} α β x₁)) -> (Eq.{(max 1 u_1 u_2)} (PSigma.{u_1 u_2} α β) x₀ x₁)
but is expected to have type
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {x₀ : PSigma.{u_1 u_2} α β} {x₁ : PSigma.{u_1 u_2} α β}, (Eq.{u_1} α (PSigma.fst.{u_1 u_2} α β x₀) (PSigma.fst.{u_1 u_2} α β x₁)) -> (HEq.{u_2} (β (PSigma.fst.{u_1 u_2} α β x₀)) (PSigma.snd.{u_1 u_2} α β x₀) (β (PSigma.fst.{u_1 u_2} α β x₁)) (PSigma.snd.{u_1 u_2} α β x₁)) -> (Eq.{(max (max 1 u_1) u_2)} (PSigma.{u_1 u_2} α β) x₀ x₁)
Case conversion may be inaccurate. Consider using '#align psigma.ext PSigma.extₓ'. -/
@[ext]
theorem ext {x₀ x₁ : PSigma β} (h₀ : x₀.1 = x₁.1) (h₁ : HEq x₀.2 x₁.2) : x₀ = x₁ := by
  cases x₀
  cases x₁
  cases h₀
  cases h₁
  rfl

/- warning: psigma.ext_iff -> PSigma.ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {x₀ : PSigma.{u_1 u_2} α β} {x₁ : PSigma.{u_1 u_2} α β}, Iff (Eq.{(max 1 u_1 u_2)} (PSigma.{u_1 u_2} α β) x₀ x₁) (And (Eq.{u_1} α (PSigma.fst.{u_1 u_2} α β x₀) (PSigma.fst.{u_1 u_2} α β x₁)) (HEq.{u_2} (β (PSigma.fst.{u_1 u_2} α β x₀)) (PSigma.snd.{u_1 u_2} α β x₀) (β (PSigma.fst.{u_1 u_2} α β x₁)) (PSigma.snd.{u_1 u_2} α β x₁)))
but is expected to have type
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {x₀ : PSigma.{u_1 u_2} α β} {x₁ : PSigma.{u_1 u_2} α β}, Iff (Eq.{(max (max 1 u_1) u_2)} (PSigma.{u_1 u_2} α β) x₀ x₁) (And (Eq.{u_1} α (PSigma.fst.{u_1 u_2} α β x₀) (PSigma.fst.{u_1 u_2} α β x₁)) (HEq.{u_2} (β (PSigma.fst.{u_1 u_2} α β x₀)) (PSigma.snd.{u_1 u_2} α β x₀) (β (PSigma.fst.{u_1 u_2} α β x₁)) (PSigma.snd.{u_1 u_2} α β x₁)))
Case conversion may be inaccurate. Consider using '#align psigma.ext_iff PSigma.ext_iffₓ'. -/
theorem ext_iff {x₀ x₁ : PSigma β} : x₀ = x₁ ↔ x₀.1 = x₁.1 ∧ HEq x₀.2 x₁.2 := by
  cases x₀
  cases x₁
  exact PSigma.mk.inj_iff

/- warning: psigma.forall -> PSigma.forall is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {p : (PSigma.{u_1 u_2} α (fun (a : α) => β a)) -> Prop}, Iff (forall (x : PSigma.{u_1 u_2} α (fun (a : α) => β a)), p x) (forall (a : α) (b : β a), p (PSigma.mk.{u_1 u_2} α (fun (a : α) => β a) a b))
but is expected to have type
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {p : (PSigma.{u_1 u_2} α (fun (a : α) => β a)) -> Prop}, Iff (forall (x : PSigma.{u_1 u_2} α (fun (a : α) => β a)), p x) (forall (a : α) (b : β a), p (PSigma.mk.{u_1 u_2} α (fun (a : α) => β a) a b))
Case conversion may be inaccurate. Consider using '#align psigma.forall PSigma.forallₓ'. -/
@[simp]
theorem forall {p : (Σ'a, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

/- warning: psigma.exists -> PSigma.exists is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {p : (PSigma.{u_1 u_2} α (fun (a : α) => β a)) -> Prop}, Iff (Exists.{(max 1 u_1 u_2)} (PSigma.{u_1 u_2} α (fun (a : α) => β a)) (fun (x : PSigma.{u_1 u_2} α (fun (a : α) => β a)) => p x)) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => p (PSigma.mk.{u_1 u_2} α (fun (a : α) => β a) a b))))
but is expected to have type
  forall {α : Sort.{u_1}} {β : α -> Sort.{u_2}} {p : (PSigma.{u_1 u_2} α (fun (a : α) => β a)) -> Prop}, Iff (Exists.{(max (max 1 u_1) u_2)} (PSigma.{u_1 u_2} α (fun (a : α) => β a)) (fun (x : PSigma.{u_1 u_2} α (fun (a : α) => β a)) => p x)) (Exists.{u_1} α (fun (a : α) => Exists.{u_2} (β a) (fun (b : β a) => p (PSigma.mk.{u_1 u_2} α (fun (a : α) => β a) a b))))
Case conversion may be inaccurate. Consider using '#align psigma.exists PSigma.existsₓ'. -/
@[simp]
theorem exists {p : (Σ'a, β a) → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

/-- A specialized ext lemma for equality of psigma types over an indexed subtype. -/
@[ext]
theorem subtype_ext {β : Sort _} {p : α → β → Prop} :
    ∀ {x₀ x₁ : Σ'a, Subtype (p a)}, x₀.fst = x₁.fst → (x₀.snd : β) = x₁.snd → x₀ = x₁
  | ⟨a₀, b₀, hb₀⟩, ⟨a₁, b₁, hb₁⟩, rfl, rfl => rfl

theorem subtype_ext_iff {β : Sort _} {p : α → β → Prop} {x₀ x₁ : Σ'a, Subtype (p a)} :
    x₀ = x₁ ↔ x₀.fst = x₁.fst ∧ (x₀.snd : β) = x₁.snd :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => subtype_ext h₁ h₂⟩

variable {α₁ : Sort _} {α₂ : Sort _} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _}

/-- Map the left and right components of a sigma -/
def map (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) : PSigma β₁ → PSigma β₂
  | ⟨a, b⟩ => ⟨f₁ a, f₂ a b⟩

end PSigma

end PSigma

