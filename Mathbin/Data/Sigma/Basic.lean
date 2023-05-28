/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.sigma.basic
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
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

-- sometimes the built-in injectivity support does not work
@[simp, nolint simp_nf]
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ HEq b₁ b₂ := by simp
#align sigma.mk.inj_iff Sigma.mk.inj_iff

@[simp]
theorem eta : ∀ x : Σa, β a, Sigma.mk x.1 x.2 = x
  | ⟨i, x⟩ => rfl
#align sigma.eta Sigma.eta

@[ext]
theorem ext {x₀ x₁ : Sigma β} (h₀ : x₀.1 = x₁.1) (h₁ : HEq x₀.2 x₁.2) : x₀ = x₁ := by cases x₀;
  cases x₁; cases h₀; cases h₁; rfl
#align sigma.ext Sigma.ext

theorem ext_iff {x₀ x₁ : Sigma β} : x₀ = x₁ ↔ x₀.1 = x₁.1 ∧ HEq x₀.2 x₁.2 := by cases x₀; cases x₁;
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

@[simp]
theorem forall {p : (Σa, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩
#align sigma.forall Sigma.forall

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

theorem Function.Injective.sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h₁ : Function.Injective f₁) (h₂ : ∀ a, Function.Injective (f₂ a)) :
    Function.Injective (Sigma.map f₁ f₂)
  | ⟨i, x⟩, ⟨j, y⟩, h => by
    obtain rfl : i = j; exact h₁ (sigma.mk.inj_iff.mp h).1
    obtain rfl : x = y; exact h₂ i (sigma_mk_injective h)
    rfl
#align function.injective.sigma_map Function.Injective.sigma_map

theorem Function.Injective.of_sigma_map {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h : Function.Injective (Sigma.map f₁ f₂)) (a : α₁) : Function.Injective (f₂ a) :=
  fun x y hxy => sigma_mk_injective <| @h ⟨a, x⟩ ⟨a, y⟩ (Sigma.ext rfl (heq_iff_eq.2 hxy))
#align function.injective.of_sigma_map Function.Injective.of_sigma_map

theorem Function.Injective.sigma_map_iff {f₁ : α₁ → α₂} {f₂ : ∀ a, β₁ a → β₂ (f₁ a)}
    (h₁ : Function.Injective f₁) :
    Function.Injective (Sigma.map f₁ f₂) ↔ ∀ a, Function.Injective (f₂ a) :=
  ⟨fun h => h.of_sigma_map, h₁.sigma_map⟩
#align function.injective.sigma_map_iff Function.Injective.sigma_map_iff

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

@[simp]
theorem Sigma.uncurry_curry {γ : ∀ a, β a → Type _} (f : ∀ x : Sigma β, γ x.1 x.2) :
    Sigma.uncurry (Sigma.curry f) = f :=
  funext fun ⟨i, j⟩ => rfl
#align sigma.uncurry_curry Sigma.uncurry_curry

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

@[simp]
theorem Prod.fst_comp_toSigma {α β} : Sigma.fst ∘ @Prod.toSigma α β = Prod.fst :=
  rfl
#align prod.fst_comp_to_sigma Prod.fst_comp_toSigma

@[simp]
theorem Prod.fst_toSigma {α β} (x : α × β) : (Prod.toSigma x).fst = x.fst :=
  rfl
#align prod.fst_to_sigma Prod.fst_toSigma

@[simp]
theorem Prod.snd_toSigma {α β} (x : α × β) : (Prod.toSigma x).snd = x.snd :=
  rfl
#align prod.snd_to_sigma Prod.snd_toSigma

@[simp]
theorem Prod.toSigma_mk {α β} (x : α) (y : β) : (x, y).toSigma = ⟨x, y⟩ :=
  rfl
#align prod.to_sigma_mk Prod.toSigma_mk

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[] -/
-- we generate this manually as `@[derive has_reflect]` fails
@[instance]
protected unsafe def sigma.reflect.{u, v} [Lean.ToLevel.{u}] [Lean.ToLevel.{v}] {α : Type u}
    (β : α → Type v) [reflected _ α] [reflected _ β] [hα : has_reflect α]
    [hβ : ∀ i, has_reflect (β i)] : has_reflect (Σa, β a) := fun ⟨a, b⟩ =>
  (by
        trace
          "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[]" :
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

theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    @PSigma.mk α β a₁ b₁ = @PSigma.mk α β a₂ b₂ ↔ a₁ = a₂ ∧ HEq b₁ b₂ :=
  Iff.intro PSigma.mk.inj fun ⟨h₁, h₂⟩ =>
    match a₁, a₂, b₁, b₂, h₁, h₂ with
    | _, _, _, _, Eq.refl a, HEq.refl b => rfl
#align psigma.mk.inj_iff PSigma.mk.inj_iff

@[ext]
theorem ext {x₀ x₁ : PSigma β} (h₀ : x₀.1 = x₁.1) (h₁ : HEq x₀.2 x₁.2) : x₀ = x₁ := by cases x₀;
  cases x₁; cases h₀; cases h₁; rfl
#align psigma.ext PSigma.ext

theorem ext_iff {x₀ x₁ : PSigma β} : x₀ = x₁ ↔ x₀.1 = x₁.1 ∧ HEq x₀.2 x₁.2 := by cases x₀; cases x₁;
  exact PSigma.mk.inj_iff
#align psigma.ext_iff PSigma.ext_iff

@[simp]
theorem forall {p : (Σ'a, β a) → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩
#align psigma.forall PSigma.forall

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

