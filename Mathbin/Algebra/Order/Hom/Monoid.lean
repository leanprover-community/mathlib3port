/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Order.WithZero
import Mathbin.Order.Hom.Basic

/-!
# Ordered monoid and group homomorphisms

This file defines morphisms between (additive) ordered monoids.

## Types of morphisms

* `order_add_monoid_hom`: Ordered additive monoid homomorphisms.
* `order_monoid_hom`: Ordered monoid homomorphisms.
* `order_monoid_with_zero_hom`: Ordered monoid with zero homomorphisms.

## Typeclasses

* `order_add_monoid_hom_class`
* `order_monoid_hom_class`
* `order_monoid_with_zero_hom_class`

## Notation

* `→+o`: Bundled ordered additive monoid homs. Also use for additive groups homs.
* `→*o`: Bundled ordered monoid homs. Also use for groups homs.
* `→*₀o`: Bundled ordered monoid with zero homs. Also use for groups with zero homs.

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical notation is to use the bundled hom as
a function via this coercion.

There is no `order_group_hom` -- the idea is that `order_monoid_hom` is used.
The constructor for `order_monoid_hom` needs a proof of `map_one` as well as `map_mul`; a separate
constructor `order_monoid_hom.mk'` will construct ordered group homs (i.e. ordered monoid homs
between ordered groups) given only a proof that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets. This is done when the
instances can be inferred because they are implicit arguments to the type `order_monoid_hom`. When
they can be inferred from the type it is faster to use this method than to use type class inference.

## Tags

ordered monoid, ordered group, monoid with zero
-/


open Function

variable {F α β γ δ : Type _}

section AddMonoid

/-- `α →+o β` is the type of monotone functions `α → β` that preserve the `ordered_add_comm_monoid`
structure.

`order_add_monoid_hom` is also used for ordered group homomorphisms.

When possible, instead of parametrizing results over `(f : α →+o β)`,
you should parametrize over `(F : Type*) [order_add_monoid_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `order_add_monoid_hom_class`. -/
structure OrderAddMonoidHom (α β : Type _) [Preorder α] [Preorder β] [AddZeroClass α] [AddZeroClass β] extends
  α →+ β where
  monotone' : Monotone to_fun

-- mathport name: «expr →+o »
infixr:25 " →+o " => OrderAddMonoidHom

section

/-- `order_add_monoid_hom_class F α β` states that `F` is a type of ordered monoid homomorphisms.

You should also extend this typeclass when you extend `order_add_monoid_hom`. -/
class OrderAddMonoidHomClass (F : Type _) (α β : outParam <| Type _) [Preorder α] [Preorder β] [AddZeroClass α]
  [AddZeroClass β] extends AddMonoidHomClass F α β where
  Monotone (f : F) : Monotone f

end

-- Instances and lemmas are defined below through `@[to_additive]`.
end AddMonoid

section Monoid

variable [Preorder α] [Preorder β] [MulOneClass α] [MulOneClass β]

/-- `α →*o β` is the type of functions `α → β` that preserve the `ordered_comm_monoid` structure.

`order_monoid_hom` is also used for ordered group homomorphisms.

When possible, instead of parametrizing results over `(f : α →*o β)`,
you should parametrize over `(F : Type*) [order_monoid_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `order_monoid_hom_class`. -/
@[to_additive]
structure OrderMonoidHom (α β : Type _) [Preorder α] [Preorder β] [MulOneClass α] [MulOneClass β] extends α →* β where
  monotone' : Monotone to_fun

-- mathport name: «expr →*o »
infixr:25 " →*o " => OrderMonoidHom

section

/-- `order_monoid_hom_class F α β` states that `F` is a type of ordered monoid homomorphisms.

You should also extend this typeclass when you extend `order_monoid_hom`. -/
@[to_additive]
class OrderMonoidHomClass (F : Type _) (α β : outParam <| Type _) [Preorder α] [Preorder β] [MulOneClass α]
  [MulOneClass β] extends MonoidHomClass F α β where
  Monotone (f : F) : Monotone f

end

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderMonoidHomClass.toOrderHomClass [OrderMonoidHomClass F α β] : OrderHomClass F α β :=
  { ‹OrderMonoidHomClass F α β› with map_rel := OrderMonoidHomClass.monotone }

@[to_additive]
instance [OrderMonoidHomClass F α β] : CoeT F (α →*o β) :=
  ⟨fun f => { toFun := f, map_one' := map_one f, map_mul' := map_mul f, monotone' := OrderMonoidHomClass.monotone _ }⟩

end Monoid

section MonoidWithZero

variable [Preorder α] [Preorder β] [MulZeroOneClass α] [MulZeroOneClass β]

/-- `order_monoid_with_zero_hom α β` is the type of functions `α → β` that preserve
the `monoid_with_zero` structure.

`order_monoid_with_zero_hom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : α →+ β)`,
you should parametrize over `(F : Type*) [order_monoid_with_zero_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `order_monoid_with_zero_hom_class`. -/
structure OrderMonoidWithZeroHom (α β : Type _) [Preorder α] [Preorder β] [MulZeroOneClass α]
  [MulZeroOneClass β] extends α →*₀ β where
  monotone' : Monotone to_fun

-- mathport name: «expr →*₀o »
infixr:25 " →*₀o " => OrderMonoidWithZeroHom

section

/-- `order_monoid_with_zero_hom_class F α β` states that `F` is a type of
ordered monoid with zero homomorphisms.

You should also extend this typeclass when you extend `order_monoid_with_zero_hom`. -/
class OrderMonoidWithZeroHomClass (F : Type _) (α β : outParam <| Type _) [Preorder α] [Preorder β] [MulZeroOneClass α]
  [MulZeroOneClass β] extends MonoidWithZeroHomClass F α β where
  Monotone (f : F) : Monotone f

end

-- See note [lower instance priority]
instance (priority := 100) OrderMonoidWithZeroHomClass.toOrderMonoidHomClass [OrderMonoidWithZeroHomClass F α β] :
    OrderMonoidHomClass F α β :=
  { ‹OrderMonoidWithZeroHomClass F α β› with }

instance [OrderMonoidWithZeroHomClass F α β] : CoeT F (α →*₀o β) :=
  ⟨fun f =>
    { toFun := f, map_one' := map_one f, map_zero' := map_zero f, map_mul' := map_mul f,
      monotone' := OrderMonoidWithZeroHomClass.monotone _ }⟩

end MonoidWithZero

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid α] [OrderedAddCommMonoid β] [OrderAddMonoidHomClass F α β] (f : F) {a : α}

include β

theorem map_nonneg (ha : 0 ≤ a) : 0 ≤ f a := by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha

theorem map_nonpos (ha : a ≤ 0) : f a ≤ 0 := by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha

end OrderedAddCommMonoid

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] [OrderedAddCommMonoid β] [AddMonoidHomClass F α β] (f : F)

theorem monotone_iff_map_nonneg : Monotone (f : α → β) ↔ ∀ a, 0 ≤ a → 0 ≤ f a :=
  ⟨fun h a => by
    rw [← map_zero f]
    apply h, fun h a b hl => by
    rw [← sub_add_cancel b a, map_add f]
    exact le_add_of_nonneg_left (h _ <| sub_nonneg.2 hl)⟩

theorem antitone_iff_map_nonpos : Antitone (f : α → β) ↔ ∀ a, 0 ≤ a → f a ≤ 0 :=
  monotone_to_dual_comp_iff.symm.trans <| monotone_iff_map_nonneg _

theorem monotone_iff_map_nonpos : Monotone (f : α → β) ↔ ∀ a ≤ 0, f a ≤ 0 :=
  antitone_comp_of_dual_iff.symm.trans <| antitone_iff_map_nonpos _

theorem antitone_iff_map_nonneg : Antitone (f : α → β) ↔ ∀ a ≤ 0, 0 ≤ f a :=
  monotone_comp_of_dual_iff.symm.trans <| monotone_iff_map_nonneg _

variable [CovariantClass β β (· + ·) (· < ·)]

theorem strict_mono_iff_map_pos : StrictMono (f : α → β) ↔ ∀ a, 0 < a → 0 < f a :=
  ⟨fun h a => by
    rw [← map_zero f]
    apply h, fun h a b hl => by
    rw [← sub_add_cancel b a, map_add f]
    exact lt_add_of_pos_left _ (h _ <| sub_pos.2 hl)⟩

theorem strict_anti_iff_map_neg : StrictAnti (f : α → β) ↔ ∀ a, 0 < a → f a < 0 :=
  strict_mono_to_dual_comp_iff.symm.trans <| strict_mono_iff_map_pos _

theorem strict_mono_iff_map_neg : StrictMono (f : α → β) ↔ ∀ a < 0, f a < 0 :=
  strict_anti_comp_of_dual_iff.symm.trans <| strict_anti_iff_map_neg _

theorem strict_anti_iff_map_pos : StrictAnti (f : α → β) ↔ ∀ a < 0, 0 < f a :=
  strict_mono_comp_of_dual_iff.symm.trans <| strict_mono_iff_map_pos _

end OrderedAddCommGroup

namespace OrderMonoidHom

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β] [MulOneClass γ]
  [MulOneClass δ] {f g : α →*o β}

@[to_additive]
instance : OrderMonoidHomClass (α →*o β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  Monotone f := f.monotone'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
@[to_additive "Helper instance for when there's too many metavariables to apply\n`fun_like.has_coe_to_fun` directly."]
instance : CoeFun (α →*o β) fun _ => α → β :=
  FunLike.hasCoeToFun

-- Other lemmas should be accessed through the `fun_like` API
@[ext, to_additive]
theorem ext (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

@[to_additive]
theorem to_fun_eq_coe (f : α →*o β) : f.toFun = (f : α → β) :=
  rfl

@[simp, to_additive]
theorem coe_mk (f : α →* β) (h) : (OrderMonoidHom.mk f h : α → β) = f :=
  rfl

@[simp, to_additive]
theorem mk_coe (f : α →*o β) (h) : OrderMonoidHom.mk (f : α →* β) h = f := by
  ext
  rfl

/-- Reinterpret an ordered monoid homomorphism as an order homomorphism. -/
@[to_additive "Reinterpret an ordered additive monoid homomorphism as an order homomorphism."]
def toOrderHom (f : α →*o β) : α →o β :=
  { f with }

@[simp, to_additive]
theorem coe_monoid_hom (f : α →*o β) : ((f : α →* β) : α → β) = f :=
  rfl

@[simp, to_additive]
theorem coe_order_hom (f : α →*o β) : ((f : α →o β) : α → β) = f :=
  rfl

@[to_additive]
theorem to_monoid_hom_injective : Injective (toMonoidHom : _ → α →* β) := fun f g h =>
  ext <| by convert FunLike.ext_iff.1 h

@[to_additive]
theorem to_order_hom_injective : Injective (toOrderHom : _ → α →o β) := fun f g h =>
  ext <| by convert FunLike.ext_iff.1 h

/-- Copy of an `order_monoid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
@[to_additive
      "Copy of an `order_monoid_hom` with a new `to_fun` equal to the old one. Useful to fix\ndefinitional equalities."]
protected def copy (f : α →*o β) (f' : α → β) (h : f' = f) : α →*o β :=
  { f.toMonoidHom.copy f' <| h with toFun := f', monotone' := h.symm.subst f.monotone' }

variable (α)

/-- The identity map as an ordered monoid homomorphism. -/
@[to_additive "The identity map as an ordered additive monoid homomorphism."]
protected def id : α →*o α :=
  { MonoidHom.id α, OrderHom.id with }

@[simp, to_additive]
theorem coe_id : ⇑(OrderMonoidHom.id α) = id :=
  rfl

@[to_additive]
instance : Inhabited (α →*o α) :=
  ⟨OrderMonoidHom.id α⟩

variable {α}

/-- Composition of `order_monoid_hom`s as an `order_monoid_hom`. -/
@[to_additive "Composition of `order_add_monoid_hom`s as an `order_add_monoid_hom`"]
def comp (f : β →*o γ) (g : α →*o β) : α →*o γ :=
  { f.toMonoidHom.comp (g : α →* β), f.toOrderHom.comp (g : α →o β) with }

@[simp, to_additive]
theorem coe_comp (f : β →*o γ) (g : α →*o β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp, to_additive]
theorem comp_apply (f : β →*o γ) (g : α →*o β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp, to_additive]
theorem coe_comp_monoid_hom (f : β →*o γ) (g : α →*o β) : (f.comp g : α →* γ) = (f : β →* γ).comp g :=
  rfl

@[simp, to_additive]
theorem coe_comp_order_hom (f : β →*o γ) (g : α →*o β) : (f.comp g : α →o γ) = (f : β →o γ).comp g :=
  rfl

@[simp, to_additive]
theorem comp_assoc (f : γ →*o δ) (g : β →*o γ) (h : α →*o β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp, to_additive]
theorem comp_id (f : α →*o β) : f.comp (OrderMonoidHom.id α) = f :=
  ext fun a => rfl

@[simp, to_additive]
theorem id_comp (f : α →*o β) : (OrderMonoidHom.id β).comp f = f :=
  ext fun a => rfl

@[to_additive]
theorem cancel_right {g₁ g₂ : β →*o γ} {f : α →*o β} (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

@[to_additive]
theorem cancel_left {g : β →*o γ} {f₁ f₂ : α →*o β} (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

/-- `1` is the homomorphism sending all elements to `1`. -/
@[to_additive "`1` is the homomorphism sending all elements to `1`."]
instance : One (α →*o β) :=
  ⟨{ (1 : α →* β) with monotone' := monotone_const }⟩

@[simp, to_additive]
theorem coe_one : ⇑(1 : α →*o β) = 1 :=
  rfl

@[simp, to_additive]
theorem one_apply (a : α) : (1 : α →*o β) a = 1 :=
  rfl

@[simp, to_additive]
theorem one_comp (f : α →*o β) : (1 : β →*o γ).comp f = 1 :=
  rfl

@[simp, to_additive]
theorem comp_one (f : β →*o γ) : f.comp (1 : α →*o β) = 1 := by
  ext
  exact map_one f

end Preorder

section Mul

variable [OrderedCommMonoid α] [OrderedCommMonoid β] [OrderedCommMonoid γ]

/-- For two ordered monoid morphisms `f` and `g`, their product is the ordered monoid morphism
sending `a` to `f a * g a`. -/
@[to_additive
      "For two ordered additive monoid morphisms `f` and `g`, their product is the ordered\nadditive monoid morphism sending `a` to `f a + g a`."]
instance : Mul (α →*o β) :=
  ⟨fun f g => { (f * g : α →* β) with monotone' := f.monotone'.mul' g.monotone' }⟩

@[simp, to_additive]
theorem coe_mul (f g : α →*o β) : ⇑(f * g) = f * g :=
  rfl

@[simp, to_additive]
theorem mul_apply (f g : α →*o β) (a : α) : (f * g) a = f a * g a :=
  rfl

@[to_additive]
theorem mul_comp (g₁ g₂ : β →*o γ) (f : α →*o β) : (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl

@[to_additive]
theorem comp_mul (g : β →*o γ) (f₁ f₂ : α →*o β) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext
  exact map_mul g _ _

end Mul

section OrderedCommMonoid

variable {hα : OrderedCommMonoid α} {hβ : OrderedCommMonoid β}

include hα hβ

@[simp, to_additive]
theorem to_monoid_hom_eq_coe (f : α →*o β) : f.toMonoidHom = f := by
  ext
  rfl

@[simp, to_additive]
theorem to_order_hom_eq_coe (f : α →*o β) : f.toOrderHom = f :=
  rfl

end OrderedCommMonoid

section OrderedCommGroup

variable {hα : OrderedCommGroup α} {hβ : OrderedCommGroup β}

include hα hβ

/-- Makes an ordered group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive "Makes an ordered additive group homomorphism from a proof that the map preserves\naddition.",
  simps (config := { fullyApplied := false })]
def mk' (f : α → β) (hf : Monotone f) (map_mul : ∀ a b : α, f (a * b) = f a * f b) : α →*o β :=
  { MonoidHom.mk' f map_mul with monotone' := hf }

end OrderedCommGroup

end OrderMonoidHom

namespace OrderMonoidWithZeroHom

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ] {f g : α →*₀o β}

instance : OrderMonoidWithZeroHomClass (α →*₀o β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'
  Monotone f := f.monotone'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →*₀o β) fun _ => α → β :=
  FunLike.hasCoeToFun

-- Other lemmas should be accessed through the `fun_like` API
@[ext]
theorem ext (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

theorem to_fun_eq_coe (f : α →*₀o β) : f.toFun = (f : α → β) :=
  rfl

@[simp]
theorem coe_mk (f : α →*₀ β) (h) : (OrderMonoidWithZeroHom.mk f h : α → β) = f :=
  rfl

@[simp]
theorem mk_coe (f : α →*₀o β) (h) : OrderMonoidWithZeroHom.mk (f : α →*₀ β) h = f := by
  ext
  rfl

/-- Reinterpret an ordered monoid with zero homomorphism as an order monoid homomorphism. -/
def toOrderMonoidHom (f : α →*₀o β) : α →*o β :=
  { f with }

@[simp]
theorem coe_monoid_with_zero_hom (f : α →*₀o β) : ⇑(f : α →*₀ β) = f :=
  rfl

@[simp]
theorem coe_order_monoid_hom (f : α →*₀o β) : ⇑(f : α →*o β) = f :=
  rfl

theorem to_order_monoid_hom_injective : Injective (toOrderMonoidHom : _ → α →*o β) := fun f g h =>
  ext <| by convert FunLike.ext_iff.1 h

theorem to_monoid_with_zero_hom_injective : Injective (toMonoidWithZeroHom : _ → α →*₀ β) := fun f g h =>
  ext <| by convert FunLike.ext_iff.1 h

/-- Copy of an `order_monoid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →*o β) (f' : α → β) (h : f' = f) : α →*o β :=
  { f.toMonoidHom.copy f' h with toFun := f', monotone' := h.symm.subst f.monotone' }

variable (α)

/-- The identity map as an ordered monoid with zero homomorphism. -/
protected def id : α →*₀o α :=
  { MonoidWithZeroHom.id α, OrderHom.id with }

@[simp]
theorem coe_id : ⇑(OrderMonoidWithZeroHom.id α) = id :=
  rfl

instance : Inhabited (α →*₀o α) :=
  ⟨OrderMonoidWithZeroHom.id α⟩

variable {α}

/-- Composition of `order_monoid_with_zero_hom`s as an `order_monoid_with_zero_hom`. -/
def comp (f : β →*₀o γ) (g : α →*₀o β) : α →*₀o γ :=
  { f.toMonoidWithZeroHom.comp (g : α →*₀ β), f.toOrderMonoidHom.comp (g : α →*o β) with }

@[simp]
theorem coe_comp (f : β →*₀o γ) (g : α →*₀o β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : β →*₀o γ) (g : α →*₀o β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem coe_comp_monoid_with_zero_hom (f : β →*₀o γ) (g : α →*₀o β) : (f.comp g : α →*₀ γ) = (f : β →*₀ γ).comp g :=
  rfl

@[simp]
theorem coe_comp_order_monoid_hom (f : β →*₀o γ) (g : α →*₀o β) : (f.comp g : α →*o γ) = (f : β →*o γ).comp g :=
  rfl

@[simp]
theorem comp_assoc (f : γ →*₀o δ) (g : β →*₀o γ) (h : α →*₀o β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : α →*₀o β) : f.comp (OrderMonoidWithZeroHom.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : α →*₀o β) : (OrderMonoidWithZeroHom.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : β →*₀o γ} {f : α →*₀o β} (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : β →*₀o γ} {f₁ f₂ : α →*₀o β} (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end Preorder

section Mul

variable [LinearOrderedCommMonoidWithZero α] [LinearOrderedCommMonoidWithZero β] [LinearOrderedCommMonoidWithZero γ]

/-- For two ordered monoid morphisms `f` and `g`, their product is the ordered monoid morphism
sending `a` to `f a * g a`. -/
instance : Mul (α →*₀o β) :=
  ⟨fun f g => { (f * g : α →*₀ β) with monotone' := f.monotone'.mul' g.monotone' }⟩

@[simp]
theorem coe_mul (f g : α →*₀o β) : ⇑(f * g) = f * g :=
  rfl

@[simp]
theorem mul_apply (f g : α →*₀o β) (a : α) : (f * g) a = f a * g a :=
  rfl

theorem mul_comp (g₁ g₂ : β →*₀o γ) (f : α →*₀o β) : (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl

theorem comp_mul (g : β →*₀o γ) (f₁ f₂ : α →*₀o β) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
  ext fun _ => map_mul g _ _

end Mul

section LinearOrderedCommMonoidWithZero

variable {hα : Preorder α} {hα' : MulZeroOneClass α} {hβ : Preorder β} {hβ' : MulZeroOneClass β}

include hα hα' hβ hβ'

@[simp]
theorem to_monoid_with_zero_hom_eq_coe (f : α →*₀o β) : f.toMonoidWithZeroHom = f := by
  ext
  rfl

@[simp]
theorem to_order_monoid_hom_eq_coe (f : α →*₀o β) : f.toOrderMonoidHom = f :=
  rfl

end LinearOrderedCommMonoidWithZero

end OrderMonoidWithZeroHom

