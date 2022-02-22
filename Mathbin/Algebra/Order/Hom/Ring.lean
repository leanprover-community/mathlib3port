/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import Mathbin.Algebra.Order.Hom.Monoid
import Mathbin.Algebra.Order.Ring

/-!
# Ordered ring homomorphisms

Homomorphisms between ordered (semi)rings that respect the ordering.

## Main definitions

* `order_ring_hom` : A monotone homomorphism `f` between two `ordered_semiring`s.

## Notation

* `→+*o`: Type of ordered ring homomorphisms.

## Tags

ordered ring homomorphism, order homomorphism
-/


open Function

variable {F α β γ δ : Type _}

/-- `order_ring_hom α β` is the type of monotone semiring homomorphisms from `α` to `β`.

When possible, instead of parametrizing results over `(f : order_ring_hom α β)`,
you should parametrize over `(F : Type*) [order_ring_hom_class F α β] (f : F)`.
When you extend this structure, make sure to extend `order_ring_hom_class`.
-/
structure OrderRingHom (α β : Type _) [OrderedSemiring α] [OrderedSemiring β] extends α →+* β where
  monotone' : Monotone to_fun

/-- Reinterpret an ordered ring homomorphism as a ring homomorphism. -/
add_decl_doc OrderRingHom.toRingHom

-- mathport name: «expr →+*o »
infixl:25 " →+*o " => OrderRingHom

/-- `order_ring_hom_class F α β` states that `F` is a type of ordered semiring homomorphisms.
You should extend this typeclass when you extend `order_ring_hom`. -/
class OrderRingHomClass (F : Type _) (α β : outParam <| Type _) [OrderedSemiring α] [OrderedSemiring β] extends
  RingHomClass F α β where
  Monotone (f : F) : Monotone f

-- See note [lower priority instance]
instance (priority := 100) OrderRingHomClass.toOrderAddMonoidHomClass [OrderedSemiring α] [OrderedSemiring β]
    [OrderRingHomClass F α β] : OrderAddMonoidHomClass F α β :=
  { ‹OrderRingHomClass F α β› with }

-- See note [lower priority instance]
instance (priority := 100) OrderRingHomClass.toOrderMonoidWithZeroHomClass [OrderedSemiring α] [OrderedSemiring β]
    [OrderRingHomClass F α β] : OrderMonoidWithZeroHomClass F α β :=
  { ‹OrderRingHomClass F α β› with }

instance [OrderedSemiring α] [OrderedSemiring β] [OrderRingHomClass F α β] : CoeTₓ F (α →+*o β) :=
  ⟨fun f =>
    { toFun := f, map_one' := map_one f, map_mul' := map_mul f, map_add' := map_add f, map_zero' := map_zero f,
      monotone' := OrderHomClass.mono f }⟩

/-! ### Ordered ring homomorphisms -/


namespace OrderRingHom

variable [OrderedSemiring α] [OrderedSemiring β] [OrderedSemiring γ] [OrderedSemiring δ]

/-- Reinterpret an ordered ring homomorphism as an ordered additive monoid homomorphism. -/
def toOrderAddMonoidHom (f : α →+*o β) : α →+o β :=
  { f with }

/-- Reinterpret an ordered ring homomorphism as an order homomorphism. -/
def toOrderMonoidWithZeroHom (f : α →+*o β) : α →*₀o β :=
  { f with }

instance : OrderRingHomClass (α →+*o β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f <;> obtain ⟨⟨_, _⟩, _⟩ := g <;> congr
  map_mul := fun f => f.map_mul'
  map_one := fun f => f.map_one'
  map_add := fun f => f.map_add'
  map_zero := fun f => f.map_zero'
  Monotone := fun f => f.monotone'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →+*o β) fun _ => α → β :=
  ⟨fun f => f.toFun⟩

theorem to_fun_eq_coe (f : α →+*o β) : f.toFun = ⇑f :=
  rfl

@[ext]
theorem ext {f g : α →+*o β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

@[simp]
theorem to_ring_hom_eq_coe (f : α →+*o β) : f.toRingHom = f :=
  RingHom.ext fun _ => rfl

@[simp]
theorem to_order_add_monoid_hom_eq_coe (f : α →+*o β) : f.toOrderAddMonoidHom = f :=
  rfl

@[simp]
theorem to_order_monoid_with_zero_hom_eq_coe (f : α →+*o β) : f.toOrderMonoidWithZeroHom = f :=
  rfl

@[simp]
theorem coe_coe_ring_hom (f : α →+*o β) : ⇑(f : α →+* β) = f :=
  rfl

@[simp]
theorem coe_coe_order_add_monoid_hom (f : α →+*o β) : ⇑(f : α →+o β) = f :=
  rfl

@[simp]
theorem coe_coe_order_monoid_with_zero_hom (f : α →+*o β) : ⇑(f : α →*₀o β) = f :=
  rfl

@[norm_cast]
theorem coe_ring_hom_apply (f : α →+*o β) (a : α) : (f : α →+* β) a = f a :=
  rfl

@[norm_cast]
theorem coe_order_add_monoid_hom_apply (f : α →+*o β) (a : α) : (f : α →+o β) a = f a :=
  rfl

@[norm_cast]
theorem coe_order_monoid_with_zero_hom_apply (f : α →+*o β) (a : α) : (f : α →*₀o β) a = f a :=
  rfl

/-- Copy of a `order_ring_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →+*o β) (f' : α → β) (h : f' = f) : α →+*o β :=
  { f.toRingHom.copy f' h, f.toOrderAddMonoidHom.copy f' h with }

variable (α)

/-- The identity as an ordered ring homomorphism. -/
protected def id : α →+*o α :=
  { RingHom.id _, OrderHom.id with }

instance : Inhabited (α →+*o α) :=
  ⟨OrderRingHom.id α⟩

@[simp]
theorem coe_id : ⇑(OrderRingHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : OrderRingHom.id α a = a :=
  rfl

@[simp]
theorem coe_ring_hom_id : (OrderRingHom.id α : α →+* α) = RingHom.id α :=
  rfl

@[simp]
theorem coe_order_add_monoid_hom_id : (OrderRingHom.id α : α →+o α) = OrderAddMonoidHom.id α :=
  rfl

@[simp]
theorem coe_order_monoid_with_zero_hom_id : (OrderRingHom.id α : α →*₀o α) = OrderMonoidWithZeroHom.id α :=
  rfl

/-- Composition of two `order_ring_hom`s as an `order_ring_hom`. -/
protected def comp (f : β →+*o γ) (g : α →+*o β) : α →+*o γ :=
  { f.toRingHom.comp g.toRingHom, f.toOrderAddMonoidHom.comp g.toOrderAddMonoidHom with }

@[simp]
theorem coe_comp (f : β →+*o γ) (g : α →+*o β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : β →+*o γ) (g : α →+*o β) (a : α) : f.comp g a = f (g a) :=
  rfl

theorem comp_assoc (f : γ →+*o δ) (g : β →+*o γ) (h : α →+*o β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : α →+*o β) : f.comp (OrderRingHom.id α) = f :=
  ext fun x => rfl

@[simp]
theorem id_comp (f : α →+*o β) : (OrderRingHom.id β).comp f = f :=
  ext fun x => rfl

theorem cancel_right {f₁ f₂ : β →+*o γ} {g : α →+*o β} (hg : Surjective g) : f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| FunLike.ext_iff.1 h, congr_argₓ _⟩

theorem cancel_left {f : β →+*o γ} {g₁ g₂ : α →+*o β} (hf : Injective f) : f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h =>
    ext fun a =>
      hf <| by
        rw [← comp_apply, h, comp_apply],
    congr_argₓ _⟩

instance : PartialOrderₓ (OrderRingHom α β) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

end OrderRingHom

