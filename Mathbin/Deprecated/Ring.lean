/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Deprecated.Group

/-!
# Unbundled semiring and ring homomorphisms (deprecated)

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines predicates for unbundled semiring and ring homomorphisms. Instead of using
this file, please use `ring_hom`, defined in `algebra.hom.ring`, with notation `→+*`, for
morphisms between semirings or rings. For example use `φ : A →+* B` to represent a
ring homomorphism.

## Main Definitions

`is_semiring_hom` (deprecated), `is_ring_hom` (deprecated)

## Tags

is_semiring_hom, is_ring_hom

-/


universe u v w

variable {α : Type u}

/- ./././Mathport/Syntax/Translate/Command.lean:353:30: infer kinds are unsupported in Lean 4: #[`map_zero] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:353:30: infer kinds are unsupported in Lean 4: #[`map_one] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:353:30: infer kinds are unsupported in Lean 4: #[`map_add] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:353:30: infer kinds are unsupported in Lean 4: #[`map_mul] [] -/
/-- Predicate for semiring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
structure IsSemiringHom {α : Type u} {β : Type v} [Semiring α] [Semiring β] (f : α → β) : Prop where
  map_zero : f 0 = 0
  map_one : f 1 = 1
  map_add : ∀ {x y}, f (x + y) = f x + f y
  map_mul : ∀ {x y}, f (x * y) = f x * f y

namespace IsSemiringHom

variable {β : Type v} [Semiring α] [Semiring β]

variable {f : α → β} (hf : IsSemiringHom f) {x y : α}

/-- The identity map is a semiring homomorphism. -/
theorem id : IsSemiringHom (@id α) := by refine' { .. } <;> intros <;> rfl

/-- The composition of two semiring homomorphisms is a semiring homomorphism. -/
theorem comp (hf : IsSemiringHom f) {γ} [Semiring γ] {g : β → γ} (hg : IsSemiringHom g) : IsSemiringHom (g ∘ f) :=
  { map_zero := by simpa [map_zero hf] using map_zero hg, map_one := by simpa [map_one hf] using map_one hg,
    map_add := fun x y => by simp [map_add hf, map_add hg], map_mul := fun x y => by simp [map_mul hf, map_mul hg] }

/-- A semiring homomorphism is an additive monoid homomorphism. -/
theorem to_is_add_monoid_hom (hf : IsSemiringHom f) : IsAddMonoidHom f :=
  { ‹IsSemiringHom f› with }

/-- A semiring homomorphism is a monoid homomorphism. -/
theorem to_is_monoid_hom (hf : IsSemiringHom f) : IsMonoidHom f :=
  { ‹IsSemiringHom f› with }

end IsSemiringHom

/- ./././Mathport/Syntax/Translate/Command.lean:353:30: infer kinds are unsupported in Lean 4: #[`map_one] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:353:30: infer kinds are unsupported in Lean 4: #[`map_mul] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:353:30: infer kinds are unsupported in Lean 4: #[`map_add] [] -/
/-- Predicate for ring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
structure IsRingHom {α : Type u} {β : Type v} [Ring α] [Ring β] (f : α → β) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ {x y}, f (x * y) = f x * f y
  map_add : ∀ {x y}, f (x + y) = f x + f y

namespace IsRingHom

variable {β : Type v} [Ring α] [Ring β]

/-- A map of rings that is a semiring homomorphism is also a ring homomorphism. -/
theorem ofSemiring {f : α → β} (H : IsSemiringHom f) : IsRingHom f :=
  { H with }

variable {f : α → β} (hf : IsRingHom f) {x y : α}

/-- Ring homomorphisms map zero to zero. -/
theorem map_zero (hf : IsRingHom f) : f 0 = 0 :=
  calc
    f 0 = f (0 + 0) - f 0 := by rw [hf.map_add] <;> simp
    _ = 0 := by simp
    

/-- Ring homomorphisms preserve additive inverses. -/
theorem map_neg (hf : IsRingHom f) : f (-x) = -f x :=
  calc
    f (-x) = f (-x + x) - f x := by rw [hf.map_add] <;> simp
    _ = -f x := by simp [hf.map_zero]
    

/-- Ring homomorphisms preserve subtraction. -/
theorem map_sub (hf : IsRingHom f) : f (x - y) = f x - f y := by simp [sub_eq_add_neg, hf.map_add, hf.map_neg]

/-- The identity map is a ring homomorphism. -/
theorem id : IsRingHom (@id α) := by refine' { .. } <;> intros <;> rfl

-- see Note [no instance on morphisms]
/-- The composition of two ring homomorphisms is a ring homomorphism. -/
theorem comp (hf : IsRingHom f) {γ} [Ring γ] {g : β → γ} (hg : IsRingHom g) : IsRingHom (g ∘ f) :=
  { map_add := fun x y => by simp [map_add hf] <;> rw [map_add hg] <;> rfl,
    map_mul := fun x y => by simp [map_mul hf] <;> rw [map_mul hg] <;> rfl,
    map_one := by simp [map_one hf] <;> exact map_one hg }

/-- A ring homomorphism is also a semiring homomorphism. -/
theorem toIsSemiringHom (hf : IsRingHom f) : IsSemiringHom f :=
  { ‹IsRingHom f› with map_zero := map_zero hf }

theorem to_is_add_group_hom (hf : IsRingHom f) : IsAddGroupHom f :=
  { map_add := fun _ _ => hf.map_add }

end IsRingHom

variable {β : Type v} {γ : Type w} [rα : Semiring α] [rβ : Semiring β]

namespace RingHom

section

include rα rβ

/-- Interpret `f : α → β` with `is_semiring_hom f` as a ring homomorphism. -/
def of {f : α → β} (hf : IsSemiringHom f) : α →+* β :=
  { MonoidHom.of hf.to_is_monoid_hom, AddMonoidHom.of hf.to_is_add_monoid_hom with toFun := f }

@[simp]
theorem coe_of {f : α → β} (hf : IsSemiringHom f) : ⇑(of hf) = f :=
  rfl

theorem toIsSemiringHom (f : α →+* β) : IsSemiringHom f :=
  { map_zero := f.map_zero, map_one := f.map_one, map_add := f.map_add, map_mul := f.map_mul }

end

theorem toIsRingHom {α γ} [Ring α] [Ring γ] (g : α →+* γ) : IsRingHom g :=
  IsRingHom.ofSemiring g.toIsSemiringHom

end RingHom

