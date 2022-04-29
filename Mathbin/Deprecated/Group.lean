/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Algebra.Group.TypeTags
import Mathbin.Algebra.Hom.Equiv
import Mathbin.Algebra.Hom.Units
import Mathbin.Algebra.Ring.Basic

/-!
# Unbundled monoid and group homomorphisms

This file defines predicates for unbundled monoid and group homomorphisms. Though
bundled morphisms are preferred in mathlib, these unbundled predicates are still occasionally used
in mathlib, and probably will not go away before Lean 4
because Lean 3 often fails to coerce a bundled homomorphism to a function.

## Main Definitions

`is_monoid_hom` (deprecated), `is_group_hom` (deprecated)

## Tags

is_group_hom, is_monoid_hom

-/


universe u v

variable {α : Type u} {β : Type v}

/-- Predicate for maps which preserve an addition. -/
structure IsAddHom {α β : Type _} [Add α] [Add β] (f : α → β) : Prop where
  map_add {} : ∀ x y, f (x + y) = f x + f y

/-- Predicate for maps which preserve a multiplication. -/
@[to_additive]
structure IsMulHom {α β : Type _} [Mul α] [Mul β] (f : α → β) : Prop where
  map_mul {} : ∀ x y, f (x * y) = f x * f y

namespace IsMulHom

variable [Mul α] [Mul β] {γ : Type _} [Mul γ]

/-- The identity map preserves multiplication. -/
@[to_additive "The identity map preserves addition"]
theorem id : IsMulHom (id : α → α) :=
  { map_mul := fun _ _ => rfl }

/-- The composition of maps which preserve multiplication, also preserves multiplication. -/
@[to_additive "The composition of addition preserving maps also preserves addition"]
theorem comp {f : α → β} {g : β → γ} (hf : IsMulHom f) (hg : IsMulHom g) : IsMulHom (g ∘ f) :=
  { map_mul := fun x y => by
      simp only [Function.comp, hf.map_mul, hg.map_mul] }

/-- A product of maps which preserve multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive]
theorem mul {α β} [Semigroupₓ α] [CommSemigroupₓ β] {f g : α → β} (hf : IsMulHom f) (hg : IsMulHom g) :
    IsMulHom fun a => f a * g a :=
  { map_mul := fun a b => by
      simp only [hf.map_mul, hg.map_mul, mul_comm, mul_assoc, mul_left_commₓ] }

/-- The inverse of a map which preserves multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive]
theorem inv {α β} [Mul α] [CommGroupₓ β] {f : α → β} (hf : IsMulHom f) : IsMulHom fun a => (f a)⁻¹ :=
  { map_mul := fun a b => (hf.map_mul a b).symm ▸ mul_inv _ _ }

end IsMulHom

/-- Predicate for add_monoid homomorphisms (deprecated -- use the bundled `monoid_hom` version). -/
structure IsAddMonoidHom [AddZeroClass α] [AddZeroClass β] (f : α → β) extends IsAddHom f : Prop where
  map_zero {} : f 0 = 0

/-- Predicate for monoid homomorphisms (deprecated -- use the bundled `monoid_hom` version). -/
@[to_additive]
structure IsMonoidHom [MulOneClassₓ α] [MulOneClassₓ β] (f : α → β) extends IsMulHom f : Prop where
  map_one {} : f 1 = 1

namespace MonoidHom

variable {M : Type _} {N : Type _} [mM : MulOneClassₓ M] [mN : MulOneClassₓ N]

include mM mN

/-- Interpret a map `f : M → N` as a homomorphism `M →* N`. -/
@[to_additive "Interpret a map `f : M → N` as a homomorphism `M →+ N`."]
def of {f : M → N} (h : IsMonoidHom f) : M →* N where
  toFun := f
  map_one' := h.2
  map_mul' := h.1.1

variable {mM mN}

@[simp, to_additive]
theorem coe_of {f : M → N} (hf : IsMonoidHom f) : ⇑(MonoidHom.of hf) = f :=
  rfl

@[to_additive]
theorem is_monoid_hom_coe (f : M →* N) : IsMonoidHom (f : M → N) :=
  { map_mul := f.map_mul, map_one := f.map_one }

end MonoidHom

namespace MulEquiv

variable {M : Type _} {N : Type _} [MulOneClassₓ M] [MulOneClassₓ N]

/-- A multiplicative isomorphism preserves multiplication (deprecated). -/
@[to_additive]
theorem is_mul_hom (h : M ≃* N) : IsMulHom h :=
  ⟨h.map_mul⟩

/-- A multiplicative bijection between two monoids is a monoid hom
  (deprecated -- use `mul_equiv.to_monoid_hom`). -/
@[to_additive]
theorem is_monoid_hom (h : M ≃* N) : IsMonoidHom h :=
  { map_mul := h.map_mul, map_one := h.map_one }

end MulEquiv

namespace IsMonoidHom

variable [MulOneClassₓ α] [MulOneClassₓ β] {f : α → β} (hf : IsMonoidHom f)

/-- A monoid homomorphism preserves multiplication. -/
@[to_additive]
theorem map_mul x y : f (x * y) = f x * f y :=
  hf.map_mul x y

/-- The inverse of a map which preserves multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive]
theorem inv {α β} [MulOneClassₓ α] [CommGroupₓ β] {f : α → β} (hf : IsMonoidHom f) : IsMonoidHom fun a => (f a)⁻¹ :=
  { map_one := hf.map_one.symm ▸ one_inv, map_mul := fun a b => (hf.map_mul a b).symm ▸ mul_inv _ _ }

end IsMonoidHom

/-- A map to a group preserving multiplication is a monoid homomorphism. -/
@[to_additive]
theorem IsMulHom.to_is_monoid_hom [MulOneClassₓ α] [Groupₓ β] {f : α → β} (hf : IsMulHom f) : IsMonoidHom f :=
  { map_one :=
      mul_right_eq_self.1 <| by
        rw [← hf.map_mul, one_mulₓ],
    map_mul := hf.map_mul }

namespace IsMonoidHom

variable [MulOneClassₓ α] [MulOneClassₓ β] {f : α → β}

/-- The identity map is a monoid homomorphism. -/
@[to_additive]
theorem id : IsMonoidHom (@id α) :=
  { map_one := rfl, map_mul := fun _ _ => rfl }

/-- The composite of two monoid homomorphisms is a monoid homomorphism. -/
@[to_additive]
theorem comp (hf : IsMonoidHom f) {γ} [MulOneClassₓ γ] {g : β → γ} (hg : IsMonoidHom g) : IsMonoidHom (g ∘ f) :=
  { IsMulHom.comp hf.to_is_mul_hom hg.to_is_mul_hom with
    map_one :=
      show g _ = 1 by
        rw [hf.map_one, hg.map_one] }

end IsMonoidHom

namespace IsAddMonoidHom

/-- Left multiplication in a ring is an additive monoid morphism. -/
theorem is_add_monoid_hom_mul_left {γ : Type _} [NonUnitalNonAssocSemiringₓ γ] (x : γ) :
    IsAddMonoidHom fun y : γ => x * y :=
  { map_zero := mul_zero x, map_add := fun y z => mul_addₓ x y z }

/-- Right multiplication in a ring is an additive monoid morphism. -/
theorem is_add_monoid_hom_mul_right {γ : Type _} [NonUnitalNonAssocSemiringₓ γ] (x : γ) :
    IsAddMonoidHom fun y : γ => y * x :=
  { map_zero := zero_mul x, map_add := fun y z => add_mulₓ y z x }

end IsAddMonoidHom

/-- Predicate for additive group homomorphism (deprecated -- use bundled `monoid_hom`). -/
structure IsAddGroupHom [AddGroupₓ α] [AddGroupₓ β] (f : α → β) extends IsAddHom f : Prop

/-- Predicate for group homomorphisms (deprecated -- use bundled `monoid_hom`). -/
@[to_additive]
structure IsGroupHom [Groupₓ α] [Groupₓ β] (f : α → β) extends IsMulHom f : Prop

@[to_additive]
theorem MonoidHom.is_group_hom {G H : Type _} {_ : Groupₓ G} {_ : Groupₓ H} (f : G →* H) : IsGroupHom (f : G → H) :=
  { map_mul := f.map_mul }

@[to_additive]
theorem MulEquiv.is_group_hom {G H : Type _} {_ : Groupₓ G} {_ : Groupₓ H} (h : G ≃* H) : IsGroupHom h :=
  { map_mul := h.map_mul }

/-- Construct `is_group_hom` from its only hypothesis. -/
@[to_additive]
theorem IsGroupHom.mk' [Groupₓ α] [Groupₓ β] {f : α → β} (hf : ∀ x y, f (x * y) = f x * f y) : IsGroupHom f :=
  { map_mul := hf }

namespace IsGroupHom

variable [Groupₓ α] [Groupₓ β] {f : α → β} (hf : IsGroupHom f)

open IsMulHom (map_mul)

theorem map_mul : ∀ x y, f (x * y) = f x * f y :=
  hf.to_is_mul_hom.map_mul

/-- A group homomorphism is a monoid homomorphism. -/
@[to_additive]
theorem to_is_monoid_hom : IsMonoidHom f :=
  hf.to_is_mul_hom.to_is_monoid_hom

/-- A group homomorphism sends 1 to 1. -/
@[to_additive]
theorem map_one : f 1 = 1 :=
  hf.to_is_monoid_hom.map_one

/-- A group homomorphism sends inverses to inverses. -/
@[to_additive]
theorem map_inv (hf : IsGroupHom f) (a : α) : f a⁻¹ = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one <| by
    rw [← hf.map_mul, inv_mul_selfₓ, hf.map_one]

/-- The identity is a group homomorphism. -/
@[to_additive]
theorem id : IsGroupHom (@id α) :=
  { map_mul := fun _ _ => rfl }

/-- The composition of two group homomorphisms is a group homomorphism. -/
@[to_additive]
theorem comp (hf : IsGroupHom f) {γ} [Groupₓ γ] {g : β → γ} (hg : IsGroupHom g) : IsGroupHom (g ∘ f) :=
  { IsMulHom.comp hf.to_is_mul_hom hg.to_is_mul_hom with }

/-- A group homomorphism is injective iff its kernel is trivial. -/
@[to_additive]
theorem injective_iff {f : α → β} (hf : IsGroupHom f) : Function.Injective f ↔ ∀ a, f a = 1 → a = 1 :=
  ⟨fun h _ => by
    rw [← hf.map_one] <;> exact @h _ _, fun h x y hxy => by
    rw [← inv_invₓ (f x), inv_eq_iff_mul_eq_one, ← hf.map_inv, ← hf.map_mul] at hxy <;>
      simpa using inv_eq_of_mul_eq_oneₓ (h _ hxy)⟩

/-- The product of group homomorphisms is a group homomorphism if the target is commutative. -/
@[to_additive]
theorem mul {α β} [Groupₓ α] [CommGroupₓ β] {f g : α → β} (hf : IsGroupHom f) (hg : IsGroupHom g) :
    IsGroupHom fun a => f a * g a :=
  { map_mul := (hf.to_is_mul_hom.mul hg.to_is_mul_hom).map_mul }

/-- The inverse of a group homomorphism is a group homomorphism if the target is commutative. -/
@[to_additive]
theorem inv {α β} [Groupₓ α] [CommGroupₓ β] {f : α → β} (hf : IsGroupHom f) : IsGroupHom fun a => (f a)⁻¹ :=
  { map_mul := hf.to_is_mul_hom.inv.map_mul }

end IsGroupHom

namespace RingHom

/-!
These instances look redundant, because `deprecated.ring` provides `is_ring_hom` for a `→+*`.
Nevertheless these are harmless, and helpful for stripping out dependencies on `deprecated.ring`.
-/


variable {R : Type _} {S : Type _}

section

variable [NonAssocSemiringₓ R] [NonAssocSemiringₓ S]

theorem to_is_monoid_hom (f : R →+* S) : IsMonoidHom f :=
  { map_one := f.map_one, map_mul := f.map_mul }

theorem to_is_add_monoid_hom (f : R →+* S) : IsAddMonoidHom f :=
  { map_zero := f.map_zero, map_add := f.map_add }

end

section

variable [Ringₓ R] [Ringₓ S]

theorem to_is_add_group_hom (f : R →+* S) : IsAddGroupHom f :=
  { map_add := f.map_add }

end

end RingHom

/-- Inversion is a group homomorphism if the group is commutative. -/
@[to_additive Neg.is_add_group_hom "Negation is an `add_group` homomorphism if the `add_group` is commutative."]
theorem Inv.is_group_hom [CommGroupₓ α] : IsGroupHom (Inv.inv : α → α) :=
  { map_mul := mul_inv }

namespace IsAddGroupHom

variable [AddGroupₓ α] [AddGroupₓ β] {f : α → β} (hf : IsAddGroupHom f)

/-- Additive group homomorphisms commute with subtraction. -/
theorem map_sub a b : f (a - b) = f a - f b :=
  calc
    f (a - b) = f (a + -b) := congr_argₓ f (sub_eq_add_neg a b)
    _ = f a + f (-b) := hf.map_add _ _
    _ = f a + -f b := by
      rw [hf.map_neg]
    _ = f a - f b := (sub_eq_add_neg _ _).symm
    

end IsAddGroupHom

/-- The difference of two additive group homomorphisms is an additive group
homomorphism if the target is commutative. -/
theorem IsAddGroupHom.sub {α β} [AddGroupₓ α] [AddCommGroupₓ β] {f g : α → β} (hf : IsAddGroupHom f)
    (hg : IsAddGroupHom g) : IsAddGroupHom fun a => f a - g a := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

namespace Units

variable {M : Type _} {N : Type _} [Monoidₓ M] [Monoidₓ N]

/-- The group homomorphism on units induced by a multiplicative morphism. -/
@[reducible]
def map' {f : M → N} (hf : IsMonoidHom f) : Mˣ →* Nˣ :=
  map (MonoidHom.of hf)

@[simp]
theorem coe_map' {f : M → N} (hf : IsMonoidHom f) (x : Mˣ) : ↑((map' hf : Mˣ → Nˣ) x) = f x :=
  rfl

theorem coe_is_monoid_hom : IsMonoidHom (coe : Mˣ → M) :=
  (coeHom M).is_monoid_hom_coe

end Units

namespace IsUnit

variable {M : Type _} {N : Type _} [Monoidₓ M] [Monoidₓ N] {x : M}

theorem map' {f : M → N} (hf : IsMonoidHom f) {x : M} (h : IsUnit x) : IsUnit (f x) :=
  h.map (MonoidHom.of hf)

end IsUnit

theorem Additive.is_add_hom [Mul α] [Mul β] {f : α → β} (hf : IsMulHom f) : @IsAddHom (Additive α) (Additive β) _ _ f :=
  { map_add := IsMulHom.map_mul hf }

theorem Multiplicative.is_mul_hom [Add α] [Add β] {f : α → β} (hf : IsAddHom f) :
    @IsMulHom (Multiplicative α) (Multiplicative β) _ _ f :=
  { map_mul := IsAddHom.map_add hf }

-- defeq abuse
theorem Additive.is_add_monoid_hom [MulOneClassₓ α] [MulOneClassₓ β] {f : α → β} (hf : IsMonoidHom f) :
    @IsAddMonoidHom (Additive α) (Additive β) _ _ f :=
  { Additive.is_add_hom hf.to_is_mul_hom with map_zero := hf.map_one }

theorem Multiplicative.is_monoid_hom [AddZeroClass α] [AddZeroClass β] {f : α → β} (hf : IsAddMonoidHom f) :
    @IsMonoidHom (Multiplicative α) (Multiplicative β) _ _ f :=
  { Multiplicative.is_mul_hom hf.to_is_add_hom with map_one := IsAddMonoidHom.map_zero hf }

theorem Additive.is_add_group_hom [Groupₓ α] [Groupₓ β] {f : α → β} (hf : IsGroupHom f) :
    @IsAddGroupHom (Additive α) (Additive β) _ _ f :=
  { map_add := hf.to_is_mul_hom.map_mul }

theorem Multiplicative.is_group_hom [AddGroupₓ α] [AddGroupₓ β] {f : α → β} (hf : IsAddGroupHom f) :
    @IsGroupHom (Multiplicative α) (Multiplicative β) _ _ f :=
  { map_mul := hf.to_is_add_hom.map_add }

