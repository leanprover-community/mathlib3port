/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Algebra.Order.Kleene
import Mathbin.Data.Set.Pointwise.Smul

#align_import data.set.semiring from "leanprover-community/mathlib"@"62e8311c791f02c47451bf14aa2501048e7c2f33"

/-!
# Sets as a semiring under union

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `set_semiring α`, an alias of `set α`, which we endow with `∪` as addition and
pointwise `*` as multiplication. If `α` is a (commutative) monoid, `set_semiring α` is a
(commutative) semiring.
-/


open Function Set

open scoped Pointwise

variable {α β : Type _}

#print SetSemiring /-
/-- An alias for `set α`, which has a semiring structure given by `∪` as "addition" and pointwise
  multiplication `*` as "multiplication". -/
def SetSemiring (α : Type _) : Type _ :=
  Set α
deriving Inhabited, PartialOrder, OrderBot
#align set_semiring SetSemiring
-/

#print Set.up /-
/-- The identity function `set α → set_semiring α`. -/
protected def Set.up : Set α ≃ SetSemiring α :=
  Equiv.refl _
#align set.up Set.up
-/

namespace SetSemiring

#print SetSemiring.down /-
/-- The identity function `set_semiring α → set α`. -/
protected def down : SetSemiring α ≃ Set α :=
  Equiv.refl _
#align set_semiring.down SetSemiring.down
-/

#print SetSemiring.down_up /-
@[simp]
protected theorem down_up (s : Set α) : s.up.down = s :=
  rfl
#align set_semiring.down_up SetSemiring.down_up
-/

#print SetSemiring.up_down /-
@[simp]
protected theorem up_down (s : SetSemiring α) : s.down.up = s :=
  rfl
#align set_semiring.up_down SetSemiring.up_down
-/

#print SetSemiring.up_le_up /-
-- TODO: These lemmas are not tagged `simp` because `set.le_eq_subset` simplifies the LHS
theorem up_le_up {s t : Set α} : s.up ≤ t.up ↔ s ⊆ t :=
  Iff.rfl
#align set_semiring.up_le_up SetSemiring.up_le_up
-/

#print SetSemiring.up_lt_up /-
theorem up_lt_up {s t : Set α} : s.up < t.up ↔ s ⊂ t :=
  Iff.rfl
#align set_semiring.up_lt_up SetSemiring.up_lt_up
-/

#print SetSemiring.down_subset_down /-
@[simp]
theorem down_subset_down {s t : SetSemiring α} : s.down ⊆ t.down ↔ s ≤ t :=
  Iff.rfl
#align set_semiring.down_subset_down SetSemiring.down_subset_down
-/

#print SetSemiring.down_ssubset_down /-
@[simp]
theorem down_ssubset_down {s t : SetSemiring α} : s.down ⊂ t.down ↔ s < t :=
  Iff.rfl
#align set_semiring.down_ssubset_down SetSemiring.down_ssubset_down
-/

instance : AddCommMonoid (SetSemiring α)
    where
  add s t := (s.down ∪ t.down).up
  zero := (∅ : Set α).up
  add_assoc := union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm

#print SetSemiring.zero_def /-
theorem zero_def : (0 : SetSemiring α) = Set.up ∅ :=
  rfl
#align set_semiring.zero_def SetSemiring.zero_def
-/

#print SetSemiring.down_zero /-
@[simp]
theorem down_zero : (0 : SetSemiring α).down = ∅ :=
  rfl
#align set_semiring.down_zero SetSemiring.down_zero
-/

#print Set.up_empty /-
@[simp]
theorem Set.up_empty : (∅ : Set α).up = 0 :=
  rfl
#align set.up_empty Set.up_empty
-/

#print SetSemiring.add_def /-
theorem add_def (s t : SetSemiring α) : s + t = (s.down ∪ t.down).up :=
  rfl
#align set_semiring.add_def SetSemiring.add_def
-/

#print SetSemiring.down_add /-
@[simp]
theorem down_add (s t : SetSemiring α) : (s + t).down = s.down ∪ t.down :=
  rfl
#align set_semiring.down_add SetSemiring.down_add
-/

#print Set.up_union /-
@[simp]
theorem Set.up_union (s t : Set α) : (s ∪ t).up = s.up + t.up :=
  rfl
#align set.up_union Set.up_union
-/

#print SetSemiring.covariantClass_add /-
/- Since addition on `set_semiring` is commutative (it is set union), there is no need
to also have the instance `covariant_class (set_semiring α) (set_semiring α) (swap (+)) (≤)`. -/
instance covariantClass_add : CovariantClass (SetSemiring α) (SetSemiring α) (· + ·) (· ≤ ·) :=
  ⟨fun a b c => union_subset_union_right _⟩
#align set_semiring.covariant_class_add SetSemiring.covariantClass_add
-/

section Mul

variable [Mul α]

instance : NonUnitalNonAssocSemiring (SetSemiring α) :=
  {-- reducibility linter complains if we use `(s.down * t.down).up`
    SetSemiring.addCommMonoid with
    mul := fun s t => (image2 (· * ·) s.down t.down).up
    zero_mul := fun s => empty_mul
    mul_zero := fun s => mul_empty
    left_distrib := fun _ _ _ => mul_union
    right_distrib := fun _ _ _ => union_mul }

#print SetSemiring.mul_def /-
theorem mul_def (s t : SetSemiring α) : s * t = (s.down * t.down).up :=
  rfl
#align set_semiring.mul_def SetSemiring.mul_def
-/

#print SetSemiring.down_mul /-
@[simp]
theorem down_mul (s t : SetSemiring α) : (s * t).down = s.down * t.down :=
  rfl
#align set_semiring.down_mul SetSemiring.down_mul
-/

#print Set.up_mul /-
@[simp]
theorem Set.up_mul (s t : Set α) : (s * t).up = s.up * t.up :=
  rfl
#align set.up_mul Set.up_mul
-/

instance : NoZeroDivisors (SetSemiring α) :=
  ⟨fun a b ab =>
    a.eq_empty_or_nonempty.imp_right fun ha =>
      b.eq_empty_or_nonempty.resolve_right fun hb =>
        Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩

#print SetSemiring.covariantClass_mul_left /-
instance covariantClass_mul_left : CovariantClass (SetSemiring α) (SetSemiring α) (· * ·) (· ≤ ·) :=
  ⟨fun a b c => mul_subset_mul_left⟩
#align set_semiring.covariant_class_mul_left SetSemiring.covariantClass_mul_left
-/

#print SetSemiring.covariantClass_mul_right /-
instance covariantClass_mul_right :
    CovariantClass (SetSemiring α) (SetSemiring α) (swap (· * ·)) (· ≤ ·) :=
  ⟨fun a b c => mul_subset_mul_right⟩
#align set_semiring.covariant_class_mul_right SetSemiring.covariantClass_mul_right
-/

end Mul

section One

variable [One α]

instance : One (SetSemiring α) where one := Set.up 1

#print SetSemiring.one_def /-
theorem one_def : (1 : SetSemiring α) = Set.up 1 :=
  rfl
#align set_semiring.one_def SetSemiring.one_def
-/

#print SetSemiring.down_one /-
@[simp]
theorem down_one : (1 : SetSemiring α).down = 1 :=
  rfl
#align set_semiring.down_one SetSemiring.down_one
-/

#print Set.up_one /-
@[simp]
theorem Set.up_one : (1 : Set α).up = 1 :=
  rfl
#align set.up_one Set.up_one
-/

end One

instance [MulOneClass α] : NonAssocSemiring (SetSemiring α) :=
  { SetSemiring.nonUnitalNonAssocSemiring,
    Set.mulOneClass with
    one := 1
    mul := (· * ·) }

instance [Semigroup α] : NonUnitalSemiring (SetSemiring α) :=
  { SetSemiring.nonUnitalNonAssocSemiring, Set.semigroup with }

instance [Monoid α] : IdemSemiring (SetSemiring α) :=
  { SetSemiring.nonAssocSemiring, SetSemiring.nonUnitalSemiring, Set.completeBooleanAlgebra with }

instance [CommSemigroup α] : NonUnitalCommSemiring (SetSemiring α) :=
  { SetSemiring.nonUnitalSemiring, Set.commSemigroup with }

instance [CommMonoid α] : IdemCommSemiring (SetSemiring α) :=
  { SetSemiring.idemSemiring, Set.commMonoid with }

instance [CommMonoid α] : CanonicallyOrderedCommSemiring (SetSemiring α) :=
  { SetSemiring.idemSemiring, Set.commMonoid,
    SetSemiring.noZeroDivisors with
    add_le_add_left := fun a b => add_le_add_left
    exists_add_of_le := fun a b ab => ⟨b, (union_eq_right_iff_subset.2 ab).symm⟩
    le_self_add := subset_union_left }

#print SetSemiring.imageHom /-
/-- The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets. -/
def imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) : SetSemiring α →+* SetSemiring β
    where
  toFun s := (image f s.down).up
  map_zero' := image_empty _
  map_one' := by rw [down_one, image_one, map_one, singleton_one, Set.up_one]
  map_add' := image_union _
  map_mul' _ _ := image_mul f
#align set_semiring.image_hom SetSemiring.imageHom
-/

#print SetSemiring.imageHom_def /-
theorem imageHom_def [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    imageHom f s = (image f s.down).up :=
  rfl
#align set_semiring.image_hom_def SetSemiring.imageHom_def
-/

#print SetSemiring.down_imageHom /-
@[simp]
theorem down_imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    (imageHom f s).down = f '' s.down :=
  rfl
#align set_semiring.down_image_hom SetSemiring.down_imageHom
-/

#print Set.up_image /-
@[simp]
theorem Set.up_image [MulOneClass α] [MulOneClass β] (f : α →* β) (s : Set α) :
    (f '' s).up = imageHom f s.up :=
  rfl
#align set.up_image Set.up_image
-/

end SetSemiring

