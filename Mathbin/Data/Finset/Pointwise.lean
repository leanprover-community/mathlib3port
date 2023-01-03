/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies

! This file was ported from Lean 3 source module data.finset.pointwise
! leanprover-community/mathlib commit 6cb77a8eaff0ddd100e87b1591c6d3ad319514ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.NAry
import Mathbin.Data.Finset.Preimage
import Mathbin.Data.Set.Pointwise.Smul
import Mathbin.Data.Set.Pointwise.ListOfFn

/-!
# Pointwise operations of finsets

This file defines pointwise algebraic operations on finsets.

## Main declarations

For finsets `s` and `t`:
* `0` (`finset.has_zero`): The singleton `{0}`.
* `1` (`finset.has_one`): The singleton `{1}`.
* `-s` (`finset.has_neg`): Negation, finset of all `-x` where `x ∈ s`.
* `s⁻¹` (`finset.has_inv`): Inversion, finset of all `x⁻¹` where `x ∈ s`.
* `s + t` (`finset.has_add`): Addition, finset of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s * t` (`finset.has_mul`): Multiplication, finset of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s - t` (`finset.has_sub`): Subtraction, finset of all `x - y` where `x ∈ s` and `y ∈ t`.
* `s / t` (`finset.has_div`): Division, finset of all `x / y` where `x ∈ s` and `y ∈ t`.
* `s +ᵥ t` (`finset.has_vadd`): Scalar addition, finset of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s • t` (`finset.has_smul`): Scalar multiplication, finset of all `x • y` where `x ∈ s` and
  `y ∈ t`.
* `s -ᵥ t` (`finset.has_vsub`): Scalar subtraction, finset of all `x -ᵥ y` where `x ∈ s` and
  `y ∈ t`.
* `a • s` (`finset.has_smul_finset`): Scaling, finset of all `a • x` where `x ∈ s`.
* `a +ᵥ s` (`finset.has_vadd_finset`): Translation, finset of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `finset α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

## Implementation notes

We put all instances in the locale `pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the locale to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`.

## Tags

finset multiplication, finset addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/


open Function

open BigOperators Pointwise

variable {F α β γ : Type _}

namespace Finset

/-! ### `0`/`1` as finsets -/


section One

variable [One α] {s : Finset α} {a : α}

/-- The finset `1 : finset α` is defined as `{1}` in locale `pointwise`. -/
@[to_additive "The finset `0 : finset α` is defined as `{0}` in locale `pointwise`."]
protected def hasOne : One (Finset α) :=
  ⟨{1}⟩
#align finset.has_one Finset.hasOne

scoped[Pointwise] attribute [instance] Finset.hasOne Finset.hasZero

@[simp, to_additive]
theorem mem_one : a ∈ (1 : Finset α) ↔ a = 1 :=
  mem_singleton
#align finset.mem_one Finset.mem_one

@[simp, norm_cast, to_additive]
theorem coe_one : ↑(1 : Finset α) = (1 : Set α) :=
  coe_singleton 1
#align finset.coe_one Finset.coe_one

@[simp, to_additive]
theorem one_subset : (1 : Finset α) ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff
#align finset.one_subset Finset.one_subset

@[to_additive]
theorem singleton_one : ({1} : Finset α) = 1 :=
  rfl
#align finset.singleton_one Finset.singleton_one

@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Finset α) :=
  mem_singleton_self _
#align finset.one_mem_one Finset.one_mem_one

@[to_additive]
theorem one_nonempty : (1 : Finset α).Nonempty :=
  ⟨1, one_mem_one⟩
#align finset.one_nonempty Finset.one_nonempty

@[simp, to_additive]
protected theorem map_one {f : α ↪ β} : map f 1 = {f 1} :=
  map_singleton f 1
#align finset.map_one Finset.map_one

@[simp, to_additive]
theorem image_one [DecidableEq β] {f : α → β} : image f 1 = {f 1} :=
  image_singleton _ _
#align finset.image_one Finset.image_one

@[to_additive]
theorem subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 :=
  subset_singleton_iff
#align finset.subset_one_iff_eq Finset.subset_one_iff_eq

@[to_additive]
theorem Nonempty.subset_one_iff (h : s.Nonempty) : s ⊆ 1 ↔ s = 1 :=
  h.subset_singleton_iff
#align finset.nonempty.subset_one_iff Finset.Nonempty.subset_one_iff

/-- The singleton operation as a `one_hom`. -/
@[to_additive "The singleton operation as a `zero_hom`."]
def singletonOneHom : OneHom α (Finset α) :=
  ⟨singleton, singleton_one⟩
#align finset.singleton_one_hom Finset.singletonOneHom

@[simp, to_additive]
theorem coe_singleton_one_hom : (singletonOneHom : α → Finset α) = singleton :=
  rfl
#align finset.coe_singleton_one_hom Finset.coe_singleton_one_hom

@[simp, to_additive]
theorem singleton_one_hom_apply (a : α) : singletonOneHom a = {a} :=
  rfl
#align finset.singleton_one_hom_apply Finset.singleton_one_hom_apply

/-- Lift a `one_hom` to `finset` via `image`. -/
@[to_additive "Lift a `zero_hom` to `finset` via `image`", simps]
def imageOneHom [DecidableEq β] [One β] [OneHomClass F α β] (f : F) : OneHom (Finset α) (Finset β)
    where
  toFun := Finset.image f
  map_one' := by rw [image_one, map_one, singleton_one]
#align finset.image_one_hom Finset.imageOneHom

end One

/-! ### Finset negation/inversion -/


section Inv

variable [DecidableEq α] [Inv α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

/-- The pointwise inversion of finset `s⁻¹` is defined as `{x⁻¹ | x ∈ s}` in locale `pointwise`. -/
@[to_additive
      "The pointwise negation of finset `-s` is defined as `{-x | x ∈ s}` in locale\n`pointwise`."]
protected def hasInv : Inv (Finset α) :=
  ⟨image Inv.inv⟩
#align finset.has_inv Finset.hasInv

scoped[Pointwise] attribute [instance] Finset.hasInv Finset.hasNeg

@[to_additive]
theorem inv_def : s⁻¹ = s.image fun x => x⁻¹ :=
  rfl
#align finset.inv_def Finset.inv_def

@[to_additive]
theorem image_inv : (s.image fun x => x⁻¹) = s⁻¹ :=
  rfl
#align finset.image_inv Finset.image_inv

@[to_additive]
theorem mem_inv {x : α} : x ∈ s⁻¹ ↔ ∃ y ∈ s, y⁻¹ = x :=
  mem_image
#align finset.mem_inv Finset.mem_inv

@[to_additive]
theorem inv_mem_inv (ha : a ∈ s) : a⁻¹ ∈ s⁻¹ :=
  mem_image_of_mem _ ha
#align finset.inv_mem_inv Finset.inv_mem_inv

@[to_additive]
theorem card_inv_le : s⁻¹.card ≤ s.card :=
  card_image_le
#align finset.card_inv_le Finset.card_inv_le

@[simp, to_additive]
theorem inv_empty : (∅ : Finset α)⁻¹ = ∅ :=
  image_empty _
#align finset.inv_empty Finset.inv_empty

@[simp, to_additive]
theorem inv_nonempty_iff : s⁻¹.Nonempty ↔ s.Nonempty :=
  Nonempty.image_iff _
#align finset.inv_nonempty_iff Finset.inv_nonempty_iff

alias inv_nonempty_iff ↔ nonempty.inv nonempty.of_inv

@[to_additive, mono]
theorem inv_subset_inv (h : s ⊆ t) : s⁻¹ ⊆ t⁻¹ :=
  image_subset_image h
#align finset.inv_subset_inv Finset.inv_subset_inv

attribute [mono] neg_subset_neg

@[simp, to_additive]
theorem inv_singleton (a : α) : ({a} : Finset α)⁻¹ = {a⁻¹} :=
  image_singleton _ _
#align finset.inv_singleton Finset.inv_singleton

@[simp, to_additive]
theorem inv_insert (a : α) (s : Finset α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ :=
  image_insert _ _ _
#align finset.inv_insert Finset.inv_insert

end Inv

open Pointwise

section InvolutiveInv

variable [DecidableEq α] [InvolutiveInv α] (s : Finset α)

@[simp, norm_cast, to_additive]
theorem coe_inv : ↑s⁻¹ = (s : Set α)⁻¹ :=
  coe_image.trans Set.image_inv
#align finset.coe_inv Finset.coe_inv

@[simp, to_additive]
theorem card_inv : s⁻¹.card = s.card :=
  card_image_of_injective _ inv_injective
#align finset.card_inv Finset.card_inv

@[simp, to_additive]
theorem preimage_inv : s.Preimage Inv.inv (inv_injective.InjOn _) = s⁻¹ :=
  coe_injective <| by rw [coe_preimage, Set.inv_preimage, coe_inv]
#align finset.preimage_inv Finset.preimage_inv

end InvolutiveInv

/-! ### Finset addition/multiplication -/


section Mul

variable [DecidableEq α] [DecidableEq β] [Mul α] [Mul β] [MulHomClass F α β] (f : F)
  {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

/-- The pointwise multiplication of finsets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}`
in locale `pointwise`. -/
@[to_additive
      "The pointwise addition of finsets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in\nlocale `pointwise`."]
protected def hasMul : Mul (Finset α) :=
  ⟨image₂ (· * ·)⟩
#align finset.has_mul Finset.hasMul

scoped[Pointwise] attribute [instance] Finset.hasMul Finset.hasAdd

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem mul_def : s * t = (s ×ˢ t).image fun p : α × α => p.1 * p.2 :=
  rfl
#align finset.mul_def Finset.mul_def

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem image_mul_product : ((s ×ˢ t).image fun x : α × α => x.fst * x.snd) = s * t :=
  rfl
#align finset.image_mul_product Finset.image_mul_product

@[to_additive]
theorem mem_mul {x : α} : x ∈ s * t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x :=
  mem_image₂
#align finset.mem_mul Finset.mem_mul

@[simp, norm_cast, to_additive]
theorem coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t :=
  coe_image₂ _ _ _
#align finset.coe_mul Finset.coe_mul

@[to_additive]
theorem mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t :=
  mem_image₂_of_mem
#align finset.mul_mem_mul Finset.mul_mem_mul

@[to_additive]
theorem card_mul_le : (s * t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _
#align finset.card_mul_le Finset.card_mul_le

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem card_mul_iff :
    (s * t).card = s.card * t.card ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => p.1 * p.2 :=
  card_image₂_iff
#align finset.card_mul_iff Finset.card_mul_iff

@[simp, to_additive]
theorem empty_mul (s : Finset α) : ∅ * s = ∅ :=
  image₂_empty_left
#align finset.empty_mul Finset.empty_mul

@[simp, to_additive]
theorem mul_empty (s : Finset α) : s * ∅ = ∅ :=
  image₂_empty_right
#align finset.mul_empty Finset.mul_empty

@[simp, to_additive]
theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.mul_eq_empty Finset.mul_eq_empty

@[simp, to_additive]
theorem mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.mul_nonempty Finset.mul_nonempty

@[to_additive]
theorem Nonempty.mul : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
  nonempty.image₂
#align finset.nonempty.mul Finset.Nonempty.mul

@[to_additive]
theorem Nonempty.of_mul_left : (s * t).Nonempty → s.Nonempty :=
  nonempty.of_image₂_left
#align finset.nonempty.of_mul_left Finset.Nonempty.of_mul_left

@[to_additive]
theorem Nonempty.of_mul_right : (s * t).Nonempty → t.Nonempty :=
  nonempty.of_image₂_right
#align finset.nonempty.of_mul_right Finset.Nonempty.of_mul_right

@[to_additive]
theorem mul_singleton (a : α) : s * {a} = s.image (· * a) :=
  image₂_singleton_right
#align finset.mul_singleton Finset.mul_singleton

@[to_additive]
theorem singleton_mul (a : α) : {a} * s = s.image ((· * ·) a) :=
  image₂_singleton_left
#align finset.singleton_mul Finset.singleton_mul

@[simp, to_additive]
theorem singleton_mul_singleton (a b : α) : ({a} : Finset α) * {b} = {a * b} :=
  image₂_singleton
#align finset.singleton_mul_singleton Finset.singleton_mul_singleton

@[to_additive, mono]
theorem mul_subset_mul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ * t₁ ⊆ s₂ * t₂ :=
  image₂_subset
#align finset.mul_subset_mul Finset.mul_subset_mul

@[to_additive]
theorem mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ :=
  image₂_subset_left
#align finset.mul_subset_mul_left Finset.mul_subset_mul_left

@[to_additive]
theorem mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t :=
  image₂_subset_right
#align finset.mul_subset_mul_right Finset.mul_subset_mul_right

@[to_additive]
theorem mul_subset_iff : s * t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x * y ∈ u :=
  image₂_subset_iff
#align finset.mul_subset_iff Finset.mul_subset_iff

attribute [mono] add_subset_add

@[to_additive]
theorem union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t :=
  image₂_union_left
#align finset.union_mul Finset.union_mul

@[to_additive]
theorem mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ :=
  image₂_union_right
#align finset.mul_union Finset.mul_union

@[to_additive]
theorem inter_mul_subset : s₁ ∩ s₂ * t ⊆ s₁ * t ∩ (s₂ * t) :=
  image₂_inter_subset_left
#align finset.inter_mul_subset Finset.inter_mul_subset

@[to_additive]
theorem mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
  image₂_inter_subset_right
#align finset.mul_inter_subset Finset.mul_inter_subset

/-- If a finset `u` is contained in the product of two sets `s * t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' * t'`. -/
@[to_additive
      "If a finset `u` is contained in the sum of two sets `s + t`, we can find two finsets\n`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' + t'`."]
theorem subset_mul {s t : Set α} :
    ↑u ⊆ s * t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' * t' :=
  subset_image₂
#align finset.subset_mul Finset.subset_mul

@[to_additive]
theorem image_mul : (s * t).image (f : α → β) = s.image f * t.image f :=
  image_image₂_distrib <| map_mul f
#align finset.image_mul Finset.image_mul

/-- The singleton operation as a `mul_hom`. -/
@[to_additive "The singleton operation as an `add_hom`."]
def singletonMulHom : α →ₙ* Finset α :=
  ⟨singleton, fun a b => (singleton_mul_singleton _ _).symm⟩
#align finset.singleton_mul_hom Finset.singletonMulHom

@[simp, to_additive]
theorem coe_singleton_mul_hom : (singletonMulHom : α → Finset α) = singleton :=
  rfl
#align finset.coe_singleton_mul_hom Finset.coe_singleton_mul_hom

@[simp, to_additive]
theorem singleton_mul_hom_apply (a : α) : singletonMulHom a = {a} :=
  rfl
#align finset.singleton_mul_hom_apply Finset.singleton_mul_hom_apply

/-- Lift a `mul_hom` to `finset` via `image`. -/
@[to_additive "Lift an `add_hom` to `finset` via `image`", simps]
def imageMulHom : Finset α →ₙ* Finset β
    where
  toFun := Finset.image f
  map_mul' s t := image_mul _
#align finset.image_mul_hom Finset.imageMulHom

end Mul

/-! ### Finset subtraction/division -/


section Div

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

/-- The pointwise division of sfinets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`pointwise`. -/
@[to_additive
      "The pointwise subtraction of finsets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}`\nin locale `pointwise`."]
protected def hasDiv : Div (Finset α) :=
  ⟨image₂ (· / ·)⟩
#align finset.has_div Finset.hasDiv

scoped[Pointwise] attribute [instance] Finset.hasDiv Finset.hasSub

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem div_def : s / t = (s ×ˢ t).image fun p : α × α => p.1 / p.2 :=
  rfl
#align finset.div_def Finset.div_def

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive add_image_prod]
theorem image_div_prod : ((s ×ˢ t).image fun x : α × α => x.fst / x.snd) = s / t :=
  rfl
#align finset.image_div_prod Finset.image_div_prod

@[to_additive]
theorem mem_div : a ∈ s / t ↔ ∃ b c, b ∈ s ∧ c ∈ t ∧ b / c = a :=
  mem_image₂
#align finset.mem_div Finset.mem_div

@[simp, norm_cast, to_additive]
theorem coe_div (s t : Finset α) : (↑(s / t) : Set α) = ↑s / ↑t :=
  coe_image₂ _ _ _
#align finset.coe_div Finset.coe_div

@[to_additive]
theorem div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t :=
  mem_image₂_of_mem
#align finset.div_mem_div Finset.div_mem_div

@[to_additive]
theorem div_card_le : (s / t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _
#align finset.div_card_le Finset.div_card_le

@[simp, to_additive]
theorem empty_div (s : Finset α) : ∅ / s = ∅ :=
  image₂_empty_left
#align finset.empty_div Finset.empty_div

@[simp, to_additive]
theorem div_empty (s : Finset α) : s / ∅ = ∅ :=
  image₂_empty_right
#align finset.div_empty Finset.div_empty

@[simp, to_additive]
theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.div_eq_empty Finset.div_eq_empty

@[simp, to_additive]
theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.div_nonempty Finset.div_nonempty

@[to_additive]
theorem Nonempty.div : s.Nonempty → t.Nonempty → (s / t).Nonempty :=
  nonempty.image₂
#align finset.nonempty.div Finset.Nonempty.div

@[to_additive]
theorem Nonempty.of_div_left : (s / t).Nonempty → s.Nonempty :=
  nonempty.of_image₂_left
#align finset.nonempty.of_div_left Finset.Nonempty.of_div_left

@[to_additive]
theorem Nonempty.of_div_right : (s / t).Nonempty → t.Nonempty :=
  nonempty.of_image₂_right
#align finset.nonempty.of_div_right Finset.Nonempty.of_div_right

@[simp, to_additive]
theorem div_singleton (a : α) : s / {a} = s.image (· / a) :=
  image₂_singleton_right
#align finset.div_singleton Finset.div_singleton

@[simp, to_additive]
theorem singleton_div (a : α) : {a} / s = s.image ((· / ·) a) :=
  image₂_singleton_left
#align finset.singleton_div Finset.singleton_div

@[simp, to_additive]
theorem singleton_div_singleton (a b : α) : ({a} : Finset α) / {b} = {a / b} :=
  image₂_singleton
#align finset.singleton_div_singleton Finset.singleton_div_singleton

@[to_additive, mono]
theorem div_subset_div : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ / t₁ ⊆ s₂ / t₂ :=
  image₂_subset
#align finset.div_subset_div Finset.div_subset_div

@[to_additive]
theorem div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ :=
  image₂_subset_left
#align finset.div_subset_div_left Finset.div_subset_div_left

@[to_additive]
theorem div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t :=
  image₂_subset_right
#align finset.div_subset_div_right Finset.div_subset_div_right

@[to_additive]
theorem div_subset_iff : s / t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x / y ∈ u :=
  image₂_subset_iff
#align finset.div_subset_iff Finset.div_subset_iff

attribute [mono] sub_subset_sub

@[to_additive]
theorem union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t :=
  image₂_union_left
#align finset.union_div Finset.union_div

@[to_additive]
theorem div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ :=
  image₂_union_right
#align finset.div_union Finset.div_union

@[to_additive]
theorem inter_div_subset : s₁ ∩ s₂ / t ⊆ s₁ / t ∩ (s₂ / t) :=
  image₂_inter_subset_left
#align finset.inter_div_subset Finset.inter_div_subset

@[to_additive]
theorem div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
  image₂_inter_subset_right
#align finset.div_inter_subset Finset.div_inter_subset

/-- If a finset `u` is contained in the product of two sets `s / t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' / t'`. -/
@[to_additive
      "If a finset `u` is contained in the sum of two sets `s - t`, we can find two finsets\n`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' - t'`."]
theorem subset_div {s t : Set α} :
    ↑u ⊆ s / t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' / t' :=
  subset_image₂
#align finset.subset_div Finset.subset_div

end Div

/-! ### Instances -/


open Pointwise

section Instances

variable [DecidableEq α] [DecidableEq β]

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `finset`. See
note [pointwise nat action]. -/
protected def hasNsmul [Zero α] [Add α] : HasSmul ℕ (Finset α) :=
  ⟨nsmulRec⟩
#align finset.has_nsmul Finset.hasNsmul

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`finset`. See note [pointwise nat action]. -/
@[to_additive]
protected def hasNpow [One α] [Mul α] : Pow (Finset α) ℕ :=
  ⟨fun s n => npowRec n s⟩
#align finset.has_npow Finset.hasNpow

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `finset`. See note [pointwise nat action]. -/
protected def hasZsmul [Zero α] [Add α] [Neg α] : HasSmul ℤ (Finset α) :=
  ⟨zsmulRec⟩
#align finset.has_zsmul Finset.hasZsmul

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `finset`. See note [pointwise nat action]. -/
@[to_additive]
protected def hasZpow [One α] [Mul α] [Inv α] : Pow (Finset α) ℤ :=
  ⟨fun s n => zpowRec n s⟩
#align finset.has_zpow Finset.hasZpow

scoped[Pointwise] attribute [instance] Finset.hasNsmul Finset.hasNpow Finset.hasZsmul Finset.hasZpow

/-- `finset α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_semigroup` under pointwise operations if `α` is. "]
protected def semigroup [Semigroup α] : Semigroup (Finset α) :=
  coe_injective.Semigroup _ coe_mul
#align finset.semigroup Finset.semigroup

/-- `finset α` is a `comm_semigroup` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_comm_semigroup` under pointwise operations if `α` is. "]
protected def commSemigroup [CommSemigroup α] : CommSemigroup (Finset α) :=
  coe_injective.CommSemigroup _ coe_mul
#align finset.comm_semigroup Finset.commSemigroup

section MulOneClass

variable [MulOneClass α]

/-- `finset α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mulOneClass : MulOneClass (Finset α) :=
  coe_injective.MulOneClass _ (coe_singleton 1) coe_mul
#align finset.mul_one_class Finset.mulOneClass

scoped[Pointwise]
  attribute [instance]
    Finset.semigroup Finset.addSemigroup Finset.commSemigroup Finset.addCommSemigroup Finset.mulOneClass Finset.addZeroClass

@[to_additive]
theorem subset_mul_left (s : Finset α) {t : Finset α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun a ha =>
  mem_mul.2 ⟨a, 1, ha, ht, mul_one _⟩
#align finset.subset_mul_left Finset.subset_mul_left

@[to_additive]
theorem subset_mul_right {s : Finset α} (t : Finset α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun a ha =>
  mem_mul.2 ⟨1, a, hs, ha, one_mul _⟩
#align finset.subset_mul_right Finset.subset_mul_right

/-- The singleton operation as a `monoid_hom`. -/
@[to_additive "The singleton operation as an `add_monoid_hom`."]
def singletonMonoidHom : α →* Finset α :=
  { singletonMulHom, singletonOneHom with }
#align finset.singleton_monoid_hom Finset.singletonMonoidHom

@[simp, to_additive]
theorem coe_singleton_monoid_hom : (singletonMonoidHom : α → Finset α) = singleton :=
  rfl
#align finset.coe_singleton_monoid_hom Finset.coe_singleton_monoid_hom

@[simp, to_additive]
theorem singleton_monoid_hom_apply (a : α) : singletonMonoidHom a = {a} :=
  rfl
#align finset.singleton_monoid_hom_apply Finset.singleton_monoid_hom_apply

/-- The coercion from `finset` to `set` as a `monoid_hom`. -/
@[to_additive "The coercion from `finset` to `set` as an `add_monoid_hom`."]
def coeMonoidHom : Finset α →* Set α where
  toFun := coe
  map_one' := coe_one
  map_mul' := coe_mul
#align finset.coe_monoid_hom Finset.coeMonoidHom

@[simp, to_additive]
theorem coe_coe_monoid_hom : (coeMonoidHom : Finset α → Set α) = coe :=
  rfl
#align finset.coe_coe_monoid_hom Finset.coe_coe_monoid_hom

@[simp, to_additive]
theorem coe_monoid_hom_apply (s : Finset α) : coeMonoidHom s = s :=
  rfl
#align finset.coe_monoid_hom_apply Finset.coe_monoid_hom_apply

/-- Lift a `monoid_hom` to `finset` via `image`. -/
@[to_additive "Lift an `add_monoid_hom` to `finset` via `image`", simps]
def imageMonoidHom [MulOneClass β] [MonoidHomClass F α β] (f : F) : Finset α →* Finset β :=
  { imageMulHom f, imageOneHom f with }
#align finset.image_monoid_hom Finset.imageMonoidHom

end MulOneClass

section Monoid

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

@[simp, norm_cast, to_additive]
theorem coe_pow (s : Finset α) (n : ℕ) : ↑(s ^ n) = (s ^ n : Set α) :=
  by
  change ↑(npowRec n s) = _
  induction' n with n ih
  · rw [npowRec, pow_zero, coe_one]
  · rw [npowRec, pow_succ, coe_mul, ih]
#align finset.coe_pow Finset.coe_pow

/-- `finset α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_monoid` under pointwise operations if `α` is. "]
protected def monoid : Monoid (Finset α) :=
  coe_injective.Monoid _ coe_one coe_mul coe_pow
#align finset.monoid Finset.monoid

scoped[Pointwise] attribute [instance] Finset.monoid Finset.addMonoid

@[to_additive]
theorem pow_mem_pow (ha : a ∈ s) : ∀ n : ℕ, a ^ n ∈ s ^ n
  | 0 => by
    rw [pow_zero]
    exact one_mem_one
  | n + 1 => by
    rw [pow_succ]
    exact mul_mem_mul ha (pow_mem_pow _)
#align finset.pow_mem_pow Finset.pow_mem_pow

@[to_additive]
theorem pow_subset_pow (hst : s ⊆ t) : ∀ n : ℕ, s ^ n ⊆ t ^ n
  | 0 => by
    rw [pow_zero]
    exact subset.rfl
  | n + 1 => by
    rw [pow_succ]
    exact mul_subset_mul hst (pow_subset_pow _)
#align finset.pow_subset_pow Finset.pow_subset_pow

@[to_additive]
theorem pow_subset_pow_of_one_mem (hs : (1 : α) ∈ s) : m ≤ n → s ^ m ⊆ s ^ n :=
  by
  refine' Nat.le_induction _ (fun n h ih => _) _
  · exact subset.rfl
  · rw [pow_succ]
    exact ih.trans (subset_mul_right _ hs)
#align finset.pow_subset_pow_of_one_mem Finset.pow_subset_pow_of_one_mem

@[simp, norm_cast, to_additive]
theorem coe_list_prod (s : List (Finset α)) : (↑s.Prod : Set α) = (s.map coe).Prod :=
  map_list_prod (coeMonoidHom : Finset α →* Set α) _
#align finset.coe_list_prod Finset.coe_list_prod

@[to_additive]
theorem mem_prod_list_of_fn {a : α} {s : Fin n → Finset α} :
    a ∈ (List.ofFn s).Prod ↔ ∃ f : ∀ i : Fin n, s i, (List.ofFn fun i => (f i : α)).Prod = a :=
  by
  rw [← mem_coe, coe_list_prod, List.map_of_fn, Set.mem_prod_list_of_fn]
  rfl
#align finset.mem_prod_list_of_fn Finset.mem_prod_list_of_fn

@[to_additive]
theorem mem_pow {a : α} {n : ℕ} :
    a ∈ s ^ n ↔ ∃ f : Fin n → s, (List.ofFn fun i => ↑(f i)).Prod = a :=
  by
  simp_rw [← mem_coe, coe_pow, Set.mem_pow]
  rfl
#align finset.mem_pow Finset.mem_pow

@[simp, to_additive]
theorem empty_pow (hn : n ≠ 0) : (∅ : Finset α) ^ n = ∅ := by
  rw [← tsub_add_cancel_of_le (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn), pow_succ, empty_mul]
#align finset.empty_pow Finset.empty_pow

@[to_additive]
theorem mul_univ_of_one_mem [Fintype α] (hs : (1 : α) ∈ s) : s * univ = univ :=
  eq_univ_iff_forall.2 fun a => mem_mul.2 ⟨_, _, hs, mem_univ _, one_mul _⟩
#align finset.mul_univ_of_one_mem Finset.mul_univ_of_one_mem

@[to_additive]
theorem univ_mul_of_one_mem [Fintype α] (ht : (1 : α) ∈ t) : univ * t = univ :=
  eq_univ_iff_forall.2 fun a => mem_mul.2 ⟨_, _, mem_univ _, ht, mul_one _⟩
#align finset.univ_mul_of_one_mem Finset.univ_mul_of_one_mem

@[simp, to_additive]
theorem univ_mul_univ [Fintype α] : (univ : Finset α) * univ = univ :=
  mul_univ_of_one_mem <| mem_univ _
#align finset.univ_mul_univ Finset.univ_mul_univ

@[simp, to_additive nsmul_univ]
theorem univ_pow [Fintype α] (hn : n ≠ 0) : (univ : Finset α) ^ n = univ :=
  coe_injective <| by rw [coe_pow, coe_univ, Set.univ_pow hn]
#align finset.univ_pow Finset.univ_pow

@[to_additive]
protected theorem IsUnit.finset : IsUnit a → IsUnit ({a} : Finset α) :=
  IsUnit.map (singletonMonoidHom : α →* Finset α)
#align is_unit.finset IsUnit.finset

end Monoid

section CommMonoid

variable [CommMonoid α]

/-- `finset α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_comm_monoid` under pointwise operations if `α` is. "]
protected def commMonoid : CommMonoid (Finset α) :=
  coe_injective.CommMonoid _ coe_one coe_mul coe_pow
#align finset.comm_monoid Finset.commMonoid

scoped[Pointwise] attribute [instance] Finset.commMonoid Finset.addCommMonoid

@[simp, norm_cast, to_additive]
theorem coe_prod {ι : Type _} (s : Finset ι) (f : ι → Finset α) :
    (↑(∏ i in s, f i) : Set α) = ∏ i in s, f i :=
  map_prod (coeMonoidHom : Finset α →* Set α) _ _
#align finset.coe_prod Finset.coe_prod

end CommMonoid

open Pointwise

section DivisionMonoid

variable [DivisionMonoid α] {s t : Finset α}

@[simp, to_additive]
theorem coe_zpow (s : Finset α) : ∀ n : ℤ, ↑(s ^ n) = (s ^ n : Set α)
  | Int.ofNat n => coe_pow _ _
  | Int.negSucc n => by
    refine' (coe_inv _).trans _
    convert congr_arg Inv.inv (coe_pow _ _)
#align finset.coe_zpow Finset.coe_zpow

@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  simp_rw [← coe_inj, coe_mul, coe_one, Set.mul_eq_one_iff, coe_singleton]
#align finset.mul_eq_one_iff Finset.mul_eq_one_iff

/-- `finset α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive "`finset α` is a subtraction monoid under pointwise operations if\n`α` is."]
protected def divisionMonoid : DivisionMonoid (Finset α) :=
  coe_injective.DivisionMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow
#align finset.division_monoid Finset.divisionMonoid

@[simp, to_additive]
theorem is_unit_iff : IsUnit s ↔ ∃ a, s = {a} ∧ IsUnit a :=
  by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Finset.mul_eq_one_iff.1 u.mul_inv
    refine' ⟨a, ha, ⟨a, b, h, singleton_injective _⟩, rfl⟩
    rw [← singleton_mul_singleton, ← ha, ← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.finset
#align finset.is_unit_iff Finset.is_unit_iff

@[simp, to_additive]
theorem is_unit_coe : IsUnit (s : Set α) ↔ IsUnit s := by
  simp_rw [is_unit_iff, Set.is_unit_iff, coe_eq_singleton]
#align finset.is_unit_coe Finset.is_unit_coe

end DivisionMonoid

/-- `finset α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive SubtractionCommMonoid
      "`finset α` is a commutative subtraction monoid under\npointwise operations if `α` is."]
protected def divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (Finset α) :=
  coe_injective.DivisionCommMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow
#align finset.division_comm_monoid Finset.divisionCommMonoid

/-- `finset α` has distributive negation if `α` has. -/
protected def hasDistribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Finset α) :=
  coe_injective.HasDistribNeg _ coe_neg coe_mul
#align finset.has_distrib_neg Finset.hasDistribNeg

scoped[Pointwise]
  attribute [instance]
    Finset.divisionMonoid Finset.subtractionMonoid Finset.divisionCommMonoid Finset.subtractionCommMonoid Finset.hasDistribNeg

section Distrib

variable [Distrib α] (s t u : Finset α)

/-!
Note that `finset α` is not a `distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.

```lean
-- {10, 16, 18, 20, 8, 9}
#eval {1, 2} * ({3, 4} + {5, 6} : finset ℕ)

-- {10, 11, 12, 13, 14, 15, 16, 18, 20, 8, 9}
#eval ({1, 2} : finset ℕ) * {3, 4} + {1, 2} * {5, 6}
```
-/


theorem mul_add_subset : s * (t + u) ⊆ s * t + s * u :=
  image₂_distrib_subset_left mul_add
#align finset.mul_add_subset Finset.mul_add_subset

theorem add_mul_subset : (s + t) * u ⊆ s * u + t * u :=
  image₂_distrib_subset_right add_mul
#align finset.add_mul_subset Finset.add_mul_subset

end Distrib

section MulZeroClass

variable [MulZeroClass α] {s t : Finset α}

/-! Note that `finset` is not a `mul_zero_class` because `0 * ∅ ≠ 0`. -/


theorem mul_zero_subset (s : Finset α) : s * 0 ⊆ 0 := by simp [subset_iff, mem_mul]
#align finset.mul_zero_subset Finset.mul_zero_subset

theorem zero_mul_subset (s : Finset α) : 0 * s ⊆ 0 := by simp [subset_iff, mem_mul]
#align finset.zero_mul_subset Finset.zero_mul_subset

theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
  s.mul_zero_subset.antisymm <| by simpa [mem_mul] using hs
#align finset.nonempty.mul_zero Finset.Nonempty.mul_zero

theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
  s.zero_mul_subset.antisymm <| by simpa [mem_mul] using hs
#align finset.nonempty.zero_mul Finset.Nonempty.zero_mul

end MulZeroClass

section Group

variable [Group α] [DivisionMonoid β] [MonoidHomClass F α β] (f : F) {s t : Finset α} {a b : α}

/-! Note that `finset` is not a `group` because `s / s ≠ 1` in general. -/


@[simp, to_additive]
theorem one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬Disjoint s t := by
  rw [← mem_coe, ← disjoint_coe, coe_div, Set.one_mem_div_iff]
#align finset.one_mem_div_iff Finset.one_mem_div_iff

@[to_additive]
theorem not_one_mem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left
#align finset.not_one_mem_div_iff Finset.not_one_mem_div_iff

@[to_additive]
theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s :=
  let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, a, ha, ha, div_self' _⟩
#align finset.nonempty.one_mem_div Finset.Nonempty.one_mem_div

@[to_additive]
theorem is_unit_singleton (a : α) : IsUnit ({a} : Finset α) :=
  (Group.isUnit a).Finset
#align finset.is_unit_singleton Finset.is_unit_singleton

@[simp]
theorem is_unit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by
  simp only [is_unit_iff, Group.isUnit, and_true_iff]
#align finset.is_unit_iff_singleton Finset.is_unit_iff_singleton

@[simp, to_additive]
theorem image_mul_left :
    image (fun b => a * b) t = preimage t (fun b => a⁻¹ * b) ((mul_right_injective _).InjOn _) :=
  coe_injective <| by simp
#align finset.image_mul_left Finset.image_mul_left

@[simp, to_additive]
theorem image_mul_right : image (· * b) t = preimage t (· * b⁻¹) ((mul_left_injective _).InjOn _) :=
  coe_injective <| by simp
#align finset.image_mul_right Finset.image_mul_right

@[to_additive]
theorem image_mul_left' :
    image (fun b => a⁻¹ * b) t = preimage t (fun b => a * b) ((mul_right_injective _).InjOn _) := by
  simp
#align finset.image_mul_left' Finset.image_mul_left'

@[to_additive]
theorem image_mul_right' :
    image (· * b⁻¹) t = preimage t (· * b) ((mul_left_injective _).InjOn _) := by simp
#align finset.image_mul_right' Finset.image_mul_right'

theorem image_div : (s / t).image (f : α → β) = s.image f / t.image f :=
  image_image₂_distrib <| map_div f
#align finset.image_div Finset.image_div

end Group

section GroupWithZero

variable [GroupWithZero α] {s t : Finset α}

theorem div_zero_subset (s : Finset α) : s / 0 ⊆ 0 := by simp [subset_iff, mem_div]
#align finset.div_zero_subset Finset.div_zero_subset

theorem zero_div_subset (s : Finset α) : 0 / s ⊆ 0 := by simp [subset_iff, mem_div]
#align finset.zero_div_subset Finset.zero_div_subset

theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
  s.div_zero_subset.antisymm <| by simpa [mem_div] using hs
#align finset.nonempty.div_zero Finset.Nonempty.div_zero

theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
  s.zero_div_subset.antisymm <| by simpa [mem_div] using hs
#align finset.nonempty.zero_div Finset.Nonempty.zero_div

end GroupWithZero

end Instances

section Group

variable [Group α] {s t : Finset α} {a b : α}

@[simp, to_additive]
theorem preimage_mul_left_singleton :
    preimage {b} ((· * ·) a) ((mul_right_injective _).InjOn _) = {a⁻¹ * b} := by
  classical rw [← image_mul_left', image_singleton]
#align finset.preimage_mul_left_singleton Finset.preimage_mul_left_singleton

@[simp, to_additive]
theorem preimage_mul_right_singleton :
    preimage {b} (· * a) ((mul_left_injective _).InjOn _) = {b * a⁻¹} := by
  classical rw [← image_mul_right', image_singleton]
#align finset.preimage_mul_right_singleton Finset.preimage_mul_right_singleton

@[simp, to_additive]
theorem preimage_mul_left_one : preimage 1 ((· * ·) a) ((mul_right_injective _).InjOn _) = {a⁻¹} :=
  by classical rw [← image_mul_left', image_one, mul_one]
#align finset.preimage_mul_left_one Finset.preimage_mul_left_one

@[simp, to_additive]
theorem preimage_mul_right_one : preimage 1 (· * b) ((mul_left_injective _).InjOn _) = {b⁻¹} := by
  classical rw [← image_mul_right', image_one, one_mul]
#align finset.preimage_mul_right_one Finset.preimage_mul_right_one

@[to_additive]
theorem preimage_mul_left_one' : preimage 1 ((· * ·) a⁻¹) ((mul_right_injective _).InjOn _) = {a} :=
  by rw [preimage_mul_left_one, inv_inv]
#align finset.preimage_mul_left_one' Finset.preimage_mul_left_one'

@[to_additive]
theorem preimage_mul_right_one' : preimage 1 (· * b⁻¹) ((mul_left_injective _).InjOn _) = {b} := by
  rw [preimage_mul_right_one, inv_inv]
#align finset.preimage_mul_right_one' Finset.preimage_mul_right_one'

end Group

/-! ### Scalar addition/multiplication of finsets -/


section HasSmul

variable [DecidableEq β] [HasSmul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

/-- The pointwise product of two finsets `s` and `t`: `s • t = {x • y | x ∈ s, y ∈ t}`. -/
@[to_additive "The pointwise sum of two finsets `s` and\n`t`: `s +ᵥ t = {x +ᵥ y | x ∈ s, y ∈ t}`."]
protected def hasSmul : HasSmul (Finset α) (Finset β) :=
  ⟨image₂ (· • ·)⟩
#align finset.has_smul Finset.hasSmul

scoped[Pointwise] attribute [instance] Finset.hasSmul Finset.hasVadd

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem smul_def : s • t = (s ×ˢ t).image fun p : α × β => p.1 • p.2 :=
  rfl
#align finset.smul_def Finset.smul_def

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem image_smul_product : ((s ×ˢ t).image fun x : α × β => x.fst • x.snd) = s • t :=
  rfl
#align finset.image_smul_product Finset.image_smul_product

@[to_additive]
theorem mem_smul {x : β} : x ∈ s • t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y • z = x :=
  mem_image₂
#align finset.mem_smul Finset.mem_smul

@[simp, norm_cast, to_additive]
theorem coe_smul (s : Finset α) (t : Finset β) : (↑(s • t) : Set β) = (s : Set α) • t :=
  coe_image₂ _ _ _
#align finset.coe_smul Finset.coe_smul

@[to_additive]
theorem smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t :=
  mem_image₂_of_mem
#align finset.smul_mem_smul Finset.smul_mem_smul

@[to_additive]
theorem smul_card_le : (s • t).card ≤ s.card • t.card :=
  card_image₂_le _ _ _
#align finset.smul_card_le Finset.smul_card_le

@[simp, to_additive]
theorem empty_smul (t : Finset β) : (∅ : Finset α) • t = ∅ :=
  image₂_empty_left
#align finset.empty_smul Finset.empty_smul

@[simp, to_additive]
theorem smul_empty (s : Finset α) : s • (∅ : Finset β) = ∅ :=
  image₂_empty_right
#align finset.smul_empty Finset.smul_empty

@[simp, to_additive]
theorem smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.smul_eq_empty Finset.smul_eq_empty

@[simp, to_additive]
theorem smul_nonempty_iff : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.smul_nonempty_iff Finset.smul_nonempty_iff

@[to_additive]
theorem Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty :=
  nonempty.image₂
#align finset.nonempty.smul Finset.Nonempty.smul

@[to_additive]
theorem Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty :=
  nonempty.of_image₂_left
#align finset.nonempty.of_smul_left Finset.Nonempty.of_smul_left

@[to_additive]
theorem Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty :=
  nonempty.of_image₂_right
#align finset.nonempty.of_smul_right Finset.Nonempty.of_smul_right

@[to_additive]
theorem smul_singleton (b : β) : s • ({b} : Finset β) = s.image (· • b) :=
  image₂_singleton_right
#align finset.smul_singleton Finset.smul_singleton

@[to_additive]
theorem singleton_smul_singleton (a : α) (b : β) : ({a} : Finset α) • ({b} : Finset β) = {a • b} :=
  image₂_singleton
#align finset.singleton_smul_singleton Finset.singleton_smul_singleton

@[to_additive, mono]
theorem smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ :=
  image₂_subset
#align finset.smul_subset_smul Finset.smul_subset_smul

@[to_additive]
theorem smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ :=
  image₂_subset_left
#align finset.smul_subset_smul_left Finset.smul_subset_smul_left

@[to_additive]
theorem smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t :=
  image₂_subset_right
#align finset.smul_subset_smul_right Finset.smul_subset_smul_right

@[to_additive]
theorem smul_subset_iff : s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u :=
  image₂_subset_iff
#align finset.smul_subset_iff Finset.smul_subset_iff

attribute [mono] vadd_subset_vadd

@[to_additive]
theorem union_smul [DecidableEq α] : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t :=
  image₂_union_left
#align finset.union_smul Finset.union_smul

@[to_additive]
theorem smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ :=
  image₂_union_right
#align finset.smul_union Finset.smul_union

@[to_additive]
theorem inter_smul_subset [DecidableEq α] : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
  image₂_inter_subset_left
#align finset.inter_smul_subset Finset.inter_smul_subset

@[to_additive]
theorem smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
  image₂_inter_subset_right
#align finset.smul_inter_subset Finset.smul_inter_subset

/-- If a finset `u` is contained in the scalar product of two sets `s • t`, we can find two finsets
`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' • t'`. -/
@[to_additive
      "If a finset `u` is contained in the scalar sum of two sets `s +ᵥ t`, we can find two\nfinsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' +ᵥ t'`."]
theorem subset_smul {s : Set α} {t : Set β} :
    ↑u ⊆ s • t → ∃ (s' : Finset α)(t' : Finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' • t' :=
  subset_image₂
#align finset.subset_smul Finset.subset_smul

end HasSmul

/-! ### Scalar subtraction of finsets -/


section VSub

variable [DecidableEq α] [VSub α β] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

include α

/-- The pointwise product of two finsets `s` and `t`: `s -ᵥ t = {x -ᵥ y | x ∈ s, y ∈ t}`. -/
protected def hasVsub : VSub (Finset α) (Finset β) :=
  ⟨image₂ (· -ᵥ ·)⟩
#align finset.has_vsub Finset.hasVsub

scoped[Pointwise] attribute [instance] Finset.hasVsub

theorem vsub_def : s -ᵥ t = image₂ (· -ᵥ ·) s t :=
  rfl
#align finset.vsub_def Finset.vsub_def

@[simp]
theorem image_vsub_product : image₂ (· -ᵥ ·) s t = s -ᵥ t :=
  rfl
#align finset.image_vsub_product Finset.image_vsub_product

theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ b c, b ∈ s ∧ c ∈ t ∧ b -ᵥ c = a :=
  mem_image₂
#align finset.mem_vsub Finset.mem_vsub

@[simp, norm_cast]
theorem coe_vsub (s t : Finset β) : (↑(s -ᵥ t) : Set α) = (s : Set β) -ᵥ t :=
  coe_image₂ _ _ _
#align finset.coe_vsub Finset.coe_vsub

theorem vsub_mem_vsub : b ∈ s → c ∈ t → b -ᵥ c ∈ s -ᵥ t :=
  mem_image₂_of_mem
#align finset.vsub_mem_vsub Finset.vsub_mem_vsub

theorem vsub_card_le : (s -ᵥ t : Finset α).card ≤ s.card * t.card :=
  card_image₂_le _ _ _
#align finset.vsub_card_le Finset.vsub_card_le

@[simp]
theorem empty_vsub (t : Finset β) : (∅ : Finset β) -ᵥ t = ∅ :=
  image₂_empty_left
#align finset.empty_vsub Finset.empty_vsub

@[simp]
theorem vsub_empty (s : Finset β) : s -ᵥ (∅ : Finset β) = ∅ :=
  image₂_empty_right
#align finset.vsub_empty Finset.vsub_empty

@[simp]
theorem vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.vsub_eq_empty Finset.vsub_eq_empty

@[simp]
theorem vsub_nonempty : (s -ᵥ t : Finset α).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.vsub_nonempty Finset.vsub_nonempty

theorem Nonempty.vsub : s.Nonempty → t.Nonempty → (s -ᵥ t : Finset α).Nonempty :=
  nonempty.image₂
#align finset.nonempty.vsub Finset.Nonempty.vsub

theorem Nonempty.of_vsub_left : (s -ᵥ t : Finset α).Nonempty → s.Nonempty :=
  nonempty.of_image₂_left
#align finset.nonempty.of_vsub_left Finset.Nonempty.of_vsub_left

theorem Nonempty.of_vsub_right : (s -ᵥ t : Finset α).Nonempty → t.Nonempty :=
  nonempty.of_image₂_right
#align finset.nonempty.of_vsub_right Finset.Nonempty.of_vsub_right

@[simp]
theorem vsub_singleton (b : β) : s -ᵥ ({b} : Finset β) = s.image (· -ᵥ b) :=
  image₂_singleton_right
#align finset.vsub_singleton Finset.vsub_singleton

theorem singleton_vsub (a : β) : ({a} : Finset β) -ᵥ t = t.image ((· -ᵥ ·) a) :=
  image₂_singleton_left
#align finset.singleton_vsub Finset.singleton_vsub

@[simp]
theorem singleton_vsub_singleton (a b : β) : ({a} : Finset β) -ᵥ {b} = {a -ᵥ b} :=
  image₂_singleton
#align finset.singleton_vsub_singleton Finset.singleton_vsub_singleton

@[mono]
theorem vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ :=
  image₂_subset
#align finset.vsub_subset_vsub Finset.vsub_subset_vsub

theorem vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ :=
  image₂_subset_left
#align finset.vsub_subset_vsub_left Finset.vsub_subset_vsub_left

theorem vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t :=
  image₂_subset_right
#align finset.vsub_subset_vsub_right Finset.vsub_subset_vsub_right

theorem vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x -ᵥ y ∈ u :=
  image₂_subset_iff
#align finset.vsub_subset_iff Finset.vsub_subset_iff

section

variable [DecidableEq β]

theorem union_vsub : s₁ ∪ s₂ -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) :=
  image₂_union_left
#align finset.union_vsub Finset.union_vsub

theorem vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) :=
  image₂_union_right
#align finset.vsub_union Finset.vsub_union

theorem inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) :=
  image₂_inter_subset_left
#align finset.inter_vsub_subset Finset.inter_vsub_subset

theorem vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) :=
  image₂_inter_subset_right
#align finset.vsub_inter_subset Finset.vsub_inter_subset

end

/-- If a finset `u` is contained in the pointwise subtraction of two sets `s -ᵥ t`, we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' -ᵥ t'`. -/
theorem subset_vsub {s t : Set β} :
    ↑u ⊆ s -ᵥ t → ∃ s' t' : Finset β, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' -ᵥ t' :=
  subset_image₂
#align finset.subset_vsub Finset.subset_vsub

end VSub

open Pointwise

/-! ### Translation/scaling of finsets -/


section HasSmul

variable [DecidableEq β] [HasSmul α β] {s s₁ s₂ t u : Finset β} {a : α} {b : β}

/-- The scaling of a finset `s` by a scalar `a`: `a • s = {a • x | x ∈ s}`. -/
@[to_additive "The translation of a finset `s` by a vector `a`:\n`a +ᵥ s = {a +ᵥ x | x ∈ s}`."]
protected def hasSmulFinset : HasSmul α (Finset β) :=
  ⟨fun a => image <| (· • ·) a⟩
#align finset.has_smul_finset Finset.hasSmulFinset

scoped[Pointwise] attribute [instance] Finset.hasSmulFinset Finset.hasVaddFinset

@[to_additive]
theorem smul_finset_def : a • s = s.image ((· • ·) a) :=
  rfl
#align finset.smul_finset_def Finset.smul_finset_def

@[to_additive]
theorem image_smul : (s.image fun x => a • x) = a • s :=
  rfl
#align finset.image_smul Finset.image_smul

@[to_additive]
theorem mem_smul_finset {x : β} : x ∈ a • s ↔ ∃ y, y ∈ s ∧ a • y = x := by
  simp only [Finset.smul_finset_def, and_assoc, mem_image, exists_prop, Prod.exists, mem_product]
#align finset.mem_smul_finset Finset.mem_smul_finset

@[simp, norm_cast, to_additive]
theorem coe_smul_finset (a : α) (s : Finset β) : (↑(a • s) : Set β) = a • s :=
  coe_image
#align finset.coe_smul_finset Finset.coe_smul_finset

@[to_additive]
theorem smul_finset_mem_smul_finset : b ∈ s → a • b ∈ a • s :=
  mem_image_of_mem _
#align finset.smul_finset_mem_smul_finset Finset.smul_finset_mem_smul_finset

@[to_additive]
theorem smul_finset_card_le : (a • s).card ≤ s.card :=
  card_image_le
#align finset.smul_finset_card_le Finset.smul_finset_card_le

@[simp, to_additive]
theorem smul_finset_empty (a : α) : a • (∅ : Finset β) = ∅ :=
  image_empty _
#align finset.smul_finset_empty Finset.smul_finset_empty

@[simp, to_additive]
theorem smul_finset_eq_empty : a • s = ∅ ↔ s = ∅ :=
  image_eq_empty
#align finset.smul_finset_eq_empty Finset.smul_finset_eq_empty

@[simp, to_additive]
theorem smul_finset_nonempty : (a • s).Nonempty ↔ s.Nonempty :=
  Nonempty.image_iff _
#align finset.smul_finset_nonempty Finset.smul_finset_nonempty

@[to_additive]
theorem Nonempty.smul_finset (hs : s.Nonempty) : (a • s).Nonempty :=
  hs.image _
#align finset.nonempty.smul_finset Finset.Nonempty.smul_finset

@[simp, to_additive]
theorem singleton_smul (a : α) : ({a} : Finset α) • t = a • t :=
  image₂_singleton_left
#align finset.singleton_smul Finset.singleton_smul

@[to_additive, mono]
theorem smul_finset_subset_smul_finset : s ⊆ t → a • s ⊆ a • t :=
  image_subset_image
#align finset.smul_finset_subset_smul_finset Finset.smul_finset_subset_smul_finset

attribute [mono] vadd_finset_subset_vadd_finset

@[simp, to_additive]
theorem smul_finset_singleton (b : β) : a • ({b} : Finset β) = {a • b} :=
  image_singleton _ _
#align finset.smul_finset_singleton Finset.smul_finset_singleton

@[to_additive]
theorem smul_finset_union : a • (s₁ ∪ s₂) = a • s₁ ∪ a • s₂ :=
  image_union _ _
#align finset.smul_finset_union Finset.smul_finset_union

@[to_additive]
theorem smul_finset_inter_subset : a • (s₁ ∩ s₂) ⊆ a • s₁ ∩ a • s₂ :=
  image_inter_subset _ _ _
#align finset.smul_finset_inter_subset Finset.smul_finset_inter_subset

@[simp]
theorem bUnion_smul_finset (s : Finset α) (t : Finset β) : s.bUnion (· • t) = s • t :=
  bUnion_image_left
#align finset.bUnion_smul_finset Finset.bUnion_smul_finset

end HasSmul

open Pointwise

section Instances

variable [DecidableEq γ]

@[to_additive]
instance smul_comm_class_finset [HasSmul α γ] [HasSmul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Finset γ) :=
  ⟨fun _ _ => commute.finset_image <| smul_comm _ _⟩
#align finset.smul_comm_class_finset Finset.smul_comm_class_finset

@[to_additive]
instance smul_comm_class_finset' [HasSmul α γ] [HasSmul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_comm]⟩
#align finset.smul_comm_class_finset' Finset.smul_comm_class_finset'

@[to_additive]
instance smul_comm_class_finset'' [HasSmul α γ] [HasSmul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Finset α) β (Finset γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _
#align finset.smul_comm_class_finset'' Finset.smul_comm_class_finset''

@[to_additive]
instance smul_comm_class [HasSmul α γ] [HasSmul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Finset α) (Finset β) (Finset γ) :=
  ⟨fun s t u => coe_injective <| by simp_rw [coe_smul, smul_comm]⟩
#align finset.smul_comm_class Finset.smul_comm_class

@[to_additive]
instance is_scalar_tower [HasSmul α β] [HasSmul α γ] [HasSmul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Finset γ) :=
  ⟨fun a b s => by simp only [← image_smul, image_image, smul_assoc]⟩
#align finset.is_scalar_tower Finset.is_scalar_tower

variable [DecidableEq β]

@[to_additive]
instance is_scalar_tower' [HasSmul α β] [HasSmul α γ] [HasSmul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩
#align finset.is_scalar_tower' Finset.is_scalar_tower'

@[to_additive]
instance is_scalar_tower'' [HasSmul α β] [HasSmul α γ] [HasSmul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Finset α) (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩
#align finset.is_scalar_tower'' Finset.is_scalar_tower''

instance is_central_scalar [HasSmul α β] [HasSmul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Finset β) :=
  ⟨fun a s => coe_injective <| by simp only [coe_smul_finset, coe_smul, op_smul_eq_smul]⟩
#align finset.is_central_scalar Finset.is_central_scalar

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of
`finset α` on `finset β`. -/
@[to_additive
      "An additive action of an additive monoid `α` on a type `β` gives an additive action\nof `finset α` on `finset β`"]
protected def mulAction [DecidableEq α] [Monoid α] [MulAction α β] : MulAction (Finset α) (Finset β)
    where
  mul_smul _ _ _ := image₂_assoc mul_smul
  one_smul s := image₂_singleton_left.trans <| by simp_rw [one_smul, image_id']
#align finset.mul_action Finset.mulAction

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `finset β`.
-/
@[to_additive
      "An additive action of an additive monoid on a type `β` gives an additive action\non `finset β`."]
protected def mulActionFinset [Monoid α] [MulAction α β] : MulAction α (Finset β) :=
  coe_injective.MulAction _ coe_smul_finset
#align finset.mul_action_finset Finset.mulActionFinset

scoped[Pointwise]
  attribute [instance]
    Finset.mulActionFinset Finset.addActionFinset Finset.mulAction Finset.addAction

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `finset β`. -/
protected def distribMulActionFinset [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Finset β) :=
  Function.Injective.distribMulAction ⟨coe, coe_zero, coe_add⟩ coe_injective coe_smul_finset
#align finset.distrib_mul_action_finset Finset.distribMulActionFinset

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `set β`. -/
protected def mulDistribMulActionFinset [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Finset β) :=
  Function.Injective.mulDistribMulAction ⟨coe, coe_one, coe_mul⟩ coe_injective coe_smul_finset
#align finset.mul_distrib_mul_action_finset Finset.mulDistribMulActionFinset

scoped[Pointwise]
  attribute [instance] Finset.distribMulActionFinset Finset.mulDistribMulActionFinset

instance [DecidableEq α] [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Finset α) :=
  coe_injective.NoZeroDivisors _ coe_zero coe_mul

instance [Zero α] [Zero β] [HasSmul α β] [NoZeroSmulDivisors α β] :
    NoZeroSmulDivisors (Finset α) (Finset β) :=
  ⟨fun s t h => by
    by_contra' H
    have hst : (s • t).Nonempty := h.symm.subst zero_nonempty
    simp_rw [← hst.of_smul_left.subset_zero_iff, ← hst.of_smul_right.subset_zero_iff, not_subset,
      mem_zero] at H
    obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H
    have := subset_of_eq h
    exact
      (eq_zero_or_eq_zero_of_smul_eq_zero <| mem_zero.1 <| this <| smul_mem_smul hs ht).elim ha hb⟩

instance no_zero_smul_divisors_finset [Zero α] [Zero β] [HasSmul α β] [NoZeroSmulDivisors α β] :
    NoZeroSmulDivisors α (Finset β) :=
  coe_injective.NoZeroSmulDivisors _ coe_zero coe_smul_finset
#align finset.no_zero_smul_divisors_finset Finset.no_zero_smul_divisors_finset

end Instances

section LeftCancelSemigroup

variable [LeftCancelSemigroup α] [DecidableEq α] (s t : Finset α) (a : α)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem pairwise_disjoint_smul_iff {s : Set α} {t : Finset α} :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => p.1 * p.2 := by
  simp_rw [← pairwise_disjoint_coe, coe_smul_finset, Set.pairwise_disjoint_smul_iff]
#align finset.pairwise_disjoint_smul_iff Finset.pairwise_disjoint_smul_iff

@[simp, to_additive]
theorem card_singleton_mul : ({a} * t).card = t.card :=
  card_image₂_singleton_left _ <| mul_right_injective _
#align finset.card_singleton_mul Finset.card_singleton_mul

@[to_additive]
theorem singleton_mul_inter : {a} * (s ∩ t) = {a} * s ∩ ({a} * t) :=
  image₂_singleton_inter _ _ <| mul_right_injective _
#align finset.singleton_mul_inter Finset.singleton_mul_inter

@[to_additive]
theorem card_le_card_mul_left {s : Finset α} (hs : s.Nonempty) : t.card ≤ (s * t).card :=
  card_le_card_image₂_left _ hs mul_right_injective
#align finset.card_le_card_mul_left Finset.card_le_card_mul_left

end LeftCancelSemigroup

section

variable [RightCancelSemigroup α] [DecidableEq α] (s t : Finset α) (a : α)

@[simp, to_additive]
theorem card_mul_singleton : (s * {a}).card = s.card :=
  card_image₂_singleton_right _ <| mul_left_injective _
#align finset.card_mul_singleton Finset.card_mul_singleton

@[to_additive]
theorem inter_mul_singleton : s ∩ t * {a} = s * {a} ∩ (t * {a}) :=
  image₂_inter_singleton _ _ <| mul_left_injective _
#align finset.inter_mul_singleton Finset.inter_mul_singleton

@[to_additive]
theorem card_le_card_mul_right {t : Finset α} (ht : t.Nonempty) : s.card ≤ (s * t).card :=
  card_le_card_image₂_right _ ht mul_left_injective
#align finset.card_le_card_mul_right Finset.card_le_card_mul_right

end

open Pointwise

section Group

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

@[simp, to_additive]
theorem smul_mem_smul_finset_iff (a : α) : a • b ∈ a • s ↔ b ∈ s :=
  (MulAction.injective _).mem_finset_image
#align finset.smul_mem_smul_finset_iff Finset.smul_mem_smul_finset_iff

@[to_additive]
theorem inv_smul_mem_iff : a⁻¹ • b ∈ s ↔ b ∈ a • s := by
  rw [← smul_mem_smul_finset_iff a, smul_inv_smul]
#align finset.inv_smul_mem_iff Finset.inv_smul_mem_iff

@[to_additive]
theorem mem_inv_smul_finset_iff : b ∈ a⁻¹ • s ↔ a • b ∈ s := by
  rw [← smul_mem_smul_finset_iff a, smul_inv_smul]
#align finset.mem_inv_smul_finset_iff Finset.mem_inv_smul_finset_iff

@[simp, to_additive]
theorem smul_finset_subset_smul_finset_iff : a • s ⊆ a • t ↔ s ⊆ t :=
  image_subset_image_iff <| MulAction.injective _
#align finset.smul_finset_subset_smul_finset_iff Finset.smul_finset_subset_smul_finset_iff

@[to_additive]
theorem smul_finset_subset_iff : a • s ⊆ t ↔ s ⊆ a⁻¹ • t :=
  by
  simp_rw [← coe_subset]
  push_cast
  exact Set.set_smul_subset_iff
#align finset.smul_finset_subset_iff Finset.smul_finset_subset_iff

@[to_additive]
theorem subset_smul_finset_iff : s ⊆ a • t ↔ a⁻¹ • s ⊆ t :=
  by
  simp_rw [← coe_subset]
  push_cast
  exact Set.subset_set_smul_iff
#align finset.subset_smul_finset_iff Finset.subset_smul_finset_iff

end Group

section GroupWithZero

variable [DecidableEq β] [GroupWithZero α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

@[simp]
theorem smul_mem_smul_finset_iff₀ (ha : a ≠ 0) : a • b ∈ a • s ↔ b ∈ s :=
  smul_mem_smul_finset_iff (Units.mk0 a ha)
#align finset.smul_mem_smul_finset_iff₀ Finset.smul_mem_smul_finset_iff₀

theorem inv_smul_mem_iff₀ (ha : a ≠ 0) : a⁻¹ • b ∈ s ↔ b ∈ a • s :=
  show _ ↔ _ ∈ Units.mk0 a ha • _ from inv_smul_mem_iff
#align finset.inv_smul_mem_iff₀ Finset.inv_smul_mem_iff₀

theorem mem_inv_smul_finset_iff₀ (ha : a ≠ 0) : b ∈ a⁻¹ • s ↔ a • b ∈ s :=
  show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_finset_iff
#align finset.mem_inv_smul_finset_iff₀ Finset.mem_inv_smul_finset_iff₀

@[simp]
theorem smul_finset_subset_smul_finset_iff₀ (ha : a ≠ 0) : a • s ⊆ a • t ↔ s ⊆ t :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_finset_subset_smul_finset_iff
#align finset.smul_finset_subset_smul_finset_iff₀ Finset.smul_finset_subset_smul_finset_iff₀

theorem smul_finset_subset_iff₀ (ha : a ≠ 0) : a • s ⊆ t ↔ s ⊆ a⁻¹ • t :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_finset_subset_iff
#align finset.smul_finset_subset_iff₀ Finset.smul_finset_subset_iff₀

theorem subset_smul_finset_iff₀ (ha : a ≠ 0) : s ⊆ a • t ↔ a⁻¹ • s ⊆ t :=
  show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_smul_finset_iff
#align finset.subset_smul_finset_iff₀ Finset.subset_smul_finset_iff₀

theorem smul_univ₀ [Fintype β] {s : Finset α} (hs : ¬s ⊆ 0) : s • (univ : Finset β) = univ :=
  coe_injective <| by
    rw [← coe_subset] at hs
    push_cast at hs⊢
    exact Set.smul_univ₀ hs
#align finset.smul_univ₀ Finset.smul_univ₀

theorem smul_finset_univ₀ [Fintype β] (ha : a ≠ 0) : a • (univ : Finset β) = univ :=
  coe_injective <| by
    push_cast
    exact Set.smul_set_univ₀ ha
#align finset.smul_finset_univ₀ Finset.smul_finset_univ₀

end GroupWithZero

section SMulWithZero

variable [Zero α] [Zero β] [SMulWithZero α β] [DecidableEq β] {s : Finset α} {t : Finset β}

/-!
Note that we have neither `smul_with_zero α (finset β)` nor `smul_with_zero (finset α) (finset β)`
because `0 * ∅ ≠ 0`.
-/


theorem smul_zero_subset (s : Finset α) : s • (0 : Finset β) ⊆ 0 := by simp [subset_iff, mem_smul]
#align finset.smul_zero_subset Finset.smul_zero_subset

theorem zero_smul_subset (t : Finset β) : (0 : Finset α) • t ⊆ 0 := by simp [subset_iff, mem_smul]
#align finset.zero_smul_subset Finset.zero_smul_subset

theorem Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Finset β) = 0 :=
  s.smul_zero_subset.antisymm <| by simpa [mem_smul] using hs
#align finset.nonempty.smul_zero Finset.Nonempty.smul_zero

theorem Nonempty.zero_smul (ht : t.Nonempty) : (0 : Finset α) • t = 0 :=
  t.zero_smul_subset.antisymm <| by simpa [mem_smul] using ht
#align finset.nonempty.zero_smul Finset.Nonempty.zero_smul

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
theorem zero_smul_finset {s : Finset β} (h : s.Nonempty) : (0 : α) • s = (0 : Finset β) :=
  coe_injective <| by simpa using Set.zero_smul_set h
#align finset.zero_smul_finset Finset.zero_smul_finset

theorem zero_smul_finset_subset (s : Finset β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ => mem_zero.2 <| zero_smul α x
#align finset.zero_smul_finset_subset Finset.zero_smul_finset_subset

theorem zero_mem_smul_finset {t : Finset β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
  mem_smul_finset.2 ⟨0, h, smul_zero _⟩
#align finset.zero_mem_smul_finset Finset.zero_mem_smul_finset

variable [NoZeroSmulDivisors α β] {a : α}

theorem zero_mem_smul_iff : (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.Nonempty ∨ (0 : β) ∈ t ∧ s.Nonempty :=
  by
  rw [← mem_coe, coe_smul, Set.zero_mem_smul_iff]
  rfl
#align finset.zero_mem_smul_iff Finset.zero_mem_smul_iff

theorem zero_mem_smul_finset_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t :=
  by
  rw [← mem_coe, coe_smul_finset, Set.zero_mem_smul_set_iff ha, mem_coe]
  infer_instance
#align finset.zero_mem_smul_finset_iff Finset.zero_mem_smul_finset_iff

end SMulWithZero

section Monoid

variable [Monoid α] [AddGroup β] [DistribMulAction α β] [DecidableEq β] (a : α) (s : Finset α)
  (t : Finset β)

@[simp]
theorem smul_finset_neg : a • -t = -(a • t) := by
  simp only [← image_smul, ← image_neg, Function.comp, image_image, smul_neg]
#align finset.smul_finset_neg Finset.smul_finset_neg

@[simp]
protected theorem smul_neg : s • -t = -(s • t) :=
  by
  simp_rw [← image_neg]
  exact image_image₂_right_comm smul_neg
#align finset.smul_neg Finset.smul_neg

end Monoid

section Ring

variable [Ring α] [AddCommGroup β] [Module α β] [DecidableEq β] {s : Finset α} {t : Finset β}
  {a : α}

@[simp]
theorem neg_smul_finset : -a • t = -(a • t) := by
  simp only [← image_smul, ← image_neg, image_image, neg_smul]
#align finset.neg_smul_finset Finset.neg_smul_finset

@[simp]
protected theorem neg_smul [DecidableEq α] : -s • t = -(s • t) :=
  by
  simp_rw [← image_neg]
  exact image₂_image_left_comm neg_smul
#align finset.neg_smul Finset.neg_smul

end Ring

end Finset

