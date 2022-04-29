/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import Mathbin.Data.Finset.Preimage
import Mathbin.Data.Set.Pointwise

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
* `s • t` (`finset.has_scalar`): Scalar multiplication, finset of all `x • y` where `x ∈ s` and
  `y ∈ t`.
* `s -ᵥ t` (`finset.has_vsub`): Scalar subtraction, finset of all `x -ᵥ y` where `x ∈ s` and
  `y ∈ t`.
* `a • s` (`finset.has_scalar_finset`): Scaling, finset of all `a • x` where `x ∈ s`.
* `a +ᵥ s` (`finset.has_vadd_finset`): Translation, finset of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `finset α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`.

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

open Pointwise

variable {F α β γ : Type _}

namespace Finset

/-! ### `0`/`1` as sets -/


section One

variable [One α] {s : Finset α} {a : α}

/-- The finset `(1 : finset α)` is defined as `{1}` in locale `pointwise`. -/
@[to_additive "The finset `(0 : finset α)` is defined as `{0}` in locale `pointwise`."]
protected def hasOne : One (Finset α) :=
  ⟨{1}⟩

localized [Pointwise] attribute [instance] Finset.hasOne Finset.hasZero

@[simp, to_additive]
theorem mem_one : a ∈ (1 : Finset α) ↔ a = 1 :=
  mem_singleton

@[simp, to_additive]
theorem coe_one : ↑(1 : Finset α) = (1 : Set α) :=
  coe_singleton 1

@[simp, to_additive]
theorem one_subset : (1 : Finset α) ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff

@[to_additive]
theorem singleton_one : ({1} : Finset α) = 1 :=
  rfl

@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Finset α) :=
  mem_singleton_self _

@[to_additive]
theorem one_nonempty : (1 : Finset α).Nonempty :=
  ⟨1, one_mem_one⟩

@[simp, to_additive]
protected theorem map_one {f : α ↪ β} : map f 1 = {f 1} :=
  map_singleton f 1

@[simp, to_additive]
theorem image_one [DecidableEq β] {f : α → β} : image f 1 = {f 1} :=
  image_singleton f 1

end One

open Pointwise

/-! ### Finset negation/inversion -/


section Inv

variable [DecidableEq α] [Inv α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

/-- The pointwise inverse of a finset `s`: `s⁻¹ = {x⁻¹ | x ∈ s}`. -/
@[to_additive "The pointwise negation of a finset `s`: `-s = {-x | x ∈ s}`."]
protected def hasInv : Inv (Finset α) :=
  ⟨image Inv.inv⟩

localized [Pointwise] attribute [instance] Finset.hasInv Finset.hasNeg

@[to_additive]
theorem inv_def : s⁻¹ = s.Image fun x => x⁻¹ :=
  rfl

@[to_additive]
theorem image_inv : (s.Image fun x => x⁻¹) = s⁻¹ :=
  rfl

@[to_additive]
theorem mem_inv {x : α} : x ∈ s⁻¹ ↔ ∃ y ∈ s, y⁻¹ = x :=
  mem_image

@[to_additive]
theorem inv_mem_inv (ha : a ∈ s) : a⁻¹ ∈ s⁻¹ :=
  mem_image_of_mem _ ha

@[to_additive]
theorem card_inv_le : s⁻¹.card ≤ s.card :=
  card_image_le

@[simp, to_additive]
theorem inv_empty : (∅ : Finset α)⁻¹ = ∅ :=
  image_empty _

@[simp, to_additive]
theorem inv_nonempty_iff : s⁻¹.Nonempty ↔ s.Nonempty :=
  Nonempty.image_iff _

alias inv_nonempty_iff ↔ Finset.Nonempty.inv Finset.Nonempty.of_inv

@[to_additive, mono]
theorem inv_subset_inv (h : s ⊆ t) : s⁻¹ ⊆ t⁻¹ :=
  image_subset_image h

attribute [mono] neg_subset_neg

@[simp, to_additive]
theorem inv_singleton (a : α) : ({a} : Finset α)⁻¹ = {a⁻¹} :=
  image_singleton _ _

end Inv

open Pointwise

section HasInvolutiveInv

variable [DecidableEq α] [HasInvolutiveInv α] {s t : Finset α}

@[simp, norm_cast, to_additive]
theorem coe_inv (s : Finset α) : ↑s⁻¹ = (s : Set α)⁻¹ :=
  coe_image.trans Set.image_inv

@[simp, to_additive]
theorem card_inv : s⁻¹.card = s.card :=
  card_image_of_injective _ inv_injective

@[simp, to_additive]
theorem preimage_inv : s.Preimage Inv.inv (inv_injective.InjOn _) = s⁻¹ :=
  coe_injective <| by
    rw [coe_preimage, Set.inv_preimage, coe_inv]

end HasInvolutiveInv

/-! ### Finset addition/multiplication -/


section Mul

variable [DecidableEq α] [Mul α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

/-- The pointwise product of two finsets `s` and `t`: `s * t = {x * y | x ∈ s, y ∈ t}`. -/
@[to_additive "The pointwise sum of two finsets `s` and `t`: `s + t = {x + y | x ∈ s, y ∈ t}`."]
protected def hasMul : Mul (Finset α) :=
  ⟨fun s t => (s.product t).Image fun p : α × α => p.1 * p.2⟩

localized [Pointwise] attribute [instance] Finset.hasMul Finset.hasAdd

@[to_additive]
theorem mul_def : s * t = (s.product t).Image fun p : α × α => p.1 * p.2 :=
  rfl

@[to_additive add_image_prod]
theorem image_mul_prod : ((s.product t).Image fun x : α × α => x.fst * x.snd) = s * t :=
  rfl

@[to_additive]
theorem mem_mul {x : α} : x ∈ s * t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x := by
  simp only [Finset.mul_def, And.assoc, mem_image, exists_prop, Prod.exists, mem_product]

@[simp, norm_cast, to_additive]
theorem coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t :=
  Set.ext fun _ => by
    simp only [mem_mul, Set.mem_mul, mem_coe]

@[to_additive]
theorem mul_mem_mul (ha : a ∈ s) (hb : b ∈ t) : a * b ∈ s * t :=
  mem_mul.2 ⟨a, b, ha, hb, rfl⟩

@[to_additive]
theorem mul_card_le : (s * t).card ≤ s.card * t.card :=
  card_image_le.trans (card_product _ _).le

@[simp, to_additive]
theorem empty_mul (s : Finset α) : ∅ * s = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp [mem_mul]

@[simp, to_additive]
theorem mul_empty (s : Finset α) : s * ∅ = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp [mem_mul]

@[simp, to_additive]
theorem mul_nonempty_iff (s t : Finset α) : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  (Nonempty.image_iff _).trans nonempty_product

@[to_additive, mono]
theorem mul_subset_mul (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ * t₁ ⊆ s₂ * t₂ :=
  image_subset_image <| product_subset_product hs ht

attribute [mono] add_subset_add

@[simp, to_additive]
theorem mul_singleton (a : α) : s * {a} = s.Image (· * a) := by
  rw [mul_def, product_singleton, map_eq_image, image_image]
  rfl

@[simp, to_additive]
theorem singleton_mul (a : α) : {a} * s = s.Image ((· * ·) a) := by
  rw [mul_def, singleton_product, map_eq_image, image_image]
  rfl

@[simp, to_additive]
theorem singleton_mul_singleton (a b : α) : ({a} : Finset α) * {b} = {a * b} := by
  rw [mul_def, singleton_product_singleton, image_singleton]

/-- If a finset `u` is contained in the product of two sets `s * t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' * t'`. -/
@[to_additive
      "If a finset `u` is contained in the sum of two sets `s + t`, we can find two finsets\n`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' + t'`."]
theorem subset_mul {s t : Set α} (f : ↑u ⊆ s * t) : ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' * t' := by
  apply Finset.induction_on' u
  · exact ⟨∅, ∅, Set.empty_subset _, Set.empty_subset _, empty_subset _⟩
    
  rintro a u ha _ _ ⟨s', t', hs, hs', h⟩
  obtain ⟨x, y, hx, hy, ha⟩ := f ha
  use insert x s', insert y t'
  simp_rw [coe_insert, Set.insert_subset]
  exact
    ⟨⟨hx, hs⟩, ⟨hy, hs'⟩,
      insert_subset.2
        ⟨mem_mul.2 ⟨x, y, mem_insert_self _ _, mem_insert_self _ _, ha⟩,
          h.trans <| mul_subset_mul (subset_insert _ _) <| subset_insert _ _⟩⟩

end Mul

open Pointwise

section MulZeroClassₓ

variable [DecidableEq α] [MulZeroClassₓ α] {s t : Finset α}

theorem mul_zero_subset (s : Finset α) : s * 0 ⊆ 0 := by
  simp [subset_iff, mem_mul]

theorem zero_mul_subset (s : Finset α) : 0 * s ⊆ 0 := by
  simp [subset_iff, mem_mul]

theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
  s.mul_zero_subset.antisymm <| by
    simpa [Finset.mem_mul] using hs

theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
  s.zero_mul_subset.antisymm <| by
    simpa [Finset.mem_mul] using hs

end MulZeroClassₓ

section Groupₓ

variable [Groupₓ α] {s t : Finset α} {a b : α}

section DecidableEq

variable [DecidableEq α]

@[simp, to_additive]
theorem image_mul_left :
    image (fun b => a * b) t = preimage t (fun b => a⁻¹ * b) fun x hx y hy => (mul_right_injₓ a⁻¹).mp :=
  coe_injective <| by
    simp

@[simp, to_additive]
theorem image_mul_right : image (· * b) t = preimage t (· * b⁻¹) fun x hx y hy => (mul_left_injₓ b⁻¹).mp :=
  coe_injective <| by
    simp

@[to_additive]
theorem image_mul_left' :
    image (fun b => a⁻¹ * b) t = preimage t (fun b => a * b) fun x hx y hy => (mul_right_injₓ a).mp := by
  simp

@[to_additive]
theorem image_mul_right' : image (· * b⁻¹) t = preimage t (· * b) fun x hx y hy => (mul_left_injₓ b).mp := by
  simp

end DecidableEq

@[simp, to_additive]
theorem preimage_mul_left_singleton : (preimage {b} ((· * ·) a) fun x hx y hy => (mul_right_injₓ a).mp) = {a⁻¹ * b} :=
  by
  classical
  rw [← image_mul_left', image_singleton]

@[simp, to_additive]
theorem preimage_mul_right_singleton : (preimage {b} (· * a) fun x hx y hy => (mul_left_injₓ a).mp) = {b * a⁻¹} := by
  classical
  rw [← image_mul_right', image_singleton]

@[simp, to_additive]
theorem preimage_mul_left_one : (preimage 1 (fun b => a * b) fun x hx y hy => (mul_right_injₓ a).mp) = {a⁻¹} := by
  classical
  rw [← image_mul_left', image_one, mul_oneₓ]

@[simp, to_additive]
theorem preimage_mul_right_one : (preimage 1 (· * b) fun x hx y hy => (mul_left_injₓ b).mp) = {b⁻¹} := by
  classical
  rw [← image_mul_right', image_one, one_mulₓ]

@[to_additive]
theorem preimage_mul_left_one' : (preimage 1 (fun b => a⁻¹ * b) fun x hx y hy => (mul_right_injₓ _).mp) = {a} := by
  rw [preimage_mul_left_one, inv_invₓ]

@[to_additive]
theorem preimage_mul_right_one' : (preimage 1 (· * b⁻¹) fun x hx y hy => (mul_left_injₓ _).mp) = {b} := by
  rw [preimage_mul_right_one, inv_invₓ]

end Groupₓ

open Pointwise

/-! ### Finset subtraction/division -/


section Div

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

/-- The pointwise product of two finsets `s` and `t`: `s / t = {x / y | x ∈ s, y ∈ t}`. -/
@[to_additive "The pointwise sum of two finsets `s` and `t`: `s - t = {x - y | x ∈ s, y ∈ t}`."]
protected def hasDiv : Div (Finset α) :=
  ⟨fun s t => (s.product t).Image fun p : α × α => p.1 / p.2⟩

localized [Pointwise] attribute [instance] Finset.hasDiv Finset.hasAdd

@[to_additive]
theorem div_def : s / t = (s.product t).Image fun p : α × α => p.1 / p.2 :=
  rfl

@[to_additive add_image_prod]
theorem image_div_prod : ((s.product t).Image fun x : α × α => x.fst / x.snd) = s / t :=
  rfl

@[to_additive]
theorem mem_div {x : α} : x ∈ s / t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y / z = x := by
  simp only [Finset.div_def, And.assoc, mem_image, exists_prop, Prod.exists, mem_product]

@[simp, norm_cast, to_additive]
theorem coe_div (s t : Finset α) : (↑(s / t) : Set α) = ↑s / ↑t :=
  Set.ext fun _ => by
    simp only [mem_div, Set.mem_div, mem_coe]

@[to_additive]
theorem div_mem_div (ha : a ∈ s) (hb : b ∈ t) : a / b ∈ s / t :=
  mem_div.2 ⟨a, b, ha, hb, rfl⟩

@[to_additive]
theorem div_card_le : (s / t).card ≤ s.card * t.card :=
  card_image_le.trans (card_product _ _).le

@[simp, to_additive]
theorem empty_div (s : Finset α) : ∅ / s = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp [mem_div]

@[simp, to_additive]
theorem div_empty (s : Finset α) : s / ∅ = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp [mem_div]

@[simp, to_additive]
theorem div_nonempty_iff (s t : Finset α) : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  (Nonempty.image_iff _).trans nonempty_product

@[to_additive, mono]
theorem div_subset_div (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ / t₁ ⊆ s₂ / t₂ :=
  image_subset_image <| product_subset_product hs ht

attribute [mono] add_subset_add

@[simp, to_additive]
theorem div_singleton (a : α) : s / {a} = s.Image (· / a) := by
  rw [div_def, product_singleton, map_eq_image, image_image]
  rfl

@[simp, to_additive]
theorem singleton_div (a : α) : {a} / s = s.Image ((· / ·) a) := by
  rw [div_def, singleton_product, map_eq_image, image_image]
  rfl

@[simp, to_additive]
theorem singleton_div_singleton (a b : α) : ({a} : Finset α) / {b} = {a / b} := by
  rw [div_def, singleton_product_singleton, image_singleton]

/-- If a finset `u` is contained in the product of two sets `s / t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' / t'`. -/
@[to_additive
      "If a finset `u` is contained in the sum of two sets `s - t`, we can find two finsets\n`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' - t'`."]
theorem subset_div {s t : Set α} (f : ↑u ⊆ s / t) : ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' / t' := by
  apply Finset.induction_on' u
  · exact ⟨∅, ∅, Set.empty_subset _, Set.empty_subset _, empty_subset _⟩
    
  rintro a u ha _ _ ⟨s', t', hs, hs', h⟩
  obtain ⟨x, y, hx, hy, ha⟩ := f ha
  use insert x s', insert y t'
  simp_rw [coe_insert, Set.insert_subset]
  exact
    ⟨⟨hx, hs⟩, ⟨hy, hs'⟩,
      insert_subset.2
        ⟨mem_div.2 ⟨x, y, mem_insert_self _ _, mem_insert_self _ _, ha⟩,
          h.trans <| div_subset_div (subset_insert _ _) <| subset_insert _ _⟩⟩

end Div

open Pointwise

section GroupWithZeroₓ

variable [DecidableEq α] [GroupWithZeroₓ α] {s t : Finset α}

theorem div_zero_subset (s : Finset α) : s / 0 ⊆ 0 := by
  simp [subset_iff, mem_div]

theorem zero_div_subset (s : Finset α) : 0 / s ⊆ 0 := by
  simp [subset_iff, mem_div]

theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
  s.div_zero_subset.antisymm <| by
    simpa [Finset.mem_div] using hs

theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
  s.zero_div_subset.antisymm <| by
    simpa [Finset.mem_div] using hs

end GroupWithZeroₓ

/-! ### Instances -/


open Pointwise

section Instances

variable [DecidableEq α]

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `finset`. -/
protected def hasNsmul [Zero α] [Add α] : HasScalar ℕ (Finset α) :=
  ⟨nsmulRec⟩

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`finset`. -/
@[to_additive]
protected def hasNpow [One α] [Mul α] : Pow (Finset α) ℕ :=
  ⟨fun s n => npowRec n s⟩

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `finset`. -/
protected def hasZsmul [Zero α] [Add α] [Neg α] : HasScalar ℤ (Finset α) :=
  ⟨zsmulRec⟩

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `finset`. -/
@[to_additive]
protected def hasZpow [One α] [Mul α] [Inv α] : Pow (Finset α) ℤ :=
  ⟨fun s n => zpowRec n s⟩

localized [Pointwise] attribute [instance] Finset.hasNsmul Finset.hasNpow Finset.hasZsmul Finset.hasZpow

@[simp, to_additive]
theorem coe_pow [Monoidₓ α] (s : Finset α) (n : ℕ) : ↑(s ^ n) = (s ^ n : Set α) := by
  change ↑(npowRec n s) = _
  induction' n with n ih
  · rw [npowRec, pow_zeroₓ, coe_one]
    
  · rw [npowRec, pow_succₓ, coe_mul, ih]
    

/- TODO: The below lemmas are duplicate because there is no typeclass greater than
`div_inv_monoid` and `has_involutive_inv` but smaller than `group` and `group_with_zero`. -/
@[simp, to_additive]
theorem coe_zpow [Groupₓ α] (s : Finset α) : ∀ n : ℤ, ↑(s ^ n) = (s ^ n : Set α)
  | Int.ofNat n => coe_pow _ _
  | Int.negSucc n => by
    refine' (coe_inv _).trans _
    convert congr_argₓ Inv.inv (coe_pow _ _)

@[simp]
theorem coe_zpow' [GroupWithZeroₓ α] (s : Finset α) : ∀ n : ℤ, ↑(s ^ n) = (s ^ n : Set α)
  | Int.ofNat n => coe_pow _ _
  | Int.negSucc n => by
    refine' (coe_inv _).trans _
    convert congr_argₓ Inv.inv (coe_pow _ _)

/-- `finset α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mulOneClass [MulOneClassₓ α] : MulOneClassₓ (Finset α) :=
  coe_injective.MulOneClass _ (coe_singleton 1)
    (by
      simp )

/-- `finset α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_semigroup` under pointwise operations if `α` is. "]
protected def semigroup [Semigroupₓ α] : Semigroupₓ (Finset α) :=
  coe_injective.Semigroup _ coe_mul

/-- `finset α` is a `comm_semigroup` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_comm_semigroup` under pointwise operations if `α` is. "]
protected def commSemigroup [CommSemigroupₓ α] : CommSemigroupₓ (Finset α) :=
  coe_injective.CommSemigroup _ coe_mul

/-- `finset α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_monoid` under pointwise operations if `α` is. "]
protected def monoid [Monoidₓ α] : Monoidₓ (Finset α) :=
  coe_injective.Monoid _ coe_one coe_mul coe_pow

/-- `finset α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_comm_monoid` under pointwise operations if `α` is. "]
protected def commMonoid [CommMonoidₓ α] : CommMonoidₓ (Finset α) :=
  coe_injective.CommMonoid _ coe_one coe_mul coe_pow

/-- `finset α` is a `div_inv_monoid` under pointwise operations if `α` is. -/
/- TODO: The below instances are duplicate because there is no typeclass greater than
`div_inv_monoid` and `has_involutive_inv` but smaller than `group` and `group_with_zero`. -/
@[to_additive "`finset α` is an `sub_neg_add_monoid` under pointwise operations if `α` is."]
protected def divInvMonoid [Groupₓ α] : DivInvMonoidₓ (Finset α) :=
  coe_injective.DivInvMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

/-- `finset α` is a `div_inv_monoid` under pointwise operations if `α` is. -/
protected def divInvMonoid' [GroupWithZeroₓ α] : DivInvMonoidₓ (Finset α) :=
  coe_injective.DivInvMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow'

localized [Pointwise]
  attribute [instance]
    Finset.mulOneClass Finset.addZeroClass Finset.semigroup Finset.addSemigroup Finset.monoid Finset.addMonoid Finset.commMonoid Finset.addCommMonoid Finset.divInvMonoid Finset.subNegAddMonoid Finset.divInvMonoid'

end Instances

/-! ### Finset addition/multiplication -/


section HasScalar

variable [DecidableEq β] [HasScalar α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

/-- The pointwise product of two finsets `s` and `t`: `s • t = {x • y | x ∈ s, y ∈ t}`. -/
@[to_additive HasVadd "The pointwise sum of two finsets `s` and\n`t`: `s +ᵥ t = {x +ᵥ y | x ∈ s, y ∈ t}`."]
protected def hasScalar : HasScalar (Finset α) (Finset β) :=
  ⟨fun s t => (s.product t).Image fun p : α × β => p.1 • p.2⟩

localized [Pointwise] attribute [instance] Finset.hasScalar Finset.hasVadd

@[to_additive]
theorem smul_def : s • t = (s.product t).Image fun p : α × β => p.1 • p.2 :=
  rfl

@[to_additive]
theorem image_smul_product : ((s.product t).Image fun x : α × β => x.fst • x.snd) = s • t :=
  rfl

@[to_additive]
theorem mem_smul {x : β} : x ∈ s • t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y • z = x := by
  simp only [Finset.smul_def, And.assoc, mem_image, exists_prop, Prod.exists, mem_product]

@[simp, norm_cast, to_additive]
theorem coe_smul (s : Finset α) (t : Finset β) : (↑(s • t) : Set β) = (s : Set α) • t :=
  Set.ext fun _ => by
    simp only [mem_smul, Set.mem_smul, mem_coe]

@[to_additive]
theorem smul_mem_smul (ha : a ∈ s) (hb : b ∈ t) : a • b ∈ s • t :=
  mem_smul.2 ⟨a, b, ha, hb, rfl⟩

@[to_additive]
theorem smul_card_le : (s • t).card ≤ s.card • t.card :=
  card_image_le.trans (card_product _ _).le

@[simp, to_additive]
theorem empty_smul (t : Finset β) : (∅ : Finset α) • t = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp [mem_smul]

@[simp, to_additive]
theorem smul_empty (s : Finset α) : s • (∅ : Finset β) = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp [mem_smul]

@[simp, to_additive]
theorem smul_nonempty_iff : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  (Nonempty.image_iff _).trans nonempty_product

@[to_additive]
theorem Nonempty.smul (hs : s.Nonempty) (ht : t.Nonempty) : (s • t).Nonempty :=
  smul_nonempty_iff.2 ⟨hs, ht⟩

@[to_additive, mono]
theorem smul_subset_smul (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ • t₁ ⊆ s₂ • t₂ :=
  image_subset_image <| product_subset_product hs ht

attribute [mono] add_subset_add

@[simp, to_additive]
theorem smul_singleton (b : β) : s • ({b} : Finset β) = s.Image (· • b) := by
  classical
  rw [smul_def, product_singleton, map_eq_image, image_image]
  rfl

@[simp, to_additive]
theorem singleton_smul (a : α) : ({a} : Finset α) • t = t.Image ((· • ·) a) := by
  classical
  rw [smul_def, singleton_product, map_eq_image, image_image]
  rfl

@[simp, to_additive]
theorem singleton_smul_singleton (a : α) (b : β) : ({a} : Finset α) • ({b} : Finset β) = {a • b} := by
  rw [smul_def, singleton_product_singleton, image_singleton]

/-- If a finset `u` is contained in the scalar product of two sets `s • t`, we can find two finsets
`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' • t'`. -/
@[to_additive
      "If a finset `u` is contained in the scalar sum of two sets `s +ᵥ t`, we can find two\nfinsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' +ᵥ t'`."]
theorem subset_smul {s : Set α} {t : Set β} (f : ↑u ⊆ s • t) :
    ∃ (s' : Finset α)(t' : Finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' • t' := by
  apply Finset.induction_on' u
  · exact ⟨∅, ∅, Set.empty_subset _, Set.empty_subset _, empty_subset _⟩
    
  rintro a u ha _ _ ⟨s', t', hs, hs', h⟩
  obtain ⟨x, y, hx, hy, ha⟩ := f ha
  classical
  use insert x s', insert y t'
  simp_rw [coe_insert, Set.insert_subset]
  refine' ⟨⟨hx, hs⟩, ⟨hy, hs'⟩, _⟩
  convert insert_subset.2 ⟨mem_smul.2 ⟨x, y, mem_insert_self _ _, mem_insert_self _ _, ha⟩, h.trans <| _⟩
  convert smul_subset_smul (subset_insert _ _) (subset_insert _ _)

end HasScalar

/-! ### Finset addition/multiplication -/


section HasVsub

variable [DecidableEq α] [HasVsub α β] {s s₁ s₂ t t₁ t₂ u : Finset β} {a : α} {b c : β}

include α

/-- The pointwise product of two finsets `s` and `t`: `s -ᵥ t = {x -ᵥ y | x ∈ s, y ∈ t}`. -/
protected def hasVsub : HasVsub (Finset α) (Finset β) :=
  ⟨fun s t => (s.product t).Image fun p : β × β => p.1 -ᵥ p.2⟩

localized [Pointwise] attribute [instance] Finset.hasVsub

theorem vsub_def : s -ᵥ t = (s.product t).Image fun p : β × β => p.1 -ᵥ p.2 :=
  rfl

theorem image_vsub_product : ((s.product t).Image fun x : β × β => x.fst -ᵥ x.snd) = s -ᵥ t :=
  rfl

theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ b c, b ∈ s ∧ c ∈ t ∧ b -ᵥ c = a := by
  simp only [Finset.vsub_def, And.assoc, mem_image, exists_prop, Prod.exists, mem_product]

@[simp, norm_cast]
theorem coe_vsub (s t : Finset β) : (↑(s -ᵥ t) : Set α) = (s : Set β) -ᵥ t :=
  Set.ext fun _ => by
    simp only [mem_vsub, Set.mem_vsub, mem_coe]

theorem vsub_mem_vsub (hb : b ∈ s) (hc : c ∈ t) : b -ᵥ c ∈ s -ᵥ t :=
  mem_vsub.2 ⟨b, c, hb, hc, rfl⟩

theorem vsub_card_le : (s -ᵥ t : Finset α).card ≤ s.card * t.card :=
  card_image_le.trans (card_product _ _).le

@[simp]
theorem empty_vsub (t : Finset β) : (∅ : Finset β) -ᵥ t = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp [mem_vsub]

@[simp]
theorem vsub_empty (s : Finset β) : s -ᵥ (∅ : Finset β) = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp [mem_vsub]

@[simp]
theorem vsub_nonempty_iff : (s -ᵥ t : Finset α).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  (Nonempty.image_iff _).trans nonempty_product

theorem Nonempty.vsub (hs : s.Nonempty) (ht : t.Nonempty) : (s -ᵥ t : Finset α).Nonempty :=
  vsub_nonempty_iff.2 ⟨hs, ht⟩

@[mono]
theorem vsub_subset_vsub (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ :=
  image_subset_image <| product_subset_product hs ht

@[simp]
theorem vsub_singleton (b : β) : s -ᵥ ({b} : Finset β) = s.Image (· -ᵥ b) := by
  classical
  rw [vsub_def, product_singleton, map_eq_image, image_image]
  rfl

@[simp]
theorem singleton_vsub (a : β) : ({a} : Finset β) -ᵥ t = t.Image ((· -ᵥ ·) a) := by
  classical
  rw [vsub_def, singleton_product, map_eq_image, image_image]
  rfl

@[simp]
theorem singleton_vsub_singleton (a b : β) : ({a} : Finset β) -ᵥ {b} = {a -ᵥ b} := by
  rw [vsub_def, singleton_product_singleton, image_singleton]

/-- If a finset `u` is contained in the pointwise subtraction of two sets `s -ᵥ t`, we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' -ᵥ t'`. -/
theorem subset_vsub {s t : Set β} {u : Finset α} (f : ↑u ⊆ s -ᵥ t) :
    ∃ s' t' : Finset β, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' -ᵥ t' := by
  apply Finset.induction_on' u
  · exact ⟨∅, ∅, Set.empty_subset _, Set.empty_subset _, empty_subset _⟩
    
  rintro a u ha _ _ ⟨s', t', hs, hs', h⟩
  obtain ⟨x, y, hx, hy, ha⟩ := f ha
  classical
  use insert x s', insert y t'
  simp_rw [coe_insert, Set.insert_subset]
  refine' ⟨⟨hx, hs⟩, ⟨hy, hs'⟩, _⟩
  convert insert_subset.2 ⟨mem_vsub.2 ⟨x, y, mem_insert_self _ _, mem_insert_self _ _, ha⟩, h.trans <| _⟩
  convert vsub_subset_vsub (subset_insert _ _) (subset_insert _ _)

end HasVsub

open Pointwise

/-! ### Translation/scaling of finsets -/


section HasScalar

variable [DecidableEq β] [HasScalar α β] {s s₁ s₂ t u : Finset β} {a : α} {b : β}

/-- The scaling of a finset `s` by a scalar `a`: `a • s = {a • x | x ∈ s}`. -/
@[to_additive has_vadd_finset "The translation of a finset `s` by a vector `a`:\n`a +ᵥ s = {a +ᵥ x | x ∈ s}`."]
protected def hasScalarFinset : HasScalar α (Finset β) :=
  ⟨fun a => image <| (· • ·) a⟩

localized [Pointwise] attribute [instance] Finset.hasScalarFinset Finset.hasVaddFinset

@[to_additive]
theorem smul_finset_def : a • s = s.Image ((· • ·) a) :=
  rfl

@[to_additive]
theorem image_smul : (s.Image fun x => a • x) = a • s :=
  rfl

@[to_additive]
theorem mem_smul_finset {x : β} : x ∈ a • s ↔ ∃ y, y ∈ s ∧ a • y = x := by
  simp only [Finset.smul_finset_def, And.assoc, mem_image, exists_prop, Prod.exists, mem_product]

@[simp, norm_cast, to_additive]
theorem coe_smul_finset (s : Finset β) : (↑(a • s) : Set β) = a • s :=
  coe_image

@[to_additive]
theorem smul_finset_mem_smul_finset (hb : b ∈ s) : a • b ∈ a • s :=
  mem_image_of_mem _ hb

@[to_additive]
theorem smul_finset_card_le : (a • s).card ≤ s.card :=
  card_image_le

@[simp, to_additive]
theorem smul_finset_empty (a : α) : a • (∅ : Finset β) = ∅ :=
  image_empty _

@[simp, to_additive]
theorem smul_finset_nonempty_iff : (a • s).Nonempty ↔ s.Nonempty :=
  Nonempty.image_iff _

@[to_additive]
theorem Nonempty.smul_finset (hs : s.Nonempty) : (a • s).Nonempty :=
  hs.Image _

@[to_additive, mono]
theorem smul_finset_subset_smul_finset : s ⊆ t → a • s ⊆ a • t :=
  image_subset_image

attribute [mono] add_subset_add

@[simp, to_additive]
theorem smul_finset_singleton (b : β) : a • ({b} : Finset β) = {a • b} :=
  image_singleton _ _

end HasScalar

open Pointwise

section Instances

variable [DecidableEq γ]

@[to_additive]
instance smul_comm_class_set [HasScalar α γ] [HasScalar β γ] [SmulCommClass α β γ] :
    SmulCommClass α (Finset β) (Finset γ) :=
  ⟨fun a s t =>
    coe_injective <| by
      simp only [coe_smul_finset, coe_smul, smul_comm]⟩

@[to_additive]
instance smul_comm_class_set' [HasScalar α γ] [HasScalar β γ] [SmulCommClass α β γ] :
    SmulCommClass (Finset α) β (Finset γ) :=
  have := SmulCommClass.symm α β γ
  SmulCommClass.symm _ _ _

@[to_additive]
instance smul_comm_class [HasScalar α γ] [HasScalar β γ] [SmulCommClass α β γ] :
    SmulCommClass (Finset α) (Finset β) (Finset γ) :=
  ⟨fun s t u =>
    coe_injective <| by
      simp_rw [coe_smul, smul_comm]⟩

instance is_scalar_tower [HasScalar α β] [HasScalar α γ] [HasScalar β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Finset γ) :=
  ⟨fun a b s => by
    simp only [← image_smul, image_image, smul_assoc]⟩

variable [DecidableEq β]

instance is_scalar_tower' [HasScalar α β] [HasScalar α γ] [HasScalar β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Finset β) (Finset γ) :=
  ⟨fun a s t =>
    coe_injective <| by
      simp only [coe_smul_finset, coe_smul, smul_assoc]⟩

instance is_scalar_tower'' [HasScalar α β] [HasScalar α γ] [HasScalar β γ] [IsScalarTower α β γ] :
    IsScalarTower (Finset α) (Finset β) (Finset γ) :=
  ⟨fun a s t =>
    coe_injective <| by
      simp only [coe_smul_finset, coe_smul, smul_assoc]⟩

instance is_central_scalar [HasScalar α β] [HasScalar αᵐᵒᵖ β] [IsCentralScalar α β] : IsCentralScalar α (Finset β) :=
  ⟨fun a s =>
    coe_injective <| by
      simp only [coe_smul_finset, coe_smul, op_smul_eq_smul]⟩

end Instances

end Finset

