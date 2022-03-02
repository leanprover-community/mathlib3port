/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.Module.Basic
import Mathbin.Data.Finset.Preimage
import Mathbin.Data.Set.Finite
import Mathbin.GroupTheory.Submonoid.Basic

/-!
# Pointwise addition, multiplication, scalar multiplication and vector subtraction of sets.

This file defines pointwise algebraic operations on sets.
* For a type `α` with multiplication, multiplication is defined on `set α` by taking
  `s * t` to be the set of all `x * y` where `x ∈ s` and `y ∈ t`. Similarly for addition.
* For `α` a semigroup, `set α` is a semigroup.
* If `α` is a (commutative) monoid, we define an alias `set_semiring α` for `set α`, which then
  becomes a (commutative) semiring with union as addition and pointwise multiplication as
  multiplication.
* For a type `β` with scalar multiplication by another type `α`, this
  file defines a scalar multiplication of `set β` by `set α` and a separate scalar
  multiplication of `set β` by `α`.
* We also define pointwise multiplication on `finset`.

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes
* The following expressions are considered in simp-normal form in a group:
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`).

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/


open Function

variable {α β γ : Type _}

namespace Set

/-! ### Properties about 1 -/


section One

variable [One α] {s : Set α} {a : α}

/-- The set `(1 : set α)` is defined as `{1}` in locale `pointwise`. -/
@[to_additive "The set `(0 : set α)` is defined as `{0}` in locale `pointwise`. "]
protected def hasOne : One (Set α) :=
  ⟨{1}⟩

localized [Pointwise] attribute [instance] Set.hasOne Set.hasZero

@[to_additive]
theorem singleton_one : ({1} : Set α) = 1 :=
  rfl

@[simp, to_additive]
theorem mem_one : a ∈ (1 : Set α) ↔ a = 1 :=
  Iff.rfl

@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Set α) :=
  Eq.refl _

@[simp, to_additive]
theorem one_subset : 1 ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff

@[to_additive]
theorem one_nonempty : (1 : Set α).Nonempty :=
  ⟨1, rfl⟩

@[simp, to_additive]
theorem image_one {f : α → β} : f '' 1 = {f 1} :=
  image_singleton

end One

open_locale Pointwise

/-! ### Properties about multiplication -/


section Mul

variable {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/-- The set `(s * t : set α)` is defined as `{x * y | x ∈ s, y ∈ t}` in locale `pointwise`. -/
@[to_additive " The set `(s + t : set α)` is defined as `{x + y | x ∈ s, y ∈ t}` in locale `pointwise`."]
protected def hasMul [Mul α] : Mul (Set α) :=
  ⟨Image2 Mul.mul⟩

localized [Pointwise] attribute [instance] Set.hasMul Set.hasAdd

section Mul

variable {ι : Sort _} {κ : ι → Sort _} [Mul α]

@[simp, to_additive]
theorem image2_mul : Image2 Mul.mul s t = s * t :=
  rfl

@[to_additive]
theorem mem_mul : a ∈ s * t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x * y = a :=
  Iff.rfl

@[to_additive]
theorem mul_mem_mul (ha : a ∈ s) (hb : b ∈ t) : a * b ∈ s * t :=
  mem_image2_of_mem ha hb

@[to_additive]
theorem mul_subset_mul (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ * s₂ ⊆ t₁ * t₂ :=
  image2_subset h₁ h₂

@[to_additive add_image_prod]
theorem image_mul_prod : (fun x : α × α => x.fst * x.snd) '' (s ×ˢ t) = s * t :=
  image_prod _

@[simp, to_additive]
theorem empty_mul : ∅ * s = ∅ :=
  image2_empty_left

@[simp, to_additive]
theorem mul_empty : s * ∅ = ∅ :=
  image2_empty_right

@[simp, to_additive]
theorem mul_singleton : s * {b} = (· * b) '' s :=
  image2_singleton_right

@[simp, to_additive]
theorem singleton_mul : {a} * t = (· * ·) a '' t :=
  image2_singleton_left

@[simp, to_additive]
theorem singleton_mul_singleton : ({a} : Set α) * {b} = {a * b} :=
  image2_singleton

@[to_additive]
theorem mul_subset_mul_left (h : t₁ ⊆ t₂) : s * t₁ ⊆ s * t₂ :=
  image2_subset_left h

@[to_additive]
theorem mul_subset_mul_right (h : s₁ ⊆ s₂) : s₁ * t ⊆ s₂ * t :=
  image2_subset_right h

@[to_additive]
theorem union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t :=
  image2_union_left

@[to_additive]
theorem mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ :=
  image2_union_right

@[to_additive]
theorem inter_mul_subset : s₁ ∩ s₂ * t ⊆ s₁ * t ∩ (s₂ * t) :=
  image2_inter_subset_left

@[to_additive]
theorem mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
  image2_inter_subset_right

@[to_additive]
theorem Union_mul_left_image : (⋃ a ∈ s, (fun x => a * x) '' t) = s * t :=
  Union_image_left _

@[to_additive]
theorem Union_mul_right_image : (⋃ a ∈ t, (fun x => x * a) '' s) = s * t :=
  Union_image_right _

@[to_additive]
theorem Union_mul (s : ι → Set α) (t : Set α) : (⋃ i, s i) * t = ⋃ i, s i * t :=
  image2_Union_left _ _ _

@[to_additive]
theorem mul_Union (s : Set α) (t : ι → Set α) : (s * ⋃ i, t i) = ⋃ i, s * t i :=
  image2_Union_right _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[to_additive]
theorem Union₂_mul (s : ∀ i, κ i → Set α) (t : Set α) : (⋃ (i) (j), s i j) * t = ⋃ (i) (j), s i j * t :=
  image2_Union₂_left _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[to_additive]
theorem mul_Union₂ (s : Set α) (t : ∀ i, κ i → Set α) : (s * ⋃ (i) (j), t i j) = ⋃ (i) (j), s * t i j :=
  image2_Union₂_right _ _ _

@[to_additive]
theorem Inter_mul_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t :=
  image2_Inter_subset_left _ _ _

@[to_additive]
theorem mul_Inter_subset (s : Set α) (t : ι → Set α) : (s * ⋂ i, t i) ⊆ ⋂ i, s * t i :=
  image2_Inter_subset_right _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[to_additive]
theorem Inter₂_mul_subset (s : ∀ i, κ i → Set α) (t : Set α) : (⋂ (i) (j), s i j) * t ⊆ ⋂ (i) (j), s i j * t :=
  image2_Inter₂_subset_left _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[to_additive]
theorem mul_Inter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) : (s * ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s * t i j :=
  image2_Inter₂_subset_right _ _ _

/-- Under `[has_mul M]`, the `singleton` map from `M` to `set M` as a `mul_hom`, that is, a map
which preserves multiplication. -/
@[to_additive
      "Under `[has_add A]`, the `singleton` map from `A` to `set A` as an `add_hom`,\nthat is, a map which preserves addition.",
  simps]
def singletonMulHom : MulHom α (Set α) where
  toFun := singleton
  map_mul' := fun a b => singleton_mul_singleton.symm

end Mul

@[simp, to_additive]
theorem image_mul_left [Groupₓ α] : (· * ·) a '' t = (· * ·) a⁻¹ ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[simp, to_additive]
theorem image_mul_right [Groupₓ α] : (· * b) '' t = (· * b⁻¹) ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive]
theorem image_mul_left' [Groupₓ α] : (fun b => a⁻¹ * b) '' t = (fun b => a * b) ⁻¹' t := by
  simp

@[to_additive]
theorem image_mul_right' [Groupₓ α] : (· * b⁻¹) '' t = (· * b) ⁻¹' t := by
  simp

@[simp, to_additive]
theorem preimage_mul_left_singleton [Groupₓ α] : (· * ·) a ⁻¹' {b} = {a⁻¹ * b} := by
  rw [← image_mul_left', image_singleton]

@[simp, to_additive]
theorem preimage_mul_right_singleton [Groupₓ α] : (· * a) ⁻¹' {b} = {b * a⁻¹} := by
  rw [← image_mul_right', image_singleton]

@[simp, to_additive]
theorem preimage_mul_left_one [Groupₓ α] : (· * ·) a ⁻¹' 1 = {a⁻¹} := by
  rw [← image_mul_left', image_one, mul_oneₓ]

@[simp, to_additive]
theorem preimage_mul_right_one [Groupₓ α] : (· * b) ⁻¹' 1 = {b⁻¹} := by
  rw [← image_mul_right', image_one, one_mulₓ]

@[to_additive]
theorem preimage_mul_left_one' [Groupₓ α] : (fun b => a⁻¹ * b) ⁻¹' 1 = {a} := by
  simp

@[to_additive]
theorem preimage_mul_right_one' [Groupₓ α] : (· * b⁻¹) ⁻¹' 1 = {b} := by
  simp

@[to_additive]
protected theorem mul_comm [CommSemigroupₓ α] : s * t = t * s := by
  simp only [← image2_mul, image2_swap _ s, mul_comm]

/-- `set α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mulOneClass [MulOneClassₓ α] : MulOneClassₓ (Set α) :=
  { Set.hasOne, Set.hasMul with
    mul_one := fun s => by
      simp only [← singleton_one, mul_singleton, mul_oneₓ, image_id'],
    one_mul := fun s => by
      simp only [← singleton_one, singleton_mul, one_mulₓ, image_id'] }

/-- `set α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_semigroup` under pointwise operations if `α` is. "]
protected def semigroup [Semigroupₓ α] : Semigroupₓ (Set α) :=
  { Set.hasMul with mul_assoc := fun _ _ _ => image2_assoc mul_assoc }

/-- `set α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_monoid` under pointwise operations if `α` is. "]
protected def monoid [Monoidₓ α] : Monoidₓ (Set α) :=
  { Set.semigroup, Set.mulOneClass with }

/-- `set α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_monoid` under pointwise operations if `α` is. "]
protected def commMonoid [CommMonoidₓ α] : CommMonoidₓ (Set α) :=
  { Set.monoid with mul_comm := fun _ _ => Set.mul_comm }

localized [Pointwise]
  attribute [instance]
    Set.mulOneClass Set.addZeroClass Set.semigroup Set.addSemigroup Set.monoid Set.addMonoid Set.commMonoid Set.addCommMonoid

@[to_additive nsmul_mem_nsmul]
theorem pow_mem_pow [Monoidₓ α] (ha : a ∈ s) (n : ℕ) : a ^ n ∈ s ^ n := by
  induction' n with n ih
  · rw [pow_zeroₓ]
    exact Set.mem_singleton 1
    
  · rw [pow_succₓ]
    exact Set.mul_mem_mul ha ih
    

@[to_additive empty_nsmul]
theorem empty_pow [Monoidₓ α] (n : ℕ) (hn : n ≠ 0) : (∅ : Set α) ^ n = ∅ := by
  rw [← tsub_add_cancel_of_le (Nat.succ_le_of_ltₓ <| Nat.pos_of_ne_zeroₓ hn), pow_succₓ, empty_mul]

instance decidableMemMul [Monoidₓ α] [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidablePred (· ∈ s * t) := fun _ => decidableOfIff _ mem_mul.symm

instance decidableMemPow [Monoidₓ α] [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)] (n : ℕ) :
    DecidablePred (· ∈ s ^ n) := by
  induction' n with n ih
  · simp_rw [pow_zeroₓ, mem_one]
    infer_instance
    
  · let this' := ih
    rw [pow_succₓ]
    infer_instance
    

@[to_additive]
theorem subset_mul_left [MulOneClassₓ α] (s : Set α) {t : Set α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun x hx =>
  ⟨x, 1, hx, ht, mul_oneₓ _⟩

@[to_additive]
theorem subset_mul_right [MulOneClassₓ α] {s : Set α} (t : Set α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun x hx =>
  ⟨1, x, hs, hx, one_mulₓ _⟩

theorem pow_subset_pow [Monoidₓ α] (hst : s ⊆ t) (n : ℕ) : s ^ n ⊆ t ^ n := by
  induction' n with n ih
  · rw [pow_zeroₓ]
    exact subset.rfl
    
  · rw [pow_succₓ, pow_succₓ]
    exact mul_subset_mul hst ih
    

@[simp, to_additive]
theorem univ_mul_univ [Monoidₓ α] : (Univ : Set α) * univ = univ := by
  have : ∀ x, ∃ a b : α, a * b = x := fun x => ⟨x, ⟨1, mul_oneₓ x⟩⟩
  simpa only [mem_mul, eq_univ_iff_forall, mem_univ, true_andₓ]

@[simp, to_additive]
theorem mul_univ [Groupₓ α] (hs : s.Nonempty) : s * (Univ : Set α) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ * b, ha, trivialₓ, mul_inv_cancel_left _ _⟩

@[simp, to_additive]
theorem univ_mul [Groupₓ α] (ht : t.Nonempty) : (Univ : Set α) * t = univ :=
  let ⟨a, ha⟩ := ht
  eq_univ_of_forall fun b => ⟨b * a⁻¹, a, trivialₓ, ha, inv_mul_cancel_right _ _⟩

/-- `singleton` is a monoid hom. -/
@[to_additive singleton_add_hom "singleton is an add monoid hom"]
def singletonHom [Monoidₓ α] : α →* Set α where
  toFun := singleton
  map_one' := rfl
  map_mul' := fun a b => singleton_mul_singleton.symm

@[to_additive]
theorem Nonempty.mul [Mul α] : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
  nonempty.image2

@[to_additive]
theorem Finite.mul [Mul α] (hs : Finite s) (ht : Finite t) : Finite (s * t) :=
  hs.Image2 _ ht

/-- multiplication preserves finiteness -/
@[to_additive "addition preserves finiteness"]
def fintypeMul [Mul α] [DecidableEq α] (s t : Set α) [hs : Fintype s] [ht : Fintype t] : Fintype (s * t : Set α) :=
  Set.fintypeImage2 _ s t

@[to_additive]
theorem bdd_above_mul [OrderedCommMonoid α] {A B : Set α} : BddAbove A → BddAbove B → BddAbove (A * B) := by
  rintro ⟨bA, hbA⟩ ⟨bB, hbB⟩
  use bA * bB
  rintro x ⟨xa, xb, hxa, hxb, rfl⟩
  exact mul_le_mul' (hbA hxa) (hbB hxb)

end Mul

open_locale Pointwise

section BigOperators

open_locale BigOperators

variable {ι : Type _} [CommMonoidₓ α]

/-- The n-ary version of `set.mem_mul`. -/
@[to_additive " The n-ary version of `set.mem_add`. "]
theorem mem_finset_prod (t : Finset ι) (f : ι → Set α) (a : α) :
    (a ∈ ∏ i in t, f i) ↔ ∃ (g : ι → α)(hg : ∀ {i}, i ∈ t → g i ∈ f i), (∏ i in t, g i) = a := by
  classical
  induction' t using Finset.induction_on with i is hi ih generalizing a
  · simp_rw [Finset.prod_empty, Set.mem_one]
    exact ⟨fun h => ⟨fun i => a, fun i => False.elim, h.symm⟩, fun ⟨f, _, hf⟩ => hf.symm⟩
    
  rw [Finset.prod_insert hi, Set.mem_mul]
  simp_rw [Finset.prod_insert hi]
  simp_rw [ih]
  constructor
  · rintro ⟨x, y, hx, ⟨g, hg, rfl⟩, rfl⟩
    refine' ⟨Function.update g i x, fun j hj => _, _⟩
    obtain rfl | hj := finset.mem_insert.mp hj
    · rw [Function.update_same]
      exact hx
      
    · rw [update_noteq (ne_of_mem_of_not_mem hj hi)]
      exact hg hj
      
    rw [Finset.prod_update_of_not_mem hi, Function.update_same]
    
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g i, is.prod g, hg (is.mem_insert_self _), ⟨g, fun i hi => hg (Finset.mem_insert_of_mem hi), rfl⟩, rfl⟩
    

/-- A version of `set.mem_finset_prod` with a simpler RHS for products over a fintype. -/
@[to_additive " A version of `set.mem_finset_sum` with a simpler RHS for sums over a fintype. "]
theorem mem_fintype_prod [Fintype ι] (f : ι → Set α) (a : α) :
    (a ∈ ∏ i, f i) ↔ ∃ (g : ι → α)(hg : ∀ i, g i ∈ f i), (∏ i, g i) = a := by
  rw [mem_finset_prod]
  simp

/-- The n-ary version of `set.mul_mem_mul`. -/
@[to_additive " The n-ary version of `set.add_mem_add`. "]
theorem finset_prod_mem_finset_prod (t : Finset ι) (f : ι → Set α) (g : ι → α) (hg : ∀, ∀ i ∈ t, ∀, g i ∈ f i) :
    (∏ i in t, g i) ∈ ∏ i in t, f i := by
  rw [mem_finset_prod]
  exact ⟨g, hg, rfl⟩

/-- The n-ary version of `set.mul_subset_mul`. -/
@[to_additive " The n-ary version of `set.add_subset_add`. "]
theorem finset_prod_subset_finset_prod (t : Finset ι) (f₁ f₂ : ι → Set α) (hf : ∀ {i}, i ∈ t → f₁ i ⊆ f₂ i) :
    (∏ i in t, f₁ i) ⊆ ∏ i in t, f₂ i := by
  intro a
  rw [mem_finset_prod, mem_finset_prod]
  rintro ⟨g, hg, rfl⟩
  exact ⟨g, fun i hi => hf hi <| hg hi, rfl⟩

@[to_additive]
theorem finset_prod_singleton {M ι : Type _} [CommMonoidₓ M] (s : Finset ι) (I : ι → M) :
    (∏ i : ι in s, ({I i} : Set M)) = {∏ i : ι in s, I i} := by
  let this' := Classical.decEq ι
  refine' Finset.induction_on s _ _
  · simpa
    
  · intro _ _ H ih
    rw [Finset.prod_insert H, Finset.prod_insert H, ih]
    simp
    

/-! TODO: define `decidable_mem_finset_prod` and `decidable_mem_finset_sum`. -/


end BigOperators

/-! ### Properties about inversion -/


section Inv

variable {s t : Set α} {a : α}

/-- The set `(s⁻¹ : set α)` is defined as `{x | x⁻¹ ∈ s}` in locale `pointwise`.
It is equal to `{x⁻¹ | x ∈ s}`, see `set.image_inv`. -/
@[to_additive
      " The set `(-s : set α)` is defined as `{x | -x ∈ s}` in locale `pointwise`.\nIt is equal to `{-x | x ∈ s}`, see `set.image_neg`. "]
protected def hasInv [Inv α] : Inv (Set α) :=
  ⟨Preimage Inv.inv⟩

localized [Pointwise] attribute [instance] Set.hasInv Set.hasNeg

@[simp, to_additive]
theorem inv_empty [Inv α] : (∅ : Set α)⁻¹ = ∅ :=
  rfl

@[simp, to_additive]
theorem inv_univ [Inv α] : (Univ : Set α)⁻¹ = univ :=
  rfl

@[simp, to_additive]
theorem nonempty_inv [HasInvolutiveInv α] {s : Set α} : s⁻¹.Nonempty ↔ s.Nonempty :=
  inv_involutive.Surjective.nonempty_preimage

@[to_additive]
theorem Nonempty.inv [HasInvolutiveInv α] {s : Set α} (h : s.Nonempty) : s⁻¹.Nonempty :=
  nonempty_inv.2 h

@[simp, to_additive]
theorem mem_inv [Inv α] : a ∈ s⁻¹ ↔ a⁻¹ ∈ s :=
  Iff.rfl

@[to_additive]
theorem inv_mem_inv [HasInvolutiveInv α] : a⁻¹ ∈ s⁻¹ ↔ a ∈ s := by
  simp only [mem_inv, inv_invₓ]

@[simp, to_additive]
theorem inv_preimage [Inv α] : Inv.inv ⁻¹' s = s⁻¹ :=
  rfl

@[simp, to_additive]
theorem image_inv [HasInvolutiveInv α] : Inv.inv '' s = s⁻¹ := by
  simp only [← inv_preimage]
  rw [image_eq_preimage_of_inverse] <;> intro <;> simp only [inv_invₓ]

@[simp, to_additive]
theorem inter_inv [Inv α] : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ :=
  preimage_inter

@[simp, to_additive]
theorem union_inv [Inv α] : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ :=
  preimage_union

@[simp, to_additive]
theorem Inter_inv {ι : Sort _} [Inv α] (s : ι → Set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ :=
  preimage_Inter

@[simp, to_additive]
theorem Union_inv {ι : Sort _} [Inv α] (s : ι → Set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ :=
  preimage_Union

@[simp, to_additive]
theorem compl_inv [Inv α] : (sᶜ)⁻¹ = s⁻¹ᶜ :=
  preimage_compl

@[simp, to_additive]
instance [HasInvolutiveInv α] : HasInvolutiveInv (Set α) where
  inv := Inv.inv
  inv_inv := fun s => by
    simp only [← inv_preimage, preimage_preimage, inv_invₓ, preimage_id']

@[simp, to_additive]
theorem inv_subset_inv [HasInvolutiveInv α] {s t : Set α} : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t :=
  (Equivₓ.inv α).Surjective.preimage_subset_preimage_iff

@[to_additive]
theorem inv_subset [HasInvolutiveInv α] {s t : Set α} : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ := by
  rw [← inv_subset_inv, inv_invₓ]

@[to_additive]
theorem Finite.inv [HasInvolutiveInv α] {s : Set α} (hs : Finite s) : Finite s⁻¹ :=
  hs.Preimage <| inv_injective.InjOn _

@[to_additive]
theorem inv_singleton {β : Type _} [HasInvolutiveInv β] (x : β) : ({x} : Set β)⁻¹ = {x⁻¹} := by
  ext1 y
  rw [mem_inv, mem_singleton_iff, mem_singleton_iff, inv_eq_iff_inv_eq, eq_comm]

@[to_additive]
protected theorem mul_inv_rev [Groupₓ α] (s t : Set α) : (s * t)⁻¹ = t⁻¹ * s⁻¹ := by
  simp_rw [← image_inv, ← image2_mul, image_image2, image2_image_left, image2_image_right, mul_inv_rev,
    image2_swap _ s t]

end Inv

/-! ### Properties about scalar multiplication -/


section Smul

/-- The scaling of a set `(x • s : set β)` by a scalar `x ∶ α` is defined as `{x • y | y ∈ s}`
in locale `pointwise`. -/
@[to_additive has_vadd_set
      "The translation of a set `(x +ᵥ s : set β)` by a scalar `x ∶ α` is\ndefined as `{x +ᵥ y | y ∈ s}` in locale `pointwise`."]
protected def hasScalarSet [HasScalar α β] : HasScalar α (Set β) :=
  ⟨fun a => Image (HasScalar.smul a)⟩

/-- The pointwise scalar multiplication `(s • t : set β)` by a set of scalars `s ∶ set α`
is defined as `{x • y | x ∈ s, y ∈ t}` in locale `pointwise`. -/
@[to_additive HasVadd
      "The pointwise translation `(s +ᵥ t : set β)` by a set of constants\n`s ∶ set α` is defined as `{x +ᵥ y | x ∈ s, y ∈ t}` in locale `pointwise`."]
protected def hasScalar [HasScalar α β] : HasScalar (Set α) (Set β) :=
  ⟨Image2 HasScalar.smul⟩

localized [Pointwise] attribute [instance] Set.hasScalarSet Set.hasScalar

localized [Pointwise] attribute [instance] Set.hasVaddSet Set.hasVadd

section HasScalar

variable {ι : Sort _} {κ : ι → Sort _} [HasScalar α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α} {b : β}

@[simp, to_additive]
theorem image2_smul : Image2 HasScalar.smul s t = s • t :=
  rfl

@[to_additive add_image_prod]
theorem image_smul_prod : (fun x : α × β => x.fst • x.snd) '' (s ×ˢ t) = s • t :=
  image_prod _

@[to_additive]
theorem mem_smul : b ∈ s • t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x • y = b :=
  Iff.rfl

@[to_additive]
theorem smul_mem_smul (ha : a ∈ s) (hb : b ∈ t) : a • b ∈ s • t :=
  mem_image2_of_mem ha hb

@[to_additive]
theorem smul_subset_smul (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ • t₁ ⊆ s₂ • t₂ :=
  image2_subset hs ht

@[to_additive]
theorem smul_subset_iff : s • t ⊆ u ↔ ∀, ∀ a ∈ s, ∀, ∀ b ∈ t, ∀, a • b ∈ u :=
  image2_subset_iff

@[simp, to_additive]
theorem empty_smul : (∅ : Set α) • t = ∅ :=
  image2_empty_left

@[simp, to_additive]
theorem smul_empty : s • (∅ : Set β) = ∅ :=
  image2_empty_right

@[simp, to_additive]
theorem smul_singleton : s • {b} = (· • b) '' s :=
  image2_singleton_right

@[simp, to_additive]
theorem singleton_smul : ({a} : Set α) • t = a • t :=
  image2_singleton_left

@[simp, to_additive]
theorem singleton_smul_singleton : ({a} : Set α) • ({b} : Set β) = {a • b} :=
  image2_singleton

@[to_additive]
theorem smul_subset_smul_left (h : t₁ ⊆ t₂) : s • t₁ ⊆ s • t₂ :=
  image2_subset_left h

@[to_additive]
theorem smul_subset_smul_right (h : s₁ ⊆ s₂) : s₁ • t ⊆ s₂ • t :=
  image2_subset_right h

@[to_additive]
theorem union_smul : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t :=
  image2_union_left

@[to_additive]
theorem smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ :=
  image2_union_right

@[to_additive]
theorem inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
  image2_inter_subset_left

@[to_additive]
theorem smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
  image2_inter_subset_right

@[to_additive]
theorem Union_smul_left_image : (⋃ a ∈ s, a • t) = s • t :=
  Union_image_left _

@[to_additive]
theorem Union_smul_right_image : (⋃ a ∈ t, (fun x => x • a) '' s) = s • t :=
  Union_image_right _

@[to_additive]
theorem Union_smul (s : ι → Set α) (t : Set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
  image2_Union_left _ _ _

@[to_additive]
theorem smul_Union (s : Set α) (t : ι → Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i :=
  image2_Union_right _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[to_additive]
theorem Union₂_smul (s : ∀ i, κ i → Set α) (t : Set β) : (⋃ (i) (j), s i j) • t = ⋃ (i) (j), s i j • t :=
  image2_Union₂_left _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[to_additive]
theorem smul_Union₂ (s : Set α) (t : ∀ i, κ i → Set β) : (s • ⋃ (i) (j), t i j) = ⋃ (i) (j), s • t i j :=
  image2_Union₂_right _ _ _

@[to_additive]
theorem Inter_smul_subset (s : ι → Set α) (t : Set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
  image2_Inter_subset_left _ _ _

@[to_additive]
theorem smul_Inter_subset (s : Set α) (t : ι → Set β) : (s • ⋂ i, t i) ⊆ ⋂ i, s • t i :=
  image2_Inter_subset_right _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[to_additive]
theorem Inter₂_smul_subset (s : ∀ i, κ i → Set α) (t : Set β) : (⋂ (i) (j), s i j) • t ⊆ ⋂ (i) (j), s i j • t :=
  image2_Inter₂_subset_left _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[to_additive]
theorem smul_Inter₂_subset (s : Set α) (t : ∀ i, κ i → Set β) : (s • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s • t i j :=
  image2_Inter₂_subset_right _ _ _

end HasScalar

section HasScalarSet

variable {ι : Sort _} {κ : ι → Sort _} [HasScalar α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

@[simp, to_additive]
theorem image_smul : (fun x => a • x) '' t = a • t :=
  rfl

@[to_additive]
theorem mem_smul_set : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x :=
  Iff.rfl

@[to_additive]
theorem smul_mem_smul_set (hy : y ∈ t) : a • y ∈ a • t :=
  ⟨y, hy, rfl⟩

@[to_additive]
theorem mem_smul_of_mem {s : Set α} (ha : a ∈ s) (hb : b ∈ t) : a • b ∈ s • t :=
  mem_image2_of_mem ha hb

@[simp, to_additive]
theorem smul_set_empty : a • (∅ : Set β) = ∅ :=
  image_empty _

@[simp, to_additive]
theorem smul_set_singleton : a • ({b} : Set β) = {a • b} :=
  image_singleton

@[to_additive]
theorem smul_set_mono (h : s ⊆ t) : a • s ⊆ a • t :=
  image_subset _ h

@[to_additive]
theorem smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ :=
  image_union _ _ _

@[to_additive]
theorem smul_set_inter_subset : a • (t₁ ∩ t₂) ⊆ a • t₁ ∩ a • t₂ :=
  image_inter_subset _ _ _

@[to_additive]
theorem smul_set_Union (a : α) (s : ι → Set β) : (a • ⋃ i, s i) = ⋃ i, a • s i :=
  image_Union

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[to_additive]
theorem smul_set_Union₂ (a : α) (s : ∀ i, κ i → Set β) : (a • ⋃ (i) (j), s i j) = ⋃ (i) (j), a • s i j :=
  image_Union₂ _ _

@[to_additive]
theorem smul_set_Inter_subset (a : α) (t : ι → Set β) : (a • ⋂ i, t i) ⊆ ⋂ i, a • t i :=
  image_Inter_subset _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[to_additive]
theorem smul_set_Inter₂_subset (a : α) (t : ∀ i, κ i → Set β) : (a • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), a • t i j :=
  image_Inter₂_subset _ _

@[to_additive]
theorem Finite.smul_set (hs : Finite s) : Finite (a • s) :=
  hs.Image _

end HasScalarSet

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

@[to_additive]
theorem smul_set_inter [Groupₓ α] [MulAction α β] {s t : Set β} : a • (s ∩ t) = a • s ∩ a • t :=
  (image_inter <| MulAction.injective a).symm

theorem smul_set_inter₀ [GroupWithZeroₓ α] [MulAction α β] {s t : Set β} (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t :=
  show Units.mk0 a ha • _ = _ from smul_set_inter

@[simp, to_additive]
theorem smul_set_univ [Groupₓ α] [MulAction α β] {a : α} : a • (Univ : Set β) = univ :=
  eq_univ_of_forall fun b => ⟨a⁻¹ • b, trivialₓ, smul_inv_smul _ _⟩

@[simp, to_additive]
theorem smul_univ [Groupₓ α] [MulAction α β] {s : Set α} (hs : s.Nonempty) : s • (Univ : Set β) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ • b, ha, trivialₓ, smul_inv_smul _ _⟩

@[to_additive]
theorem range_smul_range {ι κ : Type _} [HasScalar α β] (b : ι → α) (c : κ → β) :
    Range b • Range c = Range fun p : ι × κ => b p.1 • c p.2 :=
  ext fun x =>
    ⟨fun hx =>
      let ⟨p, q, ⟨i, hi⟩, ⟨j, hj⟩, hpq⟩ := Set.mem_smul.1 hx
      ⟨(i, j), hpq ▸ hi ▸ hj ▸ rfl⟩,
      fun ⟨⟨i, j⟩, h⟩ => Set.mem_smul.2 ⟨b i, c j, ⟨i, rfl⟩, ⟨j, rfl⟩, h⟩⟩

@[to_additive]
instance smul_comm_class_set [HasScalar α γ] [HasScalar β γ] [SmulCommClass α β γ] :
    SmulCommClass α (Set β) (Set γ) where
  smul_comm := fun a T T' => by
    simp only [← image2_smul, ← image_smul, image2_image_right, image_image2, smul_comm]

@[to_additive]
instance smul_comm_class_set' [HasScalar α γ] [HasScalar β γ] [SmulCommClass α β γ] : SmulCommClass (Set α) β (Set γ) :=
  have := SmulCommClass.symm α β γ
  SmulCommClass.symm _ _ _

@[to_additive]
instance smul_comm_class [HasScalar α γ] [HasScalar β γ] [SmulCommClass α β γ] :
    SmulCommClass (Set α) (Set β) (Set γ) where
  smul_comm := fun T T' T'' => by
    simp only [← image2_smul, image2_swap _ T]
    exact image2_assoc fun b c a => smul_comm a b c

instance is_scalar_tower [HasScalar α β] [HasScalar α γ] [HasScalar β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Set γ) where
  smul_assoc := fun a b T => by
    simp only [← image_smul, image_image, smul_assoc]

instance is_scalar_tower' [HasScalar α β] [HasScalar α γ] [HasScalar β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Set β) (Set γ) where
  smul_assoc := fun a T T' => by
    simp only [← image_smul, ← image2_smul, image_image2, image2_image_left, smul_assoc]

instance is_scalar_tower'' [HasScalar α β] [HasScalar α γ] [HasScalar β γ] [IsScalarTower α β γ] :
    IsScalarTower (Set α) (Set β) (Set γ) where
  smul_assoc := fun T T' T'' => image2_assoc smul_assoc

instance is_central_scalar [HasScalar α β] [HasScalar αᵐᵒᵖ β] [IsCentralScalar α β] : IsCentralScalar α (Set β) :=
  ⟨fun a S => (congr_argₓ fun f => f '' S) <| funext fun _ => op_smul_eq_smul _ _⟩

end Smul

section Vsub

variable {ι : Sort _} {κ : ι → Sort _} [HasVsub α β] {s s₁ s₂ t t₁ t₂ : Set β} {a : α} {b c : β}

include α

instance hasVsub : HasVsub (Set α) (Set β) :=
  ⟨Image2 (· -ᵥ ·)⟩

@[simp]
theorem image2_vsub : (Image2 HasVsub.vsub s t : Set α) = s -ᵥ t :=
  rfl

theorem image_vsub_prod : (fun x : β × β => x.fst -ᵥ x.snd) '' (s ×ˢ t) = s -ᵥ t :=
  image_prod _

theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x -ᵥ y = a :=
  Iff.rfl

theorem vsub_mem_vsub (hb : b ∈ s) (hc : c ∈ t) : b -ᵥ c ∈ s -ᵥ t :=
  mem_image2_of_mem hb hc

theorem vsub_subset_vsub (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ :=
  image2_subset hs ht

theorem vsub_subset_iff {u : Set α} : s -ᵥ t ⊆ u ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ t, ∀, x -ᵥ y ∈ u :=
  image2_subset_iff

@[simp]
theorem empty_vsub (t : Set β) : ∅ -ᵥ t = ∅ :=
  image2_empty_left

@[simp]
theorem vsub_empty (s : Set β) : s -ᵥ ∅ = ∅ :=
  image2_empty_right

@[simp]
theorem vsub_singleton (s : Set β) (b : β) : s -ᵥ {b} = (· -ᵥ b) '' s :=
  image2_singleton_right

@[simp]
theorem singleton_vsub (t : Set β) (b : β) : {b} -ᵥ t = (· -ᵥ ·) b '' t :=
  image2_singleton_left

@[simp]
theorem singleton_vsub_singleton : ({b} : Set β) -ᵥ {c} = {b -ᵥ c} :=
  image2_singleton

theorem vsub_subset_vsub_left (h : t₁ ⊆ t₂) : s -ᵥ t₁ ⊆ s -ᵥ t₂ :=
  image2_subset_left h

theorem vsub_subset_vsub_right (h : s₁ ⊆ s₂) : s₁ -ᵥ t ⊆ s₂ -ᵥ t :=
  image2_subset_right h

theorem union_vsub : s₁ ∪ s₂ -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) :=
  image2_union_left

theorem vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) :=
  image2_union_right

theorem inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) :=
  image2_inter_subset_left

theorem vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) :=
  image2_inter_subset_right

theorem Union_vsub_left_image : (⋃ a ∈ s, (· -ᵥ ·) a '' t) = s -ᵥ t :=
  Union_image_left _

theorem Union_vsub_right_image : (⋃ a ∈ t, (· -ᵥ a) '' s) = s -ᵥ t :=
  Union_image_right _

theorem Union_vsub (s : ι → Set β) (t : Set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
  image2_Union_left _ _ _

theorem vsub_Union (s : Set β) (t : ι → Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i :=
  image2_Union_right _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem Union₂_vsub (s : ∀ i, κ i → Set β) (t : Set β) : (⋃ (i) (j), s i j) -ᵥ t = ⋃ (i) (j), s i j -ᵥ t :=
  image2_Union₂_left _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem vsub_Union₂ (s : Set β) (t : ∀ i, κ i → Set β) : (s -ᵥ ⋃ (i) (j), t i j) = ⋃ (i) (j), s -ᵥ t i j :=
  image2_Union₂_right _ _ _

theorem Inter_vsub_subset (s : ι → Set β) (t : Set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
  image2_Inter_subset_left _ _ _

theorem vsub_Inter_subset (s : Set β) (t : ι → Set β) : (s -ᵥ ⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
  image2_Inter_subset_right _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem Inter₂_vsub_subset (s : ∀ i, κ i → Set β) (t : Set β) : (⋂ (i) (j), s i j) -ᵥ t ⊆ ⋂ (i) (j), s i j -ᵥ t :=
  image2_Inter₂_subset_left _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem vsub_Inter₂_subset (s : Set β) (t : ∀ i, κ i → Set β) : (s -ᵥ ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s -ᵥ t i j :=
  image2_Inter₂_subset_right _ _ _

theorem Finite.vsub (hs : Finite s) (ht : Finite t) : Finite (s -ᵥ t) :=
  hs.Image2 _ ht

theorem vsub_self_mono (h : s ⊆ t) : s -ᵥ s ⊆ t -ᵥ t :=
  vsub_subset_vsub h h

end Vsub

open_locale Pointwise

section Ringₓ

variable [Ringₓ α] [AddCommGroupₓ β] [Module α β] {s : Set α} {t : Set β} {a : α}

@[simp]
theorem neg_smul_set : -a • t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg, image_image, neg_smul]

@[simp]
theorem smul_set_neg : a • -t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg, image_image, smul_neg]

@[simp]
protected theorem neg_smul : -s • t = -(s • t) := by
  simp_rw [← image2_smul, ← image_neg, image2_image_left, image_image2, neg_smul]

@[simp]
protected theorem smul_neg : s • -t = -(s • t) := by
  simp_rw [← image2_smul, ← image_neg, image2_image_right, image_image2, smul_neg]

end Ringₓ

section Monoidₓ

/-! ### `set α` as a `(∪,*)`-semiring -/


/-- An alias for `set α`, which has a semiring structure given by `∪` as "addition" and pointwise
  multiplication `*` as "multiplication". -/
def SetSemiring (α : Type _) : Type _ :=
  Set α deriving Inhabited, PartialOrderₓ, OrderBot

/-- The identitiy function `set α → set_semiring α`. -/
protected def Up (s : Set α) : SetSemiring α :=
  s

/-- The identitiy function `set_semiring α → set α`. -/
protected def SetSemiring.Down (s : SetSemiring α) : Set α :=
  s

@[simp]
protected theorem down_up {s : Set α} : s.up.down = s :=
  rfl

@[simp]
protected theorem up_down {s : SetSemiring α} : s.down.up = s :=
  rfl

-- This lemma is not tagged `simp`, since otherwise the linter complains.
theorem up_le_up {s t : Set α} : s.up ≤ t.up ↔ s ⊆ t :=
  Iff.rfl

-- This lemma is not tagged `simp`, since otherwise the linter complains.
theorem up_lt_up {s t : Set α} : s.up < t.up ↔ s ⊂ t :=
  Iff.rfl

@[simp]
theorem down_subset_down {s t : SetSemiring α} : s.down ⊆ t.down ↔ s ≤ t :=
  Iff.rfl

@[simp]
theorem down_ssubset_down {s t : SetSemiring α} : s.down ⊂ t.down ↔ s < t :=
  Iff.rfl

instance SetSemiring.addCommMonoid : AddCommMonoidₓ (SetSemiring α) where
  add := fun s t => (s ∪ t : Set α)
  zero := (∅ : Set α)
  add_assoc := union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm

instance SetSemiring.nonUnitalNonAssocSemiring [Mul α] : NonUnitalNonAssocSemiringₓ (SetSemiring α) :=
  { Set.hasMul, SetSemiring.addCommMonoid with zero_mul := fun s => empty_mul, mul_zero := fun s => mul_empty,
    left_distrib := fun _ _ _ => mul_union, right_distrib := fun _ _ _ => union_mul }

instance SetSemiring.nonAssocSemiring [MulOneClassₓ α] : NonAssocSemiringₓ (SetSemiring α) :=
  { SetSemiring.nonUnitalNonAssocSemiring, Set.mulOneClass with }

instance SetSemiring.nonUnitalSemiring [Semigroupₓ α] : NonUnitalSemiringₓ (SetSemiring α) :=
  { SetSemiring.nonUnitalNonAssocSemiring, Set.semigroup with }

instance SetSemiring.semiring [Monoidₓ α] : Semiringₓ (SetSemiring α) :=
  { SetSemiring.nonAssocSemiring, SetSemiring.nonUnitalSemiring with }

instance SetSemiring.commSemiring [CommMonoidₓ α] : CommSemiringₓ (SetSemiring α) :=
  { Set.commMonoid, SetSemiring.semiring with }

/-- A multiplicative action of a monoid on a type β gives also a
 multiplicative action on the subsets of β. -/
@[to_additive
      "An additive action of an additive monoid on a type β gives also an additive action\non the subsets of β."]
protected def mulActionSet [Monoidₓ α] [MulAction α β] : MulAction α (Set β) :=
  { Set.hasScalarSet with
    mul_smul := by
      intros
      simp only [← image_smul, image_image, ← mul_smul],
    one_smul := by
      intros
      simp only [← image_smul, image_eta, one_smul, image_id'] }

localized [Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet

section MulHom

variable [Mul α] [Mul β] (m : MulHom α β) {s t : Set α}

@[to_additive]
theorem image_mul : m '' (s * t) = m '' s * m '' t := by
  simp only [← image2_mul, image_image2, image2_image_left, image2_image_right, m.map_mul]

@[to_additive]
theorem preimage_mul_preimage_subset {s t : Set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, _, ‹_›, ‹_›, (m.map_mul _ _).symm⟩

instance SetSemiring.no_zero_divisors : NoZeroDivisors (SetSemiring α) :=
  ⟨fun a b ab =>
    a.eq_empty_or_nonempty.imp_right fun ha =>
      b.eq_empty_or_nonempty.resolve_right fun hb => Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩

/- Since addition on `set_semiring` is commutative (it is set union), there is no need
to also have the instance `covariant_class (set_semiring α) (set_semiring α) (swap (+)) (≤)`. -/
instance SetSemiring.covariant_class_add : CovariantClass (SetSemiring α) (SetSemiring α) (· + ·) (· ≤ ·) where
  elim := fun a b c => union_subset_union_right _

instance SetSemiring.covariant_class_mul_left : CovariantClass (SetSemiring α) (SetSemiring α) (· * ·) (· ≤ ·) where
  elim := fun a b c => mul_subset_mul_left

instance SetSemiring.covariant_class_mul_right :
    CovariantClass (SetSemiring α) (SetSemiring α) (swap (· * ·)) (· ≤ ·) where
  elim := fun a b c => mul_subset_mul_right

end MulHom

/-- The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets. -/
def imageHom [Monoidₓ α] [Monoidₓ β] (f : α →* β) : SetSemiring α →+* SetSemiring β where
  toFun := Image f
  map_zero' := image_empty _
  map_one' := by
    simp only [← singleton_one, image_singleton, f.map_one]
  map_add' := image_union _
  map_mul' := fun _ _ => image_mul f.toMulHom

end Monoidₓ

section CommMonoidₓ

variable [CommMonoidₓ α]

instance : CanonicallyOrderedCommSemiring (SetSemiring α) :=
  { (inferInstance : CommSemiringₓ (SetSemiring α)), (inferInstance : PartialOrderₓ (SetSemiring α)),
    (inferInstance : OrderBot (SetSemiring α)), (inferInstance : NoZeroDivisors (SetSemiring α)) with
    add_le_add_left := fun a b => add_le_add_left,
    le_iff_exists_add := fun a b =>
      ⟨fun ab => ⟨b, (union_eq_right_iff_subset.2 ab).symm⟩, by
        rintro ⟨c, rfl⟩
        exact subset_union_left _ _⟩ }

end CommMonoidₓ

end Set

open Set

open_locale Pointwise

section

section SmulWithZero

variable [Zero α] [Zero β] [SmulWithZero α β]

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
theorem zero_smul_set {s : Set β} (h : s.Nonempty) : (0 : α) • s = (0 : Set β) := by
  simp only [← image_smul, image_eta, zero_smul, h.image_const, singleton_zero]

theorem zero_smul_subset (s : Set β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ => zero_smul α x

theorem subsingleton_zero_smul_set (s : Set β) : ((0 : α) • s).Subsingleton :=
  subsingleton_singleton.mono (zero_smul_subset s)

theorem zero_mem_smul_set {t : Set β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
  ⟨0, h, smul_zero' _ _⟩

variable [NoZeroSmulDivisors α β] {s : Set α} {t : Set β} {a : α}

theorem zero_mem_smul_iff : (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.Nonempty ∨ (0 : β) ∈ t ∧ s.Nonempty := by
  constructor
  · rintro ⟨a, b, ha, hb, h⟩
    obtain rfl | rfl := eq_zero_or_eq_zero_of_smul_eq_zero h
    · exact Or.inl ⟨ha, b, hb⟩
      
    · exact Or.inr ⟨hb, a, ha⟩
      
    
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact ⟨0, b, hs, hb, zero_smul _ _⟩
      
    · exact ⟨a, 0, ha, ht, smul_zero' _ _⟩
      
    

theorem zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t := by
  refine' ⟨_, zero_mem_smul_set⟩
  rintro ⟨b, hb, h⟩
  rwa [(eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left ha] at hb

end SmulWithZero

theorem smul_add_set [Monoidₓ α] [AddMonoidₓ β] [DistribMulAction α β] (c : α) (s t : Set β) :
    c • (s + t) = c • s + c • t :=
  image_add (DistribMulAction.toAddMonoidHom β c).toAddHom

section Groupₓ

variable [Groupₓ α] [MulAction α β] {A B : Set β} {a : α} {x : β}

@[simp, to_additive]
theorem smul_mem_smul_set_iff : a • x ∈ a • A ↔ x ∈ A :=
  ⟨fun h => by
    rw [← inv_smul_smul a x, ← inv_smul_smul a A]
    exact smul_mem_smul_set h, smul_mem_smul_set⟩

@[to_additive]
theorem mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show x ∈ MulAction.toPerm a '' A ↔ _ from mem_image_equiv

@[to_additive]
theorem mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A := by
  simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

@[to_additive]
theorem preimage_smul (a : α) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  ((MulAction.toPerm a).symm.image_eq_preimage _).symm

@[to_additive]
theorem preimage_smul_inv (a : α) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (toUnits a)⁻¹ t

@[simp, to_additive]
theorem set_smul_subset_set_smul_iff : a • A ⊆ a • B ↔ A ⊆ B :=
  image_subset_image_iff <| MulAction.injective _

@[to_additive]
theorem set_smul_subset_iff : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  image_subset_iff.trans <| iff_of_eq <| congr_argₓ _ <| preimage_equiv_eq_image_symm _ <| MulAction.toPerm _

@[to_additive]
theorem subset_set_smul_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  Iff.symm <|
    image_subset_iff.trans <|
      Iff.symm <| iff_of_eq <| congr_argₓ _ <| image_equiv_eq_preimage_symm _ <| MulAction.toPerm _

end Groupₓ

section GroupWithZeroₓ

variable [GroupWithZeroₓ α] [MulAction α β] {s : Set α} {a : α}

@[simp]
theorem smul_mem_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : a • x ∈ a • A ↔ x ∈ A :=
  show Units.mk0 a ha • _ ∈ _ ↔ _ from smul_mem_smul_set_iff

theorem mem_smul_set_iff_inv_smul_mem₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show _ ∈ Units.mk0 a ha • _ ↔ _ from mem_smul_set_iff_inv_smul_mem

theorem mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
  show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_set_iff

theorem preimage_smul₀ (ha : a ≠ 0) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  preimage_smul (Units.mk0 a ha) t

theorem preimage_smul_inv₀ (ha : a ≠ 0) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (Units.mk0 a ha)⁻¹ t

@[simp]
theorem set_smul_subset_set_smul_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ a • B ↔ A ⊆ B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_set_smul_iff

theorem set_smul_subset_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_iff

theorem subset_set_smul_iff₀ (ha : a ≠ 0) {A B : Set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_set_smul_iff

theorem smul_univ₀ (hs : ¬s ⊆ 0) : s • (Univ : Set β) = univ :=
  let ⟨a, ha, ha₀⟩ := not_subset.1 hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ • b, ha, trivialₓ, smul_inv_smul₀ ha₀ _⟩

theorem smul_set_univ₀ (ha : a ≠ 0) : a • (Univ : Set β) = univ :=
  eq_univ_of_forall fun b => ⟨a⁻¹ • b, trivialₓ, smul_inv_smul₀ ha _⟩

end GroupWithZeroₓ

end

namespace Finset

variable {a : α} {s s₁ s₂ t t₁ t₂ : Finset α}

/-- The finset `(1 : finset α)` is defined as `{1}` in locale `pointwise`. -/
@[to_additive "The finset `(0 : finset α)` is defined as `{0}` in locale `pointwise`. "]
protected def hasOne [One α] : One (Finset α) :=
  ⟨{1}⟩

localized [Pointwise] attribute [instance] Finset.hasOne Finset.hasZero

@[simp, to_additive]
theorem mem_one [One α] : a ∈ (1 : Finset α) ↔ a = 1 := by
  simp [One.one]

@[simp, to_additive]
theorem one_subset [One α] : (1 : Finset α) ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff

section DecidableEq

variable [DecidableEq α]

/-- The pointwise product of two finite sets `s` and `t`:
`st = s ⬝ t = s * t = { x * y | x ∈ s, y ∈ t }`. -/
@[to_additive "The pointwise sum of two finite sets `s` and `t`:\n`s + t = { x + y | x ∈ s, y ∈ t }`. "]
protected def hasMul [Mul α] : Mul (Finset α) :=
  ⟨fun s t => (s.product t).Image fun p : α × α => p.1 * p.2⟩

localized [Pointwise] attribute [instance] Finset.hasMul Finset.hasAdd

section Mul

variable [Mul α]

@[to_additive]
theorem mul_def : s * t = (s.product t).Image fun p : α × α => p.1 * p.2 :=
  rfl

@[to_additive]
theorem mem_mul {x : α} : x ∈ s * t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x := by
  simp only [Finset.mul_def, And.assoc, mem_image, exists_prop, Prod.exists, mem_product]

@[simp, norm_cast, to_additive]
theorem coe_mul : (↑(s * t) : Set α) = ↑s * ↑t := by
  ext
  simp only [mem_mul, Set.mem_mul, mem_coe]

@[to_additive]
theorem mul_mem_mul {x y : α} (hx : x ∈ s) (hy : y ∈ t) : x * y ∈ s * t := by
  simp only [Finset.mem_mul]
  exact ⟨x, y, hx, hy, rfl⟩

@[to_additive]
theorem mul_card_le : (s * t).card ≤ s.card * t.card := by
  convert Finset.card_image_le
  rw [Finset.card_product, mul_comm]

@[simp, to_additive]
theorem empty_mul (s : Finset α) : ∅ * s = ∅ :=
  eq_empty_of_forall_not_mem
    (by
      simp [mem_mul])

@[simp, to_additive]
theorem mul_empty (s : Finset α) : s * ∅ = ∅ :=
  eq_empty_of_forall_not_mem
    (by
      simp [mem_mul])

@[simp, to_additive]
theorem mul_nonempty_iff (s t : Finset α) : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  simp [Finset.mul_def]

@[to_additive, mono]
theorem mul_subset_mul (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ * t₁ ⊆ s₂ * t₂ :=
  image_subset_image (product_subset_product hs ht)

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

end Mul

section MulZeroClassₓ

variable [MulZeroClassₓ α]

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

theorem singleton_zero_mul (s : Finset α) : {(0 : α)} * s ⊆ {0} := by
  simp [subset_iff, mem_mul]

end MulZeroClassₓ

end DecidableEq

open_locale Pointwise

variable {u : Finset α} {b : α} {x y : β}

@[to_additive]
theorem singleton_one [One α] : ({1} : Finset α) = 1 :=
  rfl

@[to_additive]
theorem one_mem_one [One α] : (1 : α) ∈ (1 : Finset α) := by
  simp [One.one]

@[to_additive]
theorem one_nonempty [One α] : (1 : Finset α).Nonempty :=
  ⟨1, one_mem_one⟩

@[simp, to_additive]
theorem image_one [DecidableEq β] [One α] {f : α → β} : image f 1 = {f 1} :=
  image_singleton f 1

@[to_additive add_image_prod]
theorem image_mul_prod [DecidableEq α] [Mul α] : image (fun x : α × α => x.fst * x.snd) (s.product t) = s * t :=
  rfl

@[simp, to_additive]
theorem image_mul_left [DecidableEq α] [Groupₓ α] :
    image (fun b => a * b) t = preimage t (fun b => a⁻¹ * b) fun x hx y hy => (mul_right_injₓ a⁻¹).mp :=
  coe_injective <| by
    simp

@[simp, to_additive]
theorem image_mul_right [DecidableEq α] [Groupₓ α] :
    image (· * b) t = preimage t (· * b⁻¹) fun x hx y hy => (mul_left_injₓ b⁻¹).mp :=
  coe_injective <| by
    simp

@[to_additive]
theorem image_mul_left' [DecidableEq α] [Groupₓ α] :
    image (fun b => a⁻¹ * b) t = preimage t (fun b => a * b) fun x hx y hy => (mul_right_injₓ a).mp := by
  simp

@[to_additive]
theorem image_mul_right' [DecidableEq α] [Groupₓ α] :
    image (· * b⁻¹) t = preimage t (· * b) fun x hx y hy => (mul_left_injₓ b).mp := by
  simp

@[simp, to_additive]
theorem preimage_mul_left_singleton [Groupₓ α] :
    (preimage {b} ((· * ·) a) fun x hx y hy => (mul_right_injₓ a).mp) = {a⁻¹ * b} := by
  classical
  rw [← image_mul_left', image_singleton]

@[simp, to_additive]
theorem preimage_mul_right_singleton [Groupₓ α] :
    (preimage {b} (· * a) fun x hx y hy => (mul_left_injₓ a).mp) = {b * a⁻¹} := by
  classical
  rw [← image_mul_right', image_singleton]

@[simp, to_additive]
theorem preimage_mul_left_one [Groupₓ α] :
    (preimage 1 (fun b => a * b) fun x hx y hy => (mul_right_injₓ a).mp) = {a⁻¹} := by
  classical
  rw [← image_mul_left', image_one, mul_oneₓ]

@[simp, to_additive]
theorem preimage_mul_right_one [Groupₓ α] : (preimage 1 (· * b) fun x hx y hy => (mul_left_injₓ b).mp) = {b⁻¹} := by
  classical
  rw [← image_mul_right', image_one, one_mulₓ]

@[to_additive]
theorem preimage_mul_left_one' [Groupₓ α] :
    (preimage 1 (fun b => a⁻¹ * b) fun x hx y hy => (mul_right_injₓ _).mp) = {a} := by
  simp

@[to_additive]
theorem preimage_mul_right_one' [Groupₓ α] : (preimage 1 (· * b⁻¹) fun x hx y hy => (mul_left_injₓ _).mp) = {b} := by
  simp

@[to_additive]
protected theorem mul_comm [DecidableEq α] [CommSemigroupₓ α] : s * t = t * s := by
  exact_mod_cast @Set.mul_comm _ (s : Set α) t _

/-- `finset α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mulOneClass [DecidableEq α] [MulOneClassₓ α] : MulOneClassₓ (Finset α) :=
  Function.Injective.mulOneClass _ coe_injective (coe_singleton 1)
    (by
      simp )

/-- `finset α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_semigroup` under pointwise operations if `α` is. "]
protected def semigroup [DecidableEq α] [Semigroupₓ α] : Semigroupₓ (Finset α) :=
  Function.Injective.semigroup _ coe_injective
    (by
      simp )

/-- `finset α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_monoid` under pointwise operations if `α` is. "]
protected def monoid [DecidableEq α] [Monoidₓ α] : Monoidₓ (Finset α) :=
  Function.Injective.monoid _ coe_injective (coe_singleton 1)
    (by
      simp )

/-- `finset α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_comm_monoid` under pointwise operations if `α` is. "]
protected def commMonoid [DecidableEq α] [CommMonoidₓ α] : CommMonoidₓ (Finset α) :=
  Function.Injective.commMonoid _ coe_injective (coe_singleton 1)
    (by
      simp )

localized [Pointwise]
  attribute [instance]
    Finset.mulOneClass Finset.addZeroClass Finset.semigroup Finset.addSemigroup Finset.monoid Finset.addMonoid Finset.commMonoid Finset.addCommMonoid

open_locale Classical

/-- A finite set `U` contained in the product of two sets `S * S'` is also contained in the product
of two finite sets `T * T' ⊆ S * S'`. -/
@[to_additive]
theorem subset_mul {M : Type _} [Monoidₓ M] {S : Set M} {S' : Set M} {U : Finset M} (f : ↑U ⊆ S * S') :
    ∃ T T' : Finset M, ↑T ⊆ S ∧ ↑T' ⊆ S' ∧ U ⊆ T * T' := by
  apply Finset.induction_on' U
  · use ∅, ∅
    simp only [Finset.empty_subset, Finset.coe_empty, Set.empty_subset, and_selfₓ]
    
  rintro a s haU hs has ⟨T, T', hS, hS', h⟩
  obtain ⟨x, y, hx, hy, ha⟩ := Set.mem_mul.1 (f haU)
  use insert x T, insert y T'
  simp only [Finset.coe_insert]
  repeat'
    rw [Set.insert_subset]
  use hx, hS, hy, hS'
  refine' finset.insert_subset.mpr ⟨_, _⟩
  · rw [Finset.mem_mul]
    use x, y
    simpa only [true_andₓ, true_orₓ, eq_self_iff_true, Finset.mem_insert]
    
  · suffices g : (s : Set M) ⊆ insert x T * insert y T'
    · norm_cast  at g
      assumption
      
    trans ↑(T * T')
    apply h
    rw [Finset.coe_mul]
    apply Set.mul_subset_mul (Set.subset_insert x T) (Set.subset_insert y T')
    

end Finset

/-! Some lemmas about pointwise multiplication and submonoids. Ideally we put these in
  `group_theory.submonoid.basic`, but currently we cannot because that file is imported by this. -/


namespace Submonoid

variable {M : Type _} [Monoidₓ M] {s t u : Set M}

@[to_additive]
theorem mul_subset {S : Submonoid M} (hs : s ⊆ S) (ht : t ⊆ S) : s * t ⊆ S := by
  rintro _ ⟨p, q, hp, hq, rfl⟩
  exact Submonoid.mul_mem _ (hs hp) (ht hq)

@[to_additive]
theorem mul_subset_closure (hs : s ⊆ u) (ht : t ⊆ u) : s * t ⊆ Submonoid.closure u :=
  mul_subset (Subset.trans hs Submonoid.subset_closure) (Subset.trans ht Submonoid.subset_closure)

@[to_additive]
theorem coe_mul_self_eq (s : Submonoid M) : (s : Set M) * s = s := by
  ext x
  refine' ⟨_, fun h => ⟨x, 1, h, s.one_mem, mul_oneₓ x⟩⟩
  rintro ⟨a, b, ha, hb, rfl⟩
  exact s.mul_mem ha hb

@[to_additive]
theorem closure_mul_le (S T : Set M) : closure (S * T) ≤ closure S⊔closure T :=
  Inf_le fun x ⟨s, t, hs, ht, hx⟩ =>
    hx ▸
      (closure S⊔closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
        (SetLike.le_def.mp le_sup_right <| subset_closure ht)

@[to_additive]
theorem sup_eq_closure (H K : Submonoid M) : H⊔K = closure (H * K) :=
  le_antisymmₓ
    (sup_le (fun h hh => subset_closure ⟨h, 1, hh, K.one_mem, mul_oneₓ h⟩) fun k hk =>
      subset_closure ⟨1, k, H.one_mem, hk, one_mulₓ k⟩)
    (by
      conv_rhs => rw [← closure_eq H, ← closure_eq K] <;> apply closure_mul_le)

theorem pow_smul_mem_closure_smul {N : Type _} [CommMonoidₓ N] [MulAction M N] [IsScalarTower M N N] (r : M) (s : Set N)
    {x : N} (hx : x ∈ closure s) : ∃ n : ℕ, r ^ n • x ∈ closure (r • s) := by
  apply @closure_induction N _ s (fun x : N => ∃ n : ℕ, r ^ n • x ∈ closure (r • s)) _ hx
  · intro x hx
    exact
      ⟨1,
        subset_closure
          ⟨_, hx, by
            rw [pow_oneₓ]⟩⟩
    
  · exact
      ⟨0, by
        simpa using one_mem _⟩
    
  · rintro x y ⟨nx, hx⟩ ⟨ny, hy⟩
    use nx + ny
    convert mul_mem _ hx hy
    rw [pow_addₓ, smul_mul_assoc, mul_smul, mul_comm, ← smul_mul_assoc, mul_comm]
    

end Submonoid

namespace Groupₓ

theorem card_pow_eq_card_pow_card_univ_aux {f : ℕ → ℕ} (h1 : Monotone f) {B : ℕ} (h2 : ∀ n, f n ≤ B)
    (h3 : ∀ n, f n = f (n + 1) → f (n + 1) = f (n + 2)) : ∀ k, B ≤ k → f k = f B := by
  have key : ∃ n : ℕ, n ≤ B ∧ f n = f (n + 1) := by
    contrapose! h2
    suffices ∀ n : ℕ, n ≤ B + 1 → n ≤ f n by
      exact ⟨B + 1, this (B + 1) (le_reflₓ (B + 1))⟩
    exact fun n =>
      Nat.rec (fun h => Nat.zero_leₓ (f 0))
        (fun n ih h =>
          lt_of_le_of_ltₓ (ih (n.le_succ.trans h)) (lt_of_le_of_neₓ (h1 n.le_succ) (h2 n (nat.succ_le_succ_iff.mp h))))
        n
  · obtain ⟨n, hn1, hn2⟩ := key
    replace key : ∀ k : ℕ, f (n + k) = f (n + k + 1) ∧ f (n + k) = f n := fun k =>
      Nat.rec ⟨hn2, rfl⟩ (fun k ih => ⟨h3 _ ih.1, ih.1.symm.trans ih.2⟩) k
    replace key : ∀ k : ℕ, n ≤ k → f k = f n := fun k hk =>
      (congr_argₓ f (add_tsub_cancel_of_le hk)).symm.trans (key (k - n)).2
    exact fun k hk => (key k (hn1.trans hk)).trans (key B hn1).symm
    

variable {G : Type _} [Groupₓ G] [Fintype G] (S : Set G)

@[to_additive]
theorem card_pow_eq_card_pow_card_univ [∀ k : ℕ, DecidablePred (· ∈ S ^ k)] :
    ∀ k, Fintype.card G ≤ k → Fintype.card ↥(S ^ k) = Fintype.card ↥(S ^ Fintype.card G) := by
  have hG : 0 < Fintype.card G := fintype.card_pos_iff.mpr ⟨1⟩
  by_cases' hS : S = ∅
  · refine' fun k hk => Fintype.card_congr _
    rw [hS, empty_pow _ (ne_of_gtₓ (lt_of_lt_of_leₓ hG hk)), empty_pow _ (ne_of_gtₓ hG)]
    
  obtain ⟨a, ha⟩ := set.ne_empty_iff_nonempty.mp hS
  classical
  have key : ∀ a s t : Set G, (∀ b : G, b ∈ s → a * b ∈ t) → Fintype.card s ≤ Fintype.card t := by
    refine' fun a s t h => Fintype.card_le_of_injective (fun ⟨b, hb⟩ => ⟨a * b, h b hb⟩) _
    rintro ⟨b, hb⟩ ⟨c, hc⟩ hbc
    exact Subtype.ext (mul_left_cancelₓ (subtype.ext_iff.mp hbc))
  have mono : Monotone (fun n => Fintype.card ↥(S ^ n) : ℕ → ℕ) :=
    monotone_nat_of_le_succ fun n => key a _ _ fun b hb => Set.mul_mem_mul ha hb
  convert
    card_pow_eq_card_pow_card_univ_aux mono (fun n => set_fintype_card_le_univ (S ^ n)) fun n h =>
      le_antisymmₓ (mono (n + 1).le_succ) (key a⁻¹ _ _ _)
  · simp only [Finset.filter_congr_decidable, Fintype.card_of_finset]
    
  replace h : {a} * S ^ n = S ^ (n + 1)
  · refine' Set.eq_of_subset_of_card_le _ (le_transₓ (ge_of_eq h) _)
    · exact mul_subset_mul (set.singleton_subset_iff.mpr ha) Set.Subset.rfl
      
    · convert key a (S ^ n) ({a} * S ^ n) fun b hb => Set.mul_mem_mul (Set.mem_singleton a) hb
      
    
  rw [pow_succ'ₓ, ← h, mul_assoc, ← pow_succ'ₓ, h]
  rintro _ ⟨b, c, hb, hc, rfl⟩
  rwa [set.mem_singleton_iff.mp hb, inv_mul_cancel_leftₓ]

end Groupₓ

