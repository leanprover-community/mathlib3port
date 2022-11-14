/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import Mathbin.Data.Fin.Tuple.Basic
import Mathbin.Data.Set.Finite
import Mathbin.Algebra.Module.Basic

/-!
# Pointwise operations of sets

This file defines pointwise algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:
* `s * t`: Multiplication, set of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s + t`: Addition, set of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s⁻¹`: Inversion, set of all `x⁻¹` where `x ∈ s`.
* `-s`: Negation, set of all `-x` where `x ∈ s`.
* `s / t`: Division, set of all `x / y` where `x ∈ s` and `y ∈ t`.
* `s - t`: Subtraction, set of all `x - y` where `x ∈ s` and `y ∈ t`.
* `s • t`: Scalar multiplication, set of all `x • y` where `x ∈ s` and `y ∈ t`.
* `s +ᵥ t`: Scalar addition, set of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s -ᵥ t`: Scalar subtraction, set of all `x -ᵥ y` where `x ∈ s` and `y ∈ t`.
* `a • s`: Scaling, set of all `a • x` where `x ∈ s`.
* `a +ᵥ s`: Translation, set of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `set α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

### Definitions for Hahn series

* `set.add_antidiagonal s t a`, `set.mul_antidiagonal s t a`: Sets of pairs of elements of `s` and
  `t` that add/multiply to `a`.
* `finset.add_antidiagonal`, `finset.mul_antidiagonal`: Finset versions of the above when `s` and
  `t` are well-founded.

## Implementation notes

* The following expressions are considered in simp-normal form in a group:
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/


library_note "pointwise nat action"/--
Pointwise monoids (`set`, `finset`, `filter`) have derived pointwise actions of the form
`has_smul α β → has_smul α (set β)`. When `α` is `ℕ` or `ℤ`, this action conflicts with the
nat or int action coming from `set β` being a `monoid` or `div_inv_monoid`. For example,
`2 • {a, b}` can both be `{2 • a, 2 • b}` (pointwise action, pointwise repeated addition,
`set.has_smul_set`) and `{a + a, a + b, b + a, b + b}` (nat or int action, repeated pointwise
addition, `set.has_nsmul`).

Because the pointwise action can easily be spelled out in such cases, we give higher priority to the
nat and int actions.
-/


open Function

variable {F α β γ : Type _}

namespace Set

/-! ### `0`/`1` as sets -/


section One

variable [One α] {s : Set α} {a : α}

/-- The set `1 : set α` is defined as `{1}` in locale `pointwise`. -/
@[to_additive "The set `0 : set α` is defined as `{0}` in locale `pointwise`."]
protected def hasOne : One (Set α) :=
  ⟨{1}⟩
#align set.has_one Set.hasOne

localized [Pointwise] attribute [instance] Set.hasOne Set.hasZero

@[to_additive]
theorem singleton_one : ({1} : Set α) = 1 :=
  rfl
#align set.singleton_one Set.singleton_one

@[simp, to_additive]
theorem mem_one : a ∈ (1 : Set α) ↔ a = 1 :=
  Iff.rfl
#align set.mem_one Set.mem_one

@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Set α) :=
  Eq.refl _
#align set.one_mem_one Set.one_mem_one

@[simp, to_additive]
theorem one_subset : 1 ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff
#align set.one_subset Set.one_subset

@[to_additive]
theorem one_nonempty : (1 : Set α).Nonempty :=
  ⟨1, rfl⟩
#align set.one_nonempty Set.one_nonempty

@[simp, to_additive]
theorem image_one {f : α → β} : f '' 1 = {f 1} :=
  image_singleton
#align set.image_one Set.image_one

@[to_additive]
theorem subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 :=
  subset_singleton_iff_eq
#align set.subset_one_iff_eq Set.subset_one_iff_eq

@[to_additive]
theorem Nonempty.subset_one_iff (h : s.Nonempty) : s ⊆ 1 ↔ s = 1 :=
  h.subset_singleton_iff
#align set.nonempty.subset_one_iff Set.Nonempty.subset_one_iff

/-- The singleton operation as a `one_hom`. -/
@[to_additive "The singleton operation as a `zero_hom`."]
def singletonOneHom : OneHom α (Set α) :=
  ⟨singleton, singleton_one⟩
#align set.singleton_one_hom Set.singletonOneHom

@[simp, to_additive]
theorem coe_singleton_one_hom : (singletonOneHom : α → Set α) = singleton :=
  rfl
#align set.coe_singleton_one_hom Set.coe_singleton_one_hom

end One

/-! ### Set negation/inversion -/


section Inv

/-- The pointwise inversion of set `s⁻¹` is defined as `{x | x⁻¹ ∈ s}` in locale `pointwise`. It i
equal to `{x⁻¹ | x ∈ s}`, see `set.image_inv`. -/
@[to_additive
      "The pointwise negation of set `-s` is defined as `{x | -x ∈ s}` in locale\n`pointwise`. It is equal to `{-x | x ∈ s}`, see `set.image_neg`."]
protected def hasInv [Inv α] : Inv (Set α) :=
  ⟨preimage Inv.inv⟩
#align set.has_inv Set.hasInv

localized [Pointwise] attribute [instance] Set.hasInv Set.hasNeg

section Inv

variable {ι : Sort _} [Inv α] {s t : Set α} {a : α}

@[simp, to_additive]
theorem mem_inv : a ∈ s⁻¹ ↔ a⁻¹ ∈ s :=
  Iff.rfl
#align set.mem_inv Set.mem_inv

@[simp, to_additive]
theorem inv_preimage : Inv.inv ⁻¹' s = s⁻¹ :=
  rfl
#align set.inv_preimage Set.inv_preimage

@[simp, to_additive]
theorem inv_empty : (∅ : Set α)⁻¹ = ∅ :=
  rfl
#align set.inv_empty Set.inv_empty

@[simp, to_additive]
theorem inv_univ : (univ : Set α)⁻¹ = univ :=
  rfl
#align set.inv_univ Set.inv_univ

@[simp, to_additive]
theorem inter_inv : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ :=
  preimage_inter
#align set.inter_inv Set.inter_inv

@[simp, to_additive]
theorem union_inv : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ :=
  preimage_union
#align set.union_inv Set.union_inv

@[simp, to_additive]
theorem Inter_inv (s : ι → Set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ :=
  preimage_Inter
#align set.Inter_inv Set.Inter_inv

@[simp, to_additive]
theorem Union_inv (s : ι → Set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ :=
  preimage_Union
#align set.Union_inv Set.Union_inv

@[simp, to_additive]
theorem compl_inv : (sᶜ)⁻¹ = s⁻¹ᶜ :=
  preimage_compl
#align set.compl_inv Set.compl_inv

end Inv

section HasInvolutiveInv

variable [HasInvolutiveInv α] {s t : Set α} {a : α}

@[to_additive]
theorem inv_mem_inv : a⁻¹ ∈ s⁻¹ ↔ a ∈ s := by simp only [mem_inv, inv_inv]
#align set.inv_mem_inv Set.inv_mem_inv

@[simp, to_additive]
theorem nonempty_inv : s⁻¹.Nonempty ↔ s.Nonempty :=
  inv_involutive.Surjective.nonempty_preimage
#align set.nonempty_inv Set.nonempty_inv

@[to_additive]
theorem Nonempty.inv (h : s.Nonempty) : s⁻¹.Nonempty :=
  nonempty_inv.2 h
#align set.nonempty.inv Set.Nonempty.inv

@[to_additive]
theorem Finite.inv (hs : s.Finite) : s⁻¹.Finite :=
  hs.Preimage <| inv_injective.InjOn _
#align set.finite.inv Set.Finite.inv

@[simp, to_additive]
theorem image_inv : Inv.inv '' s = s⁻¹ :=
  congr_fun (image_eq_preimage_of_inverse inv_involutive.LeftInverse inv_involutive.RightInverse) _
#align set.image_inv Set.image_inv

@[simp, to_additive]
instance : HasInvolutiveInv (Set α) where
  inv := Inv.inv
  inv_inv s := by simp only [← inv_preimage, preimage_preimage, inv_inv, preimage_id']

@[simp, to_additive]
theorem inv_subset_inv : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t :=
  (Equiv.inv α).Surjective.preimage_subset_preimage_iff
#align set.inv_subset_inv Set.inv_subset_inv

@[to_additive]
theorem inv_subset : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ := by rw [← inv_subset_inv, inv_inv]
#align set.inv_subset Set.inv_subset

@[simp, to_additive]
theorem inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹} := by rw [← image_inv, image_singleton]
#align set.inv_singleton Set.inv_singleton

@[simp, to_additive]
theorem inv_insert (a : α) (s : Set α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ := by
  rw [insert_eq, union_inv, inv_singleton, insert_eq]
#align set.inv_insert Set.inv_insert

@[to_additive]
theorem inv_range {ι : Sort _} {f : ι → α} : (range f)⁻¹ = range fun i => (f i)⁻¹ := by
  rw [← image_inv]
  exact (range_comp _ _).symm
#align set.inv_range Set.inv_range

open MulOpposite

@[to_additive]
theorem image_op_inv : op '' s⁻¹ = (op '' s)⁻¹ := by simp_rw [← image_inv, Function.Semiconj.set_image op_inv s]
#align set.image_op_inv Set.image_op_inv

end HasInvolutiveInv

end Inv

open Pointwise

/-! ### Set addition/multiplication -/


section Mul

variable {ι : Sort _} {κ : ι → Sort _} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/-- The pointwise multiplication of sets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}` in
locale `pointwise`. -/
@[to_additive "The pointwise addition of sets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in\nlocale `pointwise`."]
protected def hasMul : Mul (Set α) :=
  ⟨image2 (· * ·)⟩
#align set.has_mul Set.hasMul

localized [Pointwise] attribute [instance] Set.hasMul Set.hasAdd

@[simp, to_additive]
theorem image2_mul : image2 Mul.mul s t = s * t :=
  rfl
#align set.image2_mul Set.image2_mul

@[to_additive]
theorem mem_mul : a ∈ s * t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x * y = a :=
  Iff.rfl
#align set.mem_mul Set.mem_mul

@[to_additive]
theorem mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t :=
  mem_image2_of_mem
#align set.mul_mem_mul Set.mul_mem_mul

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive add_image_prod]
theorem image_mul_prod : (fun x : α × α => x.fst * x.snd) '' s ×ˢ t = s * t :=
  image_prod _
#align set.image_mul_prod Set.image_mul_prod

@[simp, to_additive]
theorem empty_mul : ∅ * s = ∅ :=
  image2_empty_left
#align set.empty_mul Set.empty_mul

@[simp, to_additive]
theorem mul_empty : s * ∅ = ∅ :=
  image2_empty_right
#align set.mul_empty Set.mul_empty

@[simp, to_additive]
theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.mul_eq_empty Set.mul_eq_empty

@[simp, to_additive]
theorem mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.mul_nonempty Set.mul_nonempty

@[to_additive]
theorem Nonempty.mul : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
  nonempty.image2
#align set.nonempty.mul Set.Nonempty.mul

@[to_additive]
theorem Nonempty.of_mul_left : (s * t).Nonempty → s.Nonempty :=
  nonempty.of_image2_left
#align set.nonempty.of_mul_left Set.Nonempty.of_mul_left

@[to_additive]
theorem Nonempty.of_mul_right : (s * t).Nonempty → t.Nonempty :=
  nonempty.of_image2_right
#align set.nonempty.of_mul_right Set.Nonempty.of_mul_right

@[simp, to_additive]
theorem mul_singleton : s * {b} = (· * b) '' s :=
  image2_singleton_right
#align set.mul_singleton Set.mul_singleton

@[simp, to_additive]
theorem singleton_mul : {a} * t = (· * ·) a '' t :=
  image2_singleton_left
#align set.singleton_mul Set.singleton_mul

@[simp, to_additive]
theorem singleton_mul_singleton : ({a} : Set α) * {b} = {a * b} :=
  image2_singleton
#align set.singleton_mul_singleton Set.singleton_mul_singleton

@[to_additive, mono]
theorem mul_subset_mul : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ * s₂ ⊆ t₁ * t₂ :=
  image2_subset
#align set.mul_subset_mul Set.mul_subset_mul

@[to_additive]
theorem mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ :=
  image2_subset_left
#align set.mul_subset_mul_left Set.mul_subset_mul_left

@[to_additive]
theorem mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t :=
  image2_subset_right
#align set.mul_subset_mul_right Set.mul_subset_mul_right

@[to_additive]
theorem mul_subset_iff : s * t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x * y ∈ u :=
  image2_subset_iff
#align set.mul_subset_iff Set.mul_subset_iff

attribute [mono] add_subset_add

@[to_additive]
theorem union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t :=
  image2_union_left
#align set.union_mul Set.union_mul

@[to_additive]
theorem mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ :=
  image2_union_right
#align set.mul_union Set.mul_union

@[to_additive]
theorem inter_mul_subset : s₁ ∩ s₂ * t ⊆ s₁ * t ∩ (s₂ * t) :=
  image2_inter_subset_left
#align set.inter_mul_subset Set.inter_mul_subset

@[to_additive]
theorem mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
  image2_inter_subset_right
#align set.mul_inter_subset Set.mul_inter_subset

@[to_additive]
theorem Union_mul_left_image : (⋃ a ∈ s, (· * ·) a '' t) = s * t :=
  Union_image_left _
#align set.Union_mul_left_image Set.Union_mul_left_image

@[to_additive]
theorem Union_mul_right_image : (⋃ a ∈ t, (· * a) '' s) = s * t :=
  Union_image_right _
#align set.Union_mul_right_image Set.Union_mul_right_image

@[to_additive]
theorem Union_mul (s : ι → Set α) (t : Set α) : (⋃ i, s i) * t = ⋃ i, s i * t :=
  image2_Union_left _ _ _
#align set.Union_mul Set.Union_mul

@[to_additive]
theorem mul_Union (s : Set α) (t : ι → Set α) : (s * ⋃ i, t i) = ⋃ i, s * t i :=
  image2_Union_right _ _ _
#align set.mul_Union Set.mul_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem Union₂_mul (s : ∀ i, κ i → Set α) (t : Set α) : (⋃ (i) (j), s i j) * t = ⋃ (i) (j), s i j * t :=
  image2_Union₂_left _ _ _
#align set.Union₂_mul Set.Union₂_mul

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem mul_Union₂ (s : Set α) (t : ∀ i, κ i → Set α) : (s * ⋃ (i) (j), t i j) = ⋃ (i) (j), s * t i j :=
  image2_Union₂_right _ _ _
#align set.mul_Union₂ Set.mul_Union₂

@[to_additive]
theorem Inter_mul_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t :=
  image2_Inter_subset_left _ _ _
#align set.Inter_mul_subset Set.Inter_mul_subset

@[to_additive]
theorem mul_Inter_subset (s : Set α) (t : ι → Set α) : (s * ⋂ i, t i) ⊆ ⋂ i, s * t i :=
  image2_Inter_subset_right _ _ _
#align set.mul_Inter_subset Set.mul_Inter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem Inter₂_mul_subset (s : ∀ i, κ i → Set α) (t : Set α) : (⋂ (i) (j), s i j) * t ⊆ ⋂ (i) (j), s i j * t :=
  image2_Inter₂_subset_left _ _ _
#align set.Inter₂_mul_subset Set.Inter₂_mul_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem mul_Inter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) : (s * ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s * t i j :=
  image2_Inter₂_subset_right _ _ _
#align set.mul_Inter₂_subset Set.mul_Inter₂_subset

@[to_additive]
theorem Finite.mul : s.Finite → t.Finite → (s * t).Finite :=
  Finite.image2 _
#align set.finite.mul Set.Finite.mul

/-- Multiplication preserves finiteness. -/
@[to_additive "Addition preserves finiteness."]
def fintypeMul [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s * t : Set α) :=
  Set.fintypeImage2 _ _ _
#align set.fintype_mul Set.fintypeMul

/-- The singleton operation as a `mul_hom`. -/
@[to_additive "The singleton operation as an `add_hom`."]
def singletonMulHom : α →ₙ* Set α :=
  ⟨singleton, fun a b => singleton_mul_singleton.symm⟩
#align set.singleton_mul_hom Set.singletonMulHom

@[simp, to_additive]
theorem coe_singleton_mul_hom : (singletonMulHom : α → Set α) = singleton :=
  rfl
#align set.coe_singleton_mul_hom Set.coe_singleton_mul_hom

@[simp, to_additive]
theorem singleton_mul_hom_apply (a : α) : singletonMulHom a = {a} :=
  rfl
#align set.singleton_mul_hom_apply Set.singleton_mul_hom_apply

open MulOpposite

@[simp, to_additive]
theorem image_op_mul : op '' (s * t) = op '' t * op '' s :=
  image_image2_antidistrib op_mul
#align set.image_op_mul Set.image_op_mul

end Mul

/-! ### Set subtraction/division -/


section Div

variable {ι : Sort _} {κ : ι → Sort _} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/-- The pointwise division of sets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`pointwise`. -/
@[to_additive
      "The pointwise subtraction of sets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}` in\nlocale `pointwise`."]
protected def hasDiv : Div (Set α) :=
  ⟨image2 (· / ·)⟩
#align set.has_div Set.hasDiv

localized [Pointwise] attribute [instance] Set.hasDiv Set.hasSub

@[simp, to_additive]
theorem image2_div : image2 Div.div s t = s / t :=
  rfl
#align set.image2_div Set.image2_div

@[to_additive]
theorem mem_div : a ∈ s / t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x / y = a :=
  Iff.rfl
#align set.mem_div Set.mem_div

@[to_additive]
theorem div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t :=
  mem_image2_of_mem
#align set.div_mem_div Set.div_mem_div

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive add_image_prod]
theorem image_div_prod : (fun x : α × α => x.fst / x.snd) '' s ×ˢ t = s / t :=
  image_prod _
#align set.image_div_prod Set.image_div_prod

@[simp, to_additive]
theorem empty_div : ∅ / s = ∅ :=
  image2_empty_left
#align set.empty_div Set.empty_div

@[simp, to_additive]
theorem div_empty : s / ∅ = ∅ :=
  image2_empty_right
#align set.div_empty Set.div_empty

@[simp, to_additive]
theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.div_eq_empty Set.div_eq_empty

@[simp, to_additive]
theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.div_nonempty Set.div_nonempty

@[to_additive]
theorem Nonempty.div : s.Nonempty → t.Nonempty → (s / t).Nonempty :=
  nonempty.image2
#align set.nonempty.div Set.Nonempty.div

@[to_additive]
theorem Nonempty.of_div_left : (s / t).Nonempty → s.Nonempty :=
  nonempty.of_image2_left
#align set.nonempty.of_div_left Set.Nonempty.of_div_left

@[to_additive]
theorem Nonempty.of_div_right : (s / t).Nonempty → t.Nonempty :=
  nonempty.of_image2_right
#align set.nonempty.of_div_right Set.Nonempty.of_div_right

@[simp, to_additive]
theorem div_singleton : s / {b} = (· / b) '' s :=
  image2_singleton_right
#align set.div_singleton Set.div_singleton

@[simp, to_additive]
theorem singleton_div : {a} / t = (· / ·) a '' t :=
  image2_singleton_left
#align set.singleton_div Set.singleton_div

@[simp, to_additive]
theorem singleton_div_singleton : ({a} : Set α) / {b} = {a / b} :=
  image2_singleton
#align set.singleton_div_singleton Set.singleton_div_singleton

@[to_additive, mono]
theorem div_subset_div : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ / s₂ ⊆ t₁ / t₂ :=
  image2_subset
#align set.div_subset_div Set.div_subset_div

@[to_additive]
theorem div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ :=
  image2_subset_left
#align set.div_subset_div_left Set.div_subset_div_left

@[to_additive]
theorem div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t :=
  image2_subset_right
#align set.div_subset_div_right Set.div_subset_div_right

@[to_additive]
theorem div_subset_iff : s / t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x / y ∈ u :=
  image2_subset_iff
#align set.div_subset_iff Set.div_subset_iff

attribute [mono] sub_subset_sub

@[to_additive]
theorem union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t :=
  image2_union_left
#align set.union_div Set.union_div

@[to_additive]
theorem div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ :=
  image2_union_right
#align set.div_union Set.div_union

@[to_additive]
theorem inter_div_subset : s₁ ∩ s₂ / t ⊆ s₁ / t ∩ (s₂ / t) :=
  image2_inter_subset_left
#align set.inter_div_subset Set.inter_div_subset

@[to_additive]
theorem div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
  image2_inter_subset_right
#align set.div_inter_subset Set.div_inter_subset

@[to_additive]
theorem Union_div_left_image : (⋃ a ∈ s, (· / ·) a '' t) = s / t :=
  Union_image_left _
#align set.Union_div_left_image Set.Union_div_left_image

@[to_additive]
theorem Union_div_right_image : (⋃ a ∈ t, (· / a) '' s) = s / t :=
  Union_image_right _
#align set.Union_div_right_image Set.Union_div_right_image

@[to_additive]
theorem Union_div (s : ι → Set α) (t : Set α) : (⋃ i, s i) / t = ⋃ i, s i / t :=
  image2_Union_left _ _ _
#align set.Union_div Set.Union_div

@[to_additive]
theorem div_Union (s : Set α) (t : ι → Set α) : (s / ⋃ i, t i) = ⋃ i, s / t i :=
  image2_Union_right _ _ _
#align set.div_Union Set.div_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem Union₂_div (s : ∀ i, κ i → Set α) (t : Set α) : (⋃ (i) (j), s i j) / t = ⋃ (i) (j), s i j / t :=
  image2_Union₂_left _ _ _
#align set.Union₂_div Set.Union₂_div

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem div_Union₂ (s : Set α) (t : ∀ i, κ i → Set α) : (s / ⋃ (i) (j), t i j) = ⋃ (i) (j), s / t i j :=
  image2_Union₂_right _ _ _
#align set.div_Union₂ Set.div_Union₂

@[to_additive]
theorem Inter_div_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) / t ⊆ ⋂ i, s i / t :=
  image2_Inter_subset_left _ _ _
#align set.Inter_div_subset Set.Inter_div_subset

@[to_additive]
theorem div_Inter_subset (s : Set α) (t : ι → Set α) : (s / ⋂ i, t i) ⊆ ⋂ i, s / t i :=
  image2_Inter_subset_right _ _ _
#align set.div_Inter_subset Set.div_Inter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem Inter₂_div_subset (s : ∀ i, κ i → Set α) (t : Set α) : (⋂ (i) (j), s i j) / t ⊆ ⋂ (i) (j), s i j / t :=
  image2_Inter₂_subset_left _ _ _
#align set.Inter₂_div_subset Set.Inter₂_div_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem div_Inter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) : (s / ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s / t i j :=
  image2_Inter₂_subset_right _ _ _
#align set.div_Inter₂_subset Set.div_Inter₂_subset

end Div

open Pointwise

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `finset`. See
note [pointwise nat action].-/
protected def hasNsmul [Zero α] [Add α] : HasSmul ℕ (Set α) :=
  ⟨nsmulRec⟩
#align set.has_nsmul Set.hasNsmul

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`set`. See note [pointwise nat action]. -/
@[to_additive]
protected def hasNpow [One α] [Mul α] : Pow (Set α) ℕ :=
  ⟨fun s n => npowRec n s⟩
#align set.has_npow Set.hasNpow

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `set`. See note [pointwise nat action]. -/
protected def hasZsmul [Zero α] [Add α] [Neg α] : HasSmul ℤ (Set α) :=
  ⟨zsmulRec⟩
#align set.has_zsmul Set.hasZsmul

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `set`. See note [pointwise nat action]. -/
@[to_additive]
protected def hasZpow [One α] [Mul α] [Inv α] : Pow (Set α) ℤ :=
  ⟨fun s n => zpowRec n s⟩
#align set.has_zpow Set.hasZpow

localized [Pointwise] attribute [instance] Set.hasNsmul Set.hasNpow Set.hasZsmul Set.hasZpow

/-- `set α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_semigroup` under pointwise operations if `α` is."]
protected def semigroup [Semigroup α] : Semigroup (Set α) :=
  { Set.hasMul with mul_assoc := fun _ _ _ => image2_assoc mul_assoc }
#align set.semigroup Set.semigroup

/-- `set α` is a `comm_semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_semigroup` under pointwise operations if `α` is."]
protected def commSemigroup [CommSemigroup α] : CommSemigroup (Set α) :=
  { Set.semigroup with mul_comm := fun s t => image2_comm mul_comm }
#align set.comm_semigroup Set.commSemigroup

section MulOneClass

variable [MulOneClass α]

/-- `set α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mulOneClass : MulOneClass (Set α) :=
  { Set.hasOne, Set.hasMul with mul_one := fun s => by simp only [← singleton_one, mul_singleton, mul_one, image_id'],
    one_mul := fun s => by simp only [← singleton_one, singleton_mul, one_mul, image_id'] }
#align set.mul_one_class Set.mulOneClass

localized [Pointwise]
  attribute [instance]
    Set.mulOneClass Set.addZeroClass Set.semigroup Set.addSemigroup Set.commSemigroup Set.addCommSemigroup

@[to_additive]
theorem subset_mul_left (s : Set α) {t : Set α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun x hx => ⟨x, 1, hx, ht, mul_one _⟩
#align set.subset_mul_left Set.subset_mul_left

@[to_additive]
theorem subset_mul_right {s : Set α} (t : Set α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun x hx => ⟨1, x, hs, hx, one_mul _⟩
#align set.subset_mul_right Set.subset_mul_right

/-- The singleton operation as a `monoid_hom`. -/
@[to_additive "The singleton operation as an `add_monoid_hom`."]
def singletonMonoidHom : α →* Set α :=
  { singletonMulHom, singletonOneHom with }
#align set.singleton_monoid_hom Set.singletonMonoidHom

@[simp, to_additive]
theorem coe_singleton_monoid_hom : (singletonMonoidHom : α → Set α) = singleton :=
  rfl
#align set.coe_singleton_monoid_hom Set.coe_singleton_monoid_hom

@[simp, to_additive]
theorem singleton_monoid_hom_apply (a : α) : singletonMonoidHom a = {a} :=
  rfl
#align set.singleton_monoid_hom_apply Set.singleton_monoid_hom_apply

end MulOneClass

section Monoid

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

/-- `set α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_monoid` under pointwise operations if `α` is."]
protected def monoid : Monoid (Set α) :=
  { Set.semigroup, Set.mulOneClass, Set.hasNpow with }
#align set.monoid Set.monoid

localized [Pointwise] attribute [instance] Set.monoid Set.addMonoid

@[to_additive]
instance decidableMemMul [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidablePred (· ∈ s * t) := fun _ => decidable_of_iff _ mem_mul.symm
#align set.decidable_mem_mul Set.decidableMemMul

@[to_additive]
instance decidableMemPow [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)] (n : ℕ) : DecidablePred (· ∈ s ^ n) := by
  induction' n with n ih
  · simp_rw [pow_zero, mem_one]
    infer_instance
    
  · letI := ih
    rw [pow_succ]
    infer_instance
    
#align set.decidable_mem_pow Set.decidableMemPow

@[to_additive]
theorem pow_mem_pow (ha : a ∈ s) : ∀ n : ℕ, a ^ n ∈ s ^ n
  | 0 => by
    rw [pow_zero]
    exact one_mem_one
  | n + 1 => by
    rw [pow_succ]
    exact mul_mem_mul ha (pow_mem_pow _)
#align set.pow_mem_pow Set.pow_mem_pow

@[to_additive]
theorem pow_subset_pow (hst : s ⊆ t) : ∀ n : ℕ, s ^ n ⊆ t ^ n
  | 0 => by
    rw [pow_zero]
    exact subset.rfl
  | n + 1 => by
    rw [pow_succ]
    exact mul_subset_mul hst (pow_subset_pow _)
#align set.pow_subset_pow Set.pow_subset_pow

@[to_additive]
theorem pow_subset_pow_of_one_mem (hs : (1 : α) ∈ s) : m ≤ n → s ^ m ⊆ s ^ n := by
  refine' Nat.le_induction _ (fun n h ih => _) _
  · exact subset.rfl
    
  · rw [pow_succ]
    exact ih.trans (subset_mul_right _ hs)
    
#align set.pow_subset_pow_of_one_mem Set.pow_subset_pow_of_one_mem

@[to_additive]
theorem mem_prod_list_of_fn {a : α} {s : Fin n → Set α} :
    a ∈ (List.ofFn s).Prod ↔ ∃ f : ∀ i : Fin n, s i, (List.ofFn fun i => (f i : α)).Prod = a := by
  induction' n with n ih generalizing a
  · simp_rw [List.of_fn_zero, List.prod_nil, Fin.exists_fin_zero_pi, eq_comm, Set.mem_one]
    
  · simp_rw [List.of_fn_succ, List.prod_cons, Fin.exists_fin_succ_pi, Fin.cons_zero, Fin.cons_succ, mem_mul, @ih,
      exists_and_left, exists_exists_eq_and, SetCoe.exists, Subtype.coe_mk, exists_prop]
    
#align set.mem_prod_list_of_fn Set.mem_prod_list_of_fn

@[to_additive]
theorem mem_list_prod {l : List (Set α)} {a : α} :
    a ∈ l.Prod ↔
      ∃ l' : List (Σs : Set α, ↥s), List.prod (l'.map fun x => (Sigma.snd x : α)) = a ∧ l'.map Sigma.fst = l :=
  by
  induction' l using List.ofFnRec with n f
  simp_rw [List.exists_iff_exists_tuple, List.map_of_fn, List.of_fn_inj', and_left_comm, exists_and_left,
    exists_eq_left, heq_iff_eq, Function.comp, mem_prod_list_of_fn]
  constructor
  · rintro ⟨fi, rfl⟩
    exact ⟨fun i => ⟨_, fi i⟩, rfl, rfl⟩
    
  · rintro ⟨fi, rfl, rfl⟩
    exact ⟨fun i => _, rfl⟩
    
#align set.mem_list_prod Set.mem_list_prod

@[to_additive]
theorem mem_pow {a : α} {n : ℕ} : a ∈ s ^ n ↔ ∃ f : Fin n → s, (List.ofFn fun i => (f i : α)).Prod = a := by
  rw [← mem_prod_list_of_fn, List.of_fn_const, List.prod_repeat]
#align set.mem_pow Set.mem_pow

@[simp, to_additive]
theorem empty_pow {n : ℕ} (hn : n ≠ 0) : (∅ : Set α) ^ n = ∅ := by
  rw [← tsub_add_cancel_of_le (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn), pow_succ, empty_mul]
#align set.empty_pow Set.empty_pow

@[to_additive]
theorem mul_univ_of_one_mem (hs : (1 : α) ∈ s) : s * univ = univ :=
  eq_univ_iff_forall.2 fun a => mem_mul.2 ⟨_, _, hs, mem_univ _, one_mul _⟩
#align set.mul_univ_of_one_mem Set.mul_univ_of_one_mem

@[to_additive]
theorem univ_mul_of_one_mem (ht : (1 : α) ∈ t) : univ * t = univ :=
  eq_univ_iff_forall.2 fun a => mem_mul.2 ⟨_, _, mem_univ _, ht, mul_one _⟩
#align set.univ_mul_of_one_mem Set.univ_mul_of_one_mem

@[simp, to_additive]
theorem univ_mul_univ : (univ : Set α) * univ = univ :=
  mul_univ_of_one_mem <| mem_univ _
#align set.univ_mul_univ Set.univ_mul_univ

--TODO: `to_additive` trips up on the `1 : ℕ` used in the pattern-matching.
@[simp]
theorem nsmul_univ {α : Type _} [AddMonoid α] : ∀ {n : ℕ}, n ≠ 0 → n • (univ : Set α) = univ
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => one_nsmul _
  | n + 2 => fun _ => by rw [succ_nsmul, nsmul_univ n.succ_ne_zero, univ_add_univ]
#align set.nsmul_univ Set.nsmul_univ

@[simp, to_additive nsmul_univ]
theorem univ_pow : ∀ {n : ℕ}, n ≠ 0 → (univ : Set α) ^ n = univ
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => pow_one _
  | n + 2 => fun _ => by rw [pow_succ, univ_pow n.succ_ne_zero, univ_mul_univ]
#align set.univ_pow Set.univ_pow

@[to_additive]
protected theorem _root_.is_unit.set : IsUnit a → IsUnit ({a} : Set α) :=
  IsUnit.map (singletonMonoidHom : α →* Set α)
#align set._root_.is_unit.set set._root_.is_unit.set

end Monoid

/-- `set α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_monoid` under pointwise operations if `α` is."]
protected def commMonoid [CommMonoid α] : CommMonoid (Set α) :=
  { Set.monoid, Set.commSemigroup with }
#align set.comm_monoid Set.commMonoid

localized [Pointwise] attribute [instance] Set.commMonoid Set.addCommMonoid

open Pointwise

section DivisionMonoid

variable [DivisionMonoid α] {s t : Set α}

@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  refine' ⟨fun h => _, _⟩
  · have hst : (s * t).Nonempty := h.symm.subst one_nonempty
    obtain ⟨a, ha⟩ := hst.of_image2_left
    obtain ⟨b, hb⟩ := hst.of_image2_right
    have H : ∀ {a b}, a ∈ s → b ∈ t → a * b = (1 : α) := fun a b ha hb => h.subset <| mem_image2_of_mem ha hb
    refine' ⟨a, b, _, _, H ha hb⟩ <;> refine' eq_singleton_iff_unique_mem.2 ⟨‹_›, fun x hx => _⟩
    · exact (eq_inv_of_mul_eq_one_left <| H hx hb).trans (inv_eq_of_mul_eq_one_left <| H ha hb)
      
    · exact (eq_inv_of_mul_eq_one_right <| H ha hx).trans (inv_eq_of_mul_eq_one_right <| H ha hb)
      
    
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [singleton_mul_singleton, h, singleton_one]
    
#align set.mul_eq_one_iff Set.mul_eq_one_iff

/-- `set α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive SubtractionMonoid "`set α` is a subtraction monoid under pointwise operations if `α`\nis."]
protected def divisionMonoid : DivisionMonoid (Set α) :=
  { Set.monoid, Set.hasInvolutiveInv, Set.hasDiv, Set.hasZpow with
    mul_inv_rev := fun s t => by
      simp_rw [← image_inv]
      exact image_image2_antidistrib mul_inv_rev,
    inv_eq_of_mul := fun s t h => by
      obtain ⟨a, b, rfl, rfl, hab⟩ := Set.mul_eq_one_iff.1 h
      rw [inv_singleton, inv_eq_of_mul_eq_one_right hab],
    div_eq_mul_inv := fun s t => by
      rw [← image_id (s / t), ← image_inv]
      exact image_image2_distrib_right div_eq_mul_inv }
#align set.division_monoid Set.divisionMonoid

@[simp, to_additive]
theorem is_unit_iff : IsUnit s ↔ ∃ a, s = {a} ∧ IsUnit a := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Set.mul_eq_one_iff.1 u.mul_inv
    refine' ⟨a, ha, ⟨a, b, h, singleton_injective _⟩, rfl⟩
    rw [← singleton_mul_singleton, ← ha, ← hb]
    exact u.inv_mul
    
  · rintro ⟨a, rfl, ha⟩
    exact ha.set
    
#align set.is_unit_iff Set.is_unit_iff

end DivisionMonoid

/-- `set α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive SubtractionCommMonoid
      "`set α` is a commutative subtraction monoid under pointwise\noperations if `α` is."]
protected def divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (Set α) :=
  { Set.divisionMonoid, Set.commSemigroup with }
#align set.division_comm_monoid Set.divisionCommMonoid

/-- `set α` has distributive negation if `α` has. -/
protected def hasDistribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Set α) :=
  { Set.hasInvolutiveNeg with
    neg_mul := fun _ _ => by
      simp_rw [← image_neg]
      exact image2_image_left_comm neg_mul,
    mul_neg := fun _ _ => by
      simp_rw [← image_neg]
      exact image_image2_right_comm mul_neg }
#align set.has_distrib_neg Set.hasDistribNeg

localized [Pointwise]
  attribute [instance]
    Set.divisionMonoid Set.subtractionMonoid Set.divisionCommMonoid Set.subtractionCommMonoid Set.hasDistribNeg

section Distrib

variable [Distrib α] (s t u : Set α)

/-!
Note that `set α` is not a `distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.
-/


theorem mul_add_subset : s * (t + u) ⊆ s * t + s * u :=
  image2_distrib_subset_left mul_add
#align set.mul_add_subset Set.mul_add_subset

theorem add_mul_subset : (s + t) * u ⊆ s * u + t * u :=
  image2_distrib_subset_right add_mul
#align set.add_mul_subset Set.add_mul_subset

end Distrib

section MulZeroClass

variable [MulZeroClass α] {s t : Set α}

/-! Note that `set` is not a `mul_zero_class` because `0 * ∅ ≠ 0`. -/


theorem mul_zero_subset (s : Set α) : s * 0 ⊆ 0 := by simp [subset_def, mem_mul]
#align set.mul_zero_subset Set.mul_zero_subset

theorem zero_mul_subset (s : Set α) : 0 * s ⊆ 0 := by simp [subset_def, mem_mul]
#align set.zero_mul_subset Set.zero_mul_subset

theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
  s.mul_zero_subset.antisymm <| by simpa [mem_mul] using hs
#align set.nonempty.mul_zero Set.Nonempty.mul_zero

theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
  s.zero_mul_subset.antisymm <| by simpa [mem_mul] using hs
#align set.nonempty.zero_mul Set.Nonempty.zero_mul

end MulZeroClass

section Group

variable [Group α] {s t : Set α} {a b : α}

/-! Note that `set` is not a `group` because `s / s ≠ 1` in general. -/


@[simp, to_additive]
theorem one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬Disjoint s t := by
  simp [not_disjoint_iff_nonempty_inter, mem_div, div_eq_one, Set.Nonempty]
#align set.one_mem_div_iff Set.one_mem_div_iff

@[to_additive]
theorem not_one_mem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left
#align set.not_one_mem_div_iff Set.not_one_mem_div_iff

alias not_one_mem_div_iff ↔ _ _root_.disjoint.one_not_mem_div_set

attribute [to_additive] Disjoint.one_not_mem_div_set

@[to_additive]
theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s :=
  let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, a, ha, ha, div_self' _⟩
#align set.nonempty.one_mem_div Set.Nonempty.one_mem_div

@[to_additive]
theorem is_unit_singleton (a : α) : IsUnit ({a} : Set α) :=
  (Group.is_unit a).Set
#align set.is_unit_singleton Set.is_unit_singleton

@[simp, to_additive]
theorem is_unit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by simp only [is_unit_iff, Group.is_unit, and_true_iff]
#align set.is_unit_iff_singleton Set.is_unit_iff_singleton

@[simp, to_additive]
theorem image_mul_left : (· * ·) a '' t = (· * ·) a⁻¹ ⁻¹' t := by rw [image_eq_preimage_of_inverse] <;> intro c <;> simp
#align set.image_mul_left Set.image_mul_left

@[simp, to_additive]
theorem image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t := by rw [image_eq_preimage_of_inverse] <;> intro c <;> simp
#align set.image_mul_right Set.image_mul_right

@[to_additive]
theorem image_mul_left' : (fun b => a⁻¹ * b) '' t = (fun b => a * b) ⁻¹' t := by simp
#align set.image_mul_left' Set.image_mul_left'

@[to_additive]
theorem image_mul_right' : (· * b⁻¹) '' t = (· * b) ⁻¹' t := by simp
#align set.image_mul_right' Set.image_mul_right'

@[simp, to_additive]
theorem preimage_mul_left_singleton : (· * ·) a ⁻¹' {b} = {a⁻¹ * b} := by rw [← image_mul_left', image_singleton]
#align set.preimage_mul_left_singleton Set.preimage_mul_left_singleton

@[simp, to_additive]
theorem preimage_mul_right_singleton : (· * a) ⁻¹' {b} = {b * a⁻¹} := by rw [← image_mul_right', image_singleton]
#align set.preimage_mul_right_singleton Set.preimage_mul_right_singleton

@[simp, to_additive]
theorem preimage_mul_left_one : (· * ·) a ⁻¹' 1 = {a⁻¹} := by rw [← image_mul_left', image_one, mul_one]
#align set.preimage_mul_left_one Set.preimage_mul_left_one

@[simp, to_additive]
theorem preimage_mul_right_one : (· * b) ⁻¹' 1 = {b⁻¹} := by rw [← image_mul_right', image_one, one_mul]
#align set.preimage_mul_right_one Set.preimage_mul_right_one

@[to_additive]
theorem preimage_mul_left_one' : (fun b => a⁻¹ * b) ⁻¹' 1 = {a} := by simp
#align set.preimage_mul_left_one' Set.preimage_mul_left_one'

@[to_additive]
theorem preimage_mul_right_one' : (· * b⁻¹) ⁻¹' 1 = {b} := by simp
#align set.preimage_mul_right_one' Set.preimage_mul_right_one'

@[simp, to_additive]
theorem mul_univ (hs : s.Nonempty) : s * (univ : Set α) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ * b, ha, trivial, mul_inv_cancel_left _ _⟩
#align set.mul_univ Set.mul_univ

@[simp, to_additive]
theorem univ_mul (ht : t.Nonempty) : (univ : Set α) * t = univ :=
  let ⟨a, ha⟩ := ht
  eq_univ_of_forall fun b => ⟨b * a⁻¹, a, trivial, ha, inv_mul_cancel_right _ _⟩
#align set.univ_mul Set.univ_mul

end Group

section GroupWithZero

variable [GroupWithZero α] {s t : Set α}

theorem div_zero_subset (s : Set α) : s / 0 ⊆ 0 := by simp [subset_def, mem_div]
#align set.div_zero_subset Set.div_zero_subset

theorem zero_div_subset (s : Set α) : 0 / s ⊆ 0 := by simp [subset_def, mem_div]
#align set.zero_div_subset Set.zero_div_subset

theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
  s.div_zero_subset.antisymm <| by simpa [mem_div] using hs
#align set.nonempty.div_zero Set.Nonempty.div_zero

theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
  s.zero_div_subset.antisymm <| by simpa [mem_div] using hs
#align set.nonempty.zero_div Set.Nonempty.zero_div

end GroupWithZero

section Mul

variable [Mul α] [Mul β] [MulHomClass F α β] (m : F) {s t : Set α}

include α β

@[to_additive]
theorem image_mul : m '' (s * t) = m '' s * m '' t :=
  image_image2_distrib <| map_mul m
#align set.image_mul Set.image_mul

@[to_additive]
theorem preimage_mul_preimage_subset {s t : Set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, _, ‹_›, ‹_›, (map_mul m _ _).symm⟩
#align set.preimage_mul_preimage_subset Set.preimage_mul_preimage_subset

end Mul

section Group

variable [Group α] [DivisionMonoid β] [MonoidHomClass F α β] (m : F) {s t : Set α}

include α β

@[to_additive]
theorem image_div : m '' (s / t) = m '' s / m '' t :=
  image_image2_distrib <| map_div m
#align set.image_div Set.image_div

@[to_additive]
theorem preimage_div_preimage_subset {s t : Set β} : m ⁻¹' s / m ⁻¹' t ⊆ m ⁻¹' (s / t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, _, ‹_›, ‹_›, (map_div m _ _).symm⟩
#align set.preimage_div_preimage_subset Set.preimage_div_preimage_subset

end Group

@[to_additive]
theorem bdd_above_mul [OrderedCommMonoid α] {A B : Set α} : BddAbove A → BddAbove B → BddAbove (A * B) := by
  rintro ⟨bA, hbA⟩ ⟨bB, hbB⟩
  use bA * bB
  rintro x ⟨xa, xb, hxa, hxb, rfl⟩
  exact mul_le_mul' (hbA hxa) (hbB hxb)
#align set.bdd_above_mul Set.bdd_above_mul

open Pointwise

/-! ### Translation/scaling of sets -/


section Smul

/-- The dilation of set `x • s` is defined as `{x • y | y ∈ s}` in locale `pointwise`. -/
@[to_additive "The translation of set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in\nlocale `pointwise`."]
protected def hasSmulSet [HasSmul α β] : HasSmul α (Set β) :=
  ⟨fun a => image (HasSmul.smul a)⟩
#align set.has_smul_set Set.hasSmulSet

/-- The pointwise scalar multiplication of sets `s • t` is defined as `{x • y | x ∈ s, y ∈ t}` in
locale `pointwise`. -/
@[to_additive
      "The pointwise scalar addition of sets `s +ᵥ t` is defined as\n`{x +ᵥ y | x ∈ s, y ∈ t}` in locale `pointwise`."]
protected def hasSmul [HasSmul α β] : HasSmul (Set α) (Set β) :=
  ⟨image2 HasSmul.smul⟩
#align set.has_smul Set.hasSmul

localized [Pointwise] attribute [instance] Set.hasSmulSet Set.hasSmul

localized [Pointwise] attribute [instance] Set.hasVaddSet Set.hasVadd

section HasSmul

variable {ι : Sort _} {κ : ι → Sort _} [HasSmul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α} {b : β}

@[simp, to_additive]
theorem image2_smul : image2 HasSmul.smul s t = s • t :=
  rfl
#align set.image2_smul Set.image2_smul

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive add_image_prod]
theorem image_smul_prod : (fun x : α × β => x.fst • x.snd) '' s ×ˢ t = s • t :=
  image_prod _
#align set.image_smul_prod Set.image_smul_prod

@[to_additive]
theorem mem_smul : b ∈ s • t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x • y = b :=
  Iff.rfl
#align set.mem_smul Set.mem_smul

@[to_additive]
theorem smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t :=
  mem_image2_of_mem
#align set.smul_mem_smul Set.smul_mem_smul

@[simp, to_additive]
theorem empty_smul : (∅ : Set α) • t = ∅ :=
  image2_empty_left
#align set.empty_smul Set.empty_smul

@[simp, to_additive]
theorem smul_empty : s • (∅ : Set β) = ∅ :=
  image2_empty_right
#align set.smul_empty Set.smul_empty

@[simp, to_additive]
theorem smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.smul_eq_empty Set.smul_eq_empty

@[simp, to_additive]
theorem smul_nonempty : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.smul_nonempty Set.smul_nonempty

@[to_additive]
theorem Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty :=
  nonempty.image2
#align set.nonempty.smul Set.Nonempty.smul

@[to_additive]
theorem Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty :=
  nonempty.of_image2_left
#align set.nonempty.of_smul_left Set.Nonempty.of_smul_left

@[to_additive]
theorem Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty :=
  nonempty.of_image2_right
#align set.nonempty.of_smul_right Set.Nonempty.of_smul_right

@[simp, to_additive]
theorem smul_singleton : s • {b} = (· • b) '' s :=
  image2_singleton_right
#align set.smul_singleton Set.smul_singleton

@[simp, to_additive]
theorem singleton_smul : ({a} : Set α) • t = a • t :=
  image2_singleton_left
#align set.singleton_smul Set.singleton_smul

@[simp, to_additive]
theorem singleton_smul_singleton : ({a} : Set α) • ({b} : Set β) = {a • b} :=
  image2_singleton
#align set.singleton_smul_singleton Set.singleton_smul_singleton

@[to_additive, mono]
theorem smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ :=
  image2_subset
#align set.smul_subset_smul Set.smul_subset_smul

@[to_additive]
theorem smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ :=
  image2_subset_left
#align set.smul_subset_smul_left Set.smul_subset_smul_left

@[to_additive]
theorem smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t :=
  image2_subset_right
#align set.smul_subset_smul_right Set.smul_subset_smul_right

@[to_additive]
theorem smul_subset_iff : s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u :=
  image2_subset_iff
#align set.smul_subset_iff Set.smul_subset_iff

attribute [mono] vadd_subset_vadd

@[to_additive]
theorem union_smul : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t :=
  image2_union_left
#align set.union_smul Set.union_smul

@[to_additive]
theorem smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ :=
  image2_union_right
#align set.smul_union Set.smul_union

@[to_additive]
theorem inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
  image2_inter_subset_left
#align set.inter_smul_subset Set.inter_smul_subset

@[to_additive]
theorem smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
  image2_inter_subset_right
#align set.smul_inter_subset Set.smul_inter_subset

@[to_additive]
theorem Union_smul_left_image : (⋃ a ∈ s, a • t) = s • t :=
  Union_image_left _
#align set.Union_smul_left_image Set.Union_smul_left_image

@[to_additive]
theorem Union_smul_right_image : (⋃ a ∈ t, (· • a) '' s) = s • t :=
  Union_image_right _
#align set.Union_smul_right_image Set.Union_smul_right_image

@[to_additive]
theorem Union_smul (s : ι → Set α) (t : Set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
  image2_Union_left _ _ _
#align set.Union_smul Set.Union_smul

@[to_additive]
theorem smul_Union (s : Set α) (t : ι → Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i :=
  image2_Union_right _ _ _
#align set.smul_Union Set.smul_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem Union₂_smul (s : ∀ i, κ i → Set α) (t : Set β) : (⋃ (i) (j), s i j) • t = ⋃ (i) (j), s i j • t :=
  image2_Union₂_left _ _ _
#align set.Union₂_smul Set.Union₂_smul

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem smul_Union₂ (s : Set α) (t : ∀ i, κ i → Set β) : (s • ⋃ (i) (j), t i j) = ⋃ (i) (j), s • t i j :=
  image2_Union₂_right _ _ _
#align set.smul_Union₂ Set.smul_Union₂

@[to_additive]
theorem Inter_smul_subset (s : ι → Set α) (t : Set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
  image2_Inter_subset_left _ _ _
#align set.Inter_smul_subset Set.Inter_smul_subset

@[to_additive]
theorem smul_Inter_subset (s : Set α) (t : ι → Set β) : (s • ⋂ i, t i) ⊆ ⋂ i, s • t i :=
  image2_Inter_subset_right _ _ _
#align set.smul_Inter_subset Set.smul_Inter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem Inter₂_smul_subset (s : ∀ i, κ i → Set α) (t : Set β) : (⋂ (i) (j), s i j) • t ⊆ ⋂ (i) (j), s i j • t :=
  image2_Inter₂_subset_left _ _ _
#align set.Inter₂_smul_subset Set.Inter₂_smul_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem smul_Inter₂_subset (s : Set α) (t : ∀ i, κ i → Set β) : (s • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s • t i j :=
  image2_Inter₂_subset_right _ _ _
#align set.smul_Inter₂_subset Set.smul_Inter₂_subset

@[to_additive]
theorem Finite.smul : s.Finite → t.Finite → (s • t).Finite :=
  Finite.image2 _
#align set.finite.smul Set.Finite.smul

@[simp, to_additive]
theorem bUnion_smul_set (s : Set α) (t : Set β) : (⋃ a ∈ s, a • t) = s • t :=
  Union_image_left _
#align set.bUnion_smul_set Set.bUnion_smul_set

end HasSmul

section HasSmulSet

variable {ι : Sort _} {κ : ι → Sort _} [HasSmul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

@[simp, to_additive]
theorem image_smul : (fun x => a • x) '' t = a • t :=
  rfl
#align set.image_smul Set.image_smul

@[to_additive]
theorem mem_smul_set : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x :=
  Iff.rfl
#align set.mem_smul_set Set.mem_smul_set

@[to_additive]
theorem smul_mem_smul_set : b ∈ s → a • b ∈ a • s :=
  mem_image_of_mem _
#align set.smul_mem_smul_set Set.smul_mem_smul_set

@[simp, to_additive]
theorem smul_set_empty : a • (∅ : Set β) = ∅ :=
  image_empty _
#align set.smul_set_empty Set.smul_set_empty

@[simp, to_additive]
theorem smul_set_eq_empty : a • s = ∅ ↔ s = ∅ :=
  image_eq_empty
#align set.smul_set_eq_empty Set.smul_set_eq_empty

@[simp, to_additive]
theorem smul_set_nonempty : (a • s).Nonempty ↔ s.Nonempty :=
  nonempty_image_iff
#align set.smul_set_nonempty Set.smul_set_nonempty

@[simp, to_additive]
theorem smul_set_singleton : a • ({b} : Set β) = {a • b} :=
  image_singleton
#align set.smul_set_singleton Set.smul_set_singleton

@[to_additive]
theorem smul_set_mono : s ⊆ t → a • s ⊆ a • t :=
  image_subset _
#align set.smul_set_mono Set.smul_set_mono

@[to_additive]
theorem smul_set_subset_iff : a • s ⊆ t ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ t :=
  image_subset_iff
#align set.smul_set_subset_iff Set.smul_set_subset_iff

@[to_additive]
theorem smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ :=
  image_union _ _ _
#align set.smul_set_union Set.smul_set_union

@[to_additive]
theorem smul_set_inter_subset : a • (t₁ ∩ t₂) ⊆ a • t₁ ∩ a • t₂ :=
  image_inter_subset _ _ _
#align set.smul_set_inter_subset Set.smul_set_inter_subset

@[to_additive]
theorem smul_set_Union (a : α) (s : ι → Set β) : (a • ⋃ i, s i) = ⋃ i, a • s i :=
  image_Union
#align set.smul_set_Union Set.smul_set_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem smul_set_Union₂ (a : α) (s : ∀ i, κ i → Set β) : (a • ⋃ (i) (j), s i j) = ⋃ (i) (j), a • s i j :=
  image_Union₂ _ _
#align set.smul_set_Union₂ Set.smul_set_Union₂

@[to_additive]
theorem smul_set_Inter_subset (a : α) (t : ι → Set β) : (a • ⋂ i, t i) ⊆ ⋂ i, a • t i :=
  image_Inter_subset _ _
#align set.smul_set_Inter_subset Set.smul_set_Inter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem smul_set_Inter₂_subset (a : α) (t : ∀ i, κ i → Set β) : (a • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), a • t i j :=
  image_Inter₂_subset _ _
#align set.smul_set_Inter₂_subset Set.smul_set_Inter₂_subset

@[to_additive]
theorem Nonempty.smul_set : s.Nonempty → (a • s).Nonempty :=
  Nonempty.image _
#align set.nonempty.smul_set Set.Nonempty.smul_set

@[to_additive]
theorem Finite.smul_set : s.Finite → (a • s).Finite :=
  Finite.image _
#align set.finite.smul_set Set.Finite.smul_set

end HasSmulSet

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

@[simp, to_additive]
theorem bUnion_op_smul_set [Mul α] (s t : Set α) : (⋃ a ∈ t, MulOpposite.op a • s) = s * t :=
  Union_image_right _
#align set.bUnion_op_smul_set Set.bUnion_op_smul_set

@[to_additive]
theorem smul_set_inter [Group α] [MulAction α β] {s t : Set β} : a • (s ∩ t) = a • s ∩ a • t :=
  (image_inter <| MulAction.injective a).symm
#align set.smul_set_inter Set.smul_set_inter

theorem smul_set_inter₀ [GroupWithZero α] [MulAction α β] {s t : Set β} (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t :=
  show Units.mk0 a ha • _ = _ from smul_set_inter
#align set.smul_set_inter₀ Set.smul_set_inter₀

@[simp, to_additive]
theorem smul_set_univ [Group α] [MulAction α β] {a : α} : a • (univ : Set β) = univ :=
  eq_univ_of_forall fun b => ⟨a⁻¹ • b, trivial, smul_inv_smul _ _⟩
#align set.smul_set_univ Set.smul_set_univ

@[simp, to_additive]
theorem smul_univ [Group α] [MulAction α β] {s : Set α} (hs : s.Nonempty) : s • (univ : Set β) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul _ _⟩
#align set.smul_univ Set.smul_univ

@[to_additive]
theorem range_smul_range {ι κ : Type _} [HasSmul α β] (b : ι → α) (c : κ → β) :
    range b • range c = range fun p : ι × κ => b p.1 • c p.2 :=
  ext fun x =>
    ⟨fun hx =>
      let ⟨p, q, ⟨i, hi⟩, ⟨j, hj⟩, hpq⟩ := Set.mem_smul.1 hx
      ⟨(i, j), hpq ▸ hi ▸ hj ▸ rfl⟩,
      fun ⟨⟨i, j⟩, h⟩ => Set.mem_smul.2 ⟨b i, c j, ⟨i, rfl⟩, ⟨j, rfl⟩, h⟩⟩
#align set.range_smul_range Set.range_smul_range

@[to_additive]
theorem smul_set_range [HasSmul α β] {ι : Sort _} {f : ι → β} : a • range f = range fun i => a • f i :=
  (range_comp _ _).symm
#align set.smul_set_range Set.smul_set_range

@[to_additive]
instance smul_comm_class_set [HasSmul α γ] [HasSmul β γ] [SmulCommClass α β γ] : SmulCommClass α β (Set γ) :=
  ⟨fun _ _ => commute.set_image <| smul_comm _ _⟩
#align set.smul_comm_class_set Set.smul_comm_class_set

@[to_additive]
instance smul_comm_class_set' [HasSmul α γ] [HasSmul β γ] [SmulCommClass α β γ] : SmulCommClass α (Set β) (Set γ) :=
  ⟨fun _ _ _ => image_image2_distrib_right <| smul_comm _⟩
#align set.smul_comm_class_set' Set.smul_comm_class_set'

@[to_additive]
instance smul_comm_class_set'' [HasSmul α γ] [HasSmul β γ] [SmulCommClass α β γ] : SmulCommClass (Set α) β (Set γ) :=
  haveI := SmulCommClass.symm α β γ
  SmulCommClass.symm _ _ _
#align set.smul_comm_class_set'' Set.smul_comm_class_set''

@[to_additive]
instance smul_comm_class [HasSmul α γ] [HasSmul β γ] [SmulCommClass α β γ] : SmulCommClass (Set α) (Set β) (Set γ) :=
  ⟨fun _ _ _ => image2_left_comm smul_comm⟩
#align set.smul_comm_class Set.smul_comm_class

@[to_additive]
instance is_scalar_tower [HasSmul α β] [HasSmul α γ] [HasSmul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Set γ) where smul_assoc a b T := by simp only [← image_smul, image_image, smul_assoc]
#align set.is_scalar_tower Set.is_scalar_tower

@[to_additive]
instance is_scalar_tower' [HasSmul α β] [HasSmul α γ] [HasSmul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Set β) (Set γ) :=
  ⟨fun _ _ _ => image2_image_left_comm <| smul_assoc _⟩
#align set.is_scalar_tower' Set.is_scalar_tower'

@[to_additive]
instance is_scalar_tower'' [HasSmul α β] [HasSmul α γ] [HasSmul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Set α) (Set β) (Set γ) where smul_assoc T T' T'' := image2_assoc smul_assoc
#align set.is_scalar_tower'' Set.is_scalar_tower''

instance is_central_scalar [HasSmul α β] [HasSmul αᵐᵒᵖ β] [IsCentralScalar α β] : IsCentralScalar α (Set β) :=
  ⟨fun a S => (congr_arg fun f => f '' S) <| funext fun _ => op_smul_eq_smul _ _⟩
#align set.is_central_scalar Set.is_central_scalar

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of `set α`
on `set β`. -/
@[to_additive
      "An additive action of an additive monoid `α` on a type `β` gives an additive action\nof `set α` on `set β`"]
protected def mulAction [Monoid α] [MulAction α β] : MulAction (Set α) (Set β) where
  mul_smul _ _ _ := image2_assoc mul_smul
  one_smul s := image2_singleton_left.trans <| by simp_rw [one_smul, image_id']
#align set.mul_action Set.mulAction

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `set β`. -/
@[to_additive "An additive action of an additive monoid on a type `β` gives an additive action\non `set β`."]
protected def mulActionSet [Monoid α] [MulAction α β] : MulAction α (Set β) where
  mul_smul := by
    intros
    simp only [← image_smul, image_image, ← mul_smul]
  one_smul := by
    intros
    simp only [← image_smul, one_smul, image_id']
#align set.mul_action_set Set.mulActionSet

localized [Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet Set.mulAction Set.addAction

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `set β`. -/
protected def distribMulActionSet [Monoid α] [AddMonoid β] [DistribMulAction α β] : DistribMulAction α (Set β) where
  smul_add _ _ _ := image_image2_distrib <| smul_add _
  smul_zero _ := image_singleton.trans <| by rw [smul_zero, singleton_zero]
#align set.distrib_mul_action_set Set.distribMulActionSet

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `set β`. -/
protected def mulDistribMulActionSet [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Set β) where
  smul_mul _ _ _ := image_image2_distrib <| smul_mul' _
  smul_one _ := image_singleton.trans <| by rw [smul_one, singleton_one]
#align set.mul_distrib_mul_action_set Set.mulDistribMulActionSet

localized [Pointwise] attribute [instance] Set.distribMulActionSet Set.mulDistribMulActionSet

instance [Zero α] [Zero β] [HasSmul α β] [NoZeroSmulDivisors α β] : NoZeroSmulDivisors (Set α) (Set β) :=
  ⟨fun s t h => by
    by_contra' H
    have hst : (s • t).Nonempty := h.symm.subst zero_nonempty
    simp_rw [← hst.of_smul_left.subset_zero_iff, ← hst.of_smul_right.subset_zero_iff, not_subset, mem_zero] at H
    obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul hs ht).elim ha hb⟩

instance no_zero_smul_divisors_set [Zero α] [Zero β] [HasSmul α β] [NoZeroSmulDivisors α β] :
    NoZeroSmulDivisors α (Set β) :=
  ⟨fun a s h => by
    by_contra' H
    have hst : (a • s).Nonempty := h.symm.subst zero_nonempty
    simp_rw [← hst.of_image.subset_zero_iff, not_subset, mem_zero] at H
    obtain ⟨ha, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul_set ht).elim ha hb⟩
#align set.no_zero_smul_divisors_set Set.no_zero_smul_divisors_set

instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Set α) :=
  ⟨fun s t h => eq_zero_or_eq_zero_of_smul_eq_zero h⟩

end Smul

section Vsub

variable {ι : Sort _} {κ : ι → Sort _} [HasVsub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α} {b c : β}

include α

instance hasVsub : HasVsub (Set α) (Set β) :=
  ⟨image2 (· -ᵥ ·)⟩
#align set.has_vsub Set.hasVsub

@[simp]
theorem image2_vsub : (image2 HasVsub.vsub s t : Set α) = s -ᵥ t :=
  rfl
#align set.image2_vsub Set.image2_vsub

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem image_vsub_prod : (fun x : β × β => x.fst -ᵥ x.snd) '' s ×ˢ t = s -ᵥ t :=
  image_prod _
#align set.image_vsub_prod Set.image_vsub_prod

theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x -ᵥ y = a :=
  Iff.rfl
#align set.mem_vsub Set.mem_vsub

theorem vsub_mem_vsub (hb : b ∈ s) (hc : c ∈ t) : b -ᵥ c ∈ s -ᵥ t :=
  mem_image2_of_mem hb hc
#align set.vsub_mem_vsub Set.vsub_mem_vsub

@[simp]
theorem empty_vsub (t : Set β) : ∅ -ᵥ t = ∅ :=
  image2_empty_left
#align set.empty_vsub Set.empty_vsub

@[simp]
theorem vsub_empty (s : Set β) : s -ᵥ ∅ = ∅ :=
  image2_empty_right
#align set.vsub_empty Set.vsub_empty

@[simp]
theorem vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.vsub_eq_empty Set.vsub_eq_empty

@[simp]
theorem vsub_nonempty : (s -ᵥ t : Set α).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.vsub_nonempty Set.vsub_nonempty

theorem Nonempty.vsub : s.Nonempty → t.Nonempty → (s -ᵥ t : Set α).Nonempty :=
  nonempty.image2
#align set.nonempty.vsub Set.Nonempty.vsub

theorem Nonempty.of_vsub_left : (s -ᵥ t : Set α).Nonempty → s.Nonempty :=
  nonempty.of_image2_left
#align set.nonempty.of_vsub_left Set.Nonempty.of_vsub_left

theorem Nonempty.of_vsub_right : (s -ᵥ t : Set α).Nonempty → t.Nonempty :=
  nonempty.of_image2_right
#align set.nonempty.of_vsub_right Set.Nonempty.of_vsub_right

@[simp]
theorem vsub_singleton (s : Set β) (b : β) : s -ᵥ {b} = (· -ᵥ b) '' s :=
  image2_singleton_right
#align set.vsub_singleton Set.vsub_singleton

@[simp]
theorem singleton_vsub (t : Set β) (b : β) : {b} -ᵥ t = (· -ᵥ ·) b '' t :=
  image2_singleton_left
#align set.singleton_vsub Set.singleton_vsub

@[simp]
theorem singleton_vsub_singleton : ({b} : Set β) -ᵥ {c} = {b -ᵥ c} :=
  image2_singleton
#align set.singleton_vsub_singleton Set.singleton_vsub_singleton

@[mono]
theorem vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ :=
  image2_subset
#align set.vsub_subset_vsub Set.vsub_subset_vsub

theorem vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ :=
  image2_subset_left
#align set.vsub_subset_vsub_left Set.vsub_subset_vsub_left

theorem vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t :=
  image2_subset_right
#align set.vsub_subset_vsub_right Set.vsub_subset_vsub_right

theorem vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x -ᵥ y ∈ u :=
  image2_subset_iff
#align set.vsub_subset_iff Set.vsub_subset_iff

theorem vsub_self_mono (h : s ⊆ t) : s -ᵥ s ⊆ t -ᵥ t :=
  vsub_subset_vsub h h
#align set.vsub_self_mono Set.vsub_self_mono

theorem union_vsub : s₁ ∪ s₂ -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) :=
  image2_union_left
#align set.union_vsub Set.union_vsub

theorem vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) :=
  image2_union_right
#align set.vsub_union Set.vsub_union

theorem inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) :=
  image2_inter_subset_left
#align set.inter_vsub_subset Set.inter_vsub_subset

theorem vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) :=
  image2_inter_subset_right
#align set.vsub_inter_subset Set.vsub_inter_subset

theorem Union_vsub_left_image : (⋃ a ∈ s, (· -ᵥ ·) a '' t) = s -ᵥ t :=
  Union_image_left _
#align set.Union_vsub_left_image Set.Union_vsub_left_image

theorem Union_vsub_right_image : (⋃ a ∈ t, (· -ᵥ a) '' s) = s -ᵥ t :=
  Union_image_right _
#align set.Union_vsub_right_image Set.Union_vsub_right_image

theorem Union_vsub (s : ι → Set β) (t : Set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
  image2_Union_left _ _ _
#align set.Union_vsub Set.Union_vsub

theorem vsub_Union (s : Set β) (t : ι → Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i :=
  image2_Union_right _ _ _
#align set.vsub_Union Set.vsub_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Union₂_vsub (s : ∀ i, κ i → Set β) (t : Set β) : (⋃ (i) (j), s i j) -ᵥ t = ⋃ (i) (j), s i j -ᵥ t :=
  image2_Union₂_left _ _ _
#align set.Union₂_vsub Set.Union₂_vsub

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem vsub_Union₂ (s : Set β) (t : ∀ i, κ i → Set β) : (s -ᵥ ⋃ (i) (j), t i j) = ⋃ (i) (j), s -ᵥ t i j :=
  image2_Union₂_right _ _ _
#align set.vsub_Union₂ Set.vsub_Union₂

theorem Inter_vsub_subset (s : ι → Set β) (t : Set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
  image2_Inter_subset_left _ _ _
#align set.Inter_vsub_subset Set.Inter_vsub_subset

theorem vsub_Inter_subset (s : Set β) (t : ι → Set β) : (s -ᵥ ⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
  image2_Inter_subset_right _ _ _
#align set.vsub_Inter_subset Set.vsub_Inter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Inter₂_vsub_subset (s : ∀ i, κ i → Set β) (t : Set β) : (⋂ (i) (j), s i j) -ᵥ t ⊆ ⋂ (i) (j), s i j -ᵥ t :=
  image2_Inter₂_subset_left _ _ _
#align set.Inter₂_vsub_subset Set.Inter₂_vsub_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem vsub_Inter₂_subset (s : Set β) (t : ∀ i, κ i → Set β) : (s -ᵥ ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s -ᵥ t i j :=
  image2_Inter₂_subset_right _ _ _
#align set.vsub_Inter₂_subset Set.vsub_Inter₂_subset

theorem Finite.vsub (hs : s.Finite) (ht : t.Finite) : Set.Finite (s -ᵥ t) :=
  hs.image2 _ ht
#align set.finite.vsub Set.Finite.vsub

end Vsub

open Pointwise

section SmulWithZero

variable [Zero α] [Zero β] [SmulWithZero α β] {s : Set α} {t : Set β}

/-!
Note that we have neither `smul_with_zero α (set β)` nor `smul_with_zero (set α) (set β)`
because `0 * ∅ ≠ 0`.
-/


theorem smul_zero_subset (s : Set α) : s • (0 : Set β) ⊆ 0 := by simp [subset_def, mem_smul]
#align set.smul_zero_subset Set.smul_zero_subset

theorem zero_smul_subset (t : Set β) : (0 : Set α) • t ⊆ 0 := by simp [subset_def, mem_smul]
#align set.zero_smul_subset Set.zero_smul_subset

theorem Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Set β) = 0 :=
  s.smul_zero_subset.antisymm <| by simpa [mem_smul] using hs
#align set.nonempty.smul_zero Set.Nonempty.smul_zero

theorem Nonempty.zero_smul (ht : t.Nonempty) : (0 : Set α) • t = 0 :=
  t.zero_smul_subset.antisymm <| by simpa [mem_smul] using ht
#align set.nonempty.zero_smul Set.Nonempty.zero_smul

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
theorem zero_smul_set {s : Set β} (h : s.Nonempty) : (0 : α) • s = (0 : Set β) := by
  simp only [← image_smul, image_eta, zero_smul, h.image_const, singleton_zero]
#align set.zero_smul_set Set.zero_smul_set

theorem zero_smul_set_subset (s : Set β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ => zero_smul α x
#align set.zero_smul_set_subset Set.zero_smul_set_subset

theorem subsingleton_zero_smul_set (s : Set β) : ((0 : α) • s).Subsingleton :=
  subsingleton_singleton.anti <| zero_smul_set_subset s
#align set.subsingleton_zero_smul_set Set.subsingleton_zero_smul_set

theorem zero_mem_smul_set {t : Set β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
  ⟨0, h, smul_zero _⟩
#align set.zero_mem_smul_set Set.zero_mem_smul_set

variable [NoZeroSmulDivisors α β] {a : α}

theorem zero_mem_smul_iff : (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.Nonempty ∨ (0 : β) ∈ t ∧ s.Nonempty := by
  constructor
  · rintro ⟨a, b, ha, hb, h⟩
    obtain rfl | rfl := eq_zero_or_eq_zero_of_smul_eq_zero h
    · exact Or.inl ⟨ha, b, hb⟩
      
    · exact Or.inr ⟨hb, a, ha⟩
      
    
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact ⟨0, b, hs, hb, zero_smul _ _⟩
      
    · exact ⟨a, 0, ha, ht, smul_zero _⟩
      
    
#align set.zero_mem_smul_iff Set.zero_mem_smul_iff

theorem zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t := by
  refine' ⟨_, zero_mem_smul_set⟩
  rintro ⟨b, hb, h⟩
  rwa [(eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left ha] at hb
#align set.zero_mem_smul_set_iff Set.zero_mem_smul_set_iff

end SmulWithZero

section LeftCancelSemigroup

variable [LeftCancelSemigroup α] {s t : Set α}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem pairwise_disjoint_smul_iff : s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t).InjOn fun p => p.1 * p.2 :=
  pairwise_disjoint_image_right_iff fun _ _ => mul_right_injective _
#align set.pairwise_disjoint_smul_iff Set.pairwise_disjoint_smul_iff

end LeftCancelSemigroup

section Group

variable [Group α] [MulAction α β] {s t A B : Set β} {a : α} {x : β}

@[simp, to_additive]
theorem smul_mem_smul_set_iff : a • x ∈ a • s ↔ x ∈ s :=
  (MulAction.injective _).mem_set_image
#align set.smul_mem_smul_set_iff Set.smul_mem_smul_set_iff

@[to_additive]
theorem mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show x ∈ MulAction.toPerm a '' A ↔ _ from mem_image_equiv
#align set.mem_smul_set_iff_inv_smul_mem Set.mem_smul_set_iff_inv_smul_mem

@[to_additive]
theorem mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A := by
  simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]
#align set.mem_inv_smul_set_iff Set.mem_inv_smul_set_iff

@[to_additive]
theorem preimage_smul (a : α) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  ((MulAction.toPerm a).symm.image_eq_preimage _).symm
#align set.preimage_smul Set.preimage_smul

@[to_additive]
theorem preimage_smul_inv (a : α) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (toUnits a)⁻¹ t
#align set.preimage_smul_inv Set.preimage_smul_inv

@[simp, to_additive]
theorem set_smul_subset_set_smul_iff : a • A ⊆ a • B ↔ A ⊆ B :=
  image_subset_image_iff <| MulAction.injective _
#align set.set_smul_subset_set_smul_iff Set.set_smul_subset_set_smul_iff

@[to_additive]
theorem set_smul_subset_iff : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  image_subset_iff.trans <| iff_of_eq <| congr_arg _ <| preimage_equiv_eq_image_symm _ <| MulAction.toPerm _
#align set.set_smul_subset_iff Set.set_smul_subset_iff

@[to_additive]
theorem subset_set_smul_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  Iff.symm <|
    image_subset_iff.trans <|
      Iff.symm <| iff_of_eq <| congr_arg _ <| image_equiv_eq_preimage_symm _ <| MulAction.toPerm _
#align set.subset_set_smul_iff Set.subset_set_smul_iff

@[to_additive]
theorem smul_inter_ne_empty_iff {s t : Set α} {x : α} : x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x := by
  rw [ne_empty_iff_nonempty]
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨x • b, b, ⟨ha, hb⟩, by simp⟩
    
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, mem_inter (mem_smul_set.mpr ⟨b, hb, by simp⟩) ha⟩
    
#align set.smul_inter_ne_empty_iff Set.smul_inter_ne_empty_iff

@[to_additive]
theorem smul_inter_ne_empty_iff' {s t : Set α} {x : α} : x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a / b = x := by
  simp_rw [smul_inter_ne_empty_iff, div_eq_mul_inv]
#align set.smul_inter_ne_empty_iff' Set.smul_inter_ne_empty_iff'

@[to_additive]
theorem op_smul_inter_ne_empty_iff {s t : Set α} {x : αᵐᵒᵖ} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ s ∧ b ∈ t) ∧ a⁻¹ * b = MulOpposite.unop x := by
  rw [ne_empty_iff_nonempty]
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨b, x • b, ⟨hb, ha⟩, by simp⟩
    
  · rintro ⟨a, b, ⟨ha, hb⟩, H⟩
    have : MulOpposite.op (a⁻¹ * b) = x := congr_arg MulOpposite.op H
    exact ⟨b, mem_inter (mem_smul_set.mpr ⟨a, ha, by simp [← this]⟩) hb⟩
    
#align set.op_smul_inter_ne_empty_iff Set.op_smul_inter_ne_empty_iff

end Group

section GroupWithZero

variable [GroupWithZero α] [MulAction α β] {s : Set α} {a : α}

@[simp]
theorem smul_mem_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : a • x ∈ a • A ↔ x ∈ A :=
  show Units.mk0 a ha • _ ∈ _ ↔ _ from smul_mem_smul_set_iff
#align set.smul_mem_smul_set_iff₀ Set.smul_mem_smul_set_iff₀

theorem mem_smul_set_iff_inv_smul_mem₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show _ ∈ Units.mk0 a ha • _ ↔ _ from mem_smul_set_iff_inv_smul_mem
#align set.mem_smul_set_iff_inv_smul_mem₀ Set.mem_smul_set_iff_inv_smul_mem₀

theorem mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
  show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_set_iff
#align set.mem_inv_smul_set_iff₀ Set.mem_inv_smul_set_iff₀

theorem preimage_smul₀ (ha : a ≠ 0) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  preimage_smul (Units.mk0 a ha) t
#align set.preimage_smul₀ Set.preimage_smul₀

theorem preimage_smul_inv₀ (ha : a ≠ 0) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (Units.mk0 a ha)⁻¹ t
#align set.preimage_smul_inv₀ Set.preimage_smul_inv₀

@[simp]
theorem set_smul_subset_set_smul_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ a • B ↔ A ⊆ B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_set_smul_iff
#align set.set_smul_subset_set_smul_iff₀ Set.set_smul_subset_set_smul_iff₀

theorem set_smul_subset_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_iff
#align set.set_smul_subset_iff₀ Set.set_smul_subset_iff₀

theorem subset_set_smul_iff₀ (ha : a ≠ 0) {A B : Set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_set_smul_iff
#align set.subset_set_smul_iff₀ Set.subset_set_smul_iff₀

theorem smul_univ₀ (hs : ¬s ⊆ 0) : s • (univ : Set β) = univ :=
  let ⟨a, ha, ha₀⟩ := not_subset.1 hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul₀ ha₀ _⟩
#align set.smul_univ₀ Set.smul_univ₀

theorem smul_set_univ₀ (ha : a ≠ 0) : a • (univ : Set β) = univ :=
  eq_univ_of_forall fun b => ⟨a⁻¹ • b, trivial, smul_inv_smul₀ ha _⟩
#align set.smul_set_univ₀ Set.smul_set_univ₀

end GroupWithZero

section Monoid

variable [Monoid α] [AddGroup β] [DistribMulAction α β] (a : α) (s : Set α) (t : Set β)

@[simp]
theorem smul_set_neg : a • -t = -(a • t) := by simp_rw [← image_smul, ← image_neg, image_image, smul_neg]
#align set.smul_set_neg Set.smul_set_neg

@[simp]
protected theorem smul_neg : s • -t = -(s • t) := by
  simp_rw [← image_neg]
  exact image_image2_right_comm smul_neg
#align set.smul_neg Set.smul_neg

end Monoid

section Ring

variable [Ring α] [AddCommGroup β] [Module α β] (a : α) (s : Set α) (t : Set β)

@[simp]
theorem neg_smul_set : -a • t = -(a • t) := by simp_rw [← image_smul, ← image_neg, image_image, neg_smul]
#align set.neg_smul_set Set.neg_smul_set

@[simp]
protected theorem neg_smul : -s • t = -(s • t) := by
  simp_rw [← image_neg]
  exact image2_image_left_comm neg_smul
#align set.neg_smul Set.neg_smul

end Ring

end Set

/-! ### Miscellaneous -/


open Set

open Pointwise

namespace Group

theorem card_pow_eq_card_pow_card_univ_aux {f : ℕ → ℕ} (h1 : Monotone f) {B : ℕ} (h2 : ∀ n, f n ≤ B)
    (h3 : ∀ n, f n = f (n + 1) → f (n + 1) = f (n + 2)) : ∀ k, B ≤ k → f k = f B := by
  have key : ∃ n : ℕ, n ≤ B ∧ f n = f (n + 1) := by
    contrapose! h2
    suffices ∀ n : ℕ, n ≤ B + 1 → n ≤ f n by exact ⟨B + 1, this (B + 1) (le_refl (B + 1))⟩
    exact fun n =>
      Nat.rec (fun h => Nat.zero_le (f 0))
        (fun n ih h =>
          lt_of_le_of_lt (ih (n.le_succ.trans h)) (lt_of_le_of_ne (h1 n.le_succ) (h2 n (nat.succ_le_succ_iff.mp h))))
        n
  · obtain ⟨n, hn1, hn2⟩ := key
    replace key : ∀ k : ℕ, f (n + k) = f (n + k + 1) ∧ f (n + k) = f n := fun k =>
      Nat.rec ⟨hn2, rfl⟩ (fun k ih => ⟨h3 _ ih.1, ih.1.symm.trans ih.2⟩) k
    replace key : ∀ k : ℕ, n ≤ k → f k = f n := fun k hk =>
      (congr_arg f (add_tsub_cancel_of_le hk)).symm.trans (key (k - n)).2
    exact fun k hk => (key k (hn1.trans hk)).trans (key B hn1).symm
    
#align group.card_pow_eq_card_pow_card_univ_aux Group.card_pow_eq_card_pow_card_univ_aux

variable {G : Type _} [Group G] [Fintype G] (S : Set G)

@[to_additive]
theorem card_pow_eq_card_pow_card_univ [∀ k : ℕ, DecidablePred (· ∈ S ^ k)] :
    ∀ k, Fintype.card G ≤ k → Fintype.card ↥(S ^ k) = Fintype.card ↥(S ^ Fintype.card G) := by
  have hG : 0 < Fintype.card G := fintype.card_pos_iff.mpr ⟨1⟩
  by_cases hS:S = ∅
  · refine' fun k hk => Fintype.card_congr _
    rw [hS, empty_pow (ne_of_gt (lt_of_lt_of_le hG hk)), empty_pow (ne_of_gt hG)]
    
  obtain ⟨a, ha⟩ := set.ne_empty_iff_nonempty.mp hS
  classical!
  have key : ∀ (a) (s t : Set G), (∀ b : G, b ∈ s → a * b ∈ t) → Fintype.card s ≤ Fintype.card t := by
    refine' fun a s t h => Fintype.card_le_of_injective (fun ⟨b, hb⟩ => ⟨a * b, h b hb⟩) _
    rintro ⟨b, hb⟩ ⟨c, hc⟩ hbc
    exact Subtype.ext (mul_left_cancel (subtype.ext_iff.mp hbc))
  have mono : Monotone (fun n => Fintype.card ↥(S ^ n) : ℕ → ℕ) :=
    monotone_nat_of_le_succ fun n => key a _ _ fun b hb => Set.mul_mem_mul ha hb
  convert
    card_pow_eq_card_pow_card_univ_aux mono (fun n => set_fintype_card_le_univ (S ^ n)) fun n h =>
      le_antisymm (mono (n + 1).le_succ) (key a⁻¹ _ _ _)
  · simp only [Finset.filter_congr_decidable, Fintype.card_of_finset]
    
  replace h : {a} * S ^ n = S ^ (n + 1)
  · refine' Set.eq_of_subset_of_card_le _ (le_trans (ge_of_eq h) _)
    · exact mul_subset_mul (set.singleton_subset_iff.mpr ha) Set.Subset.rfl
      
    · convert key a (S ^ n) ({a} * S ^ n) fun b hb => Set.mul_mem_mul (Set.mem_singleton a) hb
      
    
  rw [pow_succ', ← h, mul_assoc, ← pow_succ', h]
  rintro _ ⟨b, c, hb, hc, rfl⟩
  rwa [set.mem_singleton_iff.mp hb, inv_mul_cancel_left]
#align group.card_pow_eq_card_pow_card_univ Group.card_pow_eq_card_pow_card_univ

end Group

