/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Algebra.Order.Archimedean
import Mathbin.Algebra.Order.Nonneg.Ring

/-!
# Semifield structure on the type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.

## Main declarations

* `{x : α // 0 ≤ x}` is a `canonically_linear_ordered_semifield` if `α` is a `linear_ordered_field`.
-/


open Set

variable {α : Type _}

namespace Nonneg

section LinearOrderedSemifield

variable [LinearOrderedSemifield α] {x y : α}

instance hasInv : Inv { x : α // 0 ≤ x } :=
  ⟨fun x => ⟨x⁻¹, inv_nonneg.2 x.2⟩⟩

@[simp, norm_cast]
protected theorem coe_inv (a : { x : α // 0 ≤ x }) : ((a⁻¹ : { x : α // 0 ≤ x }) : α) = a⁻¹ :=
  rfl

@[simp]
theorem inv_mk (hx : 0 ≤ x) : (⟨x, hx⟩ : { x : α // 0 ≤ x })⁻¹ = ⟨x⁻¹, inv_nonneg.2 hx⟩ :=
  rfl

instance hasDiv : Div { x : α // 0 ≤ x } :=
  ⟨fun x y => ⟨x / y, div_nonneg x.2 y.2⟩⟩

@[simp, norm_cast]
protected theorem coe_div (a b : { x : α // 0 ≤ x }) : ((a / b : { x : α // 0 ≤ x }) : α) = a / b :=
  rfl

@[simp]
theorem mk_div_mk (hx : 0 ≤ x) (hy : 0 ≤ y) : (⟨x, hx⟩ : { x : α // 0 ≤ x }) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ :=
  rfl

instance hasZpow : Pow { x : α // 0 ≤ x } ℤ :=
  ⟨fun a n => ⟨a ^ n, zpow_nonneg a.2 _⟩⟩

@[simp, norm_cast]
protected theorem coe_zpow (a : { x : α // 0 ≤ x }) (n : ℤ) : ((a ^ n : { x : α // 0 ≤ x }) : α) = a ^ n :=
  rfl

@[simp]
theorem mk_zpow (hx : 0 ≤ x) (n : ℤ) : (⟨x, hx⟩ : { x : α // 0 ≤ x }) ^ n = ⟨x ^ n, zpow_nonneg hx n⟩ :=
  rfl

instance linearOrderedSemifield : LinearOrderedSemifield { x : α // 0 ≤ x } :=
  Subtype.coe_injective.LinearOrderedSemifield _ Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add Nonneg.coe_mul
    Nonneg.coe_inv Nonneg.coe_div (fun _ _ => rfl) Nonneg.coe_pow Nonneg.coe_zpow Nonneg.coe_nat_cast (fun _ _ => rfl)
    fun _ _ => rfl

end LinearOrderedSemifield

instance canonicallyLinearOrderedSemifield [LinearOrderedField α] :
    CanonicallyLinearOrderedSemifield { x : α // 0 ≤ x } :=
  { Nonneg.linearOrderedSemifield, Nonneg.canonicallyOrderedCommSemiring with }

instance linearOrderedCommGroupWithZero [LinearOrderedField α] : LinearOrderedCommGroupWithZero { x : α // 0 ≤ x } :=
  inferInstance

/-! ### Floor -/


instance archimedean [OrderedAddCommMonoid α] [Archimedean α] : Archimedean { x : α // 0 ≤ x } :=
  ⟨fun x y hy =>
    let ⟨n, hr⟩ := Archimedean.arch (x : α) (hy : (0 : α) < y)
    ⟨n, show (x : α) ≤ (n • y : { x : α // 0 ≤ x }) by simp [*, -nsmul_eq_mul, nsmul_coe]⟩⟩

instance floorSemiring [OrderedSemiring α] [FloorSemiring α] : FloorSemiring { r : α // 0 ≤ r } where
  floor a := ⌊(a : α)⌋₊
  ceil a := ⌈(a : α)⌉₊
  floor_of_neg a ha := FloorSemiring.floor_of_neg ha
  gc_floor a n ha := by
    refine' (FloorSemiring.gc_floor (show 0 ≤ (a : α) from ha)).trans _
    rw [← Subtype.coe_le_coe, Nonneg.coe_nat_cast]
  gc_ceil a n := by
    refine' (FloorSemiring.gc_ceil (a : α) n).trans _
    rw [← Subtype.coe_le_coe, Nonneg.coe_nat_cast]

@[norm_cast]
theorem nat_floor_coe [OrderedSemiring α] [FloorSemiring α] (a : { r : α // 0 ≤ r }) : ⌊(a : α)⌋₊ = ⌊a⌋₊ :=
  rfl

@[norm_cast]
theorem nat_ceil_coe [OrderedSemiring α] [FloorSemiring α] (a : { r : α // 0 ≤ r }) : ⌈(a : α)⌉₊ = ⌈a⌉₊ :=
  rfl

end Nonneg

