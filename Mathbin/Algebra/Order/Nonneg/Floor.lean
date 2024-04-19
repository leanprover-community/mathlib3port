/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Algebra.Order.Nonneg.Ring
import Algebra.Order.Archimedean

#align_import algebra.order.nonneg.floor from "leanprover-community/mathlib"@"b3f4f007a962e3787aa0f3b5c7942a1317f7d88e"

/-!
# Nonnegative elements are archimedean

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.

## Main declarations

* `{x : α // 0 ≤ x}` is a `floor_semiring` if `α` is.
-/


namespace Nonneg

variable {α : Type _}

#print Nonneg.archimedean /-
instance archimedean [OrderedAddCommMonoid α] [Archimedean α] : Archimedean { x : α // 0 ≤ x } :=
  ⟨fun x y hy =>
    let ⟨n, hr⟩ := Archimedean.arch (x : α) (hy : (0 : α) < y)
    ⟨n, show (x : α) ≤ (n • y : { x : α // 0 ≤ x }) by simp [*, -nsmul_eq_mul, nsmul_coe]⟩⟩
#align nonneg.archimedean Nonneg.archimedean
-/

#print Nonneg.floorSemiring /-
instance floorSemiring [OrderedSemiring α] [FloorSemiring α] : FloorSemiring { r : α // 0 ≤ r }
    where
  floor a := ⌊(a : α)⌋₊
  ceil a := ⌈(a : α)⌉₊
  floor_of_neg a ha := FloorSemiring.floor_of_neg ha
  gc_floor a n ha :=
    by
    refine' (FloorSemiring.gc_floor (show 0 ≤ (a : α) from ha)).trans _
    rw [← Subtype.coe_le_coe, Nonneg.coe_natCast]
  gc_ceil a n := by
    refine' (FloorSemiring.gc_ceil (a : α) n).trans _
    rw [← Subtype.coe_le_coe, Nonneg.coe_natCast]
#align nonneg.floor_semiring Nonneg.floorSemiring
-/

#print Nonneg.nat_floor_coe /-
@[norm_cast]
theorem nat_floor_coe [OrderedSemiring α] [FloorSemiring α] (a : { r : α // 0 ≤ r }) :
    ⌊(a : α)⌋₊ = ⌊a⌋₊ :=
  rfl
#align nonneg.nat_floor_coe Nonneg.nat_floor_coe
-/

#print Nonneg.nat_ceil_coe /-
@[norm_cast]
theorem nat_ceil_coe [OrderedSemiring α] [FloorSemiring α] (a : { r : α // 0 ≤ r }) :
    ⌈(a : α)⌉₊ = ⌈a⌉₊ :=
  rfl
#align nonneg.nat_ceil_coe Nonneg.nat_ceil_coe
-/

end Nonneg

