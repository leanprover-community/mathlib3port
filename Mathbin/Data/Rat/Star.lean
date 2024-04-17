/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Algebra.Star.Order
import Data.Rat.Lemmas
import GroupTheory.Submonoid.Membership

#align_import data.rat.star from "leanprover-community/mathlib"@"6b31d1eebd64eab86d5bd9936bfaada6ca8b5842"

/-! # Star order structure on ℚ

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Here we put the trivial `star` operation on `ℚ` for convenience and show that it is a
`star_ordered_ring`. In particular, this means that every element of `ℚ` is a sum of squares.
-/


namespace Rat

instance : StarRing ℚ where
  unit := id
  star_involutive _ := rfl
  star_hMul _ _ := mul_comm _ _
  star_add _ _ := rfl

instance : TrivialStar ℚ where star_trivial _ := rfl

instance : StarOrderedRing ℚ :=
  StarOrderedRing.of_nonneg_iff (fun _ _ => add_le_add_left) fun x =>
    by
    refine'
      ⟨fun hx => _, fun hx =>
        AddSubmonoid.closure_induction hx (by rintro - ⟨s, rfl⟩; exact hMul_self_nonneg s) le_rfl
          fun _ _ => add_nonneg⟩
    /- If `x = p / q`, then, since `0 ≤ x`, we have `p q : ℕ`, and `p / q` is the sum of `p * q`
      copies of `(1 / q) ^ 2`, and so `x` lies in the `add_submonoid` generated by square elements.
    
      Note: it's possible to rephrase this argument as `x = (p * q) • (1 / q) ^ 2`, but this would
      be somewhat challenging without increasing import requirements. -/
    suffices
      (Finset.range (x.num.nat_abs * x.denom)).Sum
          (Function.const ℕ (Rat.mkPnat 1 ⟨x.denom, x.pos⟩ * Rat.mkPnat 1 ⟨x.denom, x.pos⟩)) =
        x
      by exact this ▸ sum_mem fun n hn => AddSubmonoid.subset_closure ⟨_, rfl⟩
    simp only [Function.const_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mk_pnat_eq]
    rw [← Int.cast_natCast, Int.ofNat_mul, Int.natCast_natAbs,
      abs_of_nonneg (num_nonneg_iff_zero_le.mpr hx), Int.cast_mul, Int.cast_natCast]
    simp only [Int.cast_mul, Int.cast_natCast, coe_int_eq_mk, coe_nat_eq_mk]
    rw [mul_assoc, ← mul_assoc (mk (x.denom : ℤ) 1), mk_mul_mk_cancel one_ne_zero, ←
      one_mul (x.denom : ℤ), div_mk_div_cancel_left (by simpa using x.pos.ne' : (x.denom : ℤ) ≠ 0),
      one_mul, mk_one_one, one_mul, mk_mul_mk_cancel one_ne_zero, Rat.num_divInt_den]

end Rat

