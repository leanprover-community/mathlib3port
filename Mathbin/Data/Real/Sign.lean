/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Eric Wieser

! This file was ported from Lean 3 source module data.real.sign
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Basic

/-!
# Real sign function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file introduces and contains some results about `real.sign` which maps negative
real numbers to -1, positive real numbers to 1, and 0 to 0.

## Main definitions

 * `real.sign r` is $\begin{cases} -1 & \text{if } r < 0, \\
                               ~~\, 0 & \text{if } r = 0, \\
                               ~~\, 1 & \text{if } r > 0. \end{cases}$

## Tags

sign function
-/


namespace Real

#print Real.sign /-
/-- The sign function that maps negative real numbers to -1, positive numbers to 1, and 0
otherwise. -/
noncomputable def sign (r : ℝ) : ℝ :=
  if r < 0 then -1 else if 0 < r then 1 else 0
#align real.sign Real.sign
-/

/- warning: real.sign_of_neg -> Real.sign_of_neg is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Real.sign r) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Real.sign r) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.sign_of_neg Real.sign_of_negₓ'. -/
theorem sign_of_neg {r : ℝ} (hr : r < 0) : sign r = -1 := by rw [SignType.sign, if_pos hr]
#align real.sign_of_neg Real.sign_of_neg

/- warning: real.sign_of_pos -> Real.sign_of_pos is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Eq.{1} Real (Real.sign r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Eq.{1} Real (Real.sign r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.sign_of_pos Real.sign_of_posₓ'. -/
theorem sign_of_pos {r : ℝ} (hr : 0 < r) : sign r = 1 := by
  rw [SignType.sign, if_pos hr, if_neg hr.not_lt]
#align real.sign_of_pos Real.sign_of_pos

/- warning: real.sign_zero -> Real.sign_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.sign (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (Real.sign (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.sign_zero Real.sign_zeroₓ'. -/
@[simp]
theorem sign_zero : sign 0 = 0 := by rw [SignType.sign, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
#align real.sign_zero Real.sign_zero

/- warning: real.sign_one -> Real.sign_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.sign (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  Eq.{1} Real (Real.sign (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.sign_one Real.sign_oneₓ'. -/
@[simp]
theorem sign_one : sign 1 = 1 :=
  sign_of_pos <| by norm_num
#align real.sign_one Real.sign_one

/- warning: real.sign_apply_eq -> Real.sign_apply_eq is a dubious translation:
lean 3 declaration is
  forall (r : Real), Or (Eq.{1} Real (Real.sign r) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Or (Eq.{1} Real (Real.sign r) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real (Real.sign r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall (r : Real), Or (Eq.{1} Real (Real.sign r) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Or (Eq.{1} Real (Real.sign r) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real (Real.sign r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.sign_apply_eq Real.sign_apply_eqₓ'. -/
theorem sign_apply_eq (r : ℝ) : sign r = -1 ∨ sign r = 0 ∨ sign r = 1 :=
  by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · exact Or.inl <| sign_of_neg hn
  · exact Or.inr <| Or.inl <| sign_zero
  · exact Or.inr <| Or.inr <| sign_of_pos hp
#align real.sign_apply_eq Real.sign_apply_eq

/- warning: real.sign_apply_eq_of_ne_zero -> Real.sign_apply_eq_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall (r : Real), (Ne.{1} Real r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Or (Eq.{1} Real (Real.sign r) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Eq.{1} Real (Real.sign r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall (r : Real), (Ne.{1} Real r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Or (Eq.{1} Real (Real.sign r) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Eq.{1} Real (Real.sign r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.sign_apply_eq_of_ne_zero Real.sign_apply_eq_of_ne_zeroₓ'. -/
/-- This lemma is useful for working with `ℝˣ` -/
theorem sign_apply_eq_of_ne_zero (r : ℝ) (h : r ≠ 0) : sign r = -1 ∨ sign r = 1 :=
  by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · exact Or.inl <| sign_of_neg hn
  · exact (h rfl).elim
  · exact Or.inr <| sign_of_pos hp
#align real.sign_apply_eq_of_ne_zero Real.sign_apply_eq_of_ne_zero

/- warning: real.sign_eq_zero_iff -> Real.sign_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {r : Real}, Iff (Eq.{1} Real (Real.sign r) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {r : Real}, Iff (Eq.{1} Real (Real.sign r) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.sign_eq_zero_iff Real.sign_eq_zero_iffₓ'. -/
@[simp]
theorem sign_eq_zero_iff {r : ℝ} : sign r = 0 ↔ r = 0 :=
  by
  refine' ⟨fun h => _, fun h => h.symm ▸ sign_zero⟩
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn, neg_eq_zero] at h
    exact (one_ne_zero h).elim
  · rfl
  · rw [sign_of_pos hp] at h
    exact (one_ne_zero h).elim
#align real.sign_eq_zero_iff Real.sign_eq_zero_iff

/- warning: real.sign_int_cast -> Real.sign_int_cast is a dubious translation:
lean 3 declaration is
  forall (z : Int), Eq.{1} Real (Real.sign ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) z)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) (Int.sign z))
but is expected to have type
  forall (z : Int), Eq.{1} Real (Real.sign (Int.cast.{0} Real Real.intCast z)) (Int.cast.{0} Real Real.intCast (Int.sign z))
Case conversion may be inaccurate. Consider using '#align real.sign_int_cast Real.sign_int_castₓ'. -/
theorem sign_int_cast (z : ℤ) : sign (z : ℝ) = ↑(Int.sign z) :=
  by
  obtain hn | rfl | hp := lt_trichotomy z (0 : ℤ)
  ·
    rw [sign_of_neg (int.cast_lt_zero.mpr hn), Int.sign_eq_neg_one_of_neg hn, Int.cast_neg,
      Int.cast_one]
  · rw [Int.cast_zero, sign_zero, Int.sign_zero, Int.cast_zero]
  · rw [sign_of_pos (int.cast_pos.mpr hp), Int.sign_eq_one_of_pos hp, Int.cast_one]
#align real.sign_int_cast Real.sign_int_cast

/- warning: real.sign_neg -> Real.sign_neg is a dubious translation:
lean 3 declaration is
  forall {r : Real}, Eq.{1} Real (Real.sign (Neg.neg.{0} Real Real.hasNeg r)) (Neg.neg.{0} Real Real.hasNeg (Real.sign r))
but is expected to have type
  forall {r : Real}, Eq.{1} Real (Real.sign (Neg.neg.{0} Real Real.instNegReal r)) (Neg.neg.{0} Real Real.instNegReal (Real.sign r))
Case conversion may be inaccurate. Consider using '#align real.sign_neg Real.sign_negₓ'. -/
theorem sign_neg {r : ℝ} : sign (-r) = -sign r :=
  by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn, sign_of_pos (neg_pos.mpr hn), neg_neg]
  · rw [sign_zero, neg_zero, sign_zero]
  · rw [sign_of_pos hp, sign_of_neg (neg_lt_zero.mpr hp)]
#align real.sign_neg Real.sign_neg

/- warning: real.sign_mul_nonneg -> Real.sign_mul_nonneg is a dubious translation:
lean 3 declaration is
  forall (r : Real), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.sign r) r)
but is expected to have type
  forall (r : Real), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.sign r) r)
Case conversion may be inaccurate. Consider using '#align real.sign_mul_nonneg Real.sign_mul_nonnegₓ'. -/
theorem sign_mul_nonneg (r : ℝ) : 0 ≤ sign r * r :=
  by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn]
    exact mul_nonneg_of_nonpos_of_nonpos (by norm_num) hn.le
  · rw [mul_zero]
  · rw [sign_of_pos hp, one_mul]
    exact hp.le
#align real.sign_mul_nonneg Real.sign_mul_nonneg

/- warning: real.sign_mul_pos_of_ne_zero -> Real.sign_mul_pos_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall (r : Real), (Ne.{1} Real r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.sign r) r))
but is expected to have type
  forall (r : Real), (Ne.{1} Real r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.sign r) r))
Case conversion may be inaccurate. Consider using '#align real.sign_mul_pos_of_ne_zero Real.sign_mul_pos_of_ne_zeroₓ'. -/
theorem sign_mul_pos_of_ne_zero (r : ℝ) (hr : r ≠ 0) : 0 < sign r * r :=
  by
  refine' lt_of_le_of_ne (sign_mul_nonneg r) fun h => hr _
  have hs0 := (zero_eq_mul.mp h).resolve_right hr
  exact sign_eq_zero_iff.mp hs0
#align real.sign_mul_pos_of_ne_zero Real.sign_mul_pos_of_ne_zero

/- warning: real.inv_sign -> Real.inv_sign is a dubious translation:
lean 3 declaration is
  forall (r : Real), Eq.{1} Real (Inv.inv.{0} Real Real.hasInv (Real.sign r)) (Real.sign r)
but is expected to have type
  forall (r : Real), Eq.{1} Real (Inv.inv.{0} Real Real.instInvReal (Real.sign r)) (Real.sign r)
Case conversion may be inaccurate. Consider using '#align real.inv_sign Real.inv_signₓ'. -/
@[simp]
theorem inv_sign (r : ℝ) : (sign r)⁻¹ = sign r :=
  by
  obtain hn | hz | hp := sign_apply_eq r
  · rw [hn]
    norm_num
  · rw [hz]
    exact inv_zero
  · rw [hp]
    exact inv_one
#align real.inv_sign Real.inv_sign

/- warning: real.sign_inv -> Real.sign_inv is a dubious translation:
lean 3 declaration is
  forall (r : Real), Eq.{1} Real (Real.sign (Inv.inv.{0} Real Real.hasInv r)) (Real.sign r)
but is expected to have type
  forall (r : Real), Eq.{1} Real (Real.sign (Inv.inv.{0} Real Real.instInvReal r)) (Real.sign r)
Case conversion may be inaccurate. Consider using '#align real.sign_inv Real.sign_invₓ'. -/
@[simp]
theorem sign_inv (r : ℝ) : sign r⁻¹ = sign r :=
  by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn, sign_of_neg (inv_lt_zero.mpr hn)]
  · rw [sign_zero, inv_zero, sign_zero]
  · rw [sign_of_pos hp, sign_of_pos (inv_pos.mpr hp)]
#align real.sign_inv Real.sign_inv

end Real

