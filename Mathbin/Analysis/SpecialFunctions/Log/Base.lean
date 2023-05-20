/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne

! This file was ported from Lean 3 source module analysis.special_functions.log.base
! leanprover-community/mathlib commit 0b9eaaa7686280fad8cce467f5c3c57ee6ce77f8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Pow.Real
import Mathbin.Data.Int.Log

/-!
# Real logarithm base `b`

In this file we define `real.logb` to be the logarithm of a real number in a given base `b`. We
define this as the division of the natural logarithms of the argument and the base, so that we have
a globally defined function with `logb b 0 = 0`, `logb b (-x) = logb b x` `logb 0 x = 0` and
`logb (-b) x = logb b x`.

We prove some basic properties of this function and its relation to `rpow`.

## Tags

logarithm, continuity
-/


open Set Filter Function

open Topology

noncomputable section

namespace Real

variable {b x y : ℝ}

#print Real.logb /-
/-- The real logarithm in a given base. As with the natural logarithm, we define `logb b x` to
be `logb b |x|` for `x < 0`, and `0` for `x = 0`.-/
@[pp_nodot]
noncomputable def logb (b x : ℝ) : ℝ :=
  log x / log b
#align real.logb Real.logb
-/

/- warning: real.log_div_log -> Real.log_div_log is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.log x) (Real.log b)) (Real.logb b x)
but is expected to have type
  forall {b : Real} {x : Real}, Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.log x) (Real.log b)) (Real.logb b x)
Case conversion may be inaccurate. Consider using '#align real.log_div_log Real.log_div_logₓ'. -/
theorem log_div_log : log x / log b = logb b x :=
  rfl
#align real.log_div_log Real.log_div_log

/- warning: real.logb_zero -> Real.logb_zero is a dubious translation:
lean 3 declaration is
  forall {b : Real}, Eq.{1} Real (Real.logb b (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {b : Real}, Eq.{1} Real (Real.logb b (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.logb_zero Real.logb_zeroₓ'. -/
@[simp]
theorem logb_zero : logb b 0 = 0 := by simp [logb]
#align real.logb_zero Real.logb_zero

/- warning: real.logb_one -> Real.logb_one is a dubious translation:
lean 3 declaration is
  forall {b : Real}, Eq.{1} Real (Real.logb b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {b : Real}, Eq.{1} Real (Real.logb b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.logb_one Real.logb_oneₓ'. -/
@[simp]
theorem logb_one : logb b 1 = 0 := by simp [logb]
#align real.logb_one Real.logb_one

/- warning: real.logb_abs -> Real.logb_abs is a dubious translation:
lean 3 declaration is
  forall {b : Real} (x : Real), Eq.{1} Real (Real.logb b (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x)) (Real.logb b x)
but is expected to have type
  forall {b : Real} (x : Real), Eq.{1} Real (Real.logb b (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x)) (Real.logb b x)
Case conversion may be inaccurate. Consider using '#align real.logb_abs Real.logb_absₓ'. -/
@[simp]
theorem logb_abs (x : ℝ) : logb b (|x|) = logb b x := by rw [logb, logb, log_abs]
#align real.logb_abs Real.logb_abs

/- warning: real.logb_neg_eq_logb -> Real.logb_neg_eq_logb is a dubious translation:
lean 3 declaration is
  forall {b : Real} (x : Real), Eq.{1} Real (Real.logb b (Neg.neg.{0} Real Real.hasNeg x)) (Real.logb b x)
but is expected to have type
  forall {b : Real} (x : Real), Eq.{1} Real (Real.logb b (Neg.neg.{0} Real Real.instNegReal x)) (Real.logb b x)
Case conversion may be inaccurate. Consider using '#align real.logb_neg_eq_logb Real.logb_neg_eq_logbₓ'. -/
@[simp]
theorem logb_neg_eq_logb (x : ℝ) : logb b (-x) = logb b x := by
  rw [← logb_abs x, ← logb_abs (-x), abs_neg]
#align real.logb_neg_eq_logb Real.logb_neg_eq_logb

/- warning: real.logb_mul -> Real.logb_mul is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Real.logb b (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Real.logb b x) (Real.logb b y)))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Real.logb b (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Real.logb b x) (Real.logb b y)))
Case conversion may be inaccurate. Consider using '#align real.logb_mul Real.logb_mulₓ'. -/
theorem logb_mul (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x * y) = logb b x + logb b y := by
  simp_rw [logb, log_mul hx hy, add_div]
#align real.logb_mul Real.logb_mul

/- warning: real.logb_div -> Real.logb_div is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Real.logb b (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x y)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.logb b x) (Real.logb b y)))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Real.logb b (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x y)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.logb b x) (Real.logb b y)))
Case conversion may be inaccurate. Consider using '#align real.logb_div Real.logb_divₓ'. -/
theorem logb_div (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x / y) = logb b x - logb b y := by
  simp_rw [logb, log_div hx hy, sub_div]
#align real.logb_div Real.logb_div

/- warning: real.logb_inv -> Real.logb_inv is a dubious translation:
lean 3 declaration is
  forall {b : Real} (x : Real), Eq.{1} Real (Real.logb b (Inv.inv.{0} Real Real.hasInv x)) (Neg.neg.{0} Real Real.hasNeg (Real.logb b x))
but is expected to have type
  forall {b : Real} (x : Real), Eq.{1} Real (Real.logb b (Inv.inv.{0} Real Real.instInvReal x)) (Neg.neg.{0} Real Real.instNegReal (Real.logb b x))
Case conversion may be inaccurate. Consider using '#align real.logb_inv Real.logb_invₓ'. -/
@[simp]
theorem logb_inv (x : ℝ) : logb b x⁻¹ = -logb b x := by simp [logb, neg_div]
#align real.logb_inv Real.logb_inv

section BPosAndNeOne

variable (b_pos : 0 < b)

variable (b_ne_one : b ≠ 1)

include b_pos b_ne_one

private theorem log_b_ne_zero : log b ≠ 0 :=
  by
  have b_ne_zero : b ≠ 0; linarith
  have b_ne_minus_one : b ≠ -1; linarith
  simp [b_ne_one, b_ne_zero, b_ne_minus_one]
#align real.log_b_ne_zero real.log_b_ne_zero

/- warning: real.logb_rpow -> Real.logb_rpow is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{1} Real (Real.logb b (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) b x)) x)
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{1} Real (Real.logb b (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) b x)) x)
Case conversion may be inaccurate. Consider using '#align real.logb_rpow Real.logb_rpowₓ'. -/
@[simp]
theorem logb_rpow : logb b (b ^ x) = x :=
  by
  rw [logb, div_eq_iff, log_rpow b_pos]
  exact log_b_ne_zero b_pos b_ne_one
#align real.logb_rpow Real.logb_rpow

/- warning: real.rpow_logb_eq_abs -> Real.rpow_logb_eq_abs is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) b (Real.logb b x)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) b (Real.logb b x)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x))
Case conversion may be inaccurate. Consider using '#align real.rpow_logb_eq_abs Real.rpow_logb_eq_absₓ'. -/
theorem rpow_logb_eq_abs (hx : x ≠ 0) : b ^ logb b x = |x| :=
  by
  apply log_inj_on_pos
  simp only [Set.mem_Ioi]
  apply rpow_pos_of_pos b_pos
  simp only [abs_pos, mem_Ioi, Ne.def, hx, not_false_iff]
  rw [log_rpow b_pos, logb, log_abs]
  field_simp [log_b_ne_zero b_pos b_ne_one]
#align real.rpow_logb_eq_abs Real.rpow_logb_eq_abs

/- warning: real.rpow_logb -> Real.rpow_logb is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) b (Real.logb b x)) x)
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) b (Real.logb b x)) x)
Case conversion may be inaccurate. Consider using '#align real.rpow_logb Real.rpow_logbₓ'. -/
@[simp]
theorem rpow_logb (hx : 0 < x) : b ^ logb b x = x :=
  by
  rw [rpow_logb_eq_abs b_pos b_ne_one hx.ne']
  exact abs_of_pos hx
#align real.rpow_logb Real.rpow_logb

/- warning: real.rpow_logb_of_neg -> Real.rpow_logb_of_neg is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) b (Real.logb b x)) (Neg.neg.{0} Real Real.hasNeg x))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) b (Real.logb b x)) (Neg.neg.{0} Real Real.instNegReal x))
Case conversion may be inaccurate. Consider using '#align real.rpow_logb_of_neg Real.rpow_logb_of_negₓ'. -/
theorem rpow_logb_of_neg (hx : x < 0) : b ^ logb b x = -x :=
  by
  rw [rpow_logb_eq_abs b_pos b_ne_one (ne_of_lt hx)]
  exact abs_of_neg hx
#align real.rpow_logb_of_neg Real.rpow_logb_of_neg

/- warning: real.surj_on_logb -> Real.surjOn_logb is a dubious translation:
lean 3 declaration is
  forall {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Set.SurjOn.{0, 0} Real Real (Real.logb b) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Set.univ.{0} Real))
but is expected to have type
  forall {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Set.SurjOn.{0, 0} Real Real (Real.logb b) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Set.univ.{0} Real))
Case conversion may be inaccurate. Consider using '#align real.surj_on_logb Real.surjOn_logbₓ'. -/
theorem surjOn_logb : SurjOn (logb b) (Ioi 0) univ := fun x _ =>
  ⟨rpow b x, rpow_pos_of_pos b_pos x, logb_rpow b_pos b_ne_one⟩
#align real.surj_on_logb Real.surjOn_logb

/- warning: real.logb_surjective -> Real.logb_surjective is a dubious translation:
lean 3 declaration is
  forall {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Function.Surjective.{1, 1} Real Real (Real.logb b))
but is expected to have type
  forall {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Function.Surjective.{1, 1} Real Real (Real.logb b))
Case conversion may be inaccurate. Consider using '#align real.logb_surjective Real.logb_surjectiveₓ'. -/
theorem logb_surjective : Surjective (logb b) := fun x => ⟨b ^ x, logb_rpow b_pos b_ne_one⟩
#align real.logb_surjective Real.logb_surjective

/- warning: real.range_logb -> Real.range_logb is a dubious translation:
lean 3 declaration is
  forall {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{1} (Set.{0} Real) (Set.range.{0, 1} Real Real (Real.logb b)) (Set.univ.{0} Real))
but is expected to have type
  forall {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{1} (Set.{0} Real) (Set.range.{0, 1} Real Real (Real.logb b)) (Set.univ.{0} Real))
Case conversion may be inaccurate. Consider using '#align real.range_logb Real.range_logbₓ'. -/
@[simp]
theorem range_logb : range (logb b) = univ :=
  (logb_surjective b_pos b_ne_one).range_eq
#align real.range_logb Real.range_logb

/- warning: real.surj_on_logb' -> Real.surjOn_logb' is a dubious translation:
lean 3 declaration is
  forall {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Set.SurjOn.{0, 0} Real Real (Real.logb b) (Set.Iio.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Set.univ.{0} Real))
but is expected to have type
  forall {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Ne.{1} Real b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Set.SurjOn.{0, 0} Real Real (Real.logb b) (Set.Iio.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Set.univ.{0} Real))
Case conversion may be inaccurate. Consider using '#align real.surj_on_logb' Real.surjOn_logb'ₓ'. -/
theorem surjOn_logb' : SurjOn (logb b) (Iio 0) univ :=
  by
  intro x x_in_univ
  use -b ^ x
  constructor
  · simp only [Right.neg_neg_iff, Set.mem_Iio]
    apply rpow_pos_of_pos b_pos
  · rw [logb_neg_eq_logb, logb_rpow b_pos b_ne_one]
#align real.surj_on_logb' Real.surjOn_logb'

end BPosAndNeOne

section OneLtB

variable (hb : 1 < b)

include hb

private theorem b_pos : 0 < b := by linarith
#align real.b_pos real.b_pos

private theorem b_ne_one : b ≠ 1 := by linarith
#align real.b_ne_one real.b_ne_one

/- warning: real.logb_le_logb -> Real.logb_le_logb is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LE.le.{0} Real Real.hasLe (Real.logb b x) (Real.logb b y)) (LE.le.{0} Real Real.hasLe x y))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.logb b x) (Real.logb b y)) (LE.le.{0} Real Real.instLEReal x y))
Case conversion may be inaccurate. Consider using '#align real.logb_le_logb Real.logb_le_logbₓ'. -/
@[simp]
theorem logb_le_logb (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ x ≤ y := by
  rw [logb, logb, div_le_div_right (log_pos hb), log_le_log h h₁]
#align real.logb_le_logb Real.logb_le_logb

/- warning: real.logb_lt_logb -> Real.logb_lt_logb is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x y) -> (LT.lt.{0} Real Real.hasLt (Real.logb b x) (Real.logb b y))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x y) -> (LT.lt.{0} Real Real.instLTReal (Real.logb b x) (Real.logb b y))
Case conversion may be inaccurate. Consider using '#align real.logb_lt_logb Real.logb_lt_logbₓ'. -/
theorem logb_lt_logb (hx : 0 < x) (hxy : x < y) : logb b x < logb b y :=
  by
  rw [logb, logb, div_lt_div_right (log_pos hb)]
  exact log_lt_log hx hxy
#align real.logb_lt_logb Real.logb_lt_logb

/- warning: real.logb_lt_logb_iff -> Real.logb_lt_logb_iff is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.logb b x) (Real.logb b y)) (LT.lt.{0} Real Real.hasLt x y))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.logb b x) (Real.logb b y)) (LT.lt.{0} Real Real.instLTReal x y))
Case conversion may be inaccurate. Consider using '#align real.logb_lt_logb_iff Real.logb_lt_logb_iffₓ'. -/
@[simp]
theorem logb_lt_logb_iff (hx : 0 < x) (hy : 0 < y) : logb b x < logb b y ↔ x < y :=
  by
  rw [logb, logb, div_lt_div_right (log_pos hb)]
  exact log_lt_log_iff hx hy
#align real.logb_lt_logb_iff Real.logb_lt_logb_iff

/- warning: real.logb_le_iff_le_rpow -> Real.logb_le_iff_le_rpow is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LE.le.{0} Real Real.hasLe (Real.logb b x) y) (LE.le.{0} Real Real.hasLe x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) b y)))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.logb b x) y) (LE.le.{0} Real Real.instLEReal x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) b y)))
Case conversion may be inaccurate. Consider using '#align real.logb_le_iff_le_rpow Real.logb_le_iff_le_rpowₓ'. -/
theorem logb_le_iff_le_rpow (hx : 0 < x) : logb b x ≤ y ↔ x ≤ b ^ y := by
  rw [← rpow_le_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one hb) hx]
#align real.logb_le_iff_le_rpow Real.logb_le_iff_le_rpow

/- warning: real.logb_lt_iff_lt_rpow -> Real.logb_lt_iff_lt_rpow is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.logb b x) y) (LT.lt.{0} Real Real.hasLt x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) b y)))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.logb b x) y) (LT.lt.{0} Real Real.instLTReal x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) b y)))
Case conversion may be inaccurate. Consider using '#align real.logb_lt_iff_lt_rpow Real.logb_lt_iff_lt_rpowₓ'. -/
theorem logb_lt_iff_lt_rpow (hx : 0 < x) : logb b x < y ↔ x < b ^ y := by
  rw [← rpow_lt_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one hb) hx]
#align real.logb_lt_iff_lt_rpow Real.logb_lt_iff_lt_rpow

/- warning: real.le_logb_iff_rpow_le -> Real.le_logb_iff_rpow_le is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LE.le.{0} Real Real.hasLe x (Real.logb b y)) (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) b x) y))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LE.le.{0} Real Real.instLEReal x (Real.logb b y)) (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) b x) y))
Case conversion may be inaccurate. Consider using '#align real.le_logb_iff_rpow_le Real.le_logb_iff_rpow_leₓ'. -/
theorem le_logb_iff_rpow_le (hy : 0 < y) : x ≤ logb b y ↔ b ^ x ≤ y := by
  rw [← rpow_le_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one hb) hy]
#align real.le_logb_iff_rpow_le Real.le_logb_iff_rpow_le

/- warning: real.lt_logb_iff_rpow_lt -> Real.lt_logb_iff_rpow_lt is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LT.lt.{0} Real Real.hasLt x (Real.logb b y)) (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) b x) y))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LT.lt.{0} Real Real.instLTReal x (Real.logb b y)) (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) b x) y))
Case conversion may be inaccurate. Consider using '#align real.lt_logb_iff_rpow_lt Real.lt_logb_iff_rpow_ltₓ'. -/
theorem lt_logb_iff_rpow_lt (hy : 0 < y) : x < logb b y ↔ b ^ x < y := by
  rw [← rpow_lt_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one hb) hy]
#align real.lt_logb_iff_rpow_lt Real.lt_logb_iff_rpow_lt

/- warning: real.logb_pos_iff -> Real.logb_pos_iff is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.logb b x)) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.logb b x)) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x))
Case conversion may be inaccurate. Consider using '#align real.logb_pos_iff Real.logb_pos_iffₓ'. -/
theorem logb_pos_iff (hx : 0 < x) : 0 < logb b x ↔ 1 < x :=
  by
  rw [← @logb_one b]
  rw [logb_lt_logb_iff hb zero_lt_one hx]
#align real.logb_pos_iff Real.logb_pos_iff

/- warning: real.logb_pos -> Real.logb_pos is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.logb b x))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.logb b x))
Case conversion may be inaccurate. Consider using '#align real.logb_pos Real.logb_posₓ'. -/
theorem logb_pos (hx : 1 < x) : 0 < logb b x :=
  by
  rw [logb_pos_iff hb (lt_trans zero_lt_one hx)]
  exact hx
#align real.logb_pos Real.logb_pos

/- warning: real.logb_neg_iff -> Real.logb_neg_iff is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.logb b x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.logb b x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.logb_neg_iff Real.logb_neg_iffₓ'. -/
theorem logb_neg_iff (h : 0 < x) : logb b x < 0 ↔ x < 1 :=
  by
  rw [← logb_one]
  exact logb_lt_logb_iff hb h zero_lt_one
#align real.logb_neg_iff Real.logb_neg_iff

/- warning: real.logb_neg -> Real.logb_neg is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (Real.logb b x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (Real.logb b x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.logb_neg Real.logb_negₓ'. -/
theorem logb_neg (h0 : 0 < x) (h1 : x < 1) : logb b x < 0 :=
  (logb_neg_iff hb h0).2 h1
#align real.logb_neg Real.logb_neg

/- warning: real.logb_nonneg_iff -> Real.logb_nonneg_iff is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.logb b x)) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.logb b x)) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x))
Case conversion may be inaccurate. Consider using '#align real.logb_nonneg_iff Real.logb_nonneg_iffₓ'. -/
theorem logb_nonneg_iff (hx : 0 < x) : 0 ≤ logb b x ↔ 1 ≤ x := by
  rw [← not_lt, logb_neg_iff hb hx, not_lt]
#align real.logb_nonneg_iff Real.logb_nonneg_iff

/- warning: real.logb_nonneg -> Real.logb_nonneg is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.logb b x))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.logb b x))
Case conversion may be inaccurate. Consider using '#align real.logb_nonneg Real.logb_nonnegₓ'. -/
theorem logb_nonneg (hx : 1 ≤ x) : 0 ≤ logb b x :=
  (logb_nonneg_iff hb (zero_lt_one.trans_le hx)).2 hx
#align real.logb_nonneg Real.logb_nonneg

/- warning: real.logb_nonpos_iff -> Real.logb_nonpos_iff is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LE.le.{0} Real Real.hasLe (Real.logb b x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.logb b x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.logb_nonpos_iff Real.logb_nonpos_iffₓ'. -/
theorem logb_nonpos_iff (hx : 0 < x) : logb b x ≤ 0 ↔ x ≤ 1 := by
  rw [← not_lt, logb_pos_iff hb hx, not_lt]
#align real.logb_nonpos_iff Real.logb_nonpos_iff

/- warning: real.logb_nonpos_iff' -> Real.logb_nonpos_iff' is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LE.le.{0} Real Real.hasLe (Real.logb b x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.logb b x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.logb_nonpos_iff' Real.logb_nonpos_iff'ₓ'. -/
theorem logb_nonpos_iff' (hx : 0 ≤ x) : logb b x ≤ 0 ↔ x ≤ 1 :=
  by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [le_refl, zero_le_one]
  exact logb_nonpos_iff hb hx
#align real.logb_nonpos_iff' Real.logb_nonpos_iff'

/- warning: real.logb_nonpos -> Real.logb_nonpos is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (Real.logb b x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (Real.logb b x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.logb_nonpos Real.logb_nonposₓ'. -/
theorem logb_nonpos (hx : 0 ≤ x) (h'x : x ≤ 1) : logb b x ≤ 0 :=
  (logb_nonpos_iff' hb hx).2 h'x
#align real.logb_nonpos Real.logb_nonpos

/- warning: real.strict_mono_on_logb -> Real.strictMonoOn_logb is a dubious translation:
lean 3 declaration is
  forall {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (StrictMonoOn.{0, 0} Real Real Real.preorder Real.preorder (Real.logb b) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (StrictMonoOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal (Real.logb b) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.strict_mono_on_logb Real.strictMonoOn_logbₓ'. -/
theorem strictMonoOn_logb : StrictMonoOn (logb b) (Set.Ioi 0) := fun x hx y hy hxy =>
  logb_lt_logb hb hx hxy
#align real.strict_mono_on_logb Real.strictMonoOn_logb

/- warning: real.strict_anti_on_logb -> Real.strictAntiOn_logb is a dubious translation:
lean 3 declaration is
  forall {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (StrictAntiOn.{0, 0} Real Real Real.preorder Real.preorder (Real.logb b) (Set.Iio.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (StrictAntiOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal (Real.logb b) (Set.Iio.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.strict_anti_on_logb Real.strictAntiOn_logbₓ'. -/
theorem strictAntiOn_logb : StrictAntiOn (logb b) (Set.Iio 0) :=
  by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs y, ← logb_abs x]
  refine' logb_lt_logb hb (abs_pos.2 hy.ne) _
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]
#align real.strict_anti_on_logb Real.strictAntiOn_logb

/- warning: real.logb_inj_on_pos -> Real.logb_injOn_pos is a dubious translation:
lean 3 declaration is
  forall {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (Set.InjOn.{0, 0} Real Real (Real.logb b) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (Set.InjOn.{0, 0} Real Real (Real.logb b) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.logb_inj_on_pos Real.logb_injOn_posₓ'. -/
theorem logb_injOn_pos : Set.InjOn (logb b) (Set.Ioi 0) :=
  (strictMonoOn_logb hb).InjOn
#align real.logb_inj_on_pos Real.logb_injOn_pos

/- warning: real.eq_one_of_pos_of_logb_eq_zero -> Real.eq_one_of_pos_of_logb_eq_zero is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Real.logb b x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Real.logb b x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.eq_one_of_pos_of_logb_eq_zero Real.eq_one_of_pos_of_logb_eq_zeroₓ'. -/
theorem eq_one_of_pos_of_logb_eq_zero (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 :=
  logb_injOn_pos hb (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.logb_one.symm)
#align real.eq_one_of_pos_of_logb_eq_zero Real.eq_one_of_pos_of_logb_eq_zero

/- warning: real.logb_ne_zero_of_pos_of_ne_one -> Real.logb_ne_zero_of_pos_of_ne_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Ne.{1} Real (Real.logb b x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Ne.{1} Real (Real.logb b x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.logb_ne_zero_of_pos_of_ne_one Real.logb_ne_zero_of_pos_of_ne_oneₓ'. -/
theorem logb_ne_zero_of_pos_of_ne_one (hx_pos : 0 < x) (hx : x ≠ 1) : logb b x ≠ 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero hb hx_pos) hx
#align real.logb_ne_zero_of_pos_of_ne_one Real.logb_ne_zero_of_pos_of_ne_one

/- warning: real.tendsto_logb_at_top -> Real.tendsto_logb_atTop is a dubious translation:
lean 3 declaration is
  forall {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (Filter.Tendsto.{0, 0} Real Real (Real.logb b) (Filter.atTop.{0} Real Real.preorder) (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  forall {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (Filter.Tendsto.{0, 0} Real Real (Real.logb b) (Filter.atTop.{0} Real Real.instPreorderReal) (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align real.tendsto_logb_at_top Real.tendsto_logb_atTopₓ'. -/
theorem tendsto_logb_atTop : Tendsto (logb b) atTop atTop :=
  Tendsto.atTop_div_const (log_pos hb) tendsto_log_atTop
#align real.tendsto_logb_at_top Real.tendsto_logb_atTop

end OneLtB

section BPosAndBLtOne

variable (b_pos : 0 < b)

variable (b_lt_one : b < 1)

include b_lt_one

private theorem b_ne_one : b ≠ 1 := by linarith
#align real.b_ne_one real.b_ne_one

include b_pos

/- warning: real.logb_le_logb_of_base_lt_one -> Real.logb_le_logb_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LE.le.{0} Real Real.hasLe (Real.logb b x) (Real.logb b y)) (LE.le.{0} Real Real.hasLe y x))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.logb b x) (Real.logb b y)) (LE.le.{0} Real Real.instLEReal y x))
Case conversion may be inaccurate. Consider using '#align real.logb_le_logb_of_base_lt_one Real.logb_le_logb_of_base_lt_oneₓ'. -/
@[simp]
theorem logb_le_logb_of_base_lt_one (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ y ≤ x := by
  rw [logb, logb, div_le_div_right_of_neg (log_neg b_pos b_lt_one), log_le_log h₁ h]
#align real.logb_le_logb_of_base_lt_one Real.logb_le_logb_of_base_lt_one

/- warning: real.logb_lt_logb_of_base_lt_one -> Real.logb_lt_logb_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x y) -> (LT.lt.{0} Real Real.hasLt (Real.logb b y) (Real.logb b x))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x y) -> (LT.lt.{0} Real Real.instLTReal (Real.logb b y) (Real.logb b x))
Case conversion may be inaccurate. Consider using '#align real.logb_lt_logb_of_base_lt_one Real.logb_lt_logb_of_base_lt_oneₓ'. -/
theorem logb_lt_logb_of_base_lt_one (hx : 0 < x) (hxy : x < y) : logb b y < logb b x :=
  by
  rw [logb, logb, div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log hx hxy
#align real.logb_lt_logb_of_base_lt_one Real.logb_lt_logb_of_base_lt_one

/- warning: real.logb_lt_logb_iff_of_base_lt_one -> Real.logb_lt_logb_iff_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.logb b x) (Real.logb b y)) (LT.lt.{0} Real Real.hasLt y x))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.logb b x) (Real.logb b y)) (LT.lt.{0} Real Real.instLTReal y x))
Case conversion may be inaccurate. Consider using '#align real.logb_lt_logb_iff_of_base_lt_one Real.logb_lt_logb_iff_of_base_lt_oneₓ'. -/
@[simp]
theorem logb_lt_logb_iff_of_base_lt_one (hx : 0 < x) (hy : 0 < y) : logb b x < logb b y ↔ y < x :=
  by
  rw [logb, logb, div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log_iff hy hx
#align real.logb_lt_logb_iff_of_base_lt_one Real.logb_lt_logb_iff_of_base_lt_one

/- warning: real.logb_le_iff_le_rpow_of_base_lt_one -> Real.logb_le_iff_le_rpow_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LE.le.{0} Real Real.hasLe (Real.logb b x) y) (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) b y) x))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.logb b x) y) (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) b y) x))
Case conversion may be inaccurate. Consider using '#align real.logb_le_iff_le_rpow_of_base_lt_one Real.logb_le_iff_le_rpow_of_base_lt_oneₓ'. -/
theorem logb_le_iff_le_rpow_of_base_lt_one (hx : 0 < x) : logb b x ≤ y ↔ b ^ y ≤ x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hx]
#align real.logb_le_iff_le_rpow_of_base_lt_one Real.logb_le_iff_le_rpow_of_base_lt_one

/- warning: real.logb_lt_iff_lt_rpow_of_base_lt_one -> Real.logb_lt_iff_lt_rpow_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.logb b x) y) (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) b y) x))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.logb b x) y) (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) b y) x))
Case conversion may be inaccurate. Consider using '#align real.logb_lt_iff_lt_rpow_of_base_lt_one Real.logb_lt_iff_lt_rpow_of_base_lt_oneₓ'. -/
theorem logb_lt_iff_lt_rpow_of_base_lt_one (hx : 0 < x) : logb b x < y ↔ b ^ y < x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hx]
#align real.logb_lt_iff_lt_rpow_of_base_lt_one Real.logb_lt_iff_lt_rpow_of_base_lt_one

/- warning: real.le_logb_iff_rpow_le_of_base_lt_one -> Real.le_logb_iff_rpow_le_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LE.le.{0} Real Real.hasLe x (Real.logb b y)) (LE.le.{0} Real Real.hasLe y (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) b x)))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LE.le.{0} Real Real.instLEReal x (Real.logb b y)) (LE.le.{0} Real Real.instLEReal y (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) b x)))
Case conversion may be inaccurate. Consider using '#align real.le_logb_iff_rpow_le_of_base_lt_one Real.le_logb_iff_rpow_le_of_base_lt_oneₓ'. -/
theorem le_logb_iff_rpow_le_of_base_lt_one (hy : 0 < y) : x ≤ logb b y ↔ y ≤ b ^ x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hy]
#align real.le_logb_iff_rpow_le_of_base_lt_one Real.le_logb_iff_rpow_le_of_base_lt_one

/- warning: real.lt_logb_iff_rpow_lt_of_base_lt_one -> Real.lt_logb_iff_rpow_lt_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LT.lt.{0} Real Real.hasLt x (Real.logb b y)) (LT.lt.{0} Real Real.hasLt y (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) b x)))
but is expected to have type
  forall {b : Real} {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LT.lt.{0} Real Real.instLTReal x (Real.logb b y)) (LT.lt.{0} Real Real.instLTReal y (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) b x)))
Case conversion may be inaccurate. Consider using '#align real.lt_logb_iff_rpow_lt_of_base_lt_one Real.lt_logb_iff_rpow_lt_of_base_lt_oneₓ'. -/
theorem lt_logb_iff_rpow_lt_of_base_lt_one (hy : 0 < y) : x < logb b y ↔ y < b ^ x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hy]
#align real.lt_logb_iff_rpow_lt_of_base_lt_one Real.lt_logb_iff_rpow_lt_of_base_lt_one

/- warning: real.logb_pos_iff_of_base_lt_one -> Real.logb_pos_iff_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.logb b x)) (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.logb b x)) (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.logb_pos_iff_of_base_lt_one Real.logb_pos_iff_of_base_lt_oneₓ'. -/
theorem logb_pos_iff_of_base_lt_one (hx : 0 < x) : 0 < logb b x ↔ x < 1 := by
  rw [← @logb_one b, logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one zero_lt_one hx]
#align real.logb_pos_iff_of_base_lt_one Real.logb_pos_iff_of_base_lt_one

/- warning: real.logb_pos_of_base_lt_one -> Real.logb_pos_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.logb b x))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.logb b x))
Case conversion may be inaccurate. Consider using '#align real.logb_pos_of_base_lt_one Real.logb_pos_of_base_lt_oneₓ'. -/
theorem logb_pos_of_base_lt_one (hx : 0 < x) (hx' : x < 1) : 0 < logb b x :=
  by
  rw [logb_pos_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'
#align real.logb_pos_of_base_lt_one Real.logb_pos_of_base_lt_one

/- warning: real.logb_neg_iff_of_base_lt_one -> Real.logb_neg_iff_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.logb b x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.logb b x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x))
Case conversion may be inaccurate. Consider using '#align real.logb_neg_iff_of_base_lt_one Real.logb_neg_iff_of_base_lt_oneₓ'. -/
theorem logb_neg_iff_of_base_lt_one (h : 0 < x) : logb b x < 0 ↔ 1 < x := by
  rw [← @logb_one b, logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one h zero_lt_one]
#align real.logb_neg_iff_of_base_lt_one Real.logb_neg_iff_of_base_lt_one

/- warning: real.logb_neg_of_base_lt_one -> Real.logb_neg_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (LT.lt.{0} Real Real.hasLt (Real.logb b x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (LT.lt.{0} Real Real.instLTReal (Real.logb b x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.logb_neg_of_base_lt_one Real.logb_neg_of_base_lt_oneₓ'. -/
theorem logb_neg_of_base_lt_one (h1 : 1 < x) : logb b x < 0 :=
  (logb_neg_iff_of_base_lt_one b_pos b_lt_one (lt_trans zero_lt_one h1)).2 h1
#align real.logb_neg_of_base_lt_one Real.logb_neg_of_base_lt_one

/- warning: real.logb_nonneg_iff_of_base_lt_one -> Real.logb_nonneg_iff_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.logb b x)) (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.logb b x)) (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.logb_nonneg_iff_of_base_lt_one Real.logb_nonneg_iff_of_base_lt_oneₓ'. -/
theorem logb_nonneg_iff_of_base_lt_one (hx : 0 < x) : 0 ≤ logb b x ↔ x ≤ 1 := by
  rw [← not_lt, logb_neg_iff_of_base_lt_one b_pos b_lt_one hx, not_lt]
#align real.logb_nonneg_iff_of_base_lt_one Real.logb_nonneg_iff_of_base_lt_one

/- warning: real.logb_nonneg_of_base_lt_one -> Real.logb_nonneg_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.logb b x))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.logb b x))
Case conversion may be inaccurate. Consider using '#align real.logb_nonneg_of_base_lt_one Real.logb_nonneg_of_base_lt_oneₓ'. -/
theorem logb_nonneg_of_base_lt_one (hx : 0 < x) (hx' : x ≤ 1) : 0 ≤ logb b x :=
  by
  rw [logb_nonneg_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'
#align real.logb_nonneg_of_base_lt_one Real.logb_nonneg_of_base_lt_one

/- warning: real.logb_nonpos_iff_of_base_lt_one -> Real.logb_nonpos_iff_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LE.le.{0} Real Real.hasLe (Real.logb b x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.logb b x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x))
Case conversion may be inaccurate. Consider using '#align real.logb_nonpos_iff_of_base_lt_one Real.logb_nonpos_iff_of_base_lt_oneₓ'. -/
theorem logb_nonpos_iff_of_base_lt_one (hx : 0 < x) : logb b x ≤ 0 ↔ 1 ≤ x := by
  rw [← not_lt, logb_pos_iff_of_base_lt_one b_pos b_lt_one hx, not_lt]
#align real.logb_nonpos_iff_of_base_lt_one Real.logb_nonpos_iff_of_base_lt_one

/- warning: real.strict_anti_on_logb_of_base_lt_one -> Real.strictAntiOn_logb_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (StrictAntiOn.{0, 0} Real Real Real.preorder Real.preorder (Real.logb b) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (StrictAntiOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal (Real.logb b) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.strict_anti_on_logb_of_base_lt_one Real.strictAntiOn_logb_of_base_lt_oneₓ'. -/
theorem strictAntiOn_logb_of_base_lt_one : StrictAntiOn (logb b) (Set.Ioi 0) := fun x hx y hy hxy =>
  logb_lt_logb_of_base_lt_one b_pos b_lt_one hx hxy
#align real.strict_anti_on_logb_of_base_lt_one Real.strictAntiOn_logb_of_base_lt_one

/- warning: real.strict_mono_on_logb_of_base_lt_one -> Real.strictMonoOn_logb_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (StrictMonoOn.{0, 0} Real Real Real.preorder Real.preorder (Real.logb b) (Set.Iio.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (StrictMonoOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal (Real.logb b) (Set.Iio.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.strict_mono_on_logb_of_base_lt_one Real.strictMonoOn_logb_of_base_lt_oneₓ'. -/
theorem strictMonoOn_logb_of_base_lt_one : StrictMonoOn (logb b) (Set.Iio 0) :=
  by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs y, ← logb_abs x]
  refine' logb_lt_logb_of_base_lt_one b_pos b_lt_one (abs_pos.2 hy.ne) _
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]
#align real.strict_mono_on_logb_of_base_lt_one Real.strictMonoOn_logb_of_base_lt_one

/- warning: real.logb_inj_on_pos_of_base_lt_one -> Real.logb_injOn_pos_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Set.InjOn.{0, 0} Real Real (Real.logb b) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Set.InjOn.{0, 0} Real Real (Real.logb b) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.logb_inj_on_pos_of_base_lt_one Real.logb_injOn_pos_of_base_lt_oneₓ'. -/
theorem logb_injOn_pos_of_base_lt_one : Set.InjOn (logb b) (Set.Ioi 0) :=
  (strictAntiOn_logb_of_base_lt_one b_pos b_lt_one).InjOn
#align real.logb_inj_on_pos_of_base_lt_one Real.logb_injOn_pos_of_base_lt_one

/- warning: real.eq_one_of_pos_of_logb_eq_zero_of_base_lt_one -> Real.eq_one_of_pos_of_logb_eq_zero_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Real.logb b x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Real.logb b x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.eq_one_of_pos_of_logb_eq_zero_of_base_lt_one Real.eq_one_of_pos_of_logb_eq_zero_of_base_lt_oneₓ'. -/
theorem eq_one_of_pos_of_logb_eq_zero_of_base_lt_one (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 :=
  logb_injOn_pos_of_base_lt_one b_pos b_lt_one (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one)
    (h₂.trans Real.logb_one.symm)
#align real.eq_one_of_pos_of_logb_eq_zero_of_base_lt_one Real.eq_one_of_pos_of_logb_eq_zero_of_base_lt_one

/- warning: real.logb_ne_zero_of_pos_of_ne_one_of_base_lt_one -> Real.logb_ne_zero_of_pos_of_ne_one_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Ne.{1} Real (Real.logb b x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {b : Real} {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Ne.{1} Real (Real.logb b x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.logb_ne_zero_of_pos_of_ne_one_of_base_lt_one Real.logb_ne_zero_of_pos_of_ne_one_of_base_lt_oneₓ'. -/
theorem logb_ne_zero_of_pos_of_ne_one_of_base_lt_one (hx_pos : 0 < x) (hx : x ≠ 1) : logb b x ≠ 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero_of_base_lt_one b_pos b_lt_one hx_pos) hx
#align real.logb_ne_zero_of_pos_of_ne_one_of_base_lt_one Real.logb_ne_zero_of_pos_of_ne_one_of_base_lt_one

/- warning: real.tendsto_logb_at_top_of_base_lt_one -> Real.tendsto_logb_atTop_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Filter.Tendsto.{0, 0} Real Real (Real.logb b) (Filter.atTop.{0} Real Real.preorder) (Filter.atBot.{0} Real Real.preorder))
but is expected to have type
  forall {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Filter.Tendsto.{0, 0} Real Real (Real.logb b) (Filter.atTop.{0} Real Real.instPreorderReal) (Filter.atBot.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align real.tendsto_logb_at_top_of_base_lt_one Real.tendsto_logb_atTop_of_base_lt_oneₓ'. -/
theorem tendsto_logb_atTop_of_base_lt_one : Tendsto (logb b) atTop atBot :=
  by
  rw [tendsto_at_top_at_bot]
  intro e
  use 1 ⊔ b ^ e
  intro a
  simp only [and_imp, sup_le_iff]
  intro ha
  rw [logb_le_iff_le_rpow_of_base_lt_one b_pos b_lt_one]
  tauto
  exact lt_of_lt_of_le zero_lt_one ha
#align real.tendsto_logb_at_top_of_base_lt_one Real.tendsto_logb_atTop_of_base_lt_one

end BPosAndBLtOne

/- warning: real.floor_logb_nat_cast -> Real.floor_logb_nat_cast is a dubious translation:
lean 3 declaration is
  forall {b : Nat} {r : Real}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) b) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Eq.{1} Int (Int.floor.{0} Real Real.linearOrderedRing Real.floorRing (Real.logb ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) b) r)) (Int.log.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.linearOrderedField) (FloorRing.toFloorSemiring.{0} Real Real.linearOrderedRing Real.floorRing) b r))
but is expected to have type
  forall {b : Nat} {r : Real}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) b) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Eq.{1} Int (Int.floor.{0} Real Real.instLinearOrderedRingReal Real.instFloorRingRealInstLinearOrderedRingReal (Real.logb (Nat.cast.{0} Real Real.natCast b) r)) (Int.log.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.instLinearOrderedFieldReal) (FloorRing.toFloorSemiring.{0} Real (LinearOrderedCommRing.toLinearOrderedRing.{0} Real (LinearOrderedField.toLinearOrderedCommRing.{0} Real Real.instLinearOrderedFieldReal)) Real.instFloorRingRealInstLinearOrderedRingReal) b r))
Case conversion may be inaccurate. Consider using '#align real.floor_logb_nat_cast Real.floor_logb_nat_castₓ'. -/
theorem floor_logb_nat_cast {b : ℕ} {r : ℝ} (hb : 1 < b) (hr : 0 ≤ r) : ⌊logb b r⌋ = Int.log b r :=
  by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.log_zero_right, Int.floor_zero]
  have hb1' : 1 < (b : ℝ) := nat.one_lt_cast.mpr hb
  apply le_antisymm
  · rw [← Int.zpow_le_iff_le_log hb hr, ← rpow_int_cast b]
    refine' le_of_le_of_eq _ (rpow_logb (zero_lt_one.trans hb1') hb1'.ne' hr)
    exact rpow_le_rpow_of_exponent_le hb1'.le (Int.floor_le _)
  · rw [Int.le_floor, le_logb_iff_rpow_le hb1' hr, rpow_int_cast]
    exact Int.zpow_log_le_self hb hr
#align real.floor_logb_nat_cast Real.floor_logb_nat_cast

/- warning: real.ceil_logb_nat_cast -> Real.ceil_logb_nat_cast is a dubious translation:
lean 3 declaration is
  forall {b : Nat} {r : Real}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) b) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Eq.{1} Int (Int.ceil.{0} Real Real.linearOrderedRing Real.floorRing (Real.logb ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) b) r)) (Int.clog.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.linearOrderedField) (FloorRing.toFloorSemiring.{0} Real Real.linearOrderedRing Real.floorRing) b r))
but is expected to have type
  forall {b : Nat} {r : Real}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) b) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Eq.{1} Int (Int.ceil.{0} Real Real.instLinearOrderedRingReal Real.instFloorRingRealInstLinearOrderedRingReal (Real.logb (Nat.cast.{0} Real Real.natCast b) r)) (Int.clog.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.instLinearOrderedFieldReal) (FloorRing.toFloorSemiring.{0} Real (LinearOrderedCommRing.toLinearOrderedRing.{0} Real (LinearOrderedField.toLinearOrderedCommRing.{0} Real Real.instLinearOrderedFieldReal)) Real.instFloorRingRealInstLinearOrderedRingReal) b r))
Case conversion may be inaccurate. Consider using '#align real.ceil_logb_nat_cast Real.ceil_logb_nat_castₓ'. -/
theorem ceil_logb_nat_cast {b : ℕ} {r : ℝ} (hb : 1 < b) (hr : 0 ≤ r) : ⌈logb b r⌉ = Int.clog b r :=
  by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.clog_zero_right, Int.ceil_zero]
  have hb1' : 1 < (b : ℝ) := nat.one_lt_cast.mpr hb
  apply le_antisymm
  · rw [Int.ceil_le, logb_le_iff_le_rpow hb1' hr, rpow_int_cast]
    refine' Int.self_le_zpow_clog hb r
  · rw [← Int.le_zpow_iff_clog_le hb hr, ← rpow_int_cast b]
    refine' (rpow_logb (zero_lt_one.trans hb1') hb1'.ne' hr).symm.trans_le _
    exact rpow_le_rpow_of_exponent_le hb1'.le (Int.le_ceil _)
#align real.ceil_logb_nat_cast Real.ceil_logb_nat_cast

/- warning: real.logb_eq_zero -> Real.logb_eq_zero is a dubious translation:
lean 3 declaration is
  forall {b : Real} {x : Real}, Iff (Eq.{1} Real (Real.logb b x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Or (Eq.{1} Real b (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Or (Eq.{1} Real b (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Or (Eq.{1} Real b (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Or (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Or (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Eq.{1} Real x (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))))))))
but is expected to have type
  forall {b : Real} {x : Real}, Iff (Eq.{1} Real (Real.logb b x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Or (Eq.{1} Real b (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Or (Eq.{1} Real b (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Or (Eq.{1} Real b (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Or (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Or (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Eq.{1} Real x (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))))))))
Case conversion may be inaccurate. Consider using '#align real.logb_eq_zero Real.logb_eq_zeroₓ'. -/
@[simp]
theorem logb_eq_zero : logb b x = 0 ↔ b = 0 ∨ b = 1 ∨ b = -1 ∨ x = 0 ∨ x = 1 ∨ x = -1 :=
  by
  simp_rw [logb, div_eq_zero_iff, log_eq_zero]
  tauto
#align real.logb_eq_zero Real.logb_eq_zero

-- TODO add other limits and continuous API lemmas analogous to those in log.lean
open BigOperators

/- warning: real.logb_prod -> Real.logb_prod is a dubious translation:
lean 3 declaration is
  forall {b : Real} {α : Type.{u1}} (s : Finset.{u1} α) (f : α -> Real), (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Eq.{1} Real (Real.logb b (Finset.prod.{0, u1} Real α Real.commMonoid s (fun (i : α) => f i))) (Finset.sum.{0, u1} Real α Real.addCommMonoid s (fun (i : α) => Real.logb b (f i))))
but is expected to have type
  forall {b : Real} {α : Type.{u1}} (s : Finset.{u1} α) (f : α -> Real), (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) -> (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Eq.{1} Real (Real.logb b (Finset.prod.{0, u1} Real α Real.instCommMonoidReal s (fun (i : α) => f i))) (Finset.sum.{0, u1} Real α Real.instAddCommMonoidReal s (fun (i : α) => Real.logb b (f i))))
Case conversion may be inaccurate. Consider using '#align real.logb_prod Real.logb_prodₓ'. -/
theorem logb_prod {α : Type _} (s : Finset α) (f : α → ℝ) (hf : ∀ x ∈ s, f x ≠ 0) :
    logb b (∏ i in s, f i) = ∑ i in s, logb b (f i) := by
  classical
    induction' s using Finset.induction_on with a s ha ih
    · simp
    simp only [Finset.mem_insert, forall_eq_or_imp] at hf
    simp [ha, ih hf.2, logb_mul hf.1 (Finset.prod_ne_zero_iff.2 hf.2)]
#align real.logb_prod Real.logb_prod

end Real

