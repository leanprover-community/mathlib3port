/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler

! This file was ported from Lean 3 source module analysis.special_functions.pow.real
! leanprover-community/mathlib commit 1b0a28e1c93409dbf6d69526863cd9984ef652ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Pow.Complex

/-! # Power function on `ℝ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct the power functions `x ^ y`, where `x` and `y` are real numbers.
-/


noncomputable section

open Classical Real BigOperators ComplexConjugate

open Finset Set

/-
## Definitions
-/
namespace Real

#print Real.rpow /-
/-- The real power function `x ^ y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`, one sets `0 ^ 0=1` and `0 ^ y=0` for
`y ≠ 0`. For `x < 0`, the definition is somewhat arbitary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log x) cos (π y)`. -/
noncomputable def rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re
#align real.rpow Real.rpow
-/

noncomputable instance : Pow ℝ ℝ :=
  ⟨rpow⟩

#print Real.rpow_eq_pow /-
@[simp]
theorem rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y :=
  rfl
#align real.rpow_eq_pow Real.rpow_eq_pow
-/

#print Real.rpow_def /-
theorem rpow_def (x y : ℝ) : x ^ y = ((x : ℂ) ^ (y : ℂ)).re :=
  rfl
#align real.rpow_def Real.rpow_def
-/

/- warning: real.rpow_def_of_nonneg -> Real.rpow_def_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (ite.{1} Real (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Real.decidableEq x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (ite.{1} Real (Eq.{1} Real y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Real.decidableEq y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.log x) y))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (ite.{1} Real (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Real.decidableEq x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (ite.{1} Real (Eq.{1} Real y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Real.decidableEq y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.log x) y))))
Case conversion may be inaccurate. Consider using '#align real.rpow_def_of_nonneg Real.rpow_def_of_nonnegₓ'. -/
theorem rpow_def_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) := by
  simp only [rpow_def, Complex.cpow_def] <;> split_ifs <;>
    simp_all [(Complex.of_real_log hx).symm, -Complex.ofReal_mul, -IsROrC.ofReal_mul,
      (Complex.ofReal_mul _ _).symm, Complex.exp_ofReal_re]
#align real.rpow_def_of_nonneg Real.rpow_def_of_nonneg

/- warning: real.rpow_def_of_pos -> Real.rpow_def_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.log x) y)))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.log x) y)))
Case conversion may be inaccurate. Consider using '#align real.rpow_def_of_pos Real.rpow_def_of_posₓ'. -/
theorem rpow_def_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y = exp (log x * y) := by
  rw [rpow_def_of_nonneg (le_of_lt hx), if_neg (ne_of_gt hx)]
#align real.rpow_def_of_pos Real.rpow_def_of_pos

/- warning: real.exp_mul -> Real.exp_mul is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} Real (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Real.exp x) y)
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} Real (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Real.exp x) y)
Case conversion may be inaccurate. Consider using '#align real.exp_mul Real.exp_mulₓ'. -/
theorem exp_mul (x y : ℝ) : exp (x * y) = exp x ^ y := by rw [rpow_def_of_pos (exp_pos _), log_exp]
#align real.exp_mul Real.exp_mul

#print Real.exp_one_rpow /-
@[simp]
theorem exp_one_rpow (x : ℝ) : exp 1 ^ x = exp x := by rw [← exp_mul, one_mul]
#align real.exp_one_rpow Real.exp_one_rpow
-/

/- warning: real.rpow_eq_zero_iff_of_nonneg -> Real.rpow_eq_zero_iff_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (And (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (And (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))))
Case conversion may be inaccurate. Consider using '#align real.rpow_eq_zero_iff_of_nonneg Real.rpow_eq_zero_iff_of_nonnegₓ'. -/
theorem rpow_eq_zero_iff_of_nonneg {x y : ℝ} (hx : 0 ≤ x) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
  by
  simp only [rpow_def_of_nonneg hx]
  split_ifs <;> simp [*, exp_ne_zero]
#align real.rpow_eq_zero_iff_of_nonneg Real.rpow_eq_zero_iff_of_nonneg

open Real

/- warning: real.rpow_def_of_neg -> Real.rpow_def_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.log x) y)) (Real.cos (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) y Real.pi))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.log x) y)) (Real.cos (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) y Real.pi))))
Case conversion may be inaccurate. Consider using '#align real.rpow_def_of_neg Real.rpow_def_of_negₓ'. -/
theorem rpow_def_of_neg {x : ℝ} (hx : x < 0) (y : ℝ) : x ^ y = exp (log x * y) * cos (y * π) :=
  by
  rw [rpow_def, Complex.cpow_def, if_neg]
  have : Complex.log x * y = ↑(log (-x) * y) + ↑(y * π) * Complex.I :=
    by
    simp only [Complex.log, abs_of_neg hx, Complex.arg_of_real_of_neg hx, Complex.abs_ofReal,
      Complex.ofReal_mul]
    ring
  · rw [this, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos, ←
      Complex.ofReal_sin, mul_add, ← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Real.log_neg_eq_log]
    ring
  · rw [Complex.ofReal_eq_zero]
    exact ne_of_lt hx
#align real.rpow_def_of_neg Real.rpow_def_of_neg

/- warning: real.rpow_def_of_nonpos -> Real.rpow_def_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (ite.{1} Real (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Real.decidableEq x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (ite.{1} Real (Eq.{1} Real y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Real.decidableEq y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.log x) y)) (Real.cos (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) y Real.pi)))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (ite.{1} Real (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Real.decidableEq x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (ite.{1} Real (Eq.{1} Real y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Real.decidableEq y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.log x) y)) (Real.cos (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) y Real.pi)))))
Case conversion may be inaccurate. Consider using '#align real.rpow_def_of_nonpos Real.rpow_def_of_nonposₓ'. -/
theorem rpow_def_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℝ) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) * cos (y * π) := by
  split_ifs <;> simp [rpow_def, *] <;> exact rpow_def_of_neg (lt_of_le_of_ne hx h) _
#align real.rpow_def_of_nonpos Real.rpow_def_of_nonpos

/- warning: real.rpow_pos_of_pos -> Real.rpow_pos_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real), LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real), LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y))
Case conversion may be inaccurate. Consider using '#align real.rpow_pos_of_pos Real.rpow_pos_of_posₓ'. -/
theorem rpow_pos_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y := by
  rw [rpow_def_of_pos hx] <;> apply exp_pos
#align real.rpow_pos_of_pos Real.rpow_pos_of_pos

/- warning: real.rpow_zero -> Real.rpow_zero is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.rpow_zero Real.rpow_zeroₓ'. -/
@[simp]
theorem rpow_zero (x : ℝ) : x ^ (0 : ℝ) = 1 := by simp [rpow_def]
#align real.rpow_zero Real.rpow_zero

/- warning: real.zero_rpow -> Real.zero_rpow is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.zero_rpow Real.zero_rpowₓ'. -/
@[simp]
theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ) ^ x = 0 := by simp [rpow_def, *]
#align real.zero_rpow Real.zero_rpow

#print Real.zero_rpow_eq_iff /-
theorem zero_rpow_eq_iff {x : ℝ} {a : ℝ} : 0 ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 :=
  by
  constructor
  · intro hyp
    simp only [rpow_def, Complex.ofReal_zero] at hyp
    by_cases x = 0
    · subst h
      simp only [Complex.one_re, Complex.ofReal_zero, Complex.cpow_zero] at hyp
      exact Or.inr ⟨rfl, hyp.symm⟩
    · rw [Complex.zero_cpow (complex.of_real_ne_zero.mpr h)] at hyp
      exact Or.inl ⟨h, hyp.symm⟩
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_rpow h
    · exact rpow_zero _
#align real.zero_rpow_eq_iff Real.zero_rpow_eq_iff
-/

#print Real.eq_zero_rpow_iff /-
theorem eq_zero_rpow_iff {x : ℝ} {a : ℝ} : a = 0 ^ x ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_rpow_eq_iff, eq_comm]
#align real.eq_zero_rpow_iff Real.eq_zero_rpow_iff
-/

/- warning: real.rpow_one -> Real.rpow_one is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) x
but is expected to have type
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x
Case conversion may be inaccurate. Consider using '#align real.rpow_one Real.rpow_oneₓ'. -/
@[simp]
theorem rpow_one (x : ℝ) : x ^ (1 : ℝ) = x := by simp [rpow_def]
#align real.rpow_one Real.rpow_one

#print Real.one_rpow /-
@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ) ^ x = 1 := by simp [rpow_def]
#align real.one_rpow Real.one_rpow
-/

/- warning: real.zero_rpow_le_one -> Real.zero_rpow_le_one is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.zero_rpow_le_one Real.zero_rpow_le_oneₓ'. -/
theorem zero_rpow_le_one (x : ℝ) : (0 : ℝ) ^ x ≤ 1 := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]
#align real.zero_rpow_le_one Real.zero_rpow_le_one

/- warning: real.zero_rpow_nonneg -> Real.zero_rpow_nonneg is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)
Case conversion may be inaccurate. Consider using '#align real.zero_rpow_nonneg Real.zero_rpow_nonnegₓ'. -/
theorem zero_rpow_nonneg (x : ℝ) : 0 ≤ (0 : ℝ) ^ x := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]
#align real.zero_rpow_nonneg Real.zero_rpow_nonneg

/- warning: real.rpow_nonneg_of_nonneg -> Real.rpow_nonneg_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y))
Case conversion may be inaccurate. Consider using '#align real.rpow_nonneg_of_nonneg Real.rpow_nonneg_of_nonnegₓ'. -/
theorem rpow_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := by
  rw [rpow_def_of_nonneg hx] <;> split_ifs <;>
    simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]
#align real.rpow_nonneg_of_nonneg Real.rpow_nonneg_of_nonneg

/- warning: real.abs_rpow_of_nonneg -> Real.abs_rpow_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) y))
Case conversion may be inaccurate. Consider using '#align real.abs_rpow_of_nonneg Real.abs_rpow_of_nonnegₓ'. -/
theorem abs_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : |x ^ y| = |x| ^ y :=
  by
  have h_rpow_nonneg : 0 ≤ x ^ y := Real.rpow_nonneg_of_nonneg hx_nonneg _
  rw [abs_eq_self.mpr hx_nonneg, abs_eq_self.mpr h_rpow_nonneg]
#align real.abs_rpow_of_nonneg Real.abs_rpow_of_nonneg

/- warning: real.abs_rpow_le_abs_rpow -> Real.abs_rpow_le_abs_rpow is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) y)
but is expected to have type
  forall (x : Real) (y : Real), LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) y)
Case conversion may be inaccurate. Consider using '#align real.abs_rpow_le_abs_rpow Real.abs_rpow_le_abs_rpowₓ'. -/
theorem abs_rpow_le_abs_rpow (x y : ℝ) : |x ^ y| ≤ |x| ^ y :=
  by
  cases' le_or_lt 0 x with hx hx
  · rw [abs_rpow_of_nonneg hx]
  · rw [abs_of_neg hx, rpow_def_of_neg hx, rpow_def_of_pos (neg_pos.2 hx), log_neg_eq_log, abs_mul,
      abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)
#align real.abs_rpow_le_abs_rpow Real.abs_rpow_le_abs_rpow

/- warning: real.abs_rpow_le_exp_log_mul -> Real.abs_rpow_le_exp_log_mul is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y)) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.log x) y))
but is expected to have type
  forall (x : Real) (y : Real), LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y)) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.log x) y))
Case conversion may be inaccurate. Consider using '#align real.abs_rpow_le_exp_log_mul Real.abs_rpow_le_exp_log_mulₓ'. -/
theorem abs_rpow_le_exp_log_mul (x y : ℝ) : |x ^ y| ≤ exp (log x * y) :=
  by
  refine' (abs_rpow_le_abs_rpow x y).trans _
  by_cases hx : x = 0
  · by_cases hy : y = 0 <;> simp [hx, hy, zero_le_one]
  · rw [rpow_def_of_pos (abs_pos.2 hx), log_abs]
#align real.abs_rpow_le_exp_log_mul Real.abs_rpow_le_exp_log_mul

/- warning: real.norm_rpow_of_nonneg -> Real.norm_rpow_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Norm.norm.{0} Real Real.hasNorm (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Norm.norm.{0} Real Real.hasNorm x) y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Norm.norm.{0} Real Real.norm (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Norm.norm.{0} Real Real.norm x) y))
Case conversion may be inaccurate. Consider using '#align real.norm_rpow_of_nonneg Real.norm_rpow_of_nonnegₓ'. -/
theorem norm_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : ‖x ^ y‖ = ‖x‖ ^ y :=
  by
  simp_rw [Real.norm_eq_abs]
  exact abs_rpow_of_nonneg hx_nonneg
#align real.norm_rpow_of_nonneg Real.norm_rpow_of_nonneg

variable {x y z : ℝ}

/- warning: real.rpow_add -> Real.rpow_add is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real) (z : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) y z)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z)))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real) (z : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) y z)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z)))
Case conversion may be inaccurate. Consider using '#align real.rpow_add Real.rpow_addₓ'. -/
theorem rpow_add (hx : 0 < x) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [rpow_def_of_pos hx, mul_add, exp_add]
#align real.rpow_add Real.rpow_add

/- warning: real.rpow_add' -> Real.rpow_add' is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Ne.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) y z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) y z)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z)))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Ne.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) y z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) y z)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z)))
Case conversion may be inaccurate. Consider using '#align real.rpow_add' Real.rpow_add'ₓ'. -/
theorem rpow_add' (hx : 0 ≤ x) (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
  by
  rcases hx.eq_or_lt with (rfl | pos)
  · rw [zero_rpow h, zero_eq_mul]
    have : y ≠ 0 ∨ z ≠ 0 := not_and_or.1 fun ⟨hy, hz⟩ => h <| hy.symm ▸ hz.symm ▸ zero_add 0
    exact this.imp zero_rpow zero_rpow
  · exact rpow_add Pos _ _
#align real.rpow_add' Real.rpow_add'

/- warning: real.rpow_add_of_nonneg -> Real.rpow_add_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) y z)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z)))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) y z)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z)))
Case conversion may be inaccurate. Consider using '#align real.rpow_add_of_nonneg Real.rpow_add_of_nonnegₓ'. -/
theorem rpow_add_of_nonneg (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : x ^ (y + z) = x ^ y * x ^ z :=
  by
  rcases hy.eq_or_lt with (rfl | hy)
  · rw [zero_add, rpow_zero, one_mul]
  exact rpow_add' hx (ne_of_gt <| add_pos_of_pos_of_nonneg hy hz)
#align real.rpow_add_of_nonneg Real.rpow_add_of_nonneg

/- warning: real.le_rpow_add -> Real.le_rpow_add is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real) (z : Real), LE.le.{0} Real Real.hasLe (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) y z)))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real) (z : Real), LE.le.{0} Real Real.instLEReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) y z)))
Case conversion may be inaccurate. Consider using '#align real.le_rpow_add Real.le_rpow_addₓ'. -/
/-- For `0 ≤ x`, the only problematic case in the equality `x ^ y * x ^ z = x ^ (y + z)` is for
`x = 0` and `y + z = 0`, where the right hand side is `1` while the left hand side can vanish.
The inequality is always true, though, and given in this lemma. -/
theorem le_rpow_add {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ y * x ^ z ≤ x ^ (y + z) :=
  by
  rcases le_iff_eq_or_lt.1 hx with (H | pos)
  · by_cases h : y + z = 0
    · simp only [H.symm, h, rpow_zero]
      calc
        (0 : ℝ) ^ y * 0 ^ z ≤ 1 * 1 :=
          mul_le_mul (zero_rpow_le_one y) (zero_rpow_le_one z) (zero_rpow_nonneg z) zero_le_one
        _ = 1 := by simp
        
    · simp [rpow_add', ← H, h]
  · simp [rpow_add Pos]
#align real.le_rpow_add Real.le_rpow_add

/- warning: real.rpow_sum_of_pos -> Real.rpow_sum_of_pos is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {a : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) a) -> (forall (f : ι -> Real) (s : Finset.{u1} ι), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) a (Finset.sum.{0, u1} Real ι Real.addCommMonoid s (fun (x : ι) => f x))) (Finset.prod.{0, u1} Real ι Real.commMonoid s (fun (x : ι) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) a (f x))))
but is expected to have type
  forall {ι : Type.{u1}} {a : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) a) -> (forall (f : ι -> Real) (s : Finset.{u1} ι), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) a (Finset.sum.{0, u1} Real ι Real.instAddCommMonoidReal s (fun (x : ι) => f x))) (Finset.prod.{0, u1} Real ι Real.instCommMonoidReal s (fun (x : ι) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) a (f x))))
Case conversion may be inaccurate. Consider using '#align real.rpow_sum_of_pos Real.rpow_sum_of_posₓ'. -/
theorem rpow_sum_of_pos {ι : Type _} {a : ℝ} (ha : 0 < a) (f : ι → ℝ) (s : Finset ι) :
    (a ^ ∑ x in s, f x) = ∏ x in s, a ^ f x :=
  @AddMonoidHom.map_sum ℝ ι (Additive ℝ) _ _ ⟨fun x : ℝ => (a ^ x : ℝ), rpow_zero a, rpow_add ha⟩ f
    s
#align real.rpow_sum_of_pos Real.rpow_sum_of_pos

/- warning: real.rpow_sum_of_nonneg -> Real.rpow_sum_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {a : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) a) -> (forall {s : Finset.{u1} ι} {f : ι -> Real}, (forall (x : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) x s) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f x))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) a (Finset.sum.{0, u1} Real ι Real.addCommMonoid s (fun (x : ι) => f x))) (Finset.prod.{0, u1} Real ι Real.commMonoid s (fun (x : ι) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) a (f x)))))
but is expected to have type
  forall {ι : Type.{u1}} {a : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) a) -> (forall {s : Finset.{u1} ι} {f : ι -> Real}, (forall (x : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f x))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) a (Finset.sum.{0, u1} Real ι Real.instAddCommMonoidReal s (fun (x : ι) => f x))) (Finset.prod.{0, u1} Real ι Real.instCommMonoidReal s (fun (x : ι) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) a (f x)))))
Case conversion may be inaccurate. Consider using '#align real.rpow_sum_of_nonneg Real.rpow_sum_of_nonnegₓ'. -/
theorem rpow_sum_of_nonneg {ι : Type _} {a : ℝ} (ha : 0 ≤ a) {s : Finset ι} {f : ι → ℝ}
    (h : ∀ x ∈ s, 0 ≤ f x) : (a ^ ∑ x in s, f x) = ∏ x in s, a ^ f x :=
  by
  induction' s using Finset.cons_induction with i s hi ihs
  · rw [sum_empty, Finset.prod_empty, rpow_zero]
  · rw [forall_mem_cons] at h
    rw [sum_cons, prod_cons, ← ihs h.2, rpow_add_of_nonneg ha h.1 (sum_nonneg h.2)]
#align real.rpow_sum_of_nonneg Real.rpow_sum_of_nonneg

/- warning: real.rpow_neg -> Real.rpow_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (Neg.neg.{0} Real Real.hasNeg y)) (Inv.inv.{0} Real Real.hasInv (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y)))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (Neg.neg.{0} Real Real.instNegReal y)) (Inv.inv.{0} Real Real.instInvReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y)))
Case conversion may be inaccurate. Consider using '#align real.rpow_neg Real.rpow_negₓ'. -/
theorem rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [rpow_def_of_nonneg hx] <;> split_ifs <;> simp_all [exp_neg]
#align real.rpow_neg Real.rpow_neg

/- warning: real.rpow_sub -> Real.rpow_sub is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real) (z : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y z)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z)))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real) (z : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y z)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z)))
Case conversion may be inaccurate. Consider using '#align real.rpow_sub Real.rpow_subₓ'. -/
theorem rpow_sub {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z := by
  simp only [sub_eq_add_neg, rpow_add hx, rpow_neg (le_of_lt hx), div_eq_mul_inv]
#align real.rpow_sub Real.rpow_sub

/- warning: real.rpow_sub' -> Real.rpow_sub' is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall {y : Real} {z : Real}, (Ne.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y z)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall {y : Real} {z : Real}, (Ne.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y z)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z))))
Case conversion may be inaccurate. Consider using '#align real.rpow_sub' Real.rpow_sub'ₓ'. -/
theorem rpow_sub' {x : ℝ} (hx : 0 ≤ x) {y z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z :=
  by
  simp only [sub_eq_add_neg] at h⊢
  simp only [rpow_add' hx h, rpow_neg hx, div_eq_mul_inv]
#align real.rpow_sub' Real.rpow_sub'

end Real

/-!
## Comparing real and complex powers
-/


namespace Complex

/- warning: complex.of_real_cpow -> Complex.of_real_cpow is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real), Eq.{1} Complex ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y)) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) y)))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real), Eq.{1} Complex (Complex.ofReal' (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y)) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Complex.ofReal' x) (Complex.ofReal' y)))
Case conversion may be inaccurate. Consider using '#align complex.of_real_cpow Complex.of_real_cpowₓ'. -/
theorem of_real_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : ((x ^ y : ℝ) : ℂ) = (x : ℂ) ^ (y : ℂ) := by
  simp only [Real.rpow_def_of_nonneg hx, Complex.cpow_def, of_real_eq_zero] <;> split_ifs <;>
    simp [Complex.of_real_log hx]
#align complex.of_real_cpow Complex.of_real_cpow

/- warning: complex.of_real_cpow_of_nonpos -> Complex.of_real_cpow_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (y : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x) y) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (Neg.neg.{0} Complex Complex.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x)) y) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi) Complex.I) y))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (y : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Complex.ofReal' x) y) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Neg.neg.{0} Complex Complex.instNegComplex (Complex.ofReal' x)) y) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' Real.pi) Complex.I) y))))
Case conversion may be inaccurate. Consider using '#align complex.of_real_cpow_of_nonpos Complex.of_real_cpow_of_nonposₓ'. -/
theorem of_real_cpow_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℂ) :
    (x : ℂ) ^ y = (-x : ℂ) ^ y * exp (π * I * y) :=
  by
  rcases hx.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne y 0 with (rfl | hy) <;> simp [*]
  have hne : (x : ℂ) ≠ 0 := of_real_ne_zero.mpr hlt.ne
  rw [cpow_def_of_ne_zero hne, cpow_def_of_ne_zero (neg_ne_zero.2 hne), ← exp_add, ← add_mul, log,
    log, abs.map_neg, arg_of_real_of_neg hlt, ← of_real_neg,
    arg_of_real_of_nonneg (neg_nonneg.2 hx), of_real_zero, MulZeroClass.zero_mul, add_zero]
#align complex.of_real_cpow_of_nonpos Complex.of_real_cpow_of_nonpos

/- warning: complex.abs_cpow_of_ne_zero -> Complex.abs_cpow_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, (Ne.{1} Complex z (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (forall (w : Complex), Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) z w)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs z) (Complex.re w)) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Complex.arg z) (Complex.im w)))))
but is expected to have type
  forall {z : Complex}, (Ne.{1} Complex z (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (forall (w : Complex), Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) z w)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) z w)) (HDiv.hDiv.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) (instHDiv.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) (LinearOrderedField.toDiv.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) (instHPow.{0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real Real.instPowReal) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs z) (Complex.re w)) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Complex.arg z) (Complex.im w)))))
Case conversion may be inaccurate. Consider using '#align complex.abs_cpow_of_ne_zero Complex.abs_cpow_of_ne_zeroₓ'. -/
theorem abs_cpow_of_ne_zero {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    abs (z ^ w) = abs z ^ w.re / Real.exp (arg z * im w) := by
  rw [cpow_def_of_ne_zero hz, abs_exp, mul_re, log_re, log_im, Real.exp_sub,
    Real.rpow_def_of_pos (abs.pos hz)]
#align complex.abs_cpow_of_ne_zero Complex.abs_cpow_of_ne_zero

/- warning: complex.abs_cpow_of_imp -> Complex.abs_cpow_of_imp is a dubious translation:
lean 3 declaration is
  forall {z : Complex} {w : Complex}, ((Eq.{1} Complex z (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Real (Complex.re w) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Complex w (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))))) -> (Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) z w)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs z) (Complex.re w)) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Complex.arg z) (Complex.im w)))))
but is expected to have type
  forall {z : Complex} {w : Complex}, ((Eq.{1} Complex z (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Real (Complex.re w) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Complex w (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)))) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) z w)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) z w)) (HDiv.hDiv.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) (instHDiv.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) (LinearOrderedField.toDiv.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) (instHPow.{0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real Real.instPowReal) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs z) (Complex.re w)) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Complex.arg z) (Complex.im w)))))
Case conversion may be inaccurate. Consider using '#align complex.abs_cpow_of_imp Complex.abs_cpow_of_impₓ'. -/
theorem abs_cpow_of_imp {z w : ℂ} (h : z = 0 → w.re = 0 → w = 0) :
    abs (z ^ w) = abs z ^ w.re / Real.exp (arg z * im w) :=
  by
  rcases ne_or_eq z 0 with (hz | rfl) <;> [exact abs_cpow_of_ne_zero hz w, rw [map_zero]]
  cases' eq_or_ne w.re 0 with hw hw
  · simp [hw, h rfl hw]
  · rw [Real.zero_rpow hw, zero_div, zero_cpow, map_zero]
    exact ne_of_apply_ne re hw
#align complex.abs_cpow_of_imp Complex.abs_cpow_of_imp

/- warning: complex.abs_cpow_le -> Complex.abs_cpow_le is a dubious translation:
lean 3 declaration is
  forall (z : Complex) (w : Complex), LE.le.{0} Real Real.hasLe (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) z w)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs z) (Complex.re w)) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Complex.arg z) (Complex.im w))))
but is expected to have type
  forall (z : Complex) (w : Complex), LE.le.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) z w)) Real.instLEReal (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) z w)) (HDiv.hDiv.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) (instHDiv.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) (LinearOrderedField.toDiv.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) (instHPow.{0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real Real.instPowReal) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs z) (Complex.re w)) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Complex.arg z) (Complex.im w))))
Case conversion may be inaccurate. Consider using '#align complex.abs_cpow_le Complex.abs_cpow_leₓ'. -/
theorem abs_cpow_le (z w : ℂ) : abs (z ^ w) ≤ abs z ^ w.re / Real.exp (arg z * im w) :=
  by
  rcases ne_or_eq z 0 with (hz | rfl) <;> [exact (abs_cpow_of_ne_zero hz w).le, rw [map_zero]]
  rcases eq_or_ne w 0 with (rfl | hw); · simp
  rw [zero_cpow hw, map_zero]
  exact div_nonneg (Real.rpow_nonneg_of_nonneg le_rfl _) (Real.exp_pos _).le
#align complex.abs_cpow_le Complex.abs_cpow_le

/- warning: complex.abs_cpow_real -> Complex.abs_cpow_real is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (y : Real), Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) y))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x) y)
but is expected to have type
  forall (x : Complex) (y : Real), Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (Complex.ofReal' y))) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (Complex.ofReal' y))) (HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (instHPow.{0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real Real.instPowReal) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x) y)
Case conversion may be inaccurate. Consider using '#align complex.abs_cpow_real Complex.abs_cpow_realₓ'. -/
@[simp]
theorem abs_cpow_real (x : ℂ) (y : ℝ) : abs (x ^ (y : ℂ)) = x.abs ^ y := by
  rcases eq_or_ne x 0 with (rfl | hx) <;> [rcases eq_or_ne y 0 with (rfl | hy), skip] <;>
    simp [*, abs_cpow_of_ne_zero]
#align complex.abs_cpow_real Complex.abs_cpow_real

/- warning: complex.abs_cpow_inv_nat -> Complex.abs_cpow_inv_nat is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (n : Nat), Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x (Inv.inv.{0} Complex Complex.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Complex (HasLiftT.mk.{1, 1} Nat Complex (CoeTCₓ.coe.{1, 1} Nat Complex (Nat.castCoe.{0} Complex (AddMonoidWithOne.toNatCast.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.addGroupWithOne))))) n)))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x) (Inv.inv.{0} Real Real.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)))
but is expected to have type
  forall (x : Complex) (n : Nat), Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (Inv.inv.{0} Complex Complex.instInvComplex (Nat.cast.{0} Complex (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) n)))) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (Inv.inv.{0} Complex Complex.instInvComplex (Nat.cast.{0} Complex (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) n)))) (HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (instHPow.{0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real Real.instPowReal) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x) (Inv.inv.{0} Real Real.instInvReal (Nat.cast.{0} Real Real.natCast n)))
Case conversion may be inaccurate. Consider using '#align complex.abs_cpow_inv_nat Complex.abs_cpow_inv_natₓ'. -/
@[simp]
theorem abs_cpow_inv_nat (x : ℂ) (n : ℕ) : abs (x ^ (n⁻¹ : ℂ)) = x.abs ^ (n⁻¹ : ℝ) := by
  rw [← abs_cpow_real] <;> simp [-abs_cpow_real]
#align complex.abs_cpow_inv_nat Complex.abs_cpow_inv_nat

/- warning: complex.abs_cpow_eq_rpow_re_of_pos -> Complex.abs_cpow_eq_rpow_re_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Complex), Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x) y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (Complex.re y)))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Complex), Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Complex.ofReal' x) y)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Complex.ofReal' x) y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (Complex.re y)))
Case conversion may be inaccurate. Consider using '#align complex.abs_cpow_eq_rpow_re_of_pos Complex.abs_cpow_eq_rpow_re_of_posₓ'. -/
theorem abs_cpow_eq_rpow_re_of_pos {x : ℝ} (hx : 0 < x) (y : ℂ) : abs (x ^ y) = x ^ y.re := by
  rw [abs_cpow_of_ne_zero (of_real_ne_zero.mpr hx.ne'), arg_of_real_of_nonneg hx.le,
    MulZeroClass.zero_mul, Real.exp_zero, div_one, abs_of_nonneg hx.le]
#align complex.abs_cpow_eq_rpow_re_of_pos Complex.abs_cpow_eq_rpow_re_of_pos

/- warning: complex.abs_cpow_eq_rpow_re_of_nonneg -> Complex.abs_cpow_eq_rpow_re_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall {y : Complex}, (Ne.{1} Real (Complex.re y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x) y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (Complex.re y))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall {y : Complex}, (Ne.{1} Real (Complex.re y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Complex.ofReal' x) y)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Complex.ofReal' x) y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (Complex.re y))))
Case conversion may be inaccurate. Consider using '#align complex.abs_cpow_eq_rpow_re_of_nonneg Complex.abs_cpow_eq_rpow_re_of_nonnegₓ'. -/
theorem abs_cpow_eq_rpow_re_of_nonneg {x : ℝ} (hx : 0 ≤ x) {y : ℂ} (hy : re y ≠ 0) :
    abs (x ^ y) = x ^ re y := by
  rcases hx.eq_or_lt with (rfl | hlt)
  · rw [of_real_zero, zero_cpow, map_zero, Real.zero_rpow hy]
    exact ne_of_apply_ne re hy
  · exact abs_cpow_eq_rpow_re_of_pos hlt y
#align complex.abs_cpow_eq_rpow_re_of_nonneg Complex.abs_cpow_eq_rpow_re_of_nonneg

end Complex

/-!
## Further algebraic properties of `rpow`
-/


namespace Real

variable {x y z : ℝ}

/- warning: real.rpow_mul -> Real.rpow_mul is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real) (z : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) y z)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) z))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real) (z : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) y z)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) z))
Case conversion may be inaccurate. Consider using '#align real.rpow_mul Real.rpow_mulₓ'. -/
theorem rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
  rw [← Complex.ofReal_inj, Complex.of_real_cpow (rpow_nonneg_of_nonneg hx _),
      Complex.of_real_cpow hx, Complex.ofReal_mul, Complex.cpow_mul, Complex.of_real_cpow hx] <;>
    simp only [(Complex.ofReal_mul _ _).symm, (Complex.of_real_log hx).symm, Complex.ofReal_im,
      neg_lt_zero, pi_pos, le_of_lt pi_pos]
#align real.rpow_mul Real.rpow_mul

/- warning: real.rpow_add_int -> Real.rpow_add_int is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (y : Real) (n : Int), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) y ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) n))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x n)))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (y : Real) (n : Int), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) y (Int.cast.{0} Real Real.intCast n))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) x n)))
Case conversion may be inaccurate. Consider using '#align real.rpow_add_int Real.rpow_add_intₓ'. -/
theorem rpow_add_int {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y + n) = x ^ y * x ^ n := by
  rw [rpow_def, Complex.ofReal_add, Complex.cpow_add _ _ (complex.of_real_ne_zero.mpr hx),
    Complex.ofReal_int_cast, Complex.cpow_int_cast, ← Complex.ofReal_zpow, mul_comm,
    Complex.ofReal_mul_re, ← rpow_def, mul_comm]
#align real.rpow_add_int Real.rpow_add_int

/- warning: real.rpow_add_nat -> Real.rpow_add_nat is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (y : Real) (n : Nat), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) y ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n)))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (y : Real) (n : Nat), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) y (Nat.cast.{0} Real Real.natCast n))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n)))
Case conversion may be inaccurate. Consider using '#align real.rpow_add_nat Real.rpow_add_natₓ'. -/
theorem rpow_add_nat {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y + n) = x ^ y * x ^ n := by
  simpa using rpow_add_int hx y n
#align real.rpow_add_nat Real.rpow_add_nat

/- warning: real.rpow_sub_int -> Real.rpow_sub_int is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (y : Real) (n : Int), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) n))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x n)))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (y : Real) (n : Nat), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y (Nat.cast.{0} Real Real.natCast n))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n)))
Case conversion may be inaccurate. Consider using '#align real.rpow_sub_int Real.rpow_sub_intₓ'. -/
theorem rpow_sub_int {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y - n) = x ^ y / x ^ n := by
  simpa using rpow_add_int hx y (-n)
#align real.rpow_sub_int Real.rpow_sub_int

/- warning: real.rpow_sub_nat -> Real.rpow_sub_nat is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (y : Real) (n : Nat), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n)))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (y : Real) (n : Nat), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y (Nat.cast.{0} Real Real.natCast n))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n)))
Case conversion may be inaccurate. Consider using '#align real.rpow_sub_nat Real.rpow_sub_natₓ'. -/
theorem rpow_sub_nat {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n := by
  simpa using rpow_sub_int hx y n
#align real.rpow_sub_nat Real.rpow_sub_nat

/- warning: real.rpow_add_one -> Real.rpow_add_one is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) y (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) x))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) y (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) x))
Case conversion may be inaccurate. Consider using '#align real.rpow_add_one Real.rpow_add_oneₓ'. -/
theorem rpow_add_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y + 1) = x ^ y * x := by
  simpa using rpow_add_nat hx y 1
#align real.rpow_add_one Real.rpow_add_one

/- warning: real.rpow_sub_one -> Real.rpow_sub_one is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) x))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) x))
Case conversion may be inaccurate. Consider using '#align real.rpow_sub_one Real.rpow_sub_oneₓ'. -/
theorem rpow_sub_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y - 1) = x ^ y / x := by
  simpa using rpow_sub_nat hx y 1
#align real.rpow_sub_one Real.rpow_sub_one

/- warning: real.rpow_int_cast -> Real.rpow_int_cast is a dubious translation:
lean 3 declaration is
  forall (x : Real) (n : Int), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) n)) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x n)
but is expected to have type
  forall (x : Real) (n : Int), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (Int.cast.{0} Real Real.intCast n)) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) x n)
Case conversion may be inaccurate. Consider using '#align real.rpow_int_cast Real.rpow_int_castₓ'. -/
@[simp, norm_cast]
theorem rpow_int_cast (x : ℝ) (n : ℤ) : x ^ (n : ℝ) = x ^ n := by
  simp only [rpow_def, ← Complex.ofReal_zpow, Complex.cpow_int_cast, Complex.ofReal_int_cast,
    Complex.ofReal_re]
#align real.rpow_int_cast Real.rpow_int_cast

/- warning: real.rpow_nat_cast -> Real.rpow_nat_cast is a dubious translation:
lean 3 declaration is
  forall (x : Real) (n : Nat), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n)
but is expected to have type
  forall (x : Real) (n : Nat), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (Nat.cast.{0} Real Real.natCast n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n)
Case conversion may be inaccurate. Consider using '#align real.rpow_nat_cast Real.rpow_nat_castₓ'. -/
@[simp, norm_cast]
theorem rpow_nat_cast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n := by simpa using rpow_int_cast x n
#align real.rpow_nat_cast Real.rpow_nat_cast

/- warning: real.rpow_two -> Real.rpow_two is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align real.rpow_two Real.rpow_twoₓ'. -/
@[simp]
theorem rpow_two (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 :=
  by
  rw [← rpow_nat_cast]
  simp only [Nat.cast_bit0, Nat.cast_one]
#align real.rpow_two Real.rpow_two

/- warning: real.rpow_neg_one -> Real.rpow_neg_one is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Inv.inv.{0} Real Real.hasInv x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Inv.inv.{0} Real Real.instInvReal x)
Case conversion may be inaccurate. Consider using '#align real.rpow_neg_one Real.rpow_neg_oneₓ'. -/
theorem rpow_neg_one (x : ℝ) : x ^ (-1 : ℝ) = x⁻¹ :=
  by
  suffices H : x ^ ((-1 : ℤ) : ℝ) = x⁻¹; · rwa [Int.cast_neg, Int.cast_one] at H
  simp only [rpow_int_cast, zpow_one, zpow_neg]
#align real.rpow_neg_one Real.rpow_neg_one

/- warning: real.mul_rpow -> Real.mul_rpow is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x y) z) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y z)))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x y) z) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y z)))
Case conversion may be inaccurate. Consider using '#align real.mul_rpow Real.mul_rpowₓ'. -/
theorem mul_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : 0 ≤ y) : (x * y) ^ z = x ^ z * y ^ z :=
  by
  iterate 3 rw [Real.rpow_def_of_nonneg]; split_ifs <;> simp_all
  · have hx : 0 < x := by
      cases' lt_or_eq_of_le h with h₂ h₂
      · exact h₂
      exfalso
      apply h_2
      exact Eq.symm h₂
    have hy : 0 < y := by
      cases' lt_or_eq_of_le h₁ with h₂ h₂
      · exact h₂
      exfalso
      apply h_3
      exact Eq.symm h₂
    rw [log_mul (ne_of_gt hx) (ne_of_gt hy), add_mul, exp_add]
  · exact h₁
  · exact h
  · exact mul_nonneg h h₁
#align real.mul_rpow Real.mul_rpow

/- warning: real.inv_rpow -> Real.inv_rpow is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Inv.inv.{0} Real Real.hasInv x) y) (Inv.inv.{0} Real Real.hasInv (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y)))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Inv.inv.{0} Real Real.instInvReal x) y) (Inv.inv.{0} Real Real.instInvReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y)))
Case conversion may be inaccurate. Consider using '#align real.inv_rpow Real.inv_rpowₓ'. -/
theorem inv_rpow (hx : 0 ≤ x) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ := by
  simp only [← rpow_neg_one, ← rpow_mul hx, mul_comm]
#align real.inv_rpow Real.inv_rpow

/- warning: real.div_rpow -> Real.div_rpow is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (forall (z : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x y) z) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y z)))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (forall (z : Real), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x y) z) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y z)))
Case conversion may be inaccurate. Consider using '#align real.div_rpow Real.div_rpowₓ'. -/
theorem div_rpow (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z := by
  simp only [div_eq_mul_inv, mul_rpow hx (inv_nonneg.2 hy), inv_rpow hy]
#align real.div_rpow Real.div_rpow

/- warning: real.log_rpow -> Real.log_rpow is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real), Eq.{1} Real (Real.log (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) y (Real.log x)))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real), Eq.{1} Real (Real.log (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) y (Real.log x)))
Case conversion may be inaccurate. Consider using '#align real.log_rpow Real.log_rpowₓ'. -/
theorem log_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : log (x ^ y) = y * log x :=
  by
  apply exp_injective
  rw [exp_log (rpow_pos_of_pos hx y), ← exp_log hx, mul_comm, rpow_def_of_pos (exp_pos (log x)) y]
#align real.log_rpow Real.log_rpow

/-!
## Order and monotonicity
-/


/- warning: real.rpow_lt_rpow -> Real.rpow_lt_rpow is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x y) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y z))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x y) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y z))
Case conversion may be inaccurate. Consider using '#align real.rpow_lt_rpow Real.rpow_lt_rpowₓ'. -/
theorem rpow_lt_rpow (hx : 0 ≤ x) (hxy : x < y) (hz : 0 < z) : x ^ z < y ^ z :=
  by
  rw [le_iff_eq_or_lt] at hx; cases hx
  · rw [← hx, zero_rpow (ne_of_gt hz)]
    exact rpow_pos_of_pos (by rwa [← hx] at hxy) _
  rw [rpow_def_of_pos hx, rpow_def_of_pos (lt_trans hx hxy), exp_lt_exp]
  exact mul_lt_mul_of_pos_right (log_lt_log hx hxy) hz
#align real.rpow_lt_rpow Real.rpow_lt_rpow

/- warning: real.rpow_le_rpow -> Real.rpow_le_rpow is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x y) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y z))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x y) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y z))
Case conversion may be inaccurate. Consider using '#align real.rpow_le_rpow Real.rpow_le_rpowₓ'. -/
theorem rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  by
  rcases eq_or_lt_of_le h₁ with (rfl | h₁'); · rfl
  rcases eq_or_lt_of_le h₂ with (rfl | h₂'); · simp
  exact le_of_lt (rpow_lt_rpow h h₁' h₂')
#align real.rpow_le_rpow Real.rpow_le_rpow

/- warning: real.rpow_lt_rpow_iff -> Real.rpow_lt_rpow_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Iff (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y z)) (LT.lt.{0} Real Real.hasLt x y))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Iff (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y z)) (LT.lt.{0} Real Real.instLTReal x y))
Case conversion may be inaccurate. Consider using '#align real.rpow_lt_rpow_iff Real.rpow_lt_rpow_iffₓ'. -/
theorem rpow_lt_rpow_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  ⟨lt_imp_lt_of_le_imp_le fun h => rpow_le_rpow hy h (le_of_lt hz), fun h => rpow_lt_rpow hx h hz⟩
#align real.rpow_lt_rpow_iff Real.rpow_lt_rpow_iff

/- warning: real.rpow_le_rpow_iff -> Real.rpow_le_rpow_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Iff (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y z)) (LE.le.{0} Real Real.hasLe x y))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Iff (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y z)) (LE.le.{0} Real Real.instLEReal x y))
Case conversion may be inaccurate. Consider using '#align real.rpow_le_rpow_iff Real.rpow_le_rpow_iffₓ'. -/
theorem rpow_le_rpow_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| rpow_lt_rpow_iff hy hx hz
#align real.rpow_le_rpow_iff Real.rpow_le_rpow_iff

/- warning: real.le_rpow_inv_iff_of_neg -> Real.le_rpow_inv_iff_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (LT.lt.{0} Real Real.hasLt z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Iff (LE.le.{0} Real Real.hasLe x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y (Inv.inv.{0} Real Real.hasInv z))) (LE.le.{0} Real Real.hasLe y (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z)))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (LT.lt.{0} Real Real.instLTReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Iff (LE.le.{0} Real Real.instLEReal x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y (Inv.inv.{0} Real Real.instInvReal z))) (LE.le.{0} Real Real.instLEReal y (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z)))
Case conversion may be inaccurate. Consider using '#align real.le_rpow_inv_iff_of_neg Real.le_rpow_inv_iff_of_negₓ'. -/
theorem le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ≤ y ^ z⁻¹ ↔ y ≤ x ^ z :=
  by
  have hz' : 0 < -z := by rwa [lt_neg, neg_zero]
  have hxz : 0 < x ^ (-z) := Real.rpow_pos_of_pos hx _
  have hyz : 0 < y ^ z⁻¹ := Real.rpow_pos_of_pos hy _
  rw [← Real.rpow_le_rpow_iff hx.le hyz.le hz', ← Real.rpow_mul hy.le]
  simp only [ne_of_lt hz, Real.rpow_neg_one, mul_neg, inv_mul_cancel, Ne.def, not_false_iff]
  rw [le_inv hxz hy, ← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
  simp
#align real.le_rpow_inv_iff_of_neg Real.le_rpow_inv_iff_of_neg

/- warning: real.lt_rpow_inv_iff_of_neg -> Real.lt_rpow_inv_iff_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (LT.lt.{0} Real Real.hasLt z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Iff (LT.lt.{0} Real Real.hasLt x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y (Inv.inv.{0} Real Real.hasInv z))) (LT.lt.{0} Real Real.hasLt y (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z)))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (LT.lt.{0} Real Real.instLTReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Iff (LT.lt.{0} Real Real.instLTReal x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y (Inv.inv.{0} Real Real.instInvReal z))) (LT.lt.{0} Real Real.instLTReal y (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z)))
Case conversion may be inaccurate. Consider using '#align real.lt_rpow_inv_iff_of_neg Real.lt_rpow_inv_iff_of_negₓ'. -/
theorem lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x < y ^ z⁻¹ ↔ y < x ^ z :=
  by
  have hz' : 0 < -z := by rwa [lt_neg, neg_zero]
  have hxz : 0 < x ^ (-z) := Real.rpow_pos_of_pos hx _
  have hyz : 0 < y ^ z⁻¹ := Real.rpow_pos_of_pos hy _
  rw [← Real.rpow_lt_rpow_iff hx.le hyz.le hz', ← Real.rpow_mul hy.le]
  simp only [ne_of_lt hz, Real.rpow_neg_one, mul_neg, inv_mul_cancel, Ne.def, not_false_iff]
  rw [lt_inv hxz hy, ← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
  simp
#align real.lt_rpow_inv_iff_of_neg Real.lt_rpow_inv_iff_of_neg

/- warning: real.rpow_inv_lt_iff_of_neg -> Real.rpow_inv_lt_iff_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (LT.lt.{0} Real Real.hasLt z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Iff (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (Inv.inv.{0} Real Real.hasInv z)) y) (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y z) x))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (LT.lt.{0} Real Real.instLTReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Iff (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (Inv.inv.{0} Real Real.instInvReal z)) y) (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y z) x))
Case conversion may be inaccurate. Consider using '#align real.rpow_inv_lt_iff_of_neg Real.rpow_inv_lt_iff_of_negₓ'. -/
theorem rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ < y ↔ y ^ z < x :=
  by
  convert lt_rpow_inv_iff_of_neg (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _) hz <;>
    simp [← Real.rpow_mul hx.le, ← Real.rpow_mul hy.le, ne_of_lt hz]
#align real.rpow_inv_lt_iff_of_neg Real.rpow_inv_lt_iff_of_neg

/- warning: real.rpow_inv_le_iff_of_neg -> Real.rpow_inv_le_iff_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (LT.lt.{0} Real Real.hasLt z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Iff (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (Inv.inv.{0} Real Real.hasInv z)) y) (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y z) x))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (LT.lt.{0} Real Real.instLTReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Iff (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (Inv.inv.{0} Real Real.instInvReal z)) y) (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y z) x))
Case conversion may be inaccurate. Consider using '#align real.rpow_inv_le_iff_of_neg Real.rpow_inv_le_iff_of_negₓ'. -/
theorem rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ ≤ y ↔ y ^ z ≤ x :=
  by
  convert le_rpow_inv_iff_of_neg (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _) hz <;>
    simp [← Real.rpow_mul hx.le, ← Real.rpow_mul hy.le, ne_of_lt hz]
#align real.rpow_inv_le_iff_of_neg Real.rpow_inv_le_iff_of_neg

/- warning: real.rpow_lt_rpow_of_exponent_lt -> Real.rpow_lt_rpow_of_exponent_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (LT.lt.{0} Real Real.hasLt y z) -> (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (LT.lt.{0} Real Real.instLTReal y z) -> (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z))
Case conversion may be inaccurate. Consider using '#align real.rpow_lt_rpow_of_exponent_lt Real.rpow_lt_rpow_of_exponent_ltₓ'. -/
theorem rpow_lt_rpow_of_exponent_lt (hx : 1 < x) (hyz : y < z) : x ^ y < x ^ z :=
  by
  repeat' rw [rpow_def_of_pos (lt_trans zero_lt_one hx)]
  rw [exp_lt_exp]; exact mul_lt_mul_of_pos_left hyz (log_pos hx)
#align real.rpow_lt_rpow_of_exponent_lt Real.rpow_lt_rpow_of_exponent_lt

/- warning: real.rpow_le_rpow_of_exponent_le -> Real.rpow_le_rpow_of_exponent_le is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (LE.le.{0} Real Real.hasLe y z) -> (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (LE.le.{0} Real Real.instLEReal y z) -> (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z))
Case conversion may be inaccurate. Consider using '#align real.rpow_le_rpow_of_exponent_le Real.rpow_le_rpow_of_exponent_leₓ'. -/
theorem rpow_le_rpow_of_exponent_le (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z :=
  by
  repeat' rw [rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hx)]
  rw [exp_le_exp]; exact mul_le_mul_of_nonneg_left hyz (log_nonneg hx)
#align real.rpow_le_rpow_of_exponent_le Real.rpow_le_rpow_of_exponent_le

/- warning: real.rpow_le_rpow_left_iff -> Real.rpow_le_rpow_left_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (Iff (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z)) (LE.le.{0} Real Real.hasLe y z))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z)) (LE.le.{0} Real Real.instLEReal y z))
Case conversion may be inaccurate. Consider using '#align real.rpow_le_rpow_left_iff Real.rpow_le_rpow_left_iffₓ'. -/
@[simp]
theorem rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y ≤ x ^ z ↔ y ≤ z :=
  by
  have x_pos : 0 < x := lt_trans zero_lt_one hx
  rw [← log_le_log (rpow_pos_of_pos x_pos y) (rpow_pos_of_pos x_pos z), log_rpow x_pos,
    log_rpow x_pos, mul_le_mul_right (log_pos hx)]
#align real.rpow_le_rpow_left_iff Real.rpow_le_rpow_left_iff

/- warning: real.rpow_lt_rpow_left_iff -> Real.rpow_lt_rpow_left_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z)) (LT.lt.{0} Real Real.hasLt y z))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z)) (LT.lt.{0} Real Real.instLTReal y z))
Case conversion may be inaccurate. Consider using '#align real.rpow_lt_rpow_left_iff Real.rpow_lt_rpow_left_iffₓ'. -/
@[simp]
theorem rpow_lt_rpow_left_iff (hx : 1 < x) : x ^ y < x ^ z ↔ y < z := by
  rw [lt_iff_not_le, rpow_le_rpow_left_iff hx, lt_iff_not_le]
#align real.rpow_lt_rpow_left_iff Real.rpow_lt_rpow_left_iff

/- warning: real.rpow_lt_rpow_of_exponent_gt -> Real.rpow_lt_rpow_of_exponent_gt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt z y) -> (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal z y) -> (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z))
Case conversion may be inaccurate. Consider using '#align real.rpow_lt_rpow_of_exponent_gt Real.rpow_lt_rpow_of_exponent_gtₓ'. -/
theorem rpow_lt_rpow_of_exponent_gt (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z :=
  by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_lt_exp]; exact mul_lt_mul_of_neg_left hyz (log_neg hx0 hx1)
#align real.rpow_lt_rpow_of_exponent_gt Real.rpow_lt_rpow_of_exponent_gt

/- warning: real.rpow_le_rpow_of_exponent_ge -> Real.rpow_le_rpow_of_exponent_ge is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe z y) -> (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal z y) -> (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z))
Case conversion may be inaccurate. Consider using '#align real.rpow_le_rpow_of_exponent_ge Real.rpow_le_rpow_of_exponent_geₓ'. -/
theorem rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z :=
  by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_le_exp]; exact mul_le_mul_of_nonpos_left hyz (log_nonpos (le_of_lt hx0) hx1)
#align real.rpow_le_rpow_of_exponent_ge Real.rpow_le_rpow_of_exponent_ge

/- warning: real.rpow_le_rpow_left_iff_of_base_lt_one -> Real.rpow_le_rpow_left_iff_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Iff (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z)) (LE.le.{0} Real Real.hasLe z y))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Iff (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z)) (LE.le.{0} Real Real.instLEReal z y))
Case conversion may be inaccurate. Consider using '#align real.rpow_le_rpow_left_iff_of_base_lt_one Real.rpow_le_rpow_left_iff_of_base_lt_oneₓ'. -/
@[simp]
theorem rpow_le_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) : x ^ y ≤ x ^ z ↔ z ≤ y :=
  by
  rw [← log_le_log (rpow_pos_of_pos hx0 y) (rpow_pos_of_pos hx0 z), log_rpow hx0, log_rpow hx0,
    mul_le_mul_right_of_neg (log_neg hx0 hx1)]
#align real.rpow_le_rpow_left_iff_of_base_lt_one Real.rpow_le_rpow_left_iff_of_base_lt_one

/- warning: real.rpow_lt_rpow_left_iff_of_base_lt_one -> Real.rpow_lt_rpow_left_iff_of_base_lt_one is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Iff (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z)) (LT.lt.{0} Real Real.hasLt z y))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Iff (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z)) (LT.lt.{0} Real Real.instLTReal z y))
Case conversion may be inaccurate. Consider using '#align real.rpow_lt_rpow_left_iff_of_base_lt_one Real.rpow_lt_rpow_left_iff_of_base_lt_oneₓ'. -/
@[simp]
theorem rpow_lt_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) : x ^ y < x ^ z ↔ z < y :=
  by rw [lt_iff_not_le, rpow_le_rpow_left_iff_of_base_lt_one hx0 hx1, lt_iff_not_le]
#align real.rpow_lt_rpow_left_iff_of_base_lt_one Real.rpow_lt_rpow_left_iff_of_base_lt_one

/- warning: real.rpow_lt_one -> Real.rpow_lt_one is a dubious translation:
lean 3 declaration is
  forall {x : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.rpow_lt_one Real.rpow_lt_oneₓ'. -/
theorem rpow_lt_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) (hz : 0 < z) : x ^ z < 1 :=
  by
  rw [← one_rpow z]
  exact rpow_lt_rpow hx1 hx2 hz
#align real.rpow_lt_one Real.rpow_lt_one

/- warning: real.rpow_le_one -> Real.rpow_le_one is a dubious translation:
lean 3 declaration is
  forall {x : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.rpow_le_one Real.rpow_le_oneₓ'. -/
theorem rpow_le_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 :=
  by
  rw [← one_rpow z]
  exact rpow_le_rpow hx1 hx2 hz
#align real.rpow_le_one Real.rpow_le_one

/- warning: real.rpow_lt_one_of_one_lt_of_neg -> Real.rpow_lt_one_of_one_lt_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (LT.lt.{0} Real Real.hasLt z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (LT.lt.{0} Real Real.instLTReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.rpow_lt_one_of_one_lt_of_neg Real.rpow_lt_one_of_one_lt_of_negₓ'. -/
theorem rpow_lt_one_of_one_lt_of_neg {x z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 :=
  by
  convert rpow_lt_rpow_of_exponent_lt hx hz
  exact (rpow_zero x).symm
#align real.rpow_lt_one_of_one_lt_of_neg Real.rpow_lt_one_of_one_lt_of_neg

/- warning: real.rpow_le_one_of_one_le_of_nonpos -> Real.rpow_le_one_of_one_le_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {x : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (LE.le.{0} Real Real.hasLe z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (LE.le.{0} Real Real.instLEReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_one_of_one_le_of_nonposₓ'. -/
theorem rpow_le_one_of_one_le_of_nonpos {x z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 :=
  by
  convert rpow_le_rpow_of_exponent_le hx hz
  exact (rpow_zero x).symm
#align real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_one_of_one_le_of_nonpos

/- warning: real.one_lt_rpow -> Real.one_lt_rpow is a dubious translation:
lean 3 declaration is
  forall {x : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z))
but is expected to have type
  forall {x : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z))
Case conversion may be inaccurate. Consider using '#align real.one_lt_rpow Real.one_lt_rpowₓ'. -/
theorem one_lt_rpow {x z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z :=
  by
  rw [← one_rpow z]
  exact rpow_lt_rpow zero_le_one hx hz
#align real.one_lt_rpow Real.one_lt_rpow

/- warning: real.one_le_rpow -> Real.one_le_rpow is a dubious translation:
lean 3 declaration is
  forall {x : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z))
but is expected to have type
  forall {x : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z))
Case conversion may be inaccurate. Consider using '#align real.one_le_rpow Real.one_le_rpowₓ'. -/
theorem one_le_rpow {x z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) : 1 ≤ x ^ z :=
  by
  rw [← one_rpow z]
  exact rpow_le_rpow zero_le_one hx hz
#align real.one_le_rpow Real.one_le_rpow

/- warning: real.one_lt_rpow_of_pos_of_lt_one_of_neg -> Real.one_lt_rpow_of_pos_of_lt_one_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z))
but is expected to have type
  forall {x : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z))
Case conversion may be inaccurate. Consider using '#align real.one_lt_rpow_of_pos_of_lt_one_of_neg Real.one_lt_rpow_of_pos_of_lt_one_of_negₓ'. -/
theorem one_lt_rpow_of_pos_of_lt_one_of_neg (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0) : 1 < x ^ z :=
  by
  convert rpow_lt_rpow_of_exponent_gt hx1 hx2 hz
  exact (rpow_zero x).symm
#align real.one_lt_rpow_of_pos_of_lt_one_of_neg Real.one_lt_rpow_of_pos_of_lt_one_of_neg

/- warning: real.one_le_rpow_of_pos_of_le_one_of_nonpos -> Real.one_le_rpow_of_pos_of_le_one_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {x : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z))
but is expected to have type
  forall {x : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z))
Case conversion may be inaccurate. Consider using '#align real.one_le_rpow_of_pos_of_le_one_of_nonpos Real.one_le_rpow_of_pos_of_le_one_of_nonposₓ'. -/
theorem one_le_rpow_of_pos_of_le_one_of_nonpos (hx1 : 0 < x) (hx2 : x ≤ 1) (hz : z ≤ 0) :
    1 ≤ x ^ z := by
  convert rpow_le_rpow_of_exponent_ge hx1 hx2 hz
  exact (rpow_zero x).symm
#align real.one_le_rpow_of_pos_of_le_one_of_nonpos Real.one_le_rpow_of_pos_of_le_one_of_nonpos

/- warning: real.rpow_lt_one_iff_of_pos -> Real.rpow_lt_one_iff_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Or (And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) (LT.lt.{0} Real Real.hasLt y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (And (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y))))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Or (And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) (LT.lt.{0} Real Real.instLTReal y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (And (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y))))
Case conversion may be inaccurate. Consider using '#align real.rpow_lt_one_iff_of_pos Real.rpow_lt_one_iff_of_posₓ'. -/
theorem rpow_lt_one_iff_of_pos (hx : 0 < x) : x ^ y < 1 ↔ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := by
  rw [rpow_def_of_pos hx, exp_lt_one_iff, mul_neg_iff, log_pos_iff hx, log_neg_iff hx]
#align real.rpow_lt_one_iff_of_pos Real.rpow_lt_one_iff_of_pos

/- warning: real.rpow_lt_one_iff -> Real.rpow_lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Or (And (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Or (And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) (LT.lt.{0} Real Real.hasLt y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (And (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y)))))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Or (And (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Or (And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) (LT.lt.{0} Real Real.instLTReal y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (And (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y)))))
Case conversion may be inaccurate. Consider using '#align real.rpow_lt_one_iff Real.rpow_lt_one_iffₓ'. -/
theorem rpow_lt_one_iff (hx : 0 ≤ x) : x ^ y < 1 ↔ x = 0 ∧ y ≠ 0 ∨ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y :=
  by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases em (y = 0) with (rfl | hy) <;> simp [*, lt_irrefl, zero_lt_one]
  · simp [rpow_lt_one_iff_of_pos hx, hx.ne.symm]
#align real.rpow_lt_one_iff Real.rpow_lt_one_iff

/- warning: real.one_lt_rpow_iff_of_pos -> Real.one_lt_rpow_iff_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y)) (Or (And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y)) (And (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (LT.lt.{0} Real Real.hasLt y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y)) (Or (And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y)) (And (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (LT.lt.{0} Real Real.instLTReal y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))))
Case conversion may be inaccurate. Consider using '#align real.one_lt_rpow_iff_of_pos Real.one_lt_rpow_iff_of_posₓ'. -/
theorem one_lt_rpow_iff_of_pos (hx : 0 < x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ x < 1 ∧ y < 0 := by
  rw [rpow_def_of_pos hx, one_lt_exp_iff, mul_pos_iff, log_pos_iff hx, log_neg_iff hx]
#align real.one_lt_rpow_iff_of_pos Real.one_lt_rpow_iff_of_pos

/- warning: real.one_lt_rpow_iff -> Real.one_lt_rpow_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y)) (Or (And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y)) (And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) (And (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (LT.lt.{0} Real Real.hasLt y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y)) (Or (And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y)) (And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) (And (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (LT.lt.{0} Real Real.instLTReal y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))))))
Case conversion may be inaccurate. Consider using '#align real.one_lt_rpow_iff Real.one_lt_rpow_iffₓ'. -/
theorem one_lt_rpow_iff (hx : 0 ≤ x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ 0 < x ∧ x < 1 ∧ y < 0 :=
  by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases em (y = 0) with (rfl | hy) <;> simp [*, lt_irrefl, (zero_lt_one' ℝ).not_lt]
  · simp [one_lt_rpow_iff_of_pos hx, hx]
#align real.one_lt_rpow_iff Real.one_lt_rpow_iff

/- warning: real.rpow_le_rpow_of_exponent_ge' -> Real.rpow_le_rpow_of_exponent_ge' is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LE.le.{0} Real Real.hasLe z y) -> (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x z))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LE.le.{0} Real Real.instLEReal z y) -> (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x z))
Case conversion may be inaccurate. Consider using '#align real.rpow_le_rpow_of_exponent_ge' Real.rpow_le_rpow_of_exponent_ge'ₓ'. -/
theorem rpow_le_rpow_of_exponent_ge' (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 ≤ z) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z := by
  rcases eq_or_lt_of_le hx0 with (rfl | hx0')
  · rcases eq_or_lt_of_le hz with (rfl | hz')
    · exact (rpow_zero 0).symm ▸ rpow_le_one hx0 hx1 hyz
    rw [zero_rpow, zero_rpow] <;> linarith
  · exact rpow_le_rpow_of_exponent_ge hx0' hx1 hyz
#align real.rpow_le_rpow_of_exponent_ge' Real.rpow_le_rpow_of_exponent_ge'

/- warning: real.rpow_left_inj_on -> Real.rpow_left_injOn is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Set.InjOn.{0, 0} Real Real (fun (y : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y x) (setOf.{0} Real (fun (y : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y)))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Set.InjOn.{0, 0} Real Real (fun (y : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y x) (setOf.{0} Real (fun (y : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y)))
Case conversion may be inaccurate. Consider using '#align real.rpow_left_inj_on Real.rpow_left_injOnₓ'. -/
theorem rpow_left_injOn {x : ℝ} (hx : x ≠ 0) : InjOn (fun y : ℝ => y ^ x) { y : ℝ | 0 ≤ y } :=
  by
  rintro y hy z hz (hyz : y ^ x = z ^ x)
  rw [← rpow_one y, ← rpow_one z, ← _root_.mul_inv_cancel hx, rpow_mul hy, rpow_mul hz, hyz]
#align real.rpow_left_inj_on Real.rpow_left_injOn

/- warning: real.le_rpow_iff_log_le -> Real.le_rpow_iff_log_le is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LE.le.{0} Real Real.hasLe x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y z)) (LE.le.{0} Real Real.hasLe (Real.log x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) z (Real.log y))))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LE.le.{0} Real Real.instLEReal x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y z)) (LE.le.{0} Real Real.instLEReal (Real.log x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) z (Real.log y))))
Case conversion may be inaccurate. Consider using '#align real.le_rpow_iff_log_le Real.le_rpow_iff_log_leₓ'. -/
theorem le_rpow_iff_log_le (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ z ↔ Real.log x ≤ z * Real.log y := by
  rw [← Real.log_le_log hx (Real.rpow_pos_of_pos hy z), Real.log_rpow hy]
#align real.le_rpow_iff_log_le Real.le_rpow_iff_log_le

/- warning: real.le_rpow_of_log_le -> Real.le_rpow_of_log_le is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (LE.le.{0} Real Real.hasLe (Real.log x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) z (Real.log y))) -> (LE.le.{0} Real Real.hasLe x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y z))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (LE.le.{0} Real Real.instLEReal (Real.log x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) z (Real.log y))) -> (LE.le.{0} Real Real.instLEReal x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y z))
Case conversion may be inaccurate. Consider using '#align real.le_rpow_of_log_le Real.le_rpow_of_log_leₓ'. -/
theorem le_rpow_of_log_le (hx : 0 ≤ x) (hy : 0 < y) (h : Real.log x ≤ z * Real.log y) : x ≤ y ^ z :=
  by
  obtain hx | rfl := hx.lt_or_eq
  · exact (le_rpow_iff_log_le hx hy).2 h
  exact (Real.rpow_pos_of_pos hy z).le
#align real.le_rpow_of_log_le Real.le_rpow_of_log_le

/- warning: real.lt_rpow_iff_log_lt -> Real.lt_rpow_iff_log_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LT.lt.{0} Real Real.hasLt x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y z)) (LT.lt.{0} Real Real.hasLt (Real.log x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) z (Real.log y))))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LT.lt.{0} Real Real.instLTReal x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y z)) (LT.lt.{0} Real Real.instLTReal (Real.log x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) z (Real.log y))))
Case conversion may be inaccurate. Consider using '#align real.lt_rpow_iff_log_lt Real.lt_rpow_iff_log_ltₓ'. -/
theorem lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : x < y ^ z ↔ Real.log x < z * Real.log y := by
  rw [← Real.log_lt_log_iff hx (Real.rpow_pos_of_pos hy z), Real.log_rpow hy]
#align real.lt_rpow_iff_log_lt Real.lt_rpow_iff_log_lt

/- warning: real.lt_rpow_of_log_lt -> Real.lt_rpow_of_log_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (LT.lt.{0} Real Real.hasLt (Real.log x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) z (Real.log y))) -> (LT.lt.{0} Real Real.hasLt x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) y z))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (LT.lt.{0} Real Real.instLTReal (Real.log x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) z (Real.log y))) -> (LT.lt.{0} Real Real.instLTReal x (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) y z))
Case conversion may be inaccurate. Consider using '#align real.lt_rpow_of_log_lt Real.lt_rpow_of_log_ltₓ'. -/
theorem lt_rpow_of_log_lt (hx : 0 ≤ x) (hy : 0 < y) (h : Real.log x < z * Real.log y) : x < y ^ z :=
  by
  obtain hx | rfl := hx.lt_or_eq
  · exact (lt_rpow_iff_log_lt hx hy).2 h
  exact Real.rpow_pos_of_pos hy z
#align real.lt_rpow_of_log_lt Real.lt_rpow_of_log_lt

/- warning: real.rpow_le_one_iff_of_pos -> Real.rpow_le_one_iff_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Or (And (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) (LE.le.{0} Real Real.hasLe y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (And (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y))))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Or (And (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) (LE.le.{0} Real Real.instLEReal y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (And (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y))))
Case conversion may be inaccurate. Consider using '#align real.rpow_le_one_iff_of_pos Real.rpow_le_one_iff_of_posₓ'. -/
theorem rpow_le_one_iff_of_pos (hx : 0 < x) : x ^ y ≤ 1 ↔ 1 ≤ x ∧ y ≤ 0 ∨ x ≤ 1 ∧ 0 ≤ y := by
  rw [rpow_def_of_pos hx, exp_le_one_iff, mul_nonpos_iff, log_nonneg_iff hx, log_nonpos_iff hx]
#align real.rpow_le_one_iff_of_pos Real.rpow_le_one_iff_of_pos

/- warning: real.abs_log_mul_self_rpow_lt -> Real.abs_log_mul_self_rpow_lt is a dubious translation:
lean 3 declaration is
  forall (x : Real) (t : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) t) -> (LT.lt.{0} Real Real.hasLt (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.log x) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x t))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) t))
but is expected to have type
  forall (x : Real) (t : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) t) -> (LT.lt.{0} Real Real.instLTReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.log x) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x t))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) t))
Case conversion may be inaccurate. Consider using '#align real.abs_log_mul_self_rpow_lt Real.abs_log_mul_self_rpow_ltₓ'. -/
/-- Bound for `|log x * x ^ t|` in the interval `(0, 1]`, for positive real `t`. -/
theorem abs_log_mul_self_rpow_lt (x t : ℝ) (h1 : 0 < x) (h2 : x ≤ 1) (ht : 0 < t) :
    |log x * x ^ t| < 1 / t := by
  rw [lt_div_iff ht]
  have := abs_log_mul_self_lt (x ^ t) (rpow_pos_of_pos h1 t) (rpow_le_one h1.le h2 ht.le)
  rwa [log_rpow h1, mul_assoc, abs_mul, abs_of_pos ht, mul_comm] at this
#align real.abs_log_mul_self_rpow_lt Real.abs_log_mul_self_rpow_lt

/- warning: real.pow_nat_rpow_nat_inv -> Real.pow_nat_rpow_nat_inv is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n) (Inv.inv.{0} Real Real.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))) x))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n) (Inv.inv.{0} Real Real.instInvReal (Nat.cast.{0} Real Real.natCast n))) x))
Case conversion may be inaccurate. Consider using '#align real.pow_nat_rpow_nat_inv Real.pow_nat_rpow_nat_invₓ'. -/
theorem pow_nat_rpow_nat_inv {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) : (x ^ n) ^ (n⁻¹ : ℝ) = x :=
  by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_nat_cast, ← rpow_mul hx, mul_inv_cancel hn0, rpow_one]
#align real.pow_nat_rpow_nat_inv Real.pow_nat_rpow_nat_inv

/- warning: real.rpow_nat_inv_pow_nat -> Real.rpow_nat_inv_pow_nat is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (Inv.inv.{0} Real Real.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))) n) x))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (Inv.inv.{0} Real Real.instInvReal (Nat.cast.{0} Real Real.natCast n))) n) x))
Case conversion may be inaccurate. Consider using '#align real.rpow_nat_inv_pow_nat Real.rpow_nat_inv_pow_natₓ'. -/
theorem rpow_nat_inv_pow_nat {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℝ)) ^ n = x :=
  by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_nat_cast, ← rpow_mul hx, inv_mul_cancel hn0, rpow_one]
#align real.rpow_nat_inv_pow_nat Real.rpow_nat_inv_pow_nat

end Real

/-!
## Square roots of reals
-/


namespace Real

variable {z x y : ℝ}

section Sqrt

/- warning: real.sqrt_eq_rpow -> Real.sqrt_eq_rpow is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.sqrt x) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.sqrt x) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.sqrt_eq_rpow Real.sqrt_eq_rpowₓ'. -/
theorem sqrt_eq_rpow (x : ℝ) : sqrt x = x ^ (1 / (2 : ℝ)) :=
  by
  obtain h | h := le_or_lt 0 x
  · rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg_of_nonneg h _), mul_self_sqrt h, ← sq,
      ← rpow_nat_cast, ← rpow_mul h]
    norm_num
  · have : 1 / (2 : ℝ) * π = π / (2 : ℝ)
    ring
    rw [sqrt_eq_zero_of_nonpos h.le, rpow_def_of_neg h, this, cos_pi_div_two, MulZeroClass.mul_zero]
#align real.sqrt_eq_rpow Real.sqrt_eq_rpow

/- warning: real.rpow_div_two_eq_sqrt -> Real.rpow_div_two_eq_sqrt is a dubious translation:
lean 3 declaration is
  forall {x : Real} (r : Real), (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) r (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Real.sqrt x) r))
but is expected to have type
  forall {x : Real} (r : Real), (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) r (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Real.sqrt x) r))
Case conversion may be inaccurate. Consider using '#align real.rpow_div_two_eq_sqrt Real.rpow_div_two_eq_sqrtₓ'. -/
theorem rpow_div_two_eq_sqrt {x : ℝ} (r : ℝ) (hx : 0 ≤ x) : x ^ (r / 2) = sqrt x ^ r :=
  by
  rw [sqrt_eq_rpow, ← rpow_mul hx]
  congr
  ring
#align real.rpow_div_two_eq_sqrt Real.rpow_div_two_eq_sqrt

end Sqrt

variable {n : ℕ}

/- warning: real.exists_rat_pow_btwn_rat_aux -> Real.exists_rat_pow_btwn_rat_aux is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (forall (x : Real) (y : Real), (LT.lt.{0} Real Real.hasLt x y) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Exists.{1} Rat (fun (q : Rat) => And (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) (And (LT.lt.{0} Real Real.hasLt x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) n)) (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) n) y)))))
but is expected to have type
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (forall (x : Real) (y : Real), (LT.lt.{0} Real Real.instLTReal x y) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Exists.{1} Rat (fun (q : Rat) => And (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (And (LT.lt.{0} Real Real.instLTReal x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Rat.cast.{0} Real Real.ratCast q) n)) (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Rat.cast.{0} Real Real.ratCast q) n) y)))))
Case conversion may be inaccurate. Consider using '#align real.exists_rat_pow_btwn_rat_aux Real.exists_rat_pow_btwn_rat_auxₓ'. -/
theorem exists_rat_pow_btwn_rat_aux (hn : n ≠ 0) (x y : ℝ) (h : x < y) (hy : 0 < y) :
    ∃ q : ℚ, 0 < q ∧ x < q ^ n ∧ ↑q ^ n < y :=
  by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn.bot_lt
  obtain ⟨q, hxq, hqy⟩ :=
    exists_rat_btwn (rpow_lt_rpow (le_max_left 0 x) (max_lt hy h) <| inv_pos.mpr hn')
  have := rpow_nonneg_of_nonneg (le_max_left 0 x) n⁻¹
  have hq := this.trans_lt hxq
  replace hxq := rpow_lt_rpow this hxq hn'
  replace hqy := rpow_lt_rpow hq.le hqy hn'
  rw [rpow_nat_cast, rpow_nat_cast, rpow_nat_inv_pow_nat _ hn] at hxq hqy
  exact ⟨q, by exact_mod_cast hq, (le_max_right _ _).trans_lt hxq, hqy⟩
  · exact le_max_left _ _
  · exact hy.le
#align real.exists_rat_pow_btwn_rat_aux Real.exists_rat_pow_btwn_rat_aux

/- warning: real.exists_rat_pow_btwn_rat -> Real.exists_rat_pow_btwn_rat is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (forall {x : Rat} {y : Rat}, (LT.lt.{0} Rat Rat.hasLt x y) -> (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) y) -> (Exists.{1} Rat (fun (q : Rat) => And (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) (And (LT.lt.{0} Rat Rat.hasLt x (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) q n)) (LT.lt.{0} Rat Rat.hasLt (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) q n) y)))))
but is expected to have type
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (forall {x : Rat} {y : Rat}, (LT.lt.{0} Rat Rat.instLTRat_1 x y) -> (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) y) -> (Exists.{1} Rat (fun (q : Rat) => And (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (And (LT.lt.{0} Rat Rat.instLTRat_1 x (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) q n)) (LT.lt.{0} Rat Rat.instLTRat_1 (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) q n) y)))))
Case conversion may be inaccurate. Consider using '#align real.exists_rat_pow_btwn_rat Real.exists_rat_pow_btwn_ratₓ'. -/
theorem exists_rat_pow_btwn_rat (hn : n ≠ 0) {x y : ℚ} (h : x < y) (hy : 0 < y) :
    ∃ q : ℚ, 0 < q ∧ x < q ^ n ∧ q ^ n < y := by
  apply_mod_cast exists_rat_pow_btwn_rat_aux hn x y <;> assumption
#align real.exists_rat_pow_btwn_rat Real.exists_rat_pow_btwn_rat

/- warning: real.exists_rat_pow_btwn -> Real.exists_rat_pow_btwn is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : Archimedean.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedSemiring.{u1} α (StrictOrderedRing.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))], (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (forall {x : α} {y : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) x y) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1))))))))))) y) -> (Exists.{1} Rat (fun (q : Rat) => And (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) (And (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) x (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))) q) n)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))) q) n) y)))))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : Archimedean.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} α (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))))], (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (forall {x : α} {y : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) x y) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommGroupWithZero.toCommMonoidWithZero.{u1} α (Semifield.toCommGroupWithZero.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))))) y) -> (Exists.{1} Rat (fun (q : Rat) => And (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (And (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) x (Rat.cast.{u1} α (LinearOrderedField.toRatCast.{u1} α _inst_1) (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) q n))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (Rat.cast.{u1} α (LinearOrderedField.toRatCast.{u1} α _inst_1) (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) q n)) y)))))
Case conversion may be inaccurate. Consider using '#align real.exists_rat_pow_btwn Real.exists_rat_pow_btwnₓ'. -/
/-- There is a rational power between any two positive elements of an archimedean ordered field. -/
theorem exists_rat_pow_btwn {α : Type _} [LinearOrderedField α] [Archimedean α] (hn : n ≠ 0)
    {x y : α} (h : x < y) (hy : 0 < y) : ∃ q : ℚ, 0 < q ∧ x < q ^ n ∧ (q ^ n : α) < y :=
  by
  obtain ⟨q₂, hx₂, hy₂⟩ := exists_rat_btwn (max_lt h hy)
  obtain ⟨q₁, hx₁, hq₁₂⟩ := exists_rat_btwn hx₂
  have : (0 : α) < q₂ := (le_max_right _ _).trans_lt hx₂
  norm_cast  at hq₁₂ this
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_rat_pow_btwn_rat hn hq₁₂ this
  refine' ⟨q, hq, (le_max_left _ _).trans_lt <| hx₁.trans _, hy₂.trans' _⟩ <;> assumption_mod_cast
#align real.exists_rat_pow_btwn Real.exists_rat_pow_btwn

end Real

section Tactics

/-!
## Tactic extensions for real powers
-/


namespace NormNum

open Tactic

theorem rpow_pos (a b : ℝ) (b' : ℕ) (c : ℝ) (hb : (b' : ℝ) = b) (h : a ^ b' = c) : a ^ b = c := by
  rw [← h, ← hb, Real.rpow_nat_cast]
#align norm_num.rpow_pos NormNum.rpow_pos

theorem rpow_neg (a b : ℝ) (b' : ℕ) (c c' : ℝ) (a0 : 0 ≤ a) (hb : (b' : ℝ) = b) (h : a ^ b' = c)
    (hc : c⁻¹ = c') : a ^ (-b) = c' := by rw [← hc, ← h, ← hb, Real.rpow_neg a0, Real.rpow_nat_cast]
#align norm_num.rpow_neg NormNum.rpow_neg

/-- Evaluate `real.rpow a b` where `a` is a rational numeral and `b` is an integer.
(This cannot go via the generalized version `prove_rpow'` because `rpow_pos` has a side condition;
we do not attempt to evaluate `a ^ b` where `a` and `b` are both negative because it comes
out to some garbage.) -/
unsafe def prove_rpow (a b : expr) : tactic (expr × expr) := do
  let na ← a.to_rat
  let ic ← mk_instance_cache q(ℝ)
  match match_sign b with
    | Sum.inl b => do
      let (ic, a0) ← guard (na ≥ 0) >> prove_nonneg ic a
      let nc ← mk_instance_cache q(ℕ)
      let (ic, nc, b', hb) ← prove_nat_uncast ic nc b
      let (ic, c, h) ← prove_pow a na ic b'
      let cr ← c
      let (ic, c', hc) ← prove_inv ic c cr
      pure (c', (expr.const `` rpow_neg []).mk_app [a, b, b', c, c', a0, hb, h, hc])
    | Sum.inr ff => pure (q((1 : ℝ)), expr.const `` Real.rpow_zero [] a)
    | Sum.inr tt => do
      let nc ← mk_instance_cache q(ℕ)
      let (ic, nc, b', hb) ← prove_nat_uncast ic nc b
      let (ic, c, h) ← prove_pow a na ic b'
      pure (c, (expr.const `` rpow_pos []).mk_app [a, b, b', c, hb, h])
#align norm_num.prove_rpow norm_num.prove_rpow

/-- Evaluates expressions of the form `rpow a b` and `a ^ b` in the special case where
`b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
@[norm_num]
unsafe def eval_rpow : expr → tactic (expr × expr)
  | q(@Pow.pow _ _ Real.hasPow $(a) $(b)) => b.to_int >> prove_rpow a b
  | q(Real.rpow $(a) $(b)) => b.to_int >> prove_rpow a b
  | _ => tactic.failed
#align norm_num.eval_rpow norm_num.eval_rpow

end NormNum

namespace Tactic

namespace Positivity

/-- Auxiliary definition for the `positivity` tactic to handle real powers of reals. -/
unsafe def prove_rpow (a b : expr) : tactic strictness := do
  let strictness_a ← core a
  match strictness_a with
    | nonnegative p => nonnegative <$> mk_app `` Real.rpow_nonneg_of_nonneg [p, b]
    | positive p => positive <$> mk_app `` Real.rpow_pos_of_pos [p, b]
    | _ => failed
#align tactic.positivity.prove_rpow tactic.positivity.prove_rpow

end Positivity

open Positivity

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when the
base is nonnegative and positive when the base is positive. -/
@[positivity]
unsafe def positivity_rpow : expr → tactic strictness
  | q(@Pow.pow _ _ Real.hasPow $(a) $(b)) => prove_rpow a b
  | q(Real.rpow $(a) $(b)) => prove_rpow a b
  | _ => failed
#align tactic.positivity_rpow tactic.positivity_rpow

end Tactic

end Tactics

