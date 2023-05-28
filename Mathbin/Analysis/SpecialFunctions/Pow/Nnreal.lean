/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler

! This file was ported from Lean 3 source module analysis.special_functions.pow.nnreal
! leanprover-community/mathlib commit 4280f5f32e16755ec7985ce11e189b6cd6ff6735
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Pow.Real

/-!
# Power function on `ℝ≥0` and `ℝ≥0∞`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct the power functions `x ^ y` where
* `x` is a nonnegative real number and `y` is a real number;
* `x` is a number from `[0, +∞]` (a.k.a. `ℝ≥0∞`) and `y` is a real number.

We also prove basic properties of these functions.
-/


noncomputable section

open Classical Real NNReal ENNReal BigOperators ComplexConjugate

open Finset Set

namespace NNReal

#print NNReal.rpow /-
/-- The nonnegative real power function `x^y`, defined for `x : ℝ≥0` and `y : ℝ ` as the
restriction of the real power function. For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`,
one sets `0 ^ 0 = 1` and `0 ^ y = 0` for `y ≠ 0`. -/
noncomputable def rpow (x : ℝ≥0) (y : ℝ) : ℝ≥0 :=
  ⟨(x : ℝ) ^ y, Real.rpow_nonneg_of_nonneg x.2 y⟩
#align nnreal.rpow NNReal.rpow
-/

noncomputable instance : Pow ℝ≥0 ℝ :=
  ⟨rpow⟩

#print NNReal.rpow_eq_pow /-
@[simp]
theorem rpow_eq_pow (x : ℝ≥0) (y : ℝ) : rpow x y = x ^ y :=
  rfl
#align nnreal.rpow_eq_pow NNReal.rpow_eq_pow
-/

/- warning: nnreal.coe_rpow -> NNReal.coe_rpow is a dubious translation:
lean 3 declaration is
  forall (x : NNReal) (y : Real), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x) y)
but is expected to have type
  forall (x : NNReal) (y : Real), Eq.{1} Real (NNReal.toReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (NNReal.toReal x) y)
Case conversion may be inaccurate. Consider using '#align nnreal.coe_rpow NNReal.coe_rpowₓ'. -/
@[simp, norm_cast]
theorem coe_rpow (x : ℝ≥0) (y : ℝ) : ((x ^ y : ℝ≥0) : ℝ) = (x : ℝ) ^ y :=
  rfl
#align nnreal.coe_rpow NNReal.coe_rpow

#print NNReal.rpow_zero /-
@[simp]
theorem rpow_zero (x : ℝ≥0) : x ^ (0 : ℝ) = 1 :=
  NNReal.eq <| Real.rpow_zero _
#align nnreal.rpow_zero NNReal.rpow_zero
-/

/- warning: nnreal.rpow_eq_zero_iff -> NNReal.rpow_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : Real}, Iff (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (And (Eq.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {x : NNReal} {y : Real}, Iff (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (And (Eq.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_eq_zero_iff NNReal.rpow_eq_zero_iffₓ'. -/
@[simp]
theorem rpow_eq_zero_iff {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
  by
  rw [← NNReal.coe_eq, coe_rpow, ← NNReal.coe_eq_zero]
  exact Real.rpow_eq_zero_iff_of_nonneg x.2
#align nnreal.rpow_eq_zero_iff NNReal.rpow_eq_zero_iff

/- warning: nnreal.zero_rpow -> NNReal.zero_rpow is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) x) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) x) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)))
Case conversion may be inaccurate. Consider using '#align nnreal.zero_rpow NNReal.zero_rpowₓ'. -/
@[simp]
theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ≥0) ^ x = 0 :=
  NNReal.eq <| Real.zero_rpow h
#align nnreal.zero_rpow NNReal.zero_rpow

#print NNReal.rpow_one /-
@[simp]
theorem rpow_one (x : ℝ≥0) : x ^ (1 : ℝ) = x :=
  NNReal.eq <| Real.rpow_one _
#align nnreal.rpow_one NNReal.rpow_one
-/

#print NNReal.one_rpow /-
@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ≥0) ^ x = 1 :=
  NNReal.eq <| Real.one_rpow _
#align nnreal.one_rpow NNReal.one_rpow
-/

/- warning: nnreal.rpow_add -> NNReal.rpow_add is a dubious translation:
lean 3 declaration is
  forall {x : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (forall (y : Real) (z : Real), Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) y z)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z)))
but is expected to have type
  forall {x : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (forall (y : Real) (z : Real), Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) y z)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z)))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_add NNReal.rpow_addₓ'. -/
theorem rpow_add {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z :=
  NNReal.eq <| Real.rpow_add (pos_iff_ne_zero.2 hx) _ _
#align nnreal.rpow_add NNReal.rpow_add

/- warning: nnreal.rpow_add' -> NNReal.rpow_add' is a dubious translation:
lean 3 declaration is
  forall (x : NNReal) {y : Real} {z : Real}, (Ne.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) y z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) y z)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z)))
but is expected to have type
  forall (x : NNReal) {y : Real} {z : Real}, (Ne.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) y z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) y z)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z)))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_add' NNReal.rpow_add'ₓ'. -/
theorem rpow_add' (x : ℝ≥0) {y z : ℝ} (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
  NNReal.eq <| Real.rpow_add' x.2 h
#align nnreal.rpow_add' NNReal.rpow_add'

#print NNReal.rpow_mul /-
theorem rpow_mul (x : ℝ≥0) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
  NNReal.eq <| Real.rpow_mul x.2 y z
#align nnreal.rpow_mul NNReal.rpow_mul
-/

#print NNReal.rpow_neg /-
theorem rpow_neg (x : ℝ≥0) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ :=
  NNReal.eq <| Real.rpow_neg x.2 _
#align nnreal.rpow_neg NNReal.rpow_neg
-/

#print NNReal.rpow_neg_one /-
theorem rpow_neg_one (x : ℝ≥0) : x ^ (-1 : ℝ) = x⁻¹ := by simp [rpow_neg]
#align nnreal.rpow_neg_one NNReal.rpow_neg_one
-/

/- warning: nnreal.rpow_sub -> NNReal.rpow_sub is a dubious translation:
lean 3 declaration is
  forall {x : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (forall (y : Real) (z : Real), Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y z)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z)))
but is expected to have type
  forall {x : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (forall (y : Real) (z : Real), Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y z)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z)))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_sub NNReal.rpow_subₓ'. -/
theorem rpow_sub {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z :=
  NNReal.eq <| Real.rpow_sub (pos_iff_ne_zero.2 hx) y z
#align nnreal.rpow_sub NNReal.rpow_sub

/- warning: nnreal.rpow_sub' -> NNReal.rpow_sub' is a dubious translation:
lean 3 declaration is
  forall (x : NNReal) {y : Real} {z : Real}, (Ne.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y z)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z)))
but is expected to have type
  forall (x : NNReal) {y : Real} {z : Real}, (Ne.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y z)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z)))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_sub' NNReal.rpow_sub'ₓ'. -/
theorem rpow_sub' (x : ℝ≥0) {y z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z :=
  NNReal.eq <| Real.rpow_sub' x.2 h
#align nnreal.rpow_sub' NNReal.rpow_sub'

/- warning: nnreal.rpow_inv_rpow_self -> NNReal.rpow_inv_rpow_self is a dubious translation:
lean 3 declaration is
  forall {y : Real}, (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (x : NNReal), Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) y)) x)
but is expected to have type
  forall {y : Real}, (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (x : NNReal), Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) y)) x)
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_inv_rpow_self NNReal.rpow_inv_rpow_selfₓ'. -/
theorem rpow_inv_rpow_self {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ y) ^ (1 / y) = x := by
  field_simp [← rpow_mul]
#align nnreal.rpow_inv_rpow_self NNReal.rpow_inv_rpow_self

/- warning: nnreal.rpow_self_rpow_inv -> NNReal.rpow_self_rpow_inv is a dubious translation:
lean 3 declaration is
  forall {y : Real}, (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (x : NNReal), Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) y)) y) x)
but is expected to have type
  forall {y : Real}, (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (x : NNReal), Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) y)) y) x)
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_self_rpow_inv NNReal.rpow_self_rpow_invₓ'. -/
theorem rpow_self_rpow_inv {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ (1 / y)) ^ y = x := by
  field_simp [← rpow_mul]
#align nnreal.rpow_self_rpow_inv NNReal.rpow_self_rpow_inv

#print NNReal.inv_rpow /-
theorem inv_rpow (x : ℝ≥0) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ :=
  NNReal.eq <| Real.inv_rpow x.2 y
#align nnreal.inv_rpow NNReal.inv_rpow
-/

#print NNReal.div_rpow /-
theorem div_rpow (x y : ℝ≥0) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z :=
  NNReal.eq <| Real.div_rpow x.2 y.2 z
#align nnreal.div_rpow NNReal.div_rpow
-/

/- warning: nnreal.sqrt_eq_rpow -> NNReal.sqrt_eq_rpow is a dubious translation:
lean 3 declaration is
  forall (x : NNReal), Eq.{1} NNReal (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt x) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall (x : NNReal), Eq.{1} NNReal (FunLike.coe.{1, 1, 1} (RelIso.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) NNReal (fun (_x : NNReal) => NNReal) (RelHomClass.toFunLike.{0, 0, 0} (RelIso.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) NNReal.sqrt x) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align nnreal.sqrt_eq_rpow NNReal.sqrt_eq_rpowₓ'. -/
theorem sqrt_eq_rpow (x : ℝ≥0) : sqrt x = x ^ (1 / (2 : ℝ)) :=
  by
  refine' NNReal.eq _
  push_cast
  exact Real.sqrt_eq_rpow x.1
#align nnreal.sqrt_eq_rpow NNReal.sqrt_eq_rpow

#print NNReal.rpow_nat_cast /-
@[simp, norm_cast]
theorem rpow_nat_cast (x : ℝ≥0) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
  NNReal.eq <| by simpa only [coe_rpow, coe_pow] using Real.rpow_nat_cast x n
#align nnreal.rpow_nat_cast NNReal.rpow_nat_cast
-/

#print NNReal.rpow_two /-
@[simp]
theorem rpow_two (x : ℝ≥0) : x ^ (2 : ℝ) = x ^ 2 :=
  by
  rw [← rpow_nat_cast]
  simp only [Nat.cast_bit0, Nat.cast_one]
#align nnreal.rpow_two NNReal.rpow_two
-/

#print NNReal.mul_rpow /-
theorem mul_rpow {x y : ℝ≥0} {z : ℝ} : (x * y) ^ z = x ^ z * y ^ z :=
  NNReal.eq <| Real.mul_rpow x.2 y.2
#align nnreal.mul_rpow NNReal.mul_rpow
-/

/- warning: nnreal.rpow_le_rpow -> NNReal.rpow_le_rpow is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal} {z : Real}, (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x y) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) y z))
but is expected to have type
  forall {x : NNReal} {y : NNReal} {z : Real}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x y) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) y z))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_le_rpow NNReal.rpow_le_rpowₓ'. -/
theorem rpow_le_rpow {x y : ℝ≥0} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  Real.rpow_le_rpow x.2 h₁ h₂
#align nnreal.rpow_le_rpow NNReal.rpow_le_rpow

/- warning: nnreal.rpow_lt_rpow -> NNReal.rpow_lt_rpow is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal} {z : Real}, (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x y) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) y z))
but is expected to have type
  forall {x : NNReal} {y : NNReal} {z : Real}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x y) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) y z))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_lt_rpow NNReal.rpow_lt_rpowₓ'. -/
theorem rpow_lt_rpow {x y : ℝ≥0} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  Real.rpow_lt_rpow x.2 h₁ h₂
#align nnreal.rpow_lt_rpow NNReal.rpow_lt_rpow

/- warning: nnreal.rpow_lt_rpow_iff -> NNReal.rpow_lt_rpow_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Iff (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) y z)) (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x y))
but is expected to have type
  forall {x : NNReal} {y : NNReal} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) y z)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x y))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_lt_rpow_iff NNReal.rpow_lt_rpow_iffₓ'. -/
theorem rpow_lt_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  Real.rpow_lt_rpow_iff x.2 y.2 hz
#align nnreal.rpow_lt_rpow_iff NNReal.rpow_lt_rpow_iff

/- warning: nnreal.rpow_le_rpow_iff -> NNReal.rpow_le_rpow_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Iff (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) y z)) (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x y))
but is expected to have type
  forall {x : NNReal} {y : NNReal} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) y z)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x y))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_le_rpow_iff NNReal.rpow_le_rpow_iffₓ'. -/
theorem rpow_le_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  Real.rpow_le_rpow_iff x.2 y.2 hz
#align nnreal.rpow_le_rpow_iff NNReal.rpow_le_rpow_iff

/- warning: nnreal.le_rpow_one_div_iff -> NNReal.le_rpow_one_div_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Iff (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) z))) (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z) y))
but is expected to have type
  forall {x : NNReal} {y : NNReal} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) z))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z) y))
Case conversion may be inaccurate. Consider using '#align nnreal.le_rpow_one_div_iff NNReal.le_rpow_one_div_iffₓ'. -/
theorem le_rpow_one_div_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ≤ y ^ (1 / z) ↔ x ^ z ≤ y := by
  rw [← rpow_le_rpow_iff hz, rpow_self_rpow_inv hz.ne']
#align nnreal.le_rpow_one_div_iff NNReal.le_rpow_one_div_iff

/- warning: nnreal.rpow_one_div_le_iff -> NNReal.rpow_one_div_le_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Iff (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) z)) y) (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) y z)))
but is expected to have type
  forall {x : NNReal} {y : NNReal} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) z)) y) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) y z)))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_one_div_le_iff NNReal.rpow_one_div_le_iffₓ'. -/
theorem rpow_one_div_le_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ (1 / z) ≤ y ↔ x ≤ y ^ z := by
  rw [← rpow_le_rpow_iff hz, rpow_self_rpow_inv hz.ne']
#align nnreal.rpow_one_div_le_iff NNReal.rpow_one_div_le_iff

/- warning: nnreal.rpow_lt_rpow_of_exponent_lt -> NNReal.rpow_lt_rpow_of_exponent_lt is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : Real} {z : Real}, (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) x) -> (LT.lt.{0} Real Real.hasLt y z) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : NNReal} {y : Real} {z : Real}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) x) -> (LT.lt.{0} Real Real.instLTReal y z) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_lt_rpow_of_exponent_lt NNReal.rpow_lt_rpow_of_exponent_ltₓ'. -/
theorem rpow_lt_rpow_of_exponent_lt {x : ℝ≥0} {y z : ℝ} (hx : 1 < x) (hyz : y < z) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_lt hx hyz
#align nnreal.rpow_lt_rpow_of_exponent_lt NNReal.rpow_lt_rpow_of_exponent_lt

/- warning: nnreal.rpow_le_rpow_of_exponent_le -> NNReal.rpow_le_rpow_of_exponent_le is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : Real} {z : Real}, (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) x) -> (LE.le.{0} Real Real.hasLe y z) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : NNReal} {y : Real} {z : Real}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) x) -> (LE.le.{0} Real Real.instLEReal y z) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_le_rpow_of_exponent_le NNReal.rpow_le_rpow_of_exponent_leₓ'. -/
theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
    x ^ y ≤ x ^ z :=
  Real.rpow_le_rpow_of_exponent_le hx hyz
#align nnreal.rpow_le_rpow_of_exponent_le NNReal.rpow_le_rpow_of_exponent_le

/- warning: nnreal.rpow_lt_rpow_of_exponent_gt -> NNReal.rpow_lt_rpow_of_exponent_gt is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : Real} {z : Real}, (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) x) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (LT.lt.{0} Real Real.hasLt z y) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : NNReal} {y : Real} {z : Real}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) x) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) -> (LT.lt.{0} Real Real.instLTReal z y) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_lt_rpow_of_exponent_gt NNReal.rpow_lt_rpow_of_exponent_gtₓ'. -/
theorem rpow_lt_rpow_of_exponent_gt {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz
#align nnreal.rpow_lt_rpow_of_exponent_gt NNReal.rpow_lt_rpow_of_exponent_gt

/- warning: nnreal.rpow_le_rpow_of_exponent_ge -> NNReal.rpow_le_rpow_of_exponent_ge is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : Real} {z : Real}, (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) x) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (LE.le.{0} Real Real.hasLe z y) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : NNReal} {y : Real} {z : Real}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) x) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) -> (LE.le.{0} Real Real.instLEReal z y) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_le_rpow_of_exponent_ge NNReal.rpow_le_rpow_of_exponent_geₓ'. -/
theorem rpow_le_rpow_of_exponent_ge {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz
#align nnreal.rpow_le_rpow_of_exponent_ge NNReal.rpow_le_rpow_of_exponent_ge

/- warning: nnreal.rpow_pos -> NNReal.rpow_pos is a dubious translation:
lean 3 declaration is
  forall {p : Real} {x : NNReal}, (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) x) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x p))
but is expected to have type
  forall {p : Real} {x : NNReal}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) x) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x p))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_pos NNReal.rpow_posₓ'. -/
theorem rpow_pos {p : ℝ} {x : ℝ≥0} (hx_pos : 0 < x) : 0 < x ^ p :=
  by
  have rpow_pos_of_nonneg : ∀ {p : ℝ}, 0 < p → 0 < x ^ p :=
    by
    intro p hp_pos
    rw [← zero_rpow hp_pos.ne']
    exact rpow_lt_rpow hx_pos hp_pos
  rcases lt_trichotomy 0 p with (hp_pos | rfl | hp_neg)
  · exact rpow_pos_of_nonneg hp_pos
  · simp only [zero_lt_one, rpow_zero]
  · rw [← neg_neg p, rpow_neg, inv_pos]
    exact rpow_pos_of_nonneg (neg_pos.mpr hp_neg)
#align nnreal.rpow_pos NNReal.rpow_pos

/- warning: nnreal.rpow_lt_one -> NNReal.rpow_lt_one is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {z : Real}, (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {x : NNReal} {z : Real}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_lt_one NNReal.rpow_lt_oneₓ'. -/
theorem rpow_lt_one {x : ℝ≥0} {z : ℝ} (hx1 : x < 1) (hz : 0 < z) : x ^ z < 1 :=
  Real.rpow_lt_one (coe_nonneg x) hx1 hz
#align nnreal.rpow_lt_one NNReal.rpow_lt_one

/- warning: nnreal.rpow_le_one -> NNReal.rpow_le_one is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {z : Real}, (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {x : NNReal} {z : Real}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_le_one NNReal.rpow_le_oneₓ'. -/
theorem rpow_le_one {x : ℝ≥0} {z : ℝ} (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 :=
  Real.rpow_le_one x.2 hx2 hz
#align nnreal.rpow_le_one NNReal.rpow_le_one

/- warning: nnreal.rpow_lt_one_of_one_lt_of_neg -> NNReal.rpow_lt_one_of_one_lt_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {z : Real}, (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) x) -> (LT.lt.{0} Real Real.hasLt z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {x : NNReal} {z : Real}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) x) -> (LT.lt.{0} Real Real.instLTReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_lt_one_of_one_lt_of_neg NNReal.rpow_lt_one_of_one_lt_of_negₓ'. -/
theorem rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hx hz
#align nnreal.rpow_lt_one_of_one_lt_of_neg NNReal.rpow_lt_one_of_one_lt_of_neg

/- warning: nnreal.rpow_le_one_of_one_le_of_nonpos -> NNReal.rpow_le_one_of_one_le_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {z : Real}, (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) x) -> (LE.le.{0} Real Real.hasLe z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {x : NNReal} {z : Real}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) x) -> (LE.le.{0} Real Real.instLEReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_le_one_of_one_le_of_nonpos NNReal.rpow_le_one_of_one_le_of_nonposₓ'. -/
theorem rpow_le_one_of_one_le_of_nonpos {x : ℝ≥0} {z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx hz
#align nnreal.rpow_le_one_of_one_le_of_nonpos NNReal.rpow_le_one_of_one_le_of_nonpos

/- warning: nnreal.one_lt_rpow -> NNReal.one_lt_rpow is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {z : Real}, (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : NNReal} {z : Real}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align nnreal.one_lt_rpow NNReal.one_lt_rpowₓ'. -/
theorem one_lt_rpow {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z :=
  Real.one_lt_rpow hx hz
#align nnreal.one_lt_rpow NNReal.one_lt_rpow

/- warning: nnreal.one_le_rpow -> NNReal.one_le_rpow is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {z : Real}, (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : NNReal} {z : Real}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align nnreal.one_le_rpow NNReal.one_le_rpowₓ'. -/
theorem one_le_rpow {x : ℝ≥0} {z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x ^ z :=
  Real.one_le_rpow h h₁
#align nnreal.one_le_rpow NNReal.one_le_rpow

/- warning: nnreal.one_lt_rpow_of_pos_of_lt_one_of_neg -> NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {z : Real}, (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) x) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (LT.lt.{0} Real Real.hasLt z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : NNReal} {z : Real}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) x) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) -> (LT.lt.{0} Real Real.instLTReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align nnreal.one_lt_rpow_of_pos_of_lt_one_of_neg NNReal.one_lt_rpow_of_pos_of_lt_one_of_negₓ'. -/
theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z :=
  Real.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz
#align nnreal.one_lt_rpow_of_pos_of_lt_one_of_neg NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg

/- warning: nnreal.one_le_rpow_of_pos_of_le_one_of_nonpos -> NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {z : Real}, (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) x) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (LE.le.{0} Real Real.hasLe z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : NNReal} {z : Real}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) x) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) -> (LE.le.{0} Real Real.instLEReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align nnreal.one_le_rpow_of_pos_of_le_one_of_nonpos NNReal.one_le_rpow_of_pos_of_le_one_of_nonposₓ'. -/
theorem one_le_rpow_of_pos_of_le_one_of_nonpos {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
    (hz : z ≤ 0) : 1 ≤ x ^ z :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 hz
#align nnreal.one_le_rpow_of_pos_of_le_one_of_nonpos NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos

/- warning: nnreal.rpow_le_self_of_le_one -> NNReal.rpow_le_self_of_le_one is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {z : Real}, (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) z) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z) x)
but is expected to have type
  forall {x : NNReal} {z : Real}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) z) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z) x)
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_le_self_of_le_one NNReal.rpow_le_self_of_le_oneₓ'. -/
theorem rpow_le_self_of_le_one {x : ℝ≥0} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x :=
  by
  rcases eq_bot_or_bot_lt x with (rfl | (h : 0 < x))
  · have : z ≠ 0 := by linarith
    simp [this]
  nth_rw 2 [← NNReal.rpow_one x]
  exact NNReal.rpow_le_rpow_of_exponent_ge h hx h_one_le
#align nnreal.rpow_le_self_of_le_one NNReal.rpow_le_self_of_le_one

/- warning: nnreal.rpow_left_injective -> NNReal.rpow_left_injective is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Function.Injective.{1, 1} NNReal NNReal (fun (y : NNReal) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) y x))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Function.Injective.{1, 1} NNReal NNReal (fun (y : NNReal) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) y x))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_left_injective NNReal.rpow_left_injectiveₓ'. -/
theorem rpow_left_injective {x : ℝ} (hx : x ≠ 0) : Function.Injective fun y : ℝ≥0 => y ^ x :=
  fun y z hyz => by simpa only [rpow_inv_rpow_self hx] using congr_arg (fun y => y ^ (1 / x)) hyz
#align nnreal.rpow_left_injective NNReal.rpow_left_injective

/- warning: nnreal.rpow_eq_rpow_iff -> NNReal.rpow_eq_rpow_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal} {z : Real}, (Ne.{1} Real z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Iff (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) y z)) (Eq.{1} NNReal x y))
but is expected to have type
  forall {x : NNReal} {y : NNReal} {z : Real}, (Ne.{1} Real z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Iff (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) y z)) (Eq.{1} NNReal x y))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_eq_rpow_iff NNReal.rpow_eq_rpow_iffₓ'. -/
theorem rpow_eq_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x ^ z = y ^ z ↔ x = y :=
  (rpow_left_injective hz).eq_iff
#align nnreal.rpow_eq_rpow_iff NNReal.rpow_eq_rpow_iff

/- warning: nnreal.rpow_left_surjective -> NNReal.rpow_left_surjective is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Function.Surjective.{1, 1} NNReal NNReal (fun (y : NNReal) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) y x))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Function.Surjective.{1, 1} NNReal NNReal (fun (y : NNReal) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) y x))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_left_surjective NNReal.rpow_left_surjectiveₓ'. -/
theorem rpow_left_surjective {x : ℝ} (hx : x ≠ 0) : Function.Surjective fun y : ℝ≥0 => y ^ x :=
  fun y => ⟨y ^ x⁻¹, by simp_rw [← rpow_mul, _root_.inv_mul_cancel hx, rpow_one]⟩
#align nnreal.rpow_left_surjective NNReal.rpow_left_surjective

/- warning: nnreal.rpow_left_bijective -> NNReal.rpow_left_bijective is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Function.Bijective.{1, 1} NNReal NNReal (fun (y : NNReal) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) y x))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Function.Bijective.{1, 1} NNReal NNReal (fun (y : NNReal) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) y x))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_left_bijective NNReal.rpow_left_bijectiveₓ'. -/
theorem rpow_left_bijective {x : ℝ} (hx : x ≠ 0) : Function.Bijective fun y : ℝ≥0 => y ^ x :=
  ⟨rpow_left_injective hx, rpow_left_surjective hx⟩
#align nnreal.rpow_left_bijective NNReal.rpow_left_bijective

/- warning: nnreal.eq_rpow_one_div_iff -> NNReal.eq_rpow_one_div_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal} {z : Real}, (Ne.{1} Real z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Iff (Eq.{1} NNReal x (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) z))) (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x z) y))
but is expected to have type
  forall {x : NNReal} {y : NNReal} {z : Real}, (Ne.{1} Real z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Iff (Eq.{1} NNReal x (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) z))) (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x z) y))
Case conversion may be inaccurate. Consider using '#align nnreal.eq_rpow_one_div_iff NNReal.eq_rpow_one_div_iffₓ'. -/
theorem eq_rpow_one_div_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x = y ^ (1 / z) ↔ x ^ z = y := by
  rw [← rpow_eq_rpow_iff hz, rpow_self_rpow_inv hz]
#align nnreal.eq_rpow_one_div_iff NNReal.eq_rpow_one_div_iff

/- warning: nnreal.rpow_one_div_eq_iff -> NNReal.rpow_one_div_eq_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal} {z : Real}, (Ne.{1} Real z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Iff (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) z)) y) (Eq.{1} NNReal x (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) y z)))
but is expected to have type
  forall {x : NNReal} {y : NNReal} {z : Real}, (Ne.{1} Real z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Iff (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) z)) y) (Eq.{1} NNReal x (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) y z)))
Case conversion may be inaccurate. Consider using '#align nnreal.rpow_one_div_eq_iff NNReal.rpow_one_div_eq_iffₓ'. -/
theorem rpow_one_div_eq_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x ^ (1 / z) = y ↔ x = y ^ z := by
  rw [← rpow_eq_rpow_iff hz, rpow_self_rpow_inv hz]
#align nnreal.rpow_one_div_eq_iff NNReal.rpow_one_div_eq_iff

#print NNReal.pow_nat_rpow_nat_inv /-
theorem pow_nat_rpow_nat_inv (x : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : (x ^ n) ^ (n⁻¹ : ℝ) = x :=
  by
  rw [← NNReal.coe_eq, coe_rpow, NNReal.coe_pow]
  exact Real.pow_nat_rpow_nat_inv x.2 hn
#align nnreal.pow_nat_rpow_nat_inv NNReal.pow_nat_rpow_nat_inv
-/

#print NNReal.rpow_nat_inv_pow_nat /-
theorem rpow_nat_inv_pow_nat (x : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℝ)) ^ n = x :=
  by
  rw [← NNReal.coe_eq, NNReal.coe_pow, coe_rpow]
  exact Real.rpow_nat_inv_pow_nat x.2 hn
#align nnreal.rpow_nat_inv_pow_nat NNReal.rpow_nat_inv_pow_nat
-/

/- warning: real.to_nnreal_rpow_of_nonneg -> Real.toNNReal_rpow_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} NNReal (Real.toNNReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y)) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) (Real.toNNReal x) y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} NNReal (Real.toNNReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y)) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) (Real.toNNReal x) y))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_rpow_of_nonneg Real.toNNReal_rpow_of_nonnegₓ'. -/
theorem Real.toNNReal_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) :
    Real.toNNReal (x ^ y) = Real.toNNReal x ^ y :=
  by
  nth_rw 1 [← Real.coe_toNNReal x hx]
  rw [← NNReal.coe_rpow, Real.toNNReal_coe]
#align real.to_nnreal_rpow_of_nonneg Real.toNNReal_rpow_of_nonneg

end NNReal

namespace ENNReal

#print ENNReal.rpow /-
/-- The real power function `x^y` on extended nonnegative reals, defined for `x : ℝ≥0∞` and
`y : ℝ` as the restriction of the real power function if `0 < x < ⊤`, and with the natural values
for `0` and `⊤` (i.e., `0 ^ x = 0` for `x > 0`, `1` for `x = 0` and `⊤` for `x < 0`, and
`⊤ ^ x = 1 / 0 ^ x`). -/
noncomputable def rpow : ℝ≥0∞ → ℝ → ℝ≥0∞
  | some x, y => if x = 0 ∧ y < 0 then ⊤ else (x ^ y : ℝ≥0)
  | none, y => if 0 < y then ⊤ else if y = 0 then 1 else 0
#align ennreal.rpow ENNReal.rpow
-/

noncomputable instance : Pow ℝ≥0∞ ℝ :=
  ⟨rpow⟩

#print ENNReal.rpow_eq_pow /-
@[simp]
theorem rpow_eq_pow (x : ℝ≥0∞) (y : ℝ) : rpow x y = x ^ y :=
  rfl
#align ennreal.rpow_eq_pow ENNReal.rpow_eq_pow
-/

/- warning: ennreal.rpow_zero -> ENNReal.rpow_zero is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal}, Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))
but is expected to have type
  forall {x : ENNReal}, Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_zero ENNReal.rpow_zeroₓ'. -/
@[simp]
theorem rpow_zero {x : ℝ≥0∞} : x ^ (0 : ℝ) = 1 := by
  cases x <;>
    · dsimp only [(· ^ ·), rpow]
      simp [lt_irrefl]
#align ennreal.rpow_zero ENNReal.rpow_zero

/- warning: ennreal.top_rpow_def -> ENNReal.top_rpow_def is a dubious translation:
lean 3 declaration is
  forall (y : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) y) (ite.{1} ENNReal (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) (Real.decidableLT (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (ite.{1} ENNReal (Eq.{1} Real y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Real.decidableEq y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall (y : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) y) (ite.{1} ENNReal (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) (Real.decidableLT (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (ite.{1} ENNReal (Eq.{1} Real y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Real.decidableEq y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align ennreal.top_rpow_def ENNReal.top_rpow_defₓ'. -/
theorem top_rpow_def (y : ℝ) : (⊤ : ℝ≥0∞) ^ y = if 0 < y then ⊤ else if y = 0 then 1 else 0 :=
  rfl
#align ennreal.top_rpow_def ENNReal.top_rpow_def

/- warning: ennreal.top_rpow_of_pos -> ENNReal.top_rpow_of_pos is a dubious translation:
lean 3 declaration is
  forall {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.top_rpow_of_pos ENNReal.top_rpow_of_posₓ'. -/
@[simp]
theorem top_rpow_of_pos {y : ℝ} (h : 0 < y) : (⊤ : ℝ≥0∞) ^ y = ⊤ := by simp [top_rpow_def, h]
#align ennreal.top_rpow_of_pos ENNReal.top_rpow_of_pos

/- warning: ennreal.top_rpow_of_neg -> ENNReal.top_rpow_of_neg is a dubious translation:
lean 3 declaration is
  forall {y : Real}, (LT.lt.{0} Real Real.hasLt y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) y) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {y : Real}, (LT.lt.{0} Real Real.instLTReal y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) y) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align ennreal.top_rpow_of_neg ENNReal.top_rpow_of_negₓ'. -/
@[simp]
theorem top_rpow_of_neg {y : ℝ} (h : y < 0) : (⊤ : ℝ≥0∞) ^ y = 0 := by
  simp [top_rpow_def, asymm h, ne_of_lt h]
#align ennreal.top_rpow_of_neg ENNReal.top_rpow_of_neg

/- warning: ennreal.zero_rpow_of_pos -> ENNReal.zero_rpow_of_pos is a dubious translation:
lean 3 declaration is
  forall {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) y) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) y) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align ennreal.zero_rpow_of_pos ENNReal.zero_rpow_of_posₓ'. -/
@[simp]
theorem zero_rpow_of_pos {y : ℝ} (h : 0 < y) : (0 : ℝ≥0∞) ^ y = 0 :=
  by
  rw [← ENNReal.coe_zero, ← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow]
  simp [h, asymm h, ne_of_gt h]
#align ennreal.zero_rpow_of_pos ENNReal.zero_rpow_of_pos

/- warning: ennreal.zero_rpow_of_neg -> ENNReal.zero_rpow_of_neg is a dubious translation:
lean 3 declaration is
  forall {y : Real}, (LT.lt.{0} Real Real.hasLt y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {y : Real}, (LT.lt.{0} Real Real.instLTReal y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.zero_rpow_of_neg ENNReal.zero_rpow_of_negₓ'. -/
@[simp]
theorem zero_rpow_of_neg {y : ℝ} (h : y < 0) : (0 : ℝ≥0∞) ^ y = ⊤ :=
  by
  rw [← ENNReal.coe_zero, ← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow]
  simp [h, ne_of_gt h]
#align ennreal.zero_rpow_of_neg ENNReal.zero_rpow_of_neg

#print ENNReal.zero_rpow_def /-
theorem zero_rpow_def (y : ℝ) : (0 : ℝ≥0∞) ^ y = if 0 < y then 0 else if y = 0 then 1 else ⊤ :=
  by
  rcases lt_trichotomy 0 y with (H | rfl | H)
  · simp [H, ne_of_gt, zero_rpow_of_pos, lt_irrefl]
  · simp [lt_irrefl]
  · simp [H, asymm H, ne_of_lt, zero_rpow_of_neg]
#align ennreal.zero_rpow_def ENNReal.zero_rpow_def
-/

/- warning: ennreal.zero_rpow_mul_self -> ENNReal.zero_rpow_mul_self is a dubious translation:
lean 3 declaration is
  forall (y : Real), Eq.{1} ENNReal (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) y)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) y)
but is expected to have type
  forall (y : Real), Eq.{1} ENNReal (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) y)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) y)
Case conversion may be inaccurate. Consider using '#align ennreal.zero_rpow_mul_self ENNReal.zero_rpow_mul_selfₓ'. -/
@[simp]
theorem zero_rpow_mul_self (y : ℝ) : (0 : ℝ≥0∞) ^ y * 0 ^ y = 0 ^ y :=
  by
  rw [zero_rpow_def]
  split_ifs
  exacts[MulZeroClass.zero_mul _, one_mul _, top_mul_top]
#align ennreal.zero_rpow_mul_self ENNReal.zero_rpow_mul_self

/- warning: ennreal.coe_rpow_of_ne_zero -> ENNReal.coe_rpow_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {x : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (forall (y : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) x) y) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y)))
but is expected to have type
  forall {x : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (forall (y : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (ENNReal.some x) y) (ENNReal.some (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y)))
Case conversion may be inaccurate. Consider using '#align ennreal.coe_rpow_of_ne_zero ENNReal.coe_rpow_of_ne_zeroₓ'. -/
@[norm_cast]
theorem coe_rpow_of_ne_zero {x : ℝ≥0} (h : x ≠ 0) (y : ℝ) : (x : ℝ≥0∞) ^ y = (x ^ y : ℝ≥0) :=
  by
  rw [← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow]
  simp [h]
#align ennreal.coe_rpow_of_ne_zero ENNReal.coe_rpow_of_ne_zero

/- warning: ennreal.coe_rpow_of_nonneg -> ENNReal.coe_rpow_of_nonneg is a dubious translation:
lean 3 declaration is
  forall (x : NNReal) {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) x) y) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y)))
but is expected to have type
  forall (x : NNReal) {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (ENNReal.some x) y) (ENNReal.some (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y)))
Case conversion may be inaccurate. Consider using '#align ennreal.coe_rpow_of_nonneg ENNReal.coe_rpow_of_nonnegₓ'. -/
@[norm_cast]
theorem coe_rpow_of_nonneg (x : ℝ≥0) {y : ℝ} (h : 0 ≤ y) : (x : ℝ≥0∞) ^ y = (x ^ y : ℝ≥0) :=
  by
  by_cases hx : x = 0
  · rcases le_iff_eq_or_lt.1 h with (H | H)
    · simp [hx, H.symm]
    · simp [hx, zero_rpow_of_pos H, NNReal.zero_rpow (ne_of_gt H)]
  · exact coe_rpow_of_ne_zero hx _
#align ennreal.coe_rpow_of_nonneg ENNReal.coe_rpow_of_nonneg

/- warning: ennreal.coe_rpow_def -> ENNReal.coe_rpow_def is a dubious translation:
lean 3 declaration is
  forall (x : NNReal) (y : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) x) y) (ite.{1} ENNReal (And (Eq.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (LT.lt.{0} Real Real.hasLt y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (And.decidable (Eq.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (LT.lt.{0} Real Real.hasLt y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Subtype.decidableEq.{0} Real (fun (x : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) (fun (a : Real) (b : Real) => Real.decidableEq a b) x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (Real.decidableLT y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y)))
but is expected to have type
  forall (x : NNReal) (y : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (ENNReal.some x) y) (ite.{1} ENNReal (And (Eq.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (LT.lt.{0} Real Real.instLTReal y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (instDecidableAnd (Eq.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (LT.lt.{0} Real Real.instLTReal y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (instDecidableEq.{0} NNReal (instLinearOrder.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal)) x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (Real.decidableLT y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (ENNReal.some (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y)))
Case conversion may be inaccurate. Consider using '#align ennreal.coe_rpow_def ENNReal.coe_rpow_defₓ'. -/
theorem coe_rpow_def (x : ℝ≥0) (y : ℝ) :
    (x : ℝ≥0∞) ^ y = if x = 0 ∧ y < 0 then ⊤ else (x ^ y : ℝ≥0) :=
  rfl
#align ennreal.coe_rpow_def ENNReal.coe_rpow_def

/- warning: ennreal.rpow_one -> ENNReal.rpow_one is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) x
but is expected to have type
  forall (x : ENNReal), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_one ENNReal.rpow_oneₓ'. -/
@[simp]
theorem rpow_one (x : ℝ≥0∞) : x ^ (1 : ℝ) = x :=
  by
  cases x
  · exact dif_pos zero_lt_one
  · change ite _ _ _ = _
    simp only [NNReal.rpow_one, some_eq_coe, ite_eq_right_iff, top_ne_coe, and_imp]
    exact fun _ => zero_le_one.not_lt
#align ennreal.rpow_one ENNReal.rpow_one

#print ENNReal.one_rpow /-
@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ≥0∞) ^ x = 1 :=
  by
  rw [← coe_one, coe_rpow_of_ne_zero one_ne_zero]
  simp
#align ennreal.one_rpow ENNReal.one_rpow
-/

/- warning: ennreal.rpow_eq_zero_iff -> ENNReal.rpow_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : Real}, Iff (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Or (And (Eq.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y)) (And (Eq.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (LT.lt.{0} Real Real.hasLt y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))
but is expected to have type
  forall {x : ENNReal} {y : Real}, Iff (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Or (And (Eq.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y)) (And (Eq.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (LT.lt.{0} Real Real.instLTReal y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_eq_zero_iff ENNReal.rpow_eq_zero_iffₓ'. -/
@[simp]
theorem rpow_eq_zero_iff {x : ℝ≥0∞} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ 0 < y ∨ x = ⊤ ∧ y < 0 :=
  by
  cases x
  ·
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  · by_cases h : x = 0
    ·
      rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [coe_rpow_of_ne_zero h, h]
#align ennreal.rpow_eq_zero_iff ENNReal.rpow_eq_zero_iff

/- warning: ennreal.rpow_eq_top_iff -> ENNReal.rpow_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : Real}, Iff (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Or (And (Eq.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (LT.lt.{0} Real Real.hasLt y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (And (Eq.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y)))
but is expected to have type
  forall {x : ENNReal} {y : Real}, Iff (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Or (And (Eq.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (LT.lt.{0} Real Real.instLTReal y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (And (Eq.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y)))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_eq_top_iff ENNReal.rpow_eq_top_iffₓ'. -/
@[simp]
theorem rpow_eq_top_iff {x : ℝ≥0∞} {y : ℝ} : x ^ y = ⊤ ↔ x = 0 ∧ y < 0 ∨ x = ⊤ ∧ 0 < y :=
  by
  cases x
  ·
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  · by_cases h : x = 0
    ·
      rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [coe_rpow_of_ne_zero h, h]
#align ennreal.rpow_eq_top_iff ENNReal.rpow_eq_top_iff

/- warning: ennreal.rpow_eq_top_iff_of_pos -> ENNReal.rpow_eq_top_iff_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Eq.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {x : ENNReal} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Eq.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_eq_top_iff_of_pos ENNReal.rpow_eq_top_iff_of_posₓ'. -/
theorem rpow_eq_top_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y = ⊤ ↔ x = ⊤ := by
  simp [rpow_eq_top_iff, hy, asymm hy]
#align ennreal.rpow_eq_top_iff_of_pos ENNReal.rpow_eq_top_iff_of_pos

/- warning: ennreal.rpow_eq_top_of_nonneg -> ENNReal.rpow_eq_top_of_nonneg is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal) {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall (x : ENNReal) {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_eq_top_of_nonneg ENNReal.rpow_eq_top_of_nonnegₓ'. -/
theorem rpow_eq_top_of_nonneg (x : ℝ≥0∞) {y : ℝ} (hy0 : 0 ≤ y) : x ^ y = ⊤ → x = ⊤ :=
  by
  rw [ENNReal.rpow_eq_top_iff]
  intro h
  cases h
  · exfalso
    rw [lt_iff_not_ge] at h
    exact h.right hy0
  · exact h.left
#align ennreal.rpow_eq_top_of_nonneg ENNReal.rpow_eq_top_of_nonneg

/- warning: ennreal.rpow_ne_top_of_nonneg -> ENNReal.rpow_ne_top_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Ne.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {x : ENNReal} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Ne.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_ne_top_of_nonneg ENNReal.rpow_ne_top_of_nonnegₓ'. -/
theorem rpow_ne_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y ≠ ⊤ :=
  mt (ENNReal.rpow_eq_top_of_nonneg x hy0) h
#align ennreal.rpow_ne_top_of_nonneg ENNReal.rpow_ne_top_of_nonneg

/- warning: ennreal.rpow_lt_top_of_nonneg -> ENNReal.rpow_lt_top_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {x : ENNReal} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_lt_top_of_nonneg ENNReal.rpow_lt_top_of_nonnegₓ'. -/
theorem rpow_lt_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y < ⊤ :=
  lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hy0 h)
#align ennreal.rpow_lt_top_of_nonneg ENNReal.rpow_lt_top_of_nonneg

/- warning: ennreal.rpow_add -> ENNReal.rpow_add is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} (y : Real) (z : Real), (Ne.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) y z)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z)))
but is expected to have type
  forall {x : ENNReal} (y : Real) (z : Real), (Ne.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) y z)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z)))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_add ENNReal.rpow_addₓ'. -/
theorem rpow_add {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y + z) = x ^ y * x ^ z :=
  by
  cases x; · exact (h'x rfl).elim
  have : x ≠ 0 := fun h => by simpa [h] using hx
  simp [coe_rpow_of_ne_zero this, NNReal.rpow_add this]
#align ennreal.rpow_add ENNReal.rpow_add

/- warning: ennreal.rpow_neg -> ENNReal.rpow_neg is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal) (y : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x (Neg.neg.{0} Real Real.hasNeg y)) (Inv.inv.{0} ENNReal ENNReal.hasInv (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y))
but is expected to have type
  forall (x : ENNReal) (y : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x (Neg.neg.{0} Real Real.instNegReal y)) (Inv.inv.{0} ENNReal ENNReal.instInvENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_neg ENNReal.rpow_negₓ'. -/
theorem rpow_neg (x : ℝ≥0∞) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ :=
  by
  cases x
  ·
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [top_rpow_of_pos, top_rpow_of_neg, H, neg_pos.mpr]
  · by_cases h : x = 0
    ·
      rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, zero_rpow_of_pos, zero_rpow_of_neg, H, neg_pos.mpr]
    · have A : x ^ y ≠ 0 := by simp [h]
      simp [coe_rpow_of_ne_zero h, ← coe_inv A, NNReal.rpow_neg]
#align ennreal.rpow_neg ENNReal.rpow_neg

/- warning: ennreal.rpow_sub -> ENNReal.rpow_sub is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} (y : Real) (z : Real), (Ne.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y z)) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z)))
but is expected to have type
  forall {x : ENNReal} (y : Real) (z : Real), (Ne.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y z)) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z)))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_sub ENNReal.rpow_subₓ'. -/
theorem rpow_sub {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y - z) = x ^ y / x ^ z := by
  rw [sub_eq_add_neg, rpow_add _ _ hx h'x, rpow_neg, div_eq_mul_inv]
#align ennreal.rpow_sub ENNReal.rpow_sub

/- warning: ennreal.rpow_neg_one -> ENNReal.rpow_neg_one is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Inv.inv.{0} ENNReal ENNReal.hasInv x)
but is expected to have type
  forall (x : ENNReal), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Inv.inv.{0} ENNReal ENNReal.instInvENNReal x)
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_neg_one ENNReal.rpow_neg_oneₓ'. -/
theorem rpow_neg_one (x : ℝ≥0∞) : x ^ (-1 : ℝ) = x⁻¹ := by simp [rpow_neg]
#align ennreal.rpow_neg_one ENNReal.rpow_neg_one

/- warning: ennreal.rpow_mul -> ENNReal.rpow_mul is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal) (y : Real) (z : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) y z)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) z)
but is expected to have type
  forall (x : ENNReal) (y : Real) (z : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) y z)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) z)
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_mul ENNReal.rpow_mulₓ'. -/
theorem rpow_mul (x : ℝ≥0∞) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
  by
  cases x
  ·
    rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
        rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
      simp [Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
        mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
  · by_cases h : x = 0
    ·
      rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
          rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
        simp [h, Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
          mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
    · have : x ^ y ≠ 0 := by simp [h]
      simp [coe_rpow_of_ne_zero h, coe_rpow_of_ne_zero this, NNReal.rpow_mul]
#align ennreal.rpow_mul ENNReal.rpow_mul

/- warning: ennreal.rpow_nat_cast -> ENNReal.rpow_nat_cast is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal) (n : Nat), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)) (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) x n)
but is expected to have type
  forall (x : ENNReal) (n : Nat), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x (Nat.cast.{0} Real Real.natCast n)) (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))) x n)
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_nat_cast ENNReal.rpow_nat_castₓ'. -/
@[simp, norm_cast]
theorem rpow_nat_cast (x : ℝ≥0∞) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
  by
  cases x
  · cases n <;> simp [top_rpow_of_pos (Nat.cast_add_one_pos _), top_pow (Nat.succ_pos _)]
  · simp [coe_rpow_of_nonneg _ (Nat.cast_nonneg n)]
#align ennreal.rpow_nat_cast ENNReal.rpow_nat_cast

/- warning: ennreal.rpow_two -> ENNReal.rpow_two is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall (x : ENNReal), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_two ENNReal.rpow_twoₓ'. -/
@[simp]
theorem rpow_two (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 :=
  by
  rw [← rpow_nat_cast]
  simp only [Nat.cast_bit0, Nat.cast_one]
#align ennreal.rpow_two ENNReal.rpow_two

/- warning: ennreal.mul_rpow_eq_ite -> ENNReal.mul_rpow_eq_ite is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ennreal.mul_rpow_eq_ite ENNReal.mul_rpow_eq_iteₓ'. -/
theorem mul_rpow_eq_ite (x y : ℝ≥0∞) (z : ℝ) :
    (x * y) ^ z = if (x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0) ∧ z < 0 then ⊤ else x ^ z * y ^ z :=
  by
  rcases eq_or_ne z 0 with (rfl | hz); · simp
  replace hz := hz.lt_or_lt
  wlog hxy : x ≤ y
  · convert this y x z hz (le_of_not_le hxy) using 2 <;> simp only [mul_comm, and_comm', or_comm']
  rcases eq_or_ne x 0 with (rfl | hx0)
  · induction y using WithTop.recTopCoe <;> cases' hz with hz hz <;> simp [*, hz.not_lt]
  rcases eq_or_ne y 0 with (rfl | hy0); · exact (hx0 (bot_unique hxy)).elim
  induction x using WithTop.recTopCoe; · cases' hz with hz hz <;> simp [hz, top_unique hxy]
  induction y using WithTop.recTopCoe; · cases' hz with hz hz <;> simp [*]
  simp only [*, false_and_iff, and_false_iff, false_or_iff, if_false]
  norm_cast  at *
  rw [coe_rpow_of_ne_zero (mul_ne_zero hx0 hy0), NNReal.mul_rpow]
#align ennreal.mul_rpow_eq_ite ENNReal.mul_rpow_eq_ite

/- warning: ennreal.mul_rpow_of_ne_top -> ENNReal.mul_rpow_of_ne_top is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Ne.{1} ENNReal y (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall (z : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) x y) z) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y z)))
but is expected to have type
  forall {x : ENNReal} {y : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Ne.{1} ENNReal y (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall (z : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) x y) z) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y z)))
Case conversion may be inaccurate. Consider using '#align ennreal.mul_rpow_of_ne_top ENNReal.mul_rpow_of_ne_topₓ'. -/
theorem mul_rpow_of_ne_top {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_rpow_eq_ite]
#align ennreal.mul_rpow_of_ne_top ENNReal.mul_rpow_of_ne_top

/- warning: ennreal.coe_mul_rpow -> ENNReal.coe_mul_rpow is a dubious translation:
lean 3 declaration is
  forall (x : NNReal) (y : NNReal) (z : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) y)) z) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) x) z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) y) z))
but is expected to have type
  forall (x : NNReal) (y : NNReal) (z : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some x) (ENNReal.some y)) z) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (ENNReal.some x) z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (ENNReal.some y) z))
Case conversion may be inaccurate. Consider using '#align ennreal.coe_mul_rpow ENNReal.coe_mul_rpowₓ'. -/
@[norm_cast]
theorem coe_mul_rpow (x y : ℝ≥0) (z : ℝ) : ((x : ℝ≥0∞) * y) ^ z = x ^ z * y ^ z :=
  mul_rpow_of_ne_top coe_ne_top coe_ne_top z
#align ennreal.coe_mul_rpow ENNReal.coe_mul_rpow

/- warning: ennreal.mul_rpow_of_ne_zero -> ENNReal.mul_rpow_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : ENNReal}, (Ne.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Ne.{1} ENNReal y (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (forall (z : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) x y) z) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y z)))
but is expected to have type
  forall {x : ENNReal} {y : ENNReal}, (Ne.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Ne.{1} ENNReal y (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (forall (z : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) x y) z) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y z)))
Case conversion may be inaccurate. Consider using '#align ennreal.mul_rpow_of_ne_zero ENNReal.mul_rpow_of_ne_zeroₓ'. -/
theorem mul_rpow_of_ne_zero {x y : ℝ≥0∞} (hx : x ≠ 0) (hy : y ≠ 0) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_rpow_eq_ite]
#align ennreal.mul_rpow_of_ne_zero ENNReal.mul_rpow_of_ne_zero

/- warning: ennreal.mul_rpow_of_nonneg -> ENNReal.mul_rpow_of_nonneg is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal) (y : ENNReal) {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) x y) z) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y z)))
but is expected to have type
  forall (x : ENNReal) (y : ENNReal) {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) x y) z) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y z)))
Case conversion may be inaccurate. Consider using '#align ennreal.mul_rpow_of_nonneg ENNReal.mul_rpow_of_nonnegₓ'. -/
theorem mul_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x * y) ^ z = x ^ z * y ^ z := by
  simp [hz.not_lt, mul_rpow_eq_ite]
#align ennreal.mul_rpow_of_nonneg ENNReal.mul_rpow_of_nonneg

/- warning: ennreal.inv_rpow -> ENNReal.inv_rpow is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal) (y : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (Inv.inv.{0} ENNReal ENNReal.hasInv x) y) (Inv.inv.{0} ENNReal ENNReal.hasInv (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y))
but is expected to have type
  forall (x : ENNReal) (y : Real), Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (Inv.inv.{0} ENNReal ENNReal.instInvENNReal x) y) (Inv.inv.{0} ENNReal ENNReal.instInvENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y))
Case conversion may be inaccurate. Consider using '#align ennreal.inv_rpow ENNReal.inv_rpowₓ'. -/
theorem inv_rpow (x : ℝ≥0∞) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ :=
  by
  rcases eq_or_ne y 0 with (rfl | hy); · simp only [rpow_zero, inv_one]
  replace hy := hy.lt_or_lt
  rcases eq_or_ne x 0 with (rfl | h0); · cases hy <;> simp [*]
  rcases eq_or_ne x ⊤ with (rfl | h_top); · cases hy <;> simp [*]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [← mul_rpow_of_ne_zero (ENNReal.inv_ne_zero.2 h_top) h0, ENNReal.inv_mul_cancel h0 h_top,
    one_rpow]
#align ennreal.inv_rpow ENNReal.inv_rpow

/- warning: ennreal.div_rpow_of_nonneg -> ENNReal.div_rpow_of_nonneg is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal) (y : ENNReal) {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) x y) z) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y z)))
but is expected to have type
  forall (x : ENNReal) (y : ENNReal) {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) x y) z) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y z)))
Case conversion may be inaccurate. Consider using '#align ennreal.div_rpow_of_nonneg ENNReal.div_rpow_of_nonnegₓ'. -/
theorem div_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x / y) ^ z = x ^ z / y ^ z := by
  rw [div_eq_mul_inv, mul_rpow_of_nonneg _ _ hz, inv_rpow, div_eq_mul_inv]
#align ennreal.div_rpow_of_nonneg ENNReal.div_rpow_of_nonneg

/- warning: ennreal.strict_mono_rpow_of_pos -> ENNReal.strictMono_rpow_of_pos is a dubious translation:
lean 3 declaration is
  forall {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (StrictMono.{0, 0} ENNReal ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (fun (x : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z))
but is expected to have type
  forall {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (StrictMono.{0, 0} ENNReal ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (fun (x : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align ennreal.strict_mono_rpow_of_pos ENNReal.strictMono_rpow_of_posₓ'. -/
theorem strictMono_rpow_of_pos {z : ℝ} (h : 0 < z) : StrictMono fun x : ℝ≥0∞ => x ^ z :=
  by
  intro x y hxy
  lift x to ℝ≥0 using ne_top_of_lt hxy
  rcases eq_or_ne y ∞ with (rfl | hy)
  · simp only [top_rpow_of_pos h, coe_rpow_of_nonneg _ h.le, coe_lt_top]
  · lift y to ℝ≥0 using hy
    simp only [coe_rpow_of_nonneg _ h.le, NNReal.rpow_lt_rpow (coe_lt_coe.1 hxy) h, coe_lt_coe]
#align ennreal.strict_mono_rpow_of_pos ENNReal.strictMono_rpow_of_pos

/- warning: ennreal.monotone_rpow_of_nonneg -> ENNReal.monotone_rpow_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {z : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Monotone.{0, 0} ENNReal ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (fun (x : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z))
but is expected to have type
  forall {z : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Monotone.{0, 0} ENNReal ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (fun (x : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align ennreal.monotone_rpow_of_nonneg ENNReal.monotone_rpow_of_nonnegₓ'. -/
theorem monotone_rpow_of_nonneg {z : ℝ} (h : 0 ≤ z) : Monotone fun x : ℝ≥0∞ => x ^ z :=
  h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).Monotone
#align ennreal.monotone_rpow_of_nonneg ENNReal.monotone_rpow_of_nonneg

/- warning: ennreal.order_iso_rpow -> ENNReal.orderIsoRpow is a dubious translation:
lean 3 declaration is
  forall (y : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (OrderIso.{0, 0} ENNReal ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))))
but is expected to have type
  forall (y : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (OrderIso.{0, 0} ENNReal ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))))
Case conversion may be inaccurate. Consider using '#align ennreal.order_iso_rpow ENNReal.orderIsoRpowₓ'. -/
/-- Bundles `λ x : ℝ≥0∞, x ^ y` into an order isomorphism when `y : ℝ` is positive,
where the inverse is `λ x : ℝ≥0∞, x ^ (1 / y)`. -/
@[simps apply]
def orderIsoRpow (y : ℝ) (hy : 0 < y) : ℝ≥0∞ ≃o ℝ≥0∞ :=
  (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
    dsimp
    rw [← rpow_mul, one_div_mul_cancel hy.ne.symm, rpow_one]
#align ennreal.order_iso_rpow ENNReal.orderIsoRpow

/- warning: ennreal.order_iso_rpow_symm_apply -> ENNReal.orderIsoRpow_symm_apply is a dubious translation:
lean 3 declaration is
  forall (y : Real) (hy : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y), Eq.{1} (OrderIso.{0, 0} ENNReal ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) (OrderIso.symm.{0, 0} ENNReal ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (ENNReal.orderIsoRpow y hy)) (ENNReal.orderIsoRpow (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real (NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (Semiring.toNonAssocSemiring.{0} Real (StrictOrderedSemiring.toSemiring.{0} Real (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Real (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Real (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.linearOrderedField)))))))))))) y) (Iff.mpr (LT.lt.{0} Real (Preorder.toHasLt.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedCancelAddCommMonoid.toPartialOrder.{0} Real (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Real (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Real (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Real (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.linearOrderedField)))))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real (MulZeroClass.toHasZero.{0} Real (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (StrictOrderedSemiring.toSemiring.{0} Real (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Real (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Real (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.linearOrderedField)))))))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (GroupWithZero.toDivInvMonoid.{0} Real (DivisionSemiring.toGroupWithZero.{0} Real (Semifield.toDivisionSemiring.{0} Real (LinearOrderedSemifield.toSemifield.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.linearOrderedField))))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real (NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (Semiring.toNonAssocSemiring.{0} Real (StrictOrderedSemiring.toSemiring.{0} Real (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Real (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Real (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.linearOrderedField)))))))))))) y)) (LT.lt.{0} Real (Preorder.toHasLt.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedCancelAddCommMonoid.toPartialOrder.{0} Real (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Real (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Real (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Real (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.linearOrderedField)))))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real (MulZeroClass.toHasZero.{0} Real (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (StrictOrderedSemiring.toSemiring.{0} Real (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Real (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Real (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.linearOrderedField)))))))))))) y) (one_div_pos.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.linearOrderedField) y) hy))
but is expected to have type
  forall (y : Real) (hy : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y), Eq.{1} (OrderIso.{0, 0} ENNReal ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) (OrderIso.symm.{0, 0} ENNReal ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (ENNReal.orderIsoRpow y hy)) (ENNReal.orderIsoRpow (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real (Semiring.toOne.{0} Real (StrictOrderedSemiring.toSemiring.{0} Real (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Real (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Real (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.instLinearOrderedFieldReal)))))))) y) (Iff.mpr (LT.lt.{0} Real (Preorder.toLT.{0} Real (PartialOrder.toPreorder.{0} Real (StrictOrderedSemiring.toPartialOrder.{0} Real (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Real (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Real (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.instLinearOrderedFieldReal))))))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real (CommMonoidWithZero.toZero.{0} Real (CommGroupWithZero.toCommMonoidWithZero.{0} Real (Semifield.toCommGroupWithZero.{0} Real (LinearOrderedSemifield.toSemifield.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.instLinearOrderedFieldReal))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedSemifield.toDiv.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.instLinearOrderedFieldReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real (Semiring.toOne.{0} Real (StrictOrderedSemiring.toSemiring.{0} Real (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Real (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Real (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.instLinearOrderedFieldReal)))))))) y)) (LT.lt.{0} Real (Preorder.toLT.{0} Real (PartialOrder.toPreorder.{0} Real (StrictOrderedSemiring.toPartialOrder.{0} Real (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Real (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Real (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.instLinearOrderedFieldReal))))))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real (CommMonoidWithZero.toZero.{0} Real (CommGroupWithZero.toCommMonoidWithZero.{0} Real (Semifield.toCommGroupWithZero.{0} Real (LinearOrderedSemifield.toSemifield.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.instLinearOrderedFieldReal))))))) y) (one_div_pos.{0} Real (LinearOrderedField.toLinearOrderedSemifield.{0} Real Real.instLinearOrderedFieldReal) y) hy))
Case conversion may be inaccurate. Consider using '#align ennreal.order_iso_rpow_symm_apply ENNReal.orderIsoRpow_symm_applyₓ'. -/
theorem orderIsoRpow_symm_apply (y : ℝ) (hy : 0 < y) :
    (orderIsoRpow y hy).symm = orderIsoRpow (1 / y) (one_div_pos.2 hy) :=
  by
  simp only [order_iso_rpow, one_div_one_div]
  rfl
#align ennreal.order_iso_rpow_symm_apply ENNReal.orderIsoRpow_symm_apply

/- warning: ennreal.rpow_le_rpow -> ENNReal.rpow_le_rpow is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x y) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y z))
but is expected to have type
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x y) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y z))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_le_rpow ENNReal.rpow_le_rpowₓ'. -/
theorem rpow_le_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  monotone_rpow_of_nonneg h₂ h₁
#align ennreal.rpow_le_rpow ENNReal.rpow_le_rpow

/- warning: ennreal.rpow_lt_rpow -> ENNReal.rpow_lt_rpow is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x y) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y z))
but is expected to have type
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x y) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y z))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_lt_rpow ENNReal.rpow_lt_rpowₓ'. -/
theorem rpow_lt_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  strictMono_rpow_of_pos h₂ h₁
#align ennreal.rpow_lt_rpow ENNReal.rpow_lt_rpow

/- warning: ennreal.rpow_le_rpow_iff -> ENNReal.rpow_le_rpow_iff is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Iff (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y z)) (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x y))
but is expected to have type
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y z)) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x y))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_le_rpow_iff ENNReal.rpow_le_rpow_iffₓ'. -/
theorem rpow_le_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  (strictMono_rpow_of_pos hz).le_iff_le
#align ennreal.rpow_le_rpow_iff ENNReal.rpow_le_rpow_iff

/- warning: ennreal.rpow_lt_rpow_iff -> ENNReal.rpow_lt_rpow_iff is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y z)) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x y))
but is expected to have type
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y z)) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x y))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_lt_rpow_iff ENNReal.rpow_lt_rpow_iffₓ'. -/
theorem rpow_lt_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  (strictMono_rpow_of_pos hz).lt_iff_lt
#align ennreal.rpow_lt_rpow_iff ENNReal.rpow_lt_rpow_iff

/- warning: ennreal.le_rpow_one_div_iff -> ENNReal.le_rpow_one_div_iff is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Iff (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) z))) (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) y))
but is expected to have type
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) z))) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) y))
Case conversion may be inaccurate. Consider using '#align ennreal.le_rpow_one_div_iff ENNReal.le_rpow_one_div_iffₓ'. -/
theorem le_rpow_one_div_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ≤ y ^ (1 / z) ↔ x ^ z ≤ y :=
  by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @_root_.mul_inv_cancel _ _ z hz.ne']
  rw [rpow_mul, ← one_div, @rpow_le_rpow_iff _ _ (1 / z) (by simp [hz])]
#align ennreal.le_rpow_one_div_iff ENNReal.le_rpow_one_div_iff

/- warning: ennreal.lt_rpow_one_div_iff -> ENNReal.lt_rpow_one_div_iff is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) z))) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) y))
but is expected to have type
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) z))) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) y))
Case conversion may be inaccurate. Consider using '#align ennreal.lt_rpow_one_div_iff ENNReal.lt_rpow_one_div_iffₓ'. -/
theorem lt_rpow_one_div_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x < y ^ (1 / z) ↔ x ^ z < y :=
  by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @_root_.mul_inv_cancel _ _ z (ne_of_lt hz).symm]
  rw [rpow_mul, ← one_div, @rpow_lt_rpow_iff _ _ (1 / z) (by simp [hz])]
#align ennreal.lt_rpow_one_div_iff ENNReal.lt_rpow_one_div_iff

/- warning: ennreal.rpow_one_div_le_iff -> ENNReal.rpow_one_div_le_iff is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (Iff (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) z)) y) (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y z)))
but is expected to have type
  forall {x : ENNReal} {y : ENNReal} {z : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) z)) y) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y z)))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_one_div_le_iff ENNReal.rpow_one_div_le_iffₓ'. -/
theorem rpow_one_div_le_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ (1 / z) ≤ y ↔ x ≤ y ^ z :=
  by
  nth_rw 1 [← ENNReal.rpow_one y]
  nth_rw 2 [← @_root_.mul_inv_cancel _ _ z hz.ne.symm]
  rw [ENNReal.rpow_mul, ← one_div, ENNReal.rpow_le_rpow_iff (one_div_pos.2 hz)]
#align ennreal.rpow_one_div_le_iff ENNReal.rpow_one_div_le_iff

/- warning: ennreal.rpow_lt_rpow_of_exponent_lt -> ENNReal.rpow_lt_rpow_of_exponent_lt is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : Real} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) x) -> (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LT.lt.{0} Real Real.hasLt y z) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : ENNReal} {y : Real} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) x) -> (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LT.lt.{0} Real Real.instLTReal y z) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_lt_rpow_of_exponent_lt ENNReal.rpow_lt_rpow_of_exponent_ltₓ'. -/
theorem rpow_lt_rpow_of_exponent_lt {x : ℝ≥0∞} {y z : ℝ} (hx : 1 < x) (hx' : x ≠ ⊤) (hyz : y < z) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using hx'
  rw [one_lt_coe_iff] at hx
  simp [coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
    NNReal.rpow_lt_rpow_of_exponent_lt hx hyz]
#align ennreal.rpow_lt_rpow_of_exponent_lt ENNReal.rpow_lt_rpow_of_exponent_lt

/- warning: ennreal.rpow_le_rpow_of_exponent_le -> ENNReal.rpow_le_rpow_of_exponent_le is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : Real} {z : Real}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) x) -> (LE.le.{0} Real Real.hasLe y z) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : ENNReal} {y : Real} {z : Real}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) x) -> (LE.le.{0} Real Real.instLEReal y z) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_le_rpow_of_exponent_le ENNReal.rpow_le_rpow_of_exponent_leₓ'. -/
theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0∞} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
    x ^ y ≤ x ^ z := by
  cases x
  ·
    rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
          rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
        simp [Hy, Hz, top_rpow_of_neg, top_rpow_of_pos, le_refl] <;>
      linarith
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_rpow_of_exponent_le hx hyz]
#align ennreal.rpow_le_rpow_of_exponent_le ENNReal.rpow_le_rpow_of_exponent_le

/- warning: ennreal.rpow_lt_rpow_of_exponent_gt -> ENNReal.rpow_lt_rpow_of_exponent_gt is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : Real} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) x) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) -> (LT.lt.{0} Real Real.hasLt z y) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : ENNReal} {y : Real} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) x) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) -> (LT.lt.{0} Real Real.instLTReal z y) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_lt_rpow_of_exponent_gt ENNReal.rpow_lt_rpow_of_exponent_gtₓ'. -/
theorem rpow_lt_rpow_of_exponent_gt {x : ℝ≥0∞} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx1 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx0 hx1
  simp [coe_rpow_of_ne_zero (ne_of_gt hx0), NNReal.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz]
#align ennreal.rpow_lt_rpow_of_exponent_gt ENNReal.rpow_lt_rpow_of_exponent_gt

/- warning: ennreal.rpow_le_rpow_of_exponent_ge -> ENNReal.rpow_le_rpow_of_exponent_ge is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : Real} {z : Real}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) -> (LE.le.{0} Real Real.hasLe z y) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : ENNReal} {y : Real} {z : Real}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) -> (LE.le.{0} Real Real.instLEReal z y) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_le_rpow_of_exponent_ge ENNReal.rpow_le_rpow_of_exponent_geₓ'. -/
theorem rpow_le_rpow_of_exponent_ge {x : ℝ≥0∞} {y z : ℝ} (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z :=
  by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx1 coe_lt_top)
  by_cases h : x = 0
  ·
    rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
          rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
        simp [Hy, Hz, h, zero_rpow_of_neg, zero_rpow_of_pos, le_refl] <;>
      linarith
  · rw [coe_le_one_iff] at hx1
    simp [coe_rpow_of_ne_zero h,
      NNReal.rpow_le_rpow_of_exponent_ge (bot_lt_iff_ne_bot.mpr h) hx1 hyz]
#align ennreal.rpow_le_rpow_of_exponent_ge ENNReal.rpow_le_rpow_of_exponent_ge

/- warning: ennreal.rpow_le_self_of_le_one -> ENNReal.rpow_le_self_of_le_one is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {z : Real}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) z) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) x)
but is expected to have type
  forall {x : ENNReal} {z : Real}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) z) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) x)
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_le_self_of_le_one ENNReal.rpow_le_self_of_le_oneₓ'. -/
theorem rpow_le_self_of_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x :=
  by
  nth_rw 2 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_ge hx h_one_le
#align ennreal.rpow_le_self_of_le_one ENNReal.rpow_le_self_of_le_one

/- warning: ennreal.le_rpow_self_of_one_le -> ENNReal.le_rpow_self_of_one_le is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {z : Real}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) z) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : ENNReal} {z : Real}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) z) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align ennreal.le_rpow_self_of_one_le ENNReal.le_rpow_self_of_one_leₓ'. -/
theorem le_rpow_self_of_one_le {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (h_one_le : 1 ≤ z) : x ≤ x ^ z :=
  by
  nth_rw 1 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_le hx h_one_le
#align ennreal.le_rpow_self_of_one_le ENNReal.le_rpow_self_of_one_le

/- warning: ennreal.rpow_pos_of_nonneg -> ENNReal.rpow_pos_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {p : Real} {x : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x p))
but is expected to have type
  forall {p : Real} {x : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x p))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_pos_of_nonneg ENNReal.rpow_pos_of_nonnegₓ'. -/
theorem rpow_pos_of_nonneg {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hp_nonneg : 0 ≤ p) : 0 < x ^ p :=
  by
  by_cases hp_zero : p = 0
  · simp [hp_zero, zero_lt_one]
  · rw [← Ne.def] at hp_zero
    have hp_pos := lt_of_le_of_ne hp_nonneg hp_zero.symm
    rw [← zero_rpow_of_pos hp_pos]
    exact rpow_lt_rpow hx_pos hp_pos
#align ennreal.rpow_pos_of_nonneg ENNReal.rpow_pos_of_nonneg

/- warning: ennreal.rpow_pos -> ENNReal.rpow_pos is a dubious translation:
lean 3 declaration is
  forall {p : Real} {x : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) x) -> (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x p))
but is expected to have type
  forall {p : Real} {x : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) x) -> (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x p))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_pos ENNReal.rpow_posₓ'. -/
theorem rpow_pos {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hx_ne_top : x ≠ ⊤) : 0 < x ^ p :=
  by
  cases' lt_or_le 0 p with hp_pos hp_nonpos
  · exact rpow_pos_of_nonneg hx_pos (le_of_lt hp_pos)
  · rw [← neg_neg p, rpow_neg, ENNReal.inv_pos]
    exact rpow_ne_top_of_nonneg (right.nonneg_neg_iff.mpr hp_nonpos) hx_ne_top
#align ennreal.rpow_pos ENNReal.rpow_pos

/- warning: ennreal.rpow_lt_one -> ENNReal.rpow_lt_one is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))))
but is expected to have type
  forall {x : ENNReal} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_lt_one ENNReal.rpow_lt_oneₓ'. -/
theorem rpow_lt_one {x : ℝ≥0∞} {z : ℝ} (hx : x < 1) (hz : 0 < z) : x ^ z < 1 :=
  by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx le_top)
  simp only [coe_lt_one_iff] at hx
  simp [coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.rpow_lt_one hx hz]
#align ennreal.rpow_lt_one ENNReal.rpow_lt_one

/- warning: ennreal.rpow_le_one -> ENNReal.rpow_le_one is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {z : Real}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))))
but is expected to have type
  forall {x : ENNReal} {z : Real}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_le_one ENNReal.rpow_le_oneₓ'. -/
theorem rpow_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 :=
  by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx coe_lt_top)
  simp only [coe_le_one_iff] at hx
  simp [coe_rpow_of_nonneg _ hz, NNReal.rpow_le_one hx hz]
#align ennreal.rpow_le_one ENNReal.rpow_le_one

/- warning: ennreal.rpow_lt_one_of_one_lt_of_neg -> ENNReal.rpow_lt_one_of_one_lt_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) x) -> (LT.lt.{0} Real Real.hasLt z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))))
but is expected to have type
  forall {x : ENNReal} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) x) -> (LT.lt.{0} Real Real.instLTReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_lt_one_of_one_lt_of_neg ENNReal.rpow_lt_one_of_one_lt_of_negₓ'. -/
theorem rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 :=
  by
  cases x
  · simp [top_rpow_of_neg hz, zero_lt_one]
  · simp only [some_eq_coe, one_lt_coe_iff] at hx
    simp [coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
      NNReal.rpow_lt_one_of_one_lt_of_neg hx hz]
#align ennreal.rpow_lt_one_of_one_lt_of_neg ENNReal.rpow_lt_one_of_one_lt_of_neg

/- warning: ennreal.rpow_le_one_of_one_le_of_neg -> ENNReal.rpow_le_one_of_one_le_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {z : Real}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) x) -> (LT.lt.{0} Real Real.hasLt z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))))
but is expected to have type
  forall {x : ENNReal} {z : Real}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) x) -> (LT.lt.{0} Real Real.instLTReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_le_one_of_one_le_of_neg ENNReal.rpow_le_one_of_one_le_of_negₓ'. -/
theorem rpow_le_one_of_one_le_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : z < 0) : x ^ z ≤ 1 :=
  by
  cases x
  · simp [top_rpow_of_neg hz, zero_lt_one]
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_one_of_one_le_of_nonpos hx (le_of_lt hz)]
#align ennreal.rpow_le_one_of_one_le_of_neg ENNReal.rpow_le_one_of_one_le_of_neg

/- warning: ennreal.one_lt_rpow -> ENNReal.one_lt_rpow is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : ENNReal} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align ennreal.one_lt_rpow ENNReal.one_lt_rpowₓ'. -/
theorem one_lt_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z :=
  by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [some_eq_coe, one_lt_coe_iff] at hx
    simp [coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_lt_rpow hx hz]
#align ennreal.one_lt_rpow ENNReal.one_lt_rpow

/- warning: ennreal.one_le_rpow -> ENNReal.one_le_rpow is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {z : Real}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) z) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : ENNReal} {z : Real}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) z) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align ennreal.one_le_rpow ENNReal.one_le_rpowₓ'. -/
theorem one_le_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : 0 < z) : 1 ≤ x ^ z :=
  by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_le_rpow hx (le_of_lt hz)]
#align ennreal.one_le_rpow ENNReal.one_le_rpow

/- warning: ennreal.one_lt_rpow_of_pos_of_lt_one_of_neg -> ENNReal.one_lt_rpow_of_pos_of_lt_one_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) x) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) -> (LT.lt.{0} Real Real.hasLt z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : ENNReal} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) x) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) -> (LT.lt.{0} Real Real.instLTReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align ennreal.one_lt_rpow_of_pos_of_lt_one_of_neg ENNReal.one_lt_rpow_of_pos_of_lt_one_of_negₓ'. -/
theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z :=
  by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx2 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx1 hx2⊢
  simp [coe_rpow_of_ne_zero (ne_of_gt hx1), NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz]
#align ennreal.one_lt_rpow_of_pos_of_lt_one_of_neg ENNReal.one_lt_rpow_of_pos_of_lt_one_of_neg

/- warning: ennreal.one_le_rpow_of_pos_of_le_one_of_neg -> ENNReal.one_le_rpow_of_pos_of_le_one_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) x) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) -> (LT.lt.{0} Real Real.hasLt z (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x z))
but is expected to have type
  forall {x : ENNReal} {z : Real}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) x) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) x (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) -> (LT.lt.{0} Real Real.instLTReal z (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x z))
Case conversion may be inaccurate. Consider using '#align ennreal.one_le_rpow_of_pos_of_le_one_of_neg ENNReal.one_le_rpow_of_pos_of_le_one_of_negₓ'. -/
theorem one_le_rpow_of_pos_of_le_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
    (hz : z < 0) : 1 ≤ x ^ z :=
  by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx2 coe_lt_top)
  simp only [coe_le_one_iff, coe_pos] at hx1 hx2⊢
  simp [coe_rpow_of_ne_zero (ne_of_gt hx1),
    NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 (le_of_lt hz)]
#align ennreal.one_le_rpow_of_pos_of_le_one_of_neg ENNReal.one_le_rpow_of_pos_of_le_one_of_neg

#print ENNReal.toNNReal_rpow /-
theorem toNNReal_rpow (x : ℝ≥0∞) (z : ℝ) : x.toNNReal ^ z = (x ^ z).toNNReal :=
  by
  rcases lt_trichotomy z 0 with (H | H | H)
  · cases x
    · simp [H, ne_of_lt]
    by_cases hx : x = 0
    · simp [hx, H, ne_of_lt]
    · simp [coe_rpow_of_ne_zero hx]
  · simp [H]
  · cases x
    · simp [H, ne_of_gt]
    simp [coe_rpow_of_nonneg _ (le_of_lt H)]
#align ennreal.to_nnreal_rpow ENNReal.toNNReal_rpow
-/

#print ENNReal.toReal_rpow /-
theorem toReal_rpow (x : ℝ≥0∞) (z : ℝ) : x.toReal ^ z = (x ^ z).toReal := by
  rw [ENNReal.toReal, ENNReal.toReal, ← NNReal.coe_rpow, ENNReal.toNNReal_rpow]
#align ennreal.to_real_rpow ENNReal.toReal_rpow
-/

/- warning: ennreal.of_real_rpow_of_pos -> ENNReal.ofReal_rpow_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real} {p : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (ENNReal.ofReal x) p) (ENNReal.ofReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x p)))
but is expected to have type
  forall {x : Real} {p : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (ENNReal.ofReal x) p) (ENNReal.ofReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x p)))
Case conversion may be inaccurate. Consider using '#align ennreal.of_real_rpow_of_pos ENNReal.ofReal_rpow_of_posₓ'. -/
theorem ofReal_rpow_of_pos {x p : ℝ} (hx_pos : 0 < x) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) :=
  by
  simp_rw [ENNReal.ofReal]
  rw [coe_rpow_of_ne_zero, coe_eq_coe, Real.toNNReal_rpow_of_nonneg hx_pos.le]
  simp [hx_pos]
#align ennreal.of_real_rpow_of_pos ENNReal.ofReal_rpow_of_pos

/- warning: ennreal.of_real_rpow_of_nonneg -> ENNReal.ofReal_rpow_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real} {p : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (ENNReal.ofReal x) p) (ENNReal.ofReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x p)))
but is expected to have type
  forall {x : Real} {p : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (ENNReal.ofReal x) p) (ENNReal.ofReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x p)))
Case conversion may be inaccurate. Consider using '#align ennreal.of_real_rpow_of_nonneg ENNReal.ofReal_rpow_of_nonnegₓ'. -/
theorem ofReal_rpow_of_nonneg {x p : ℝ} (hx_nonneg : 0 ≤ x) (hp_nonneg : 0 ≤ p) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) :=
  by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hx0 : x = 0
  · rw [← Ne.def] at hp0
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg hp0.symm
    simp [hx0, hp_pos, hp_pos.ne.symm]
  rw [← Ne.def] at hx0
  exact of_real_rpow_of_pos (hx_nonneg.lt_of_ne hx0.symm)
#align ennreal.of_real_rpow_of_nonneg ENNReal.ofReal_rpow_of_nonneg

/- warning: ennreal.rpow_left_injective -> ENNReal.rpow_left_injective is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Function.Injective.{1, 1} ENNReal ENNReal (fun (y : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y x))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Function.Injective.{1, 1} ENNReal ENNReal (fun (y : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y x))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_left_injective ENNReal.rpow_left_injectiveₓ'. -/
theorem rpow_left_injective {x : ℝ} (hx : x ≠ 0) : Function.Injective fun y : ℝ≥0∞ => y ^ x :=
  by
  intro y z hyz
  dsimp only at hyz
  rw [← rpow_one y, ← rpow_one z, ← _root_.mul_inv_cancel hx, rpow_mul, rpow_mul, hyz]
#align ennreal.rpow_left_injective ENNReal.rpow_left_injective

/- warning: ennreal.rpow_left_surjective -> ENNReal.rpow_left_surjective is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Function.Surjective.{1, 1} ENNReal ENNReal (fun (y : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y x))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Function.Surjective.{1, 1} ENNReal ENNReal (fun (y : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y x))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_left_surjective ENNReal.rpow_left_surjectiveₓ'. -/
theorem rpow_left_surjective {x : ℝ} (hx : x ≠ 0) : Function.Surjective fun y : ℝ≥0∞ => y ^ x :=
  fun y => ⟨y ^ x⁻¹, by simp_rw [← rpow_mul, _root_.inv_mul_cancel hx, rpow_one]⟩
#align ennreal.rpow_left_surjective ENNReal.rpow_left_surjective

/- warning: ennreal.rpow_left_bijective -> ENNReal.rpow_left_bijective is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Function.Bijective.{1, 1} ENNReal ENNReal (fun (y : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) y x))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Function.Bijective.{1, 1} ENNReal ENNReal (fun (y : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) y x))
Case conversion may be inaccurate. Consider using '#align ennreal.rpow_left_bijective ENNReal.rpow_left_bijectiveₓ'. -/
theorem rpow_left_bijective {x : ℝ} (hx : x ≠ 0) : Function.Bijective fun y : ℝ≥0∞ => y ^ x :=
  ⟨rpow_left_injective hx, rpow_left_surjective hx⟩
#align ennreal.rpow_left_bijective ENNReal.rpow_left_bijective

end ENNReal

section Tactics

/-!
## Tactic extensions for powers on `ℝ≥0` and `ℝ≥0∞`
-/


namespace NormNum

theorem nnrpow_pos (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c : ℝ≥0) (hb : b = b') (h : a ^ b' = c) :
    a ^ b = c := by rw [← h, hb, NNReal.rpow_nat_cast]
#align norm_num.nnrpow_pos NormNum.nnrpow_pos

theorem nnrpow_neg (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0) (hb : b = b') (h : a ^ b' = c)
    (hc : c⁻¹ = c') : a ^ (-b) = c' := by rw [← hc, ← h, hb, NNReal.rpow_neg, NNReal.rpow_nat_cast]
#align norm_num.nnrpow_neg NormNum.nnrpow_neg

theorem ennrpow_pos (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c) :
    a ^ b = c := by rw [← h, hb, ENNReal.rpow_nat_cast]
#align norm_num.ennrpow_pos NormNum.ennrpow_pos

theorem ennrpow_neg (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c)
    (hc : c⁻¹ = c') : a ^ (-b) = c' := by
  rw [← hc, ← h, hb, ENNReal.rpow_neg, ENNReal.rpow_nat_cast]
#align norm_num.ennrpow_neg NormNum.ennrpow_neg

/-- Evaluate `nnreal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
unsafe def prove_nnrpow : expr → expr → tactic (expr × expr) :=
  prove_rpow' `` nnrpow_pos `` nnrpow_neg `` NNReal.rpow_zero q(ℝ≥0) q(ℝ) q((1 : ℝ≥0))
#align norm_num.prove_nnrpow norm_num.prove_nnrpow

/-- Evaluate `ennreal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
unsafe def prove_ennrpow : expr → expr → tactic (expr × expr) :=
  prove_rpow' `` ennrpow_pos `` ennrpow_neg `` ENNReal.rpow_zero q(ℝ≥0∞) q(ℝ) q((1 : ℝ≥0∞))
#align norm_num.prove_ennrpow norm_num.prove_ennrpow

/-- Evaluates expressions of the form `rpow a b` and `a ^ b` in the special case where
`b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
@[norm_num]
unsafe def eval_nnrpow_ennrpow : expr → tactic (expr × expr)
  | q(@Pow.pow _ _ NNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_nnrpow a b
  | q(NNReal.rpow $(a) $(b)) => b.to_int >> prove_nnrpow a b
  | q(@Pow.pow _ _ ENNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_ennrpow a b
  | q(ENNReal.rpow $(a) $(b)) => b.to_int >> prove_ennrpow a b
  | _ => tactic.failed
#align norm_num.eval_nnrpow_ennrpow norm_num.eval_nnrpow_ennrpow

end NormNum

namespace Tactic

namespace Positivity

private theorem nnrpow_pos {a : ℝ≥0} (ha : 0 < a) (b : ℝ) : 0 < a ^ b :=
  NNReal.rpow_pos ha

/-- Auxiliary definition for the `positivity` tactic to handle real powers of nonnegative reals. -/
unsafe def prove_nnrpow (a b : expr) : tactic strictness := do
  let strictness_a ← core a
  match strictness_a with
    | positive p => positive <$> mk_app `` nnrpow_pos [p, b]
    | _ => failed
#align tactic.positivity.prove_nnrpow tactic.positivity.prove_nnrpow

-- We already know `0 ≤ x` for all `x : ℝ≥0`
private theorem ennrpow_pos {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ b :=
  ENNReal.rpow_pos_of_nonneg ha hb.le

/-- Auxiliary definition for the `positivity` tactic to handle real powers of extended nonnegative
reals. -/
unsafe def prove_ennrpow (a b : expr) : tactic strictness := do
  let strictness_a ← core a
  let strictness_b ← core b
  match strictness_a, strictness_b with
    | positive pa, positive pb => positive <$> mk_app `` ennrpow_pos [pa, pb]
    | positive pa, nonnegative pb => positive <$> mk_app `` ENNReal.rpow_pos_of_nonneg [pa, pb]
    | _, _ => failed
#align tactic.positivity.prove_ennrpow tactic.positivity.prove_ennrpow

-- We already know `0 ≤ x` for all `x : ℝ≥0∞`
end Positivity

open Positivity

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when the
base is nonnegative and positive when the base is positive. -/
@[positivity]
unsafe def positivity_nnrpow_ennrpow : expr → tactic strictness
  | q(@Pow.pow _ _ NNReal.Real.hasPow $(a) $(b)) => prove_nnrpow a b
  | q(NNReal.rpow $(a) $(b)) => prove_nnrpow a b
  | q(@Pow.pow _ _ ENNReal.Real.hasPow $(a) $(b)) => prove_ennrpow a b
  | q(ENNReal.rpow $(a) $(b)) => prove_ennrpow a b
  | _ => failed
#align tactic.positivity_nnrpow_ennrpow tactic.positivity_nnrpow_ennrpow

end Tactic

end Tactics

