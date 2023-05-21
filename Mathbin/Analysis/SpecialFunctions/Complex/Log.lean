/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson

! This file was ported from Lean 3 source module analysis.special_functions.complex.log
! leanprover-community/mathlib commit 33c67ae661dd8988516ff7f247b0be3018cdd952
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Complex.Arg
import Mathbin.Analysis.SpecialFunctions.Log.Basic

/-!
# The complex `log` function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Basic properties, relationship with `exp`.
-/


noncomputable section

namespace Complex

open Set Filter

open Real Topology ComplexConjugate

#print Complex.log /-
/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0`-/
@[pp_nodot]
noncomputable def log (x : ℂ) : ℂ :=
  x.abs.log + arg x * I
#align complex.log Complex.log
-/

/- warning: complex.log_re -> Complex.log_re is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Real (Complex.re (Complex.log x)) (Real.log (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x))
but is expected to have type
  forall (x : Complex), Eq.{1} Real (Complex.re (Complex.log x)) (Real.log (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x))
Case conversion may be inaccurate. Consider using '#align complex.log_re Complex.log_reₓ'. -/
theorem log_re (x : ℂ) : x.log.re = x.abs.log := by simp [log]
#align complex.log_re Complex.log_re

#print Complex.log_im /-
theorem log_im (x : ℂ) : x.log.im = x.arg := by simp [log]
#align complex.log_im Complex.log_im
-/

/- warning: complex.neg_pi_lt_log_im -> Complex.neg_pi_lt_log_im is a dubious translation:
lean 3 declaration is
  forall (x : Complex), LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg Real.pi) (Complex.im (Complex.log x))
but is expected to have type
  forall (x : Complex), LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal Real.pi) (Complex.im (Complex.log x))
Case conversion may be inaccurate. Consider using '#align complex.neg_pi_lt_log_im Complex.neg_pi_lt_log_imₓ'. -/
theorem neg_pi_lt_log_im (x : ℂ) : -π < (log x).im := by simp only [log_im, neg_pi_lt_arg]
#align complex.neg_pi_lt_log_im Complex.neg_pi_lt_log_im

/- warning: complex.log_im_le_pi -> Complex.log_im_le_pi is a dubious translation:
lean 3 declaration is
  forall (x : Complex), LE.le.{0} Real Real.hasLe (Complex.im (Complex.log x)) Real.pi
but is expected to have type
  forall (x : Complex), LE.le.{0} Real Real.instLEReal (Complex.im (Complex.log x)) Real.pi
Case conversion may be inaccurate. Consider using '#align complex.log_im_le_pi Complex.log_im_le_piₓ'. -/
theorem log_im_le_pi (x : ℂ) : (log x).im ≤ π := by simp only [log_im, arg_le_pi]
#align complex.log_im_le_pi Complex.log_im_le_pi

/- warning: complex.exp_log -> Complex.exp_log is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Complex (Complex.exp (Complex.log x)) x)
but is expected to have type
  forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Complex (Complex.exp (Complex.log x)) x)
Case conversion may be inaccurate. Consider using '#align complex.exp_log Complex.exp_logₓ'. -/
theorem exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x := by
  rw [log, exp_add_mul_I, ← of_real_sin, sin_arg, ← of_real_cos, cos_arg hx, ← of_real_exp,
    Real.exp_log (abs.pos hx), mul_add, of_real_div, of_real_div,
    mul_div_cancel' _ (of_real_ne_zero.2 <| abs.ne_zero hx), ← mul_assoc,
    mul_div_cancel' _ (of_real_ne_zero.2 <| abs.ne_zero hx), re_add_im]
#align complex.exp_log Complex.exp_log

/- warning: complex.range_exp -> Complex.range_exp is a dubious translation:
lean 3 declaration is
  Eq.{1} (Set.{0} Complex) (Set.range.{0, 1} Complex Complex Complex.exp) (HasCompl.compl.{0} (Set.{0} Complex) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Complex) (Set.booleanAlgebra.{0} Complex)) (Singleton.singleton.{0, 0} Complex (Set.{0} Complex) (Set.hasSingleton.{0} Complex) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))))
but is expected to have type
  Eq.{1} (Set.{0} Complex) (Set.range.{0, 1} Complex Complex Complex.exp) (HasCompl.compl.{0} (Set.{0} Complex) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Complex) (Set.instBooleanAlgebraSet.{0} Complex)) (Singleton.singleton.{0, 0} Complex (Set.{0} Complex) (Set.instSingletonSet.{0} Complex) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))))
Case conversion may be inaccurate. Consider using '#align complex.range_exp Complex.range_expₓ'. -/
@[simp]
theorem range_exp : range exp = {0}ᶜ :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨x, rfl⟩
      exact exp_ne_zero x, fun hx => ⟨log x, exp_log hx⟩⟩
#align complex.range_exp Complex.range_exp

/- warning: complex.log_exp -> Complex.log_exp is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg Real.pi) (Complex.im x)) -> (LE.le.{0} Real Real.hasLe (Complex.im x) Real.pi) -> (Eq.{1} Complex (Complex.log (Complex.exp x)) x)
but is expected to have type
  forall {x : Complex}, (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal Real.pi) (Complex.im x)) -> (LE.le.{0} Real Real.instLEReal (Complex.im x) Real.pi) -> (Eq.{1} Complex (Complex.log (Complex.exp x)) x)
Case conversion may be inaccurate. Consider using '#align complex.log_exp Complex.log_expₓ'. -/
theorem log_exp {x : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π) : log (exp x) = x := by
  rw [log, abs_exp, Real.log_exp, exp_eq_exp_re_mul_sin_add_cos, ← of_real_exp,
    arg_mul_cos_add_sin_mul_I (Real.exp_pos _) ⟨hx₁, hx₂⟩, re_add_im]
#align complex.log_exp Complex.log_exp

/- warning: complex.exp_inj_of_neg_pi_lt_of_le_pi -> Complex.exp_inj_of_neg_pi_lt_of_le_pi is a dubious translation:
lean 3 declaration is
  forall {x : Complex} {y : Complex}, (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg Real.pi) (Complex.im x)) -> (LE.le.{0} Real Real.hasLe (Complex.im x) Real.pi) -> (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg Real.pi) (Complex.im y)) -> (LE.le.{0} Real Real.hasLe (Complex.im y) Real.pi) -> (Eq.{1} Complex (Complex.exp x) (Complex.exp y)) -> (Eq.{1} Complex x y)
but is expected to have type
  forall {x : Complex} {y : Complex}, (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal Real.pi) (Complex.im x)) -> (LE.le.{0} Real Real.instLEReal (Complex.im x) Real.pi) -> (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal Real.pi) (Complex.im y)) -> (LE.le.{0} Real Real.instLEReal (Complex.im y) Real.pi) -> (Eq.{1} Complex (Complex.exp x) (Complex.exp y)) -> (Eq.{1} Complex x y)
Case conversion may be inaccurate. Consider using '#align complex.exp_inj_of_neg_pi_lt_of_le_pi Complex.exp_inj_of_neg_pi_lt_of_le_piₓ'. -/
theorem exp_inj_of_neg_pi_lt_of_le_pi {x y : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π) (hy₁ : -π < y.im)
    (hy₂ : y.im ≤ π) (hxy : exp x = exp y) : x = y := by
  rw [← log_exp hx₁ hx₂, ← log_exp hy₁ hy₂, hxy]
#align complex.exp_inj_of_neg_pi_lt_of_le_pi Complex.exp_inj_of_neg_pi_lt_of_le_pi

/- warning: complex.of_real_log -> Complex.of_real_log is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Complex ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.log x)) (Complex.log ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x)))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Complex (Complex.ofReal' (Real.log x)) (Complex.log (Complex.ofReal' x)))
Case conversion may be inaccurate. Consider using '#align complex.of_real_log Complex.of_real_logₓ'. -/
theorem of_real_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x :=
  Complex.ext (by rw [log_re, of_real_re, abs_of_nonneg hx])
    (by rw [of_real_im, log_im, arg_of_real_of_nonneg hx])
#align complex.of_real_log Complex.of_real_log

/- warning: complex.log_of_real_re -> Complex.log_of_real_re is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Complex.re (Complex.log ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x))) (Real.log x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (Complex.re (Complex.log (Complex.ofReal' x))) (Real.log x)
Case conversion may be inaccurate. Consider using '#align complex.log_of_real_re Complex.log_of_real_reₓ'. -/
theorem log_of_real_re (x : ℝ) : (log (x : ℂ)).re = Real.log x := by simp [log_re]
#align complex.log_of_real_re Complex.log_of_real_re

/- warning: complex.log_of_real_mul -> Complex.log_of_real_mul is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Complex (Complex.log (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) r) x)) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.log r)) (Complex.log x))))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Complex (Complex.log (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' r) x)) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.ofReal' (Real.log r)) (Complex.log x))))
Case conversion may be inaccurate. Consider using '#align complex.log_of_real_mul Complex.log_of_real_mulₓ'. -/
theorem log_of_real_mul {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ≠ 0) :
    log (r * x) = Real.log r + log x :=
  by
  replace hx := complex.abs.ne_zero_iff.mpr hx
  simp_rw [log, map_mul, abs_of_real, arg_real_mul _ hr, abs_of_pos hr, Real.log_mul hr.ne' hx,
    of_real_add, add_assoc]
#align complex.log_of_real_mul Complex.log_of_real_mul

/- warning: complex.log_mul_of_real -> Complex.log_mul_of_real is a dubious translation:
lean 3 declaration is
  forall (r : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (forall (x : Complex), (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Complex (Complex.log (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) r))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.log r)) (Complex.log x))))
but is expected to have type
  forall (r : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (forall (x : Complex), (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Complex (Complex.log (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) x (Complex.ofReal' r))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.ofReal' (Real.log r)) (Complex.log x))))
Case conversion may be inaccurate. Consider using '#align complex.log_mul_of_real Complex.log_mul_of_realₓ'. -/
theorem log_mul_of_real (r : ℝ) (hr : 0 < r) (x : ℂ) (hx : x ≠ 0) :
    log (x * r) = Real.log r + log x := by rw [mul_comm, log_of_real_mul hr hx, add_comm]
#align complex.log_mul_of_real Complex.log_mul_of_real

/- warning: complex.log_zero -> Complex.log_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Complex (Complex.log (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))
but is expected to have type
  Eq.{1} Complex (Complex.log (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))
Case conversion may be inaccurate. Consider using '#align complex.log_zero Complex.log_zeroₓ'. -/
@[simp]
theorem log_zero : log 0 = 0 := by simp [log]
#align complex.log_zero Complex.log_zero

/- warning: complex.log_one -> Complex.log_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Complex (Complex.log (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))
but is expected to have type
  Eq.{1} Complex (Complex.log (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))
Case conversion may be inaccurate. Consider using '#align complex.log_one Complex.log_oneₓ'. -/
@[simp]
theorem log_one : log 1 = 0 := by simp [log]
#align complex.log_one Complex.log_one

/- warning: complex.log_neg_one -> Complex.log_neg_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Complex (Complex.log (Neg.neg.{0} Complex Complex.hasNeg (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi) Complex.I)
but is expected to have type
  Eq.{1} Complex (Complex.log (Neg.neg.{0} Complex Complex.instNegComplex (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' Real.pi) Complex.I)
Case conversion may be inaccurate. Consider using '#align complex.log_neg_one Complex.log_neg_oneₓ'. -/
theorem log_neg_one : log (-1) = π * I := by simp [log]
#align complex.log_neg_one Complex.log_neg_one

/- warning: complex.log_I -> Complex.log_I is a dubious translation:
lean 3 declaration is
  Eq.{1} Complex (Complex.log Complex.I) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (NormedDivisionRing.toDivisionRing.{0} Complex (NormedField.toNormedDivisionRing.{0} Complex Complex.normedField))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne))))) Complex.I)
but is expected to have type
  Eq.{1} Complex (Complex.log Complex.I) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (Complex.ofReal' Real.pi) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) Complex.I)
Case conversion may be inaccurate. Consider using '#align complex.log_I Complex.log_Iₓ'. -/
theorem log_I : log I = π / 2 * I := by simp [log]
#align complex.log_I Complex.log_I

/- warning: complex.log_neg_I -> Complex.log_neg_I is a dubious translation:
lean 3 declaration is
  Eq.{1} Complex (Complex.log (Neg.neg.{0} Complex Complex.hasNeg Complex.I)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Neg.neg.{0} Complex Complex.hasNeg (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (NormedDivisionRing.toDivisionRing.{0} Complex (NormedField.toNormedDivisionRing.{0} Complex Complex.normedField))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))))) Complex.I)
but is expected to have type
  Eq.{1} Complex (Complex.log (Neg.neg.{0} Complex Complex.instNegComplex Complex.I)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Neg.neg.{0} Complex Complex.instNegComplex (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (Complex.ofReal' Real.pi) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) Complex.I)
Case conversion may be inaccurate. Consider using '#align complex.log_neg_I Complex.log_neg_Iₓ'. -/
theorem log_neg_I : log (-I) = -(π / 2) * I := by simp [log]
#align complex.log_neg_I Complex.log_neg_I

/- warning: complex.log_conj_eq_ite -> Complex.log_conj_eq_ite is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (Complex.log (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) x)) (ite.{1} Complex (Eq.{1} Real (Complex.arg x) Real.pi) (Real.decidableEq (Complex.arg x) Real.pi) (Complex.log x) (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) (Complex.log x)))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (Complex.log (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) x)) (ite.{1} Complex (Eq.{1} Real (Complex.arg x) Real.pi) (Real.decidableEq (Complex.arg x) Real.pi) (Complex.log x) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) (Complex.log x)))
Case conversion may be inaccurate. Consider using '#align complex.log_conj_eq_ite Complex.log_conj_eq_iteₓ'. -/
theorem log_conj_eq_ite (x : ℂ) : log (conj x) = if x.arg = π then log x else conj (log x) :=
  by
  simp_rw [log, abs_conj, arg_conj, map_add, map_mul, conj_of_real]
  split_ifs with hx
  · rw [hx]
  simp_rw [of_real_neg, conj_I, mul_neg, neg_mul]
#align complex.log_conj_eq_ite Complex.log_conj_eq_ite

/- warning: complex.log_conj -> Complex.log_conj is a dubious translation:
lean 3 declaration is
  forall (x : Complex), (Ne.{1} Real (Complex.arg x) Real.pi) -> (Eq.{1} Complex (Complex.log (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) x)) (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) (Complex.log x)))
but is expected to have type
  forall (x : Complex), (Ne.{1} Real (Complex.arg x) Real.pi) -> (Eq.{1} Complex (Complex.log (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) x)) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) (Complex.log x)))
Case conversion may be inaccurate. Consider using '#align complex.log_conj Complex.log_conjₓ'. -/
theorem log_conj (x : ℂ) (h : x.arg ≠ π) : log (conj x) = conj (log x) := by
  rw [log_conj_eq_ite, if_neg h]
#align complex.log_conj Complex.log_conj

/- warning: complex.log_inv_eq_ite -> Complex.log_inv_eq_ite is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (Complex.log (Inv.inv.{0} Complex Complex.hasInv x)) (ite.{1} Complex (Eq.{1} Real (Complex.arg x) Real.pi) (Real.decidableEq (Complex.arg x) Real.pi) (Neg.neg.{0} Complex Complex.hasNeg (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) (Complex.log x))) (Neg.neg.{0} Complex Complex.hasNeg (Complex.log x)))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (Complex.log (Inv.inv.{0} Complex Complex.instInvComplex x)) (ite.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) (Complex.log x)) (Eq.{1} Real (Complex.arg x) Real.pi) (Real.decidableEq (Complex.arg x) Real.pi) (Neg.neg.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) (Complex.log x)) Complex.instNegComplex (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) (Complex.log x))) (Neg.neg.{0} Complex Complex.instNegComplex (Complex.log x)))
Case conversion may be inaccurate. Consider using '#align complex.log_inv_eq_ite Complex.log_inv_eq_iteₓ'. -/
theorem log_inv_eq_ite (x : ℂ) : log x⁻¹ = if x.arg = π then -conj (log x) else -log x :=
  by
  by_cases hx : x = 0
  · simp [hx]
  rw [inv_def, log_mul_of_real, Real.log_inv, of_real_neg, ← sub_eq_neg_add, log_conj_eq_ite]
  · simp_rw [log, map_add, map_mul, conj_of_real, conj_I, norm_sq_eq_abs, Real.log_pow,
      Nat.cast_two, of_real_mul, of_real_bit0, of_real_one, neg_add, mul_neg, two_mul, neg_neg]
    split_ifs
    · rw [add_sub_right_comm, sub_add_cancel']
    · rw [add_sub_right_comm, sub_add_cancel']
  · rwa [inv_pos, Complex.normSq_pos]
  · rwa [map_ne_zero]
#align complex.log_inv_eq_ite Complex.log_inv_eq_ite

/- warning: complex.log_inv -> Complex.log_inv is a dubious translation:
lean 3 declaration is
  forall (x : Complex), (Ne.{1} Real (Complex.arg x) Real.pi) -> (Eq.{1} Complex (Complex.log (Inv.inv.{0} Complex Complex.hasInv x)) (Neg.neg.{0} Complex Complex.hasNeg (Complex.log x)))
but is expected to have type
  forall (x : Complex), (Ne.{1} Real (Complex.arg x) Real.pi) -> (Eq.{1} Complex (Complex.log (Inv.inv.{0} Complex Complex.instInvComplex x)) (Neg.neg.{0} Complex Complex.instNegComplex (Complex.log x)))
Case conversion may be inaccurate. Consider using '#align complex.log_inv Complex.log_invₓ'. -/
theorem log_inv (x : ℂ) (hx : x.arg ≠ π) : log x⁻¹ = -log x := by rw [log_inv_eq_ite, if_neg hx]
#align complex.log_inv Complex.log_inv

/- warning: complex.two_pi_I_ne_zero -> Complex.two_pi_I_ne_zero is a dubious translation:
lean 3 declaration is
  Ne.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi)) Complex.I) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))
but is expected to have type
  Ne.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.ofReal' Real.pi)) Complex.I) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))
Case conversion may be inaccurate. Consider using '#align complex.two_pi_I_ne_zero Complex.two_pi_I_ne_zeroₓ'. -/
theorem two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 := by norm_num [Real.pi_ne_zero, I_ne_zero]
#align complex.two_pi_I_ne_zero Complex.two_pi_I_ne_zero

/- warning: complex.exp_eq_one_iff -> Complex.exp_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, Iff (Eq.{1} Complex (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))) (Exists.{1} Int (fun (n : Int) => Eq.{1} Complex x (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Complex (HasLiftT.mk.{1, 1} Int Complex (CoeTCₓ.coe.{1, 1} Int Complex (Int.castCoe.{0} Complex (AddGroupWithOne.toHasIntCast.{0} Complex Complex.addGroupWithOne)))) n) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi)) Complex.I))))
but is expected to have type
  forall {x : Complex}, Iff (Eq.{1} Complex (Complex.exp x) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))) (Exists.{1} Int (fun (n : Int) => Eq.{1} Complex x (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Int.cast.{0} Complex (Ring.toIntCast.{0} Complex Complex.instRingComplex) n) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.ofReal' Real.pi)) Complex.I))))
Case conversion may be inaccurate. Consider using '#align complex.exp_eq_one_iff Complex.exp_eq_one_iffₓ'. -/
theorem exp_eq_one_iff {x : ℂ} : exp x = 1 ↔ ∃ n : ℤ, x = n * (2 * π * I) :=
  by
  constructor
  · intro h
    rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos x.im (-π) with ⟨n, hn, -⟩
    use -n
    rw [Int.cast_neg, neg_mul, eq_neg_iff_add_eq_zero]
    have : (x + n * (2 * π * I)).im ∈ Ioc (-π) π := by simpa [two_mul, mul_add] using hn
    rw [← log_exp this.1 this.2, exp_periodic.int_mul n, h, log_one]
  · rintro ⟨n, rfl⟩
    exact (exp_periodic.int_mul n).Eq.trans exp_zero
#align complex.exp_eq_one_iff Complex.exp_eq_one_iff

/- warning: complex.exp_eq_exp_iff_exp_sub_eq_one -> Complex.exp_eq_exp_iff_exp_sub_eq_one is a dubious translation:
lean 3 declaration is
  forall {x : Complex} {y : Complex}, Iff (Eq.{1} Complex (Complex.exp x) (Complex.exp y)) (Eq.{1} Complex (Complex.exp (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) x y)) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))))
but is expected to have type
  forall {x : Complex} {y : Complex}, Iff (Eq.{1} Complex (Complex.exp x) (Complex.exp y)) (Eq.{1} Complex (Complex.exp (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) x y)) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))
Case conversion may be inaccurate. Consider using '#align complex.exp_eq_exp_iff_exp_sub_eq_one Complex.exp_eq_exp_iff_exp_sub_eq_oneₓ'. -/
theorem exp_eq_exp_iff_exp_sub_eq_one {x y : ℂ} : exp x = exp y ↔ exp (x - y) = 1 := by
  rw [exp_sub, div_eq_one_iff_eq (exp_ne_zero _)]
#align complex.exp_eq_exp_iff_exp_sub_eq_one Complex.exp_eq_exp_iff_exp_sub_eq_one

/- warning: complex.exp_eq_exp_iff_exists_int -> Complex.exp_eq_exp_iff_exists_int is a dubious translation:
lean 3 declaration is
  forall {x : Complex} {y : Complex}, Iff (Eq.{1} Complex (Complex.exp x) (Complex.exp y)) (Exists.{1} Int (fun (n : Int) => Eq.{1} Complex x (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) y (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Complex (HasLiftT.mk.{1, 1} Int Complex (CoeTCₓ.coe.{1, 1} Int Complex (Int.castCoe.{0} Complex (AddGroupWithOne.toHasIntCast.{0} Complex Complex.addGroupWithOne)))) n) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi)) Complex.I)))))
but is expected to have type
  forall {x : Complex} {y : Complex}, Iff (Eq.{1} Complex (Complex.exp x) (Complex.exp y)) (Exists.{1} Int (fun (n : Int) => Eq.{1} Complex x (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) y (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Int.cast.{0} Complex (Ring.toIntCast.{0} Complex Complex.instRingComplex) n) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.ofReal' Real.pi)) Complex.I)))))
Case conversion may be inaccurate. Consider using '#align complex.exp_eq_exp_iff_exists_int Complex.exp_eq_exp_iff_exists_intₓ'. -/
theorem exp_eq_exp_iff_exists_int {x y : ℂ} : exp x = exp y ↔ ∃ n : ℤ, x = y + n * (2 * π * I) := by
  simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']
#align complex.exp_eq_exp_iff_exists_int Complex.exp_eq_exp_iff_exists_int

#print Complex.countable_preimage_exp /-
@[simp]
theorem countable_preimage_exp {s : Set ℂ} : (exp ⁻¹' s).Countable ↔ s.Countable :=
  by
  refine' ⟨fun hs => _, fun hs => _⟩
  · refine' ((hs.image exp).insert 0).mono _
    rw [image_preimage_eq_inter_range, range_exp, ← diff_eq, ← union_singleton, diff_union_self]
    exact subset_union_left _ _
  · rw [← bUnion_preimage_singleton]
    refine' hs.bUnion fun z hz => _
    rcases em (∃ w, exp w = z) with (⟨w, rfl⟩ | hne)
    · simp only [preimage, mem_singleton_iff, exp_eq_exp_iff_exists_int, set_of_exists]
      exact countable_Union fun m => countable_singleton _
    · push_neg  at hne
      simp [preimage, hne]
#align complex.countable_preimage_exp Complex.countable_preimage_exp
-/

alias countable_preimage_exp ↔ _ _root_.set.countable.preimage_cexp
#align set.countable.preimage_cexp Set.Countable.preimage_cexp

/- warning: complex.tendsto_log_nhds_within_im_neg_of_re_neg_of_im_zero -> Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, (LT.lt.{0} Real Real.hasLt (Complex.re z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Tendsto.{0, 0} Complex Complex Complex.log (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) z (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.log (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs z))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi) Complex.I))))
but is expected to have type
  forall {z : Complex}, (LT.lt.{0} Real Real.instLTReal (Complex.re z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Tendsto.{0, 0} Complex Complex Complex.log (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) z (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) (Complex.ofReal' (Real.log (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs z))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' Real.pi) Complex.I))))
Case conversion may be inaccurate. Consider using '#align complex.tendsto_log_nhds_within_im_neg_of_re_neg_of_im_zero Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zeroₓ'. -/
theorem tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto log (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 <| Real.log (abs z) - π * I) :=
  by
  have :=
    (continuous_of_real.continuous_at.comp_continuous_within_at
            (continuous_abs.continuous_within_at.log _)).Tendsto.add
      (((continuous_of_real.tendsto _).comp <|
            tendsto_arg_nhds_within_im_neg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds)
  convert this
  · simp [sub_eq_add_neg]
  · lift z to ℝ using him
    simpa using hre.ne
#align complex.tendsto_log_nhds_within_im_neg_of_re_neg_of_im_zero Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero

/- warning: complex.continuous_within_at_log_of_re_neg_of_im_zero -> Complex.continuousWithinAt_log_of_re_neg_of_im_zero is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, (LT.lt.{0} Real Real.hasLt (Complex.re z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (ContinuousWithinAt.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) Complex.log (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im z))) z)
but is expected to have type
  forall {z : Complex}, (LT.lt.{0} Real Real.instLTReal (Complex.re z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (ContinuousWithinAt.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) Complex.log (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im z))) z)
Case conversion may be inaccurate. Consider using '#align complex.continuous_within_at_log_of_re_neg_of_im_zero Complex.continuousWithinAt_log_of_re_neg_of_im_zeroₓ'. -/
theorem continuousWithinAt_log_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    ContinuousWithinAt log { z : ℂ | 0 ≤ z.im } z :=
  by
  have :=
    (continuous_of_real.continuous_at.comp_continuous_within_at
            (continuous_abs.continuous_within_at.log _)).Tendsto.add
      ((continuous_of_real.continuous_at.comp_continuous_within_at <|
            continuous_within_at_arg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds)
  convert this
  · lift z to ℝ using him
    simpa using hre.ne
#align complex.continuous_within_at_log_of_re_neg_of_im_zero Complex.continuousWithinAt_log_of_re_neg_of_im_zero

/- warning: complex.tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero -> Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, (LT.lt.{0} Real Real.hasLt (Complex.re z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Tendsto.{0, 0} Complex Complex Complex.log (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) z (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im z)))) (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.log (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs z))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi) Complex.I))))
but is expected to have type
  forall {z : Complex}, (LT.lt.{0} Real Real.instLTReal (Complex.re z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Tendsto.{0, 0} Complex Complex Complex.log (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) z (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im z)))) (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.ofReal' (Real.log (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs z))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' Real.pi) Complex.I))))
Case conversion may be inaccurate. Consider using '#align complex.tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zeroₓ'. -/
theorem tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto log (𝓝[{ z : ℂ | 0 ≤ z.im }] z) (𝓝 <| Real.log (abs z) + π * I) := by
  simpa only [log, arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuous_within_at_log_of_re_neg_of_im_zero hre him).Tendsto
#align complex.tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero

/- warning: complex.map_exp_comap_re_at_bot -> Complex.map_exp_comap_re_atBot is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} Complex) (Filter.map.{0, 0} Complex Complex Complex.exp (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atBot.{0} Real Real.preorder))) (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))) (HasCompl.compl.{0} (Set.{0} Complex) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Complex) (Set.booleanAlgebra.{0} Complex)) (Singleton.singleton.{0, 0} Complex (Set.{0} Complex) (Set.hasSingleton.{0} Complex) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))))))
but is expected to have type
  Eq.{1} (Filter.{0} Complex) (Filter.map.{0, 0} Complex Complex Complex.exp (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atBot.{0} Real Real.instPreorderReal))) (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)) (HasCompl.compl.{0} (Set.{0} Complex) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Complex) (Set.instBooleanAlgebraSet.{0} Complex)) (Singleton.singleton.{0, 0} Complex (Set.{0} Complex) (Set.instSingletonSet.{0} Complex) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)))))
Case conversion may be inaccurate. Consider using '#align complex.map_exp_comap_re_at_bot Complex.map_exp_comap_re_atBotₓ'. -/
@[simp]
theorem map_exp_comap_re_atBot : map exp (comap re atBot) = 𝓝[≠] 0 := by
  rw [← comap_exp_nhds_zero, map_comap, range_exp, nhdsWithin]
#align complex.map_exp_comap_re_at_bot Complex.map_exp_comap_re_atBot

/- warning: complex.map_exp_comap_re_at_top -> Complex.map_exp_comap_re_atTop is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} Complex) (Filter.map.{0, 0} Complex Complex Complex.exp (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atTop.{0} Real Real.preorder))) (Filter.comap.{0, 0} Complex Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs) (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  Eq.{1} (Filter.{0} Complex) (Filter.map.{0, 0} Complex Complex Complex.exp (Filter.comap.{0, 0} Complex Real Complex.re (Filter.atTop.{0} Real Real.instPreorderReal))) (Filter.comap.{0, 0} Complex Real (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs) (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align complex.map_exp_comap_re_at_top Complex.map_exp_comap_re_atTopₓ'. -/
@[simp]
theorem map_exp_comap_re_atTop : map exp (comap re atTop) = comap abs atTop :=
  by
  rw [← comap_exp_comap_abs_at_top, map_comap, range_exp, inf_eq_left, le_principal_iff]
  exact eventually_ne_of_tendsto_norm_atTop tendsto_comap 0
#align complex.map_exp_comap_re_at_top Complex.map_exp_comap_re_atTop

end Complex

section LogDeriv

open Complex Filter

open Topology

variable {α : Type _}

/- warning: continuous_at_clog -> continuousAt_clog is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re x)) (Ne.{1} Real (Complex.im x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (ContinuousAt.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) Complex.log x)
but is expected to have type
  forall {x : Complex}, (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re x)) (Ne.{1} Real (Complex.im x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (ContinuousAt.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) Complex.log x)
Case conversion may be inaccurate. Consider using '#align continuous_at_clog continuousAt_clogₓ'. -/
theorem continuousAt_clog {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) : ContinuousAt log x :=
  by
  refine' ContinuousAt.add _ _
  · refine' continuous_of_real.continuous_at.comp _
    refine' (Real.continuousAt_log _).comp complex.continuous_abs.continuous_at
    rw [complex.abs.ne_zero_iff]
    rintro rfl
    simpa using h
  · have h_cont_mul : Continuous fun x : ℂ => x * I := continuous_id'.mul continuous_const
    refine' h_cont_mul.continuous_at.comp (continuous_of_real.continuous_at.comp _)
    exact continuous_at_arg h
#align continuous_at_clog continuousAt_clog

/- warning: filter.tendsto.clog -> Filter.Tendsto.clog is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {x : Complex}, (Filter.Tendsto.{u1, 0} α Complex f l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) x)) -> (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re x)) (Ne.{1} Real (Complex.im x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Filter.Tendsto.{u1, 0} α Complex (fun (t : α) => Complex.log (f t)) l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (Complex.log x)))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {x : Complex}, (Filter.Tendsto.{u1, 0} α Complex f l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) x)) -> (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re x)) (Ne.{1} Real (Complex.im x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Filter.Tendsto.{u1, 0} α Complex (fun (t : α) => Complex.log (f t)) l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (Complex.log x)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.clog Filter.Tendsto.clogₓ'. -/
theorem Filter.Tendsto.clog {l : Filter α} {f : α → ℂ} {x : ℂ} (h : Tendsto f l (𝓝 x))
    (hx : 0 < x.re ∨ x.im ≠ 0) : Tendsto (fun t => log (f t)) l (𝓝 <| log x) :=
  (continuousAt_clog hx).Tendsto.comp h
#align filter.tendsto.clog Filter.Tendsto.clog

variable [TopologicalSpace α]

/- warning: continuous_at.clog -> ContinuousAt.clog is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {x : α}, (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f x) -> (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re (f x))) (Ne.{1} Real (Complex.im (f x)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (t : α) => Complex.log (f t)) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {x : α}, (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f x) -> (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re (f x))) (Ne.{1} Real (Complex.im (f x)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (t : α) => Complex.log (f t)) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.clog ContinuousAt.clogₓ'. -/
theorem ContinuousAt.clog {f : α → ℂ} {x : α} (h₁ : ContinuousAt f x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : ContinuousAt (fun t => log (f t)) x :=
  h₁.clog h₂
#align continuous_at.clog ContinuousAt.clog

/- warning: continuous_within_at.clog -> ContinuousWithinAt.clog is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f s x) -> (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re (f x))) (Ne.{1} Real (Complex.im (f x)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (t : α) => Complex.log (f t)) s x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f s x) -> (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re (f x))) (Ne.{1} Real (Complex.im (f x)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (t : α) => Complex.log (f t)) s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.clog ContinuousWithinAt.clogₓ'. -/
theorem ContinuousWithinAt.clog {f : α → ℂ} {s : Set α} {x : α} (h₁ : ContinuousWithinAt f s x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : ContinuousWithinAt (fun t => log (f t)) s x :=
  h₁.clog h₂
#align continuous_within_at.clog ContinuousWithinAt.clog

/- warning: continuous_on.clog -> ContinuousOn.clog is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α}, (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re (f x))) (Ne.{1} Real (Complex.im (f x)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) -> (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (t : α) => Complex.log (f t)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α}, (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f s) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re (f x))) (Ne.{1} Real (Complex.im (f x)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) -> (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (t : α) => Complex.log (f t)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.clog ContinuousOn.clogₓ'. -/
theorem ContinuousOn.clog {f : α → ℂ} {s : Set α} (h₁ : ContinuousOn f s)
    (h₂ : ∀ x ∈ s, 0 < (f x).re ∨ (f x).im ≠ 0) : ContinuousOn (fun t => log (f t)) s := fun x hx =>
  (h₁ x hx).clog (h₂ x hx)
#align continuous_on.clog ContinuousOn.clog

/- warning: continuous.clog -> Continuous.clog is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex}, (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f) -> (forall (x : α), Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re (f x))) (Ne.{1} Real (Complex.im (f x)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (t : α) => Complex.log (f t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex}, (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f) -> (forall (x : α), Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re (f x))) (Ne.{1} Real (Complex.im (f x)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (t : α) => Complex.log (f t)))
Case conversion may be inaccurate. Consider using '#align continuous.clog Continuous.clogₓ'. -/
theorem Continuous.clog {f : α → ℂ} (h₁ : Continuous f) (h₂ : ∀ x, 0 < (f x).re ∨ (f x).im ≠ 0) :
    Continuous fun t => log (f t) :=
  continuous_iff_continuousAt.2 fun x => h₁.ContinuousAt.clog (h₂ x)
#align continuous.clog Continuous.clog

end LogDeriv

