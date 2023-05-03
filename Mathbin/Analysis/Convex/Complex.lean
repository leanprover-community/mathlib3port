/-
Copyright (c) 2019 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, Yaël Dillies

! This file was ported from Lean 3 source module analysis.convex.complex
! leanprover-community/mathlib commit 15730e8d0af237a2ebafeb8cfbbcf71f6160c2e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Basic
import Mathbin.Data.Complex.Module

/-!
# Convexity of half spaces in ℂ

The open and closed half-spaces in ℂ given by an inequality on either the real or imaginary part
are all convex over ℝ.
-/


/- warning: convex_halfspace_re_lt -> convex_halfspace_re_lt is a dubious translation:
lean 3 declaration is
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.hasSmul.{0} Real (Mul.toSMul.{0} Real Real.hasMul)) (setOf.{0} Complex (fun (c : Complex) => LT.lt.{0} Real Real.hasLt (Complex.re c) r))
but is expected to have type
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instSMulComplex.{0} Real (Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))) (setOf.{0} Complex (fun (c : Complex) => LT.lt.{0} Real Real.instLTReal (Complex.re c) r))
Case conversion may be inaccurate. Consider using '#align convex_halfspace_re_lt convex_halfspace_re_ltₓ'. -/
theorem convex_halfspace_re_lt (r : ℝ) : Convex ℝ { c : ℂ | c.re < r } :=
  convex_halfspace_lt (IsLinearMap.mk Complex.add_re Complex.smul_re) _
#align convex_halfspace_re_lt convex_halfspace_re_lt

/- warning: convex_halfspace_re_le -> convex_halfspace_re_le is a dubious translation:
lean 3 declaration is
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.hasSmul.{0} Real (Mul.toSMul.{0} Real Real.hasMul)) (setOf.{0} Complex (fun (c : Complex) => LE.le.{0} Real Real.hasLe (Complex.re c) r))
but is expected to have type
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instSMulComplex.{0} Real (Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))) (setOf.{0} Complex (fun (c : Complex) => LE.le.{0} Real Real.instLEReal (Complex.re c) r))
Case conversion may be inaccurate. Consider using '#align convex_halfspace_re_le convex_halfspace_re_leₓ'. -/
theorem convex_halfspace_re_le (r : ℝ) : Convex ℝ { c : ℂ | c.re ≤ r } :=
  convex_halfspace_le (IsLinearMap.mk Complex.add_re Complex.smul_re) _
#align convex_halfspace_re_le convex_halfspace_re_le

/- warning: convex_halfspace_re_gt -> convex_halfspace_re_gt is a dubious translation:
lean 3 declaration is
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.hasSmul.{0} Real (Mul.toSMul.{0} Real Real.hasMul)) (setOf.{0} Complex (fun (c : Complex) => LT.lt.{0} Real Real.hasLt r (Complex.re c)))
but is expected to have type
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instSMulComplex.{0} Real (Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))) (setOf.{0} Complex (fun (c : Complex) => LT.lt.{0} Real Real.instLTReal r (Complex.re c)))
Case conversion may be inaccurate. Consider using '#align convex_halfspace_re_gt convex_halfspace_re_gtₓ'. -/
theorem convex_halfspace_re_gt (r : ℝ) : Convex ℝ { c : ℂ | r < c.re } :=
  convex_halfspace_gt (IsLinearMap.mk Complex.add_re Complex.smul_re) _
#align convex_halfspace_re_gt convex_halfspace_re_gt

/- warning: convex_halfspace_re_ge -> convex_halfspace_re_ge is a dubious translation:
lean 3 declaration is
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.hasSmul.{0} Real (Mul.toSMul.{0} Real Real.hasMul)) (setOf.{0} Complex (fun (c : Complex) => LE.le.{0} Real Real.hasLe r (Complex.re c)))
but is expected to have type
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instSMulComplex.{0} Real (Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))) (setOf.{0} Complex (fun (c : Complex) => LE.le.{0} Real Real.instLEReal r (Complex.re c)))
Case conversion may be inaccurate. Consider using '#align convex_halfspace_re_ge convex_halfspace_re_geₓ'. -/
theorem convex_halfspace_re_ge (r : ℝ) : Convex ℝ { c : ℂ | r ≤ c.re } :=
  convex_halfspace_ge (IsLinearMap.mk Complex.add_re Complex.smul_re) _
#align convex_halfspace_re_ge convex_halfspace_re_ge

/- warning: convex_halfspace_im_lt -> convex_halfspace_im_lt is a dubious translation:
lean 3 declaration is
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.hasSmul.{0} Real (Mul.toSMul.{0} Real Real.hasMul)) (setOf.{0} Complex (fun (c : Complex) => LT.lt.{0} Real Real.hasLt (Complex.im c) r))
but is expected to have type
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instSMulComplex.{0} Real (Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))) (setOf.{0} Complex (fun (c : Complex) => LT.lt.{0} Real Real.instLTReal (Complex.im c) r))
Case conversion may be inaccurate. Consider using '#align convex_halfspace_im_lt convex_halfspace_im_ltₓ'. -/
theorem convex_halfspace_im_lt (r : ℝ) : Convex ℝ { c : ℂ | c.im < r } :=
  convex_halfspace_lt (IsLinearMap.mk Complex.add_im Complex.smul_im) _
#align convex_halfspace_im_lt convex_halfspace_im_lt

/- warning: convex_halfspace_im_le -> convex_halfspace_im_le is a dubious translation:
lean 3 declaration is
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.hasSmul.{0} Real (Mul.toSMul.{0} Real Real.hasMul)) (setOf.{0} Complex (fun (c : Complex) => LE.le.{0} Real Real.hasLe (Complex.im c) r))
but is expected to have type
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instSMulComplex.{0} Real (Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))) (setOf.{0} Complex (fun (c : Complex) => LE.le.{0} Real Real.instLEReal (Complex.im c) r))
Case conversion may be inaccurate. Consider using '#align convex_halfspace_im_le convex_halfspace_im_leₓ'. -/
theorem convex_halfspace_im_le (r : ℝ) : Convex ℝ { c : ℂ | c.im ≤ r } :=
  convex_halfspace_le (IsLinearMap.mk Complex.add_im Complex.smul_im) _
#align convex_halfspace_im_le convex_halfspace_im_le

/- warning: convex_halfspace_im_gt -> convex_halfspace_im_gt is a dubious translation:
lean 3 declaration is
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.hasSmul.{0} Real (Mul.toSMul.{0} Real Real.hasMul)) (setOf.{0} Complex (fun (c : Complex) => LT.lt.{0} Real Real.hasLt r (Complex.im c)))
but is expected to have type
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instSMulComplex.{0} Real (Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))) (setOf.{0} Complex (fun (c : Complex) => LT.lt.{0} Real Real.instLTReal r (Complex.im c)))
Case conversion may be inaccurate. Consider using '#align convex_halfspace_im_gt convex_halfspace_im_gtₓ'. -/
theorem convex_halfspace_im_gt (r : ℝ) : Convex ℝ { c : ℂ | r < c.im } :=
  convex_halfspace_gt (IsLinearMap.mk Complex.add_im Complex.smul_im) _
#align convex_halfspace_im_gt convex_halfspace_im_gt

/- warning: convex_halfspace_im_ge -> convex_halfspace_im_ge is a dubious translation:
lean 3 declaration is
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.hasSmul.{0} Real (Mul.toSMul.{0} Real Real.hasMul)) (setOf.{0} Complex (fun (c : Complex) => LE.le.{0} Real Real.hasLe r (Complex.im c)))
but is expected to have type
  forall (r : Real), Convex.{0, 0} Real Complex Real.orderedSemiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instSMulComplex.{0} Real (Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))) (setOf.{0} Complex (fun (c : Complex) => LE.le.{0} Real Real.instLEReal r (Complex.im c)))
Case conversion may be inaccurate. Consider using '#align convex_halfspace_im_ge convex_halfspace_im_geₓ'. -/
theorem convex_halfspace_im_ge (r : ℝ) : Convex ℝ { c : ℂ | r ≤ c.im } :=
  convex_halfspace_ge (IsLinearMap.mk Complex.add_im Complex.smul_im) _
#align convex_halfspace_im_ge convex_halfspace_im_ge

