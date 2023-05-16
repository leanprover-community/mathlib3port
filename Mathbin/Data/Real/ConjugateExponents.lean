/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module data.real.conjugate_exponents
! leanprover-community/mathlib commit 2196ab363eb097c008d4497125e0dde23fb36db2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Ennreal

/-!
# Real conjugate exponents

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

`p.is_conjugate_exponent q` registers the fact that the real numbers `p` and `q` are `> 1` and
satisfy `1/p + 1/q = 1`. This property shows up often in analysis, especially when dealing with
`L^p` spaces.

We make several basic facts available through dot notation in this situation.

We also introduce `p.conjugate_exponent` for `p / (p-1)`. When `p > 1`, it is conjugate to `p`.
-/


noncomputable section

namespace Real

#print Real.IsConjugateExponent /-
/-- Two real exponents `p, q` are conjugate if they are `> 1` and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. -/
structure IsConjugateExponent (p q : ℝ) : Prop where
  one_lt : 1 < p
  inv_add_inv_conj : 1 / p + 1 / q = 1
#align real.is_conjugate_exponent Real.IsConjugateExponent
-/

#print Real.conjugateExponent /-
/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `1/p + 1/q = 1`. -/
def conjugateExponent (p : ℝ) : ℝ :=
  p / (p - 1)
#align real.conjugate_exponent Real.conjugateExponent
-/

namespace IsConjugateExponent

variable {p q : ℝ} (h : p.IsConjugateExponent q)

include h

/- warning: real.is_conjugate_exponent.pos -> Real.IsConjugateExponent.pos is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p)
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p)
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.pos Real.IsConjugateExponent.posₓ'. -/
/- Register several non-vanishing results following from the fact that `p` has a conjugate exponent
`q`: many computations using these exponents require clearing out denominators, which can be done
with `field_simp` given a proof that these denominators are non-zero, so we record the most usual
ones. -/
theorem pos : 0 < p :=
  lt_trans zero_lt_one h.one_lt
#align real.is_conjugate_exponent.pos Real.IsConjugateExponent.pos

/- warning: real.is_conjugate_exponent.nonneg -> Real.IsConjugateExponent.nonneg is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p)
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p)
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.nonneg Real.IsConjugateExponent.nonnegₓ'. -/
theorem nonneg : 0 ≤ p :=
  le_of_lt h.Pos
#align real.is_conjugate_exponent.nonneg Real.IsConjugateExponent.nonneg

/- warning: real.is_conjugate_exponent.ne_zero -> Real.IsConjugateExponent.ne_zero is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Ne.{1} Real p (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Ne.{1} Real p (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.ne_zero Real.IsConjugateExponent.ne_zeroₓ'. -/
theorem ne_zero : p ≠ 0 :=
  ne_of_gt h.Pos
#align real.is_conjugate_exponent.ne_zero Real.IsConjugateExponent.ne_zero

/- warning: real.is_conjugate_exponent.sub_one_pos -> Real.IsConjugateExponent.sub_one_pos is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) p (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) p (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.sub_one_pos Real.IsConjugateExponent.sub_one_posₓ'. -/
theorem sub_one_pos : 0 < p - 1 :=
  sub_pos.2 h.one_lt
#align real.is_conjugate_exponent.sub_one_pos Real.IsConjugateExponent.sub_one_pos

/- warning: real.is_conjugate_exponent.sub_one_ne_zero -> Real.IsConjugateExponent.sub_one_ne_zero is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Ne.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) p (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Ne.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) p (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.sub_one_ne_zero Real.IsConjugateExponent.sub_one_ne_zeroₓ'. -/
theorem sub_one_ne_zero : p - 1 ≠ 0 :=
  ne_of_gt h.sub_one_pos
#align real.is_conjugate_exponent.sub_one_ne_zero Real.IsConjugateExponent.sub_one_ne_zero

/- warning: real.is_conjugate_exponent.one_div_pos -> Real.IsConjugateExponent.one_div_pos is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p))
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.one_div_pos Real.IsConjugateExponent.one_div_posₓ'. -/
theorem one_div_pos : 0 < 1 / p :=
  one_div_pos.2 h.Pos
#align real.is_conjugate_exponent.one_div_pos Real.IsConjugateExponent.one_div_pos

/- warning: real.is_conjugate_exponent.one_div_nonneg -> Real.IsConjugateExponent.one_div_nonneg is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p))
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.one_div_nonneg Real.IsConjugateExponent.one_div_nonnegₓ'. -/
theorem one_div_nonneg : 0 ≤ 1 / p :=
  le_of_lt h.one_div_pos
#align real.is_conjugate_exponent.one_div_nonneg Real.IsConjugateExponent.one_div_nonneg

/- warning: real.is_conjugate_exponent.one_div_ne_zero -> Real.IsConjugateExponent.one_div_ne_zero is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Ne.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Ne.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.one_div_ne_zero Real.IsConjugateExponent.one_div_ne_zeroₓ'. -/
theorem one_div_ne_zero : 1 / p ≠ 0 :=
  ne_of_gt h.one_div_pos
#align real.is_conjugate_exponent.one_div_ne_zero Real.IsConjugateExponent.one_div_ne_zero

/- warning: real.is_conjugate_exponent.conj_eq -> Real.IsConjugateExponent.conj_eq is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Eq.{1} Real q (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) p (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) p (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Eq.{1} Real q (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) p (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) p (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.conj_eq Real.IsConjugateExponent.conj_eqₓ'. -/
theorem conj_eq : q = p / (p - 1) :=
  by
  have := h.inv_add_inv_conj
  rw [← eq_sub_iff_add_eq', one_div, inv_eq_iff_eq_inv] at this
  field_simp [this, h.ne_zero]
#align real.is_conjugate_exponent.conj_eq Real.IsConjugateExponent.conj_eq

#print Real.IsConjugateExponent.conjugate_eq /-
theorem conjugate_eq : conjugateExponent p = q :=
  h.conj_eq.symm
#align real.is_conjugate_exponent.conjugate_eq Real.IsConjugateExponent.conjugate_eq
-/

/- warning: real.is_conjugate_exponent.sub_one_mul_conj -> Real.IsConjugateExponent.sub_one_mul_conj is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) p (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) q) p)
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) p (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) q) p)
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.sub_one_mul_conj Real.IsConjugateExponent.sub_one_mul_conjₓ'. -/
theorem sub_one_mul_conj : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conj_eq
#align real.is_conjugate_exponent.sub_one_mul_conj Real.IsConjugateExponent.sub_one_mul_conj

/- warning: real.is_conjugate_exponent.mul_eq_add -> Real.IsConjugateExponent.mul_eq_add is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) p q) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) p q))
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) p q) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) p q))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.mul_eq_add Real.IsConjugateExponent.mul_eq_addₓ'. -/
theorem mul_eq_add : p * q = p + q := by
  simpa only [sub_mul, sub_eq_iff_eq_add, one_mul] using h.sub_one_mul_conj
#align real.is_conjugate_exponent.mul_eq_add Real.IsConjugateExponent.mul_eq_add

#print Real.IsConjugateExponent.symm /-
@[symm]
protected theorem symm : q.IsConjugateExponent p :=
  { one_lt := by
      rw [h.conj_eq]
      exact (one_lt_div h.sub_one_pos).mpr (sub_one_lt p)
    inv_add_inv_conj := by simpa [add_comm] using h.inv_add_inv_conj }
#align real.is_conjugate_exponent.symm Real.IsConjugateExponent.symm
-/

/- warning: real.is_conjugate_exponent.div_conj_eq_sub_one -> Real.IsConjugateExponent.div_conj_eq_sub_one is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) p q) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) p (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) p q) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) p (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.div_conj_eq_sub_one Real.IsConjugateExponent.div_conj_eq_sub_oneₓ'. -/
theorem div_conj_eq_sub_one : p / q = p - 1 :=
  by
  field_simp [h.symm.ne_zero]
  rw [h.sub_one_mul_conj]
#align real.is_conjugate_exponent.div_conj_eq_sub_one Real.IsConjugateExponent.div_conj_eq_sub_one

/- warning: real.is_conjugate_exponent.one_lt_nnreal -> Real.IsConjugateExponent.one_lt_nnreal is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (Real.toNNReal p))
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (Real.toNNReal p))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.one_lt_nnreal Real.IsConjugateExponent.one_lt_nnrealₓ'. -/
theorem one_lt_nnreal : 1 < Real.toNNReal p :=
  by
  rw [← Real.toNNReal_one, Real.toNNReal_lt_toNNReal_iff h.pos]
  exact h.one_lt
#align real.is_conjugate_exponent.one_lt_nnreal Real.IsConjugateExponent.one_lt_nnreal

/- warning: real.is_conjugate_exponent.inv_add_inv_conj_nnreal -> Real.IsConjugateExponent.inv_add_inv_conj_nnreal is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Eq.{1} NNReal (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (Real.toNNReal p)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (Real.toNNReal q))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Eq.{1} NNReal (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (Real.toNNReal p)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (Real.toNNReal q))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.inv_add_inv_conj_nnreal Real.IsConjugateExponent.inv_add_inv_conj_nnrealₓ'. -/
theorem inv_add_inv_conj_nnreal : 1 / Real.toNNReal p + 1 / Real.toNNReal q = 1 := by
  rw [← Real.toNNReal_one, ← Real.toNNReal_div' h.nonneg, ← Real.toNNReal_div' h.symm.nonneg, ←
    Real.toNNReal_add h.one_div_nonneg h.symm.one_div_nonneg, h.inv_add_inv_conj]
#align real.is_conjugate_exponent.inv_add_inv_conj_nnreal Real.IsConjugateExponent.inv_add_inv_conj_nnreal

/- warning: real.is_conjugate_exponent.inv_add_inv_conj_ennreal -> Real.IsConjugateExponent.inv_add_inv_conj_ennreal is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) (ENNReal.ofReal p)) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) (ENNReal.ofReal q))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))))
but is expected to have type
  forall {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (ENNReal.ofReal p)) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (ENNReal.ofReal q))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent.inv_add_inv_conj_ennreal Real.IsConjugateExponent.inv_add_inv_conj_ennrealₓ'. -/
theorem inv_add_inv_conj_ennreal : 1 / ENNReal.ofReal p + 1 / ENNReal.ofReal q = 1 := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos h.pos, ←
    ENNReal.ofReal_div_of_pos h.symm.pos, ←
    ENNReal.ofReal_add h.one_div_nonneg h.symm.one_div_nonneg, h.inv_add_inv_conj]
#align real.is_conjugate_exponent.inv_add_inv_conj_ennreal Real.IsConjugateExponent.inv_add_inv_conj_ennreal

end IsConjugateExponent

/- warning: real.is_conjugate_exponent_iff -> Real.isConjugateExponent_iff is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p) -> (Iff (Real.IsConjugateExponent p q) (Eq.{1} Real q (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) p (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) p (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))))
but is expected to have type
  forall {p : Real} {q : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p) -> (Iff (Real.IsConjugateExponent p q) (Eq.{1} Real q (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) p (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) p (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent_iff Real.isConjugateExponent_iffₓ'. -/
theorem isConjugateExponent_iff {p q : ℝ} (h : 1 < p) : p.IsConjugateExponent q ↔ q = p / (p - 1) :=
  ⟨fun H => H.conj_eq, fun H => ⟨h, by field_simp [H, ne_of_gt (lt_trans zero_lt_one h)] ⟩⟩
#align real.is_conjugate_exponent_iff Real.isConjugateExponent_iff

/- warning: real.is_conjugate_exponent_conjugate_exponent -> Real.isConjugateExponent_conjugateExponent is a dubious translation:
lean 3 declaration is
  forall {p : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p) -> (Real.IsConjugateExponent p (Real.conjugateExponent p))
but is expected to have type
  forall {p : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p) -> (Real.IsConjugateExponent p (Real.conjugateExponent p))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent_conjugate_exponent Real.isConjugateExponent_conjugateExponentₓ'. -/
theorem isConjugateExponent_conjugateExponent {p : ℝ} (h : 1 < p) :
    p.IsConjugateExponent (conjugateExponent p) :=
  (isConjugateExponent_iff h).2 rfl
#align real.is_conjugate_exponent_conjugate_exponent Real.isConjugateExponent_conjugateExponent

/- warning: real.is_conjugate_exponent_one_div -> Real.isConjugateExponent_one_div is a dubious translation:
lean 3 declaration is
  forall {a : Real} {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) a) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) a b) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Real.IsConjugateExponent (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) a) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b))
but is expected to have type
  forall {a : Real} {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) a) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) a b) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Real.IsConjugateExponent (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) a) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b))
Case conversion may be inaccurate. Consider using '#align real.is_conjugate_exponent_one_div Real.isConjugateExponent_one_divₓ'. -/
theorem isConjugateExponent_one_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (1 / a).IsConjugateExponent (1 / b) :=
  ⟨by
    rw [lt_div_iff ha, one_mul]
    linarith, by
    simp_rw [one_div_one_div]
    exact hab⟩
#align real.is_conjugate_exponent_one_div Real.isConjugateExponent_one_div

end Real

