/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson

! This file was ported from Lean 3 source module analysis.special_functions.complex.arg
! leanprover-community/mathlib commit 2c1d8ca2812b64f88992a5294ea3dba144755cd1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The argument of a complex number.

We define `arg : ℂ → ℝ`, returing a real number in the range (-π, π],
such that for `x ≠ 0`, `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
while `arg 0` defaults to `0`
-/


noncomputable section

namespace Complex

open ComplexConjugate Real Topology

open Filter Set

#print Complex.arg /-
/-- `arg` returns values in the range (-π, π], such that for `x ≠ 0`,
  `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
  `arg 0` defaults to `0` -/
noncomputable def arg (x : ℂ) : ℝ :=
  if 0 ≤ x.re then Real.arcsin (x.im / x.abs)
  else if 0 ≤ x.im then Real.arcsin ((-x).im / x.abs) + π else Real.arcsin ((-x).im / x.abs) - π
#align complex.arg Complex.arg
-/

/- warning: complex.sin_arg -> Complex.sin_arg is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Real (Real.sin (Complex.arg x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.im x) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x))
but is expected to have type
  forall (x : Complex), Eq.{1} Real (Real.sin (Complex.arg x)) (HDiv.hDiv.{0, 0, 0} Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.im x) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x))
Case conversion may be inaccurate. Consider using '#align complex.sin_arg Complex.sin_argₓ'. -/
theorem sin_arg (x : ℂ) : Real.sin (arg x) = x.im / x.abs := by
  unfold arg <;> split_ifs <;>
    simp [sub_eq_add_neg, arg,
      Real.sin_arcsin (abs_le.1 (abs_im_div_abs_le_one x)).1 (abs_le.1 (abs_im_div_abs_le_one x)).2,
      Real.sin_add, neg_div, Real.arcsin_neg, Real.sin_neg]
#align complex.sin_arg Complex.sin_arg

/- warning: complex.cos_arg -> Complex.cos_arg is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Real (Real.cos (Complex.arg x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.re x) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x)))
but is expected to have type
  forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Real (Real.cos (Complex.arg x)) (HDiv.hDiv.{0, 0, 0} Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.re x) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x)))
Case conversion may be inaccurate. Consider using '#align complex.cos_arg Complex.cos_argₓ'. -/
theorem cos_arg {x : ℂ} (hx : x ≠ 0) : Real.cos (arg x) = x.re / x.abs :=
  by
  have habs : 0 < abs x := abs.pos hx
  have him : |im x / abs x| ≤ 1 := by
    rw [_root_.abs_div, abs_abs]
    exact div_le_one_of_le x.abs_im_le_abs (abs.nonneg x)
  rw [abs_le] at him
  rw [arg]
  split_ifs with h₁ h₂ h₂
  · rw [Real.cos_arcsin]
    field_simp [Real.sqrt_sq, habs.le, *]
  · rw [Real.cos_add_pi, Real.cos_arcsin]
    field_simp [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, _root_.abs_of_neg (not_le.1 h₁),
      *]
  · rw [Real.cos_sub_pi, Real.cos_arcsin]
    field_simp [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, _root_.abs_of_neg (not_le.1 h₁),
      *]
#align complex.cos_arg Complex.cos_arg

/- warning: complex.abs_mul_exp_arg_mul_I -> Complex.abs_mul_exp_arg_mul_I is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x)) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.arg x)) Complex.I))) x
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x)) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' (Complex.arg x)) Complex.I))) x
Case conversion may be inaccurate. Consider using '#align complex.abs_mul_exp_arg_mul_I Complex.abs_mul_exp_arg_mul_Iₓ'. -/
@[simp]
theorem abs_mul_exp_arg_mul_I (x : ℂ) : ↑(abs x) * exp (arg x * I) = x :=
  by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · have : abs x ≠ 0 := abs.ne_zero hx
    ext <;> field_simp [sin_arg, cos_arg hx, this, mul_comm (abs x)]
#align complex.abs_mul_exp_arg_mul_I Complex.abs_mul_exp_arg_mul_I

/- warning: complex.abs_mul_cos_add_sin_mul_I -> Complex.abs_mul_cos_add_sin_mul_I is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x)) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.arg x))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Complex.arg x))) Complex.I))) x
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x)) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos (Complex.ofReal' (Complex.arg x))) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' (Complex.arg x))) Complex.I))) x
Case conversion may be inaccurate. Consider using '#align complex.abs_mul_cos_add_sin_mul_I Complex.abs_mul_cos_add_sin_mul_Iₓ'. -/
@[simp]
theorem abs_mul_cos_add_sin_mul_I (x : ℂ) : (abs x * (cos (arg x) + sin (arg x) * I) : ℂ) = x := by
  rw [← exp_mul_I, abs_mul_exp_arg_mul_I]
#align complex.abs_mul_cos_add_sin_mul_I Complex.abs_mul_cos_add_sin_mul_I

/- warning: complex.abs_eq_one_iff -> Complex.abs_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall (z : Complex), Iff (Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs z) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Exists.{1} Real (fun (θ : Real) => Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) θ) Complex.I)) z))
but is expected to have type
  forall (z : Complex), Iff (Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs z) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real.instOneReal))) (Exists.{1} Real (fun (θ : Real) => Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' θ) Complex.I)) z))
Case conversion may be inaccurate. Consider using '#align complex.abs_eq_one_iff Complex.abs_eq_one_iffₓ'. -/
theorem abs_eq_one_iff (z : ℂ) : abs z = 1 ↔ ∃ θ : ℝ, exp (θ * I) = z :=
  by
  refine' ⟨fun hz => ⟨arg z, _⟩, _⟩
  ·
    calc
      exp (arg z * I) = abs z * exp (arg z * I) := by rw [hz, of_real_one, one_mul]
      _ = z := abs_mul_exp_arg_mul_I z
      
  · rintro ⟨θ, rfl⟩
    exact Complex.abs_exp_ofReal_mul_I θ
#align complex.abs_eq_one_iff Complex.abs_eq_one_iff

#print Complex.range_exp_mul_I /-
@[simp]
theorem range_exp_mul_I : (range fun x : ℝ => exp (x * I)) = Metric.sphere 0 1 :=
  by
  ext x
  simp only [mem_sphere_zero_iff_norm, norm_eq_abs, abs_eq_one_iff, mem_range]
#align complex.range_exp_mul_I Complex.range_exp_mul_I
-/

/- warning: complex.arg_mul_cos_add_sin_mul_I -> Complex.arg_mul_cos_add_sin_mul_I is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (forall {θ : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) θ (Set.Ioc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg Real.pi) Real.pi)) -> (Eq.{1} Real (Complex.arg (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) r) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) θ)) Complex.I)))) θ))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (forall {θ : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) θ (Set.Ioc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal Real.pi) Real.pi)) -> (Eq.{1} Real (Complex.arg (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' r) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos (Complex.ofReal' θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' θ)) Complex.I)))) θ))
Case conversion may be inaccurate. Consider using '#align complex.arg_mul_cos_add_sin_mul_I Complex.arg_mul_cos_add_sin_mul_Iₓ'. -/
theorem arg_mul_cos_add_sin_mul_I {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Ioc (-π) π) :
    arg (r * (cos θ + sin θ * I)) = θ :=
  by
  simp only [arg, map_mul, abs_cos_add_sin_mul_I, abs_of_nonneg hr.le, mul_one]
  simp only [of_real_mul_re, of_real_mul_im, neg_im, ← of_real_cos, ← of_real_sin, ←
    mk_eq_add_mul_I, neg_div, mul_div_cancel_left _ hr.ne', mul_nonneg_iff_right_nonneg_of_pos hr]
  by_cases h₁ : θ ∈ Icc (-(π / 2)) (π / 2)
  · rw [if_pos]
    exacts[Real.arcsin_sin' h₁, Real.cos_nonneg_of_mem_Icc h₁]
  · rw [mem_Icc, not_and_or, not_le, not_le] at h₁
    cases h₁
    · replace hθ := hθ.1
      have hcos : Real.cos θ < 0 := by
        rw [← neg_pos, ← Real.cos_add_pi]
        refine' Real.cos_pos_of_mem_Ioo ⟨_, _⟩ <;> linarith
      have hsin : Real.sin θ < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) hθ
      rw [if_neg, if_neg, ← Real.sin_add_pi, Real.arcsin_sin, add_sub_cancel] <;> [linarith,
        linarith, exact hsin.not_le, exact hcos.not_le]
    · replace hθ := hθ.2
      have hcos : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h₁ (by linarith)
      have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨by linarith, hθ⟩
      rw [if_neg, if_pos, ← Real.sin_sub_pi, Real.arcsin_sin, sub_add_cancel] <;> [linarith,
        linarith, exact hsin, exact hcos.not_le]
#align complex.arg_mul_cos_add_sin_mul_I Complex.arg_mul_cos_add_sin_mul_I

/- warning: complex.arg_cos_add_sin_mul_I -> Complex.arg_cos_add_sin_mul_I is a dubious translation:
lean 3 declaration is
  forall {θ : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) θ (Set.Ioc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg Real.pi) Real.pi)) -> (Eq.{1} Real (Complex.arg (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) θ)) Complex.I))) θ)
but is expected to have type
  forall {θ : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) θ (Set.Ioc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal Real.pi) Real.pi)) -> (Eq.{1} Real (Complex.arg (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos (Complex.ofReal' θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' θ)) Complex.I))) θ)
Case conversion may be inaccurate. Consider using '#align complex.arg_cos_add_sin_mul_I Complex.arg_cos_add_sin_mul_Iₓ'. -/
theorem arg_cos_add_sin_mul_I {θ : ℝ} (hθ : θ ∈ Ioc (-π) π) : arg (cos θ + sin θ * I) = θ := by
  rw [← one_mul (_ + _), ← of_real_one, arg_mul_cos_add_sin_mul_I zero_lt_one hθ]
#align complex.arg_cos_add_sin_mul_I Complex.arg_cos_add_sin_mul_I

/- warning: complex.arg_zero -> Complex.arg_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Complex.arg (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (Complex.arg (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align complex.arg_zero Complex.arg_zeroₓ'. -/
@[simp]
theorem arg_zero : arg 0 = 0 := by simp [arg, le_refl]
#align complex.arg_zero Complex.arg_zero

/- warning: complex.ext_abs_arg -> Complex.ext_abs_arg is a dubious translation:
lean 3 declaration is
  forall {x : Complex} {y : Complex}, (Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs y)) -> (Eq.{1} Real (Complex.arg x) (Complex.arg y)) -> (Eq.{1} Complex x y)
but is expected to have type
  forall {x : Complex} {y : Complex}, (Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs y)) -> (Eq.{1} Real (Complex.arg x) (Complex.arg y)) -> (Eq.{1} Complex x y)
Case conversion may be inaccurate. Consider using '#align complex.ext_abs_arg Complex.ext_abs_argₓ'. -/
theorem ext_abs_arg {x y : ℂ} (h₁ : x.abs = y.abs) (h₂ : x.arg = y.arg) : x = y := by
  rw [← abs_mul_exp_arg_mul_I x, ← abs_mul_exp_arg_mul_I y, h₁, h₂]
#align complex.ext_abs_arg Complex.ext_abs_arg

/- warning: complex.ext_abs_arg_iff -> Complex.ext_abs_arg_iff is a dubious translation:
lean 3 declaration is
  forall {x : Complex} {y : Complex}, Iff (Eq.{1} Complex x y) (And (Eq.{1} Real (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs y)) (Eq.{1} Real (Complex.arg x) (Complex.arg y)))
but is expected to have type
  forall {x : Complex} {y : Complex}, Iff (Eq.{1} Complex x y) (And (Eq.{1} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs y)) (Eq.{1} Real (Complex.arg x) (Complex.arg y)))
Case conversion may be inaccurate. Consider using '#align complex.ext_abs_arg_iff Complex.ext_abs_arg_iffₓ'. -/
theorem ext_abs_arg_iff {x y : ℂ} : x = y ↔ abs x = abs y ∧ arg x = arg y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, and_imp.2 ext_abs_arg⟩
#align complex.ext_abs_arg_iff Complex.ext_abs_arg_iff

/- warning: complex.arg_mem_Ioc -> Complex.arg_mem_Ioc is a dubious translation:
lean 3 declaration is
  forall (z : Complex), Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (Complex.arg z) (Set.Ioc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg Real.pi) Real.pi)
but is expected to have type
  forall (z : Complex), Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (Complex.arg z) (Set.Ioc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal Real.pi) Real.pi)
Case conversion may be inaccurate. Consider using '#align complex.arg_mem_Ioc Complex.arg_mem_Iocₓ'. -/
theorem arg_mem_Ioc (z : ℂ) : arg z ∈ Ioc (-π) π :=
  by
  have hπ : 0 < π := Real.pi_pos
  rcases eq_or_ne z 0 with (rfl | hz); simp [hπ, hπ.le]
  rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos (arg z) (-π) with ⟨N, hN, -⟩
  rw [two_mul, neg_add_cancel_left, ← two_mul, zsmul_eq_mul] at hN
  rw [← abs_mul_cos_add_sin_mul_I z, ← cos_add_int_mul_two_pi _ N, ← sin_add_int_mul_two_pi _ N]
  simp only [← of_real_one, ← of_real_bit0, ← of_real_mul, ← of_real_add, ← of_real_int_cast]
  rwa [arg_mul_cos_add_sin_mul_I (abs.pos hz) hN]
#align complex.arg_mem_Ioc Complex.arg_mem_Ioc

/- warning: complex.range_arg -> Complex.range_arg is a dubious translation:
lean 3 declaration is
  Eq.{1} (Set.{0} Real) (Set.range.{0, 1} Real Complex Complex.arg) (Set.Ioc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg Real.pi) Real.pi)
but is expected to have type
  Eq.{1} (Set.{0} Real) (Set.range.{0, 1} Real Complex Complex.arg) (Set.Ioc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal Real.pi) Real.pi)
Case conversion may be inaccurate. Consider using '#align complex.range_arg Complex.range_argₓ'. -/
@[simp]
theorem range_arg : range arg = Ioc (-π) π :=
  (range_subset_iff.2 arg_mem_Ioc).antisymm fun x hx => ⟨_, arg_cos_add_sin_mul_I hx⟩
#align complex.range_arg Complex.range_arg

/- warning: complex.arg_le_pi -> Complex.arg_le_pi is a dubious translation:
lean 3 declaration is
  forall (x : Complex), LE.le.{0} Real Real.hasLe (Complex.arg x) Real.pi
but is expected to have type
  forall (x : Complex), LE.le.{0} Real Real.instLEReal (Complex.arg x) Real.pi
Case conversion may be inaccurate. Consider using '#align complex.arg_le_pi Complex.arg_le_piₓ'. -/
theorem arg_le_pi (x : ℂ) : arg x ≤ π :=
  (arg_mem_Ioc x).2
#align complex.arg_le_pi Complex.arg_le_pi

/- warning: complex.neg_pi_lt_arg -> Complex.neg_pi_lt_arg is a dubious translation:
lean 3 declaration is
  forall (x : Complex), LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg Real.pi) (Complex.arg x)
but is expected to have type
  forall (x : Complex), LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal Real.pi) (Complex.arg x)
Case conversion may be inaccurate. Consider using '#align complex.neg_pi_lt_arg Complex.neg_pi_lt_argₓ'. -/
theorem neg_pi_lt_arg (x : ℂ) : -π < arg x :=
  (arg_mem_Ioc x).1
#align complex.neg_pi_lt_arg Complex.neg_pi_lt_arg

/- warning: complex.abs_arg_le_pi -> Complex.abs_arg_le_pi is a dubious translation:
lean 3 declaration is
  forall (z : Complex), LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Complex.arg z)) Real.pi
but is expected to have type
  forall (z : Complex), LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Complex.arg z)) Real.pi
Case conversion may be inaccurate. Consider using '#align complex.abs_arg_le_pi Complex.abs_arg_le_piₓ'. -/
theorem abs_arg_le_pi (z : ℂ) : |arg z| ≤ π :=
  abs_le.2 ⟨(neg_pi_lt_arg z).le, arg_le_pi z⟩
#align complex.abs_arg_le_pi Complex.abs_arg_le_pi

/- warning: complex.arg_nonneg_iff -> Complex.arg_nonneg_iff is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, Iff (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.arg z)) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im z))
but is expected to have type
  forall {z : Complex}, Iff (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.arg z)) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im z))
Case conversion may be inaccurate. Consider using '#align complex.arg_nonneg_iff Complex.arg_nonneg_iffₓ'. -/
@[simp]
theorem arg_nonneg_iff {z : ℂ} : 0 ≤ arg z ↔ 0 ≤ z.im :=
  by
  rcases eq_or_ne z 0 with (rfl | h₀); · simp
  calc
    0 ≤ arg z ↔ 0 ≤ Real.sin (arg z) :=
      ⟨fun h => Real.sin_nonneg_of_mem_Icc ⟨h, arg_le_pi z⟩,
        by
        contrapose!
        intro h
        exact Real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_arg _)⟩
    _ ↔ _ := by rw [sin_arg, le_div_iff (abs.pos h₀), MulZeroClass.zero_mul]
    
#align complex.arg_nonneg_iff Complex.arg_nonneg_iff

/- warning: complex.arg_neg_iff -> Complex.arg_neg_iff is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, Iff (LT.lt.{0} Real Real.hasLt (Complex.arg z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {z : Complex}, Iff (LT.lt.{0} Real Real.instLTReal (Complex.arg z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align complex.arg_neg_iff Complex.arg_neg_iffₓ'. -/
@[simp]
theorem arg_neg_iff {z : ℂ} : arg z < 0 ↔ z.im < 0 :=
  lt_iff_lt_of_le_iff_le arg_nonneg_iff
#align complex.arg_neg_iff Complex.arg_neg_iff

/- warning: complex.arg_real_mul -> Complex.arg_real_mul is a dubious translation:
lean 3 declaration is
  forall (x : Complex) {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Eq.{1} Real (Complex.arg (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) r) x)) (Complex.arg x))
but is expected to have type
  forall (x : Complex) {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Eq.{1} Real (Complex.arg (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' r) x)) (Complex.arg x))
Case conversion may be inaccurate. Consider using '#align complex.arg_real_mul Complex.arg_real_mulₓ'. -/
theorem arg_real_mul (x : ℂ) {r : ℝ} (hr : 0 < r) : arg (r * x) = arg x :=
  by
  rcases eq_or_ne x 0 with (rfl | hx); · rw [MulZeroClass.mul_zero]
  conv_lhs =>
    rw [← abs_mul_cos_add_sin_mul_I x, ← mul_assoc, ← of_real_mul,
      arg_mul_cos_add_sin_mul_I (mul_pos hr (abs.pos hx)) x.arg_mem_Ioc]
#align complex.arg_real_mul Complex.arg_real_mul

/- warning: complex.arg_eq_arg_iff -> Complex.arg_eq_arg_iff is a dubious translation:
lean 3 declaration is
  forall {x : Complex} {y : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Ne.{1} Complex y (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Iff (Eq.{1} Real (Complex.arg x) (Complex.arg y)) (Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (NormedDivisionRing.toDivisionRing.{0} Complex (NormedField.toNormedDivisionRing.{0} Complex Complex.normedField))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs y)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x))) x) y))
but is expected to have type
  forall {x : Complex} {y : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Ne.{1} Complex y (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Iff (Eq.{1} Real (Complex.arg x) (Complex.arg y)) (Eq.{1} Complex (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (Complex.ofReal' (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs y)) (Complex.ofReal' (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x))) x) y))
Case conversion may be inaccurate. Consider using '#align complex.arg_eq_arg_iff Complex.arg_eq_arg_iffₓ'. -/
theorem arg_eq_arg_iff {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    arg x = arg y ↔ (abs y / abs x : ℂ) * x = y :=
  by
  simp only [ext_abs_arg_iff, map_mul, map_div₀, abs_of_real, abs_abs,
    div_mul_cancel _ (abs.ne_zero hx), eq_self_iff_true, true_and_iff]
  rw [← of_real_div, arg_real_mul]
  exact div_pos (abs.pos hy) (abs.pos hx)
#align complex.arg_eq_arg_iff Complex.arg_eq_arg_iff

/- warning: complex.arg_one -> Complex.arg_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Complex.arg (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (Complex.arg (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align complex.arg_one Complex.arg_oneₓ'. -/
@[simp]
theorem arg_one : arg 1 = 0 := by simp [arg, zero_le_one]
#align complex.arg_one Complex.arg_one

/- warning: complex.arg_neg_one -> Complex.arg_neg_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Complex.arg (Neg.neg.{0} Complex Complex.hasNeg (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))))) Real.pi
but is expected to have type
  Eq.{1} Real (Complex.arg (Neg.neg.{0} Complex Complex.instNegComplex (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))) Real.pi
Case conversion may be inaccurate. Consider using '#align complex.arg_neg_one Complex.arg_neg_oneₓ'. -/
@[simp]
theorem arg_neg_one : arg (-1) = π := by simp [arg, le_refl, not_le.2 (zero_lt_one' ℝ)]
#align complex.arg_neg_one Complex.arg_neg_one

/- warning: complex.arg_I -> Complex.arg_I is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Complex.arg Complex.I) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  Eq.{1} Real (Complex.arg Complex.I) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align complex.arg_I Complex.arg_Iₓ'. -/
@[simp]
theorem arg_I : arg I = π / 2 := by simp [arg, le_refl]
#align complex.arg_I Complex.arg_I

/- warning: complex.arg_neg_I -> Complex.arg_neg_I is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Complex.arg (Neg.neg.{0} Complex Complex.hasNeg Complex.I)) (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  Eq.{1} Real (Complex.arg (Neg.neg.{0} Complex Complex.instNegComplex Complex.I)) (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align complex.arg_neg_I Complex.arg_neg_Iₓ'. -/
@[simp]
theorem arg_neg_I : arg (-I) = -(π / 2) := by simp [arg, le_refl]
#align complex.arg_neg_I Complex.arg_neg_I

/- warning: complex.tan_arg -> Complex.tan_arg is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Real (Real.tan (Complex.arg x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.im x) (Complex.re x))
but is expected to have type
  forall (x : Complex), Eq.{1} Real (Real.tan (Complex.arg x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.im x) (Complex.re x))
Case conversion may be inaccurate. Consider using '#align complex.tan_arg Complex.tan_argₓ'. -/
@[simp]
theorem tan_arg (x : ℂ) : Real.tan (arg x) = x.im / x.re :=
  by
  by_cases h : x = 0
  · simp only [h, zero_div, Complex.zero_im, Complex.arg_zero, Real.tan_zero, Complex.zero_re]
  rw [Real.tan_eq_sin_div_cos, sin_arg, cos_arg h, div_div_div_cancel_right _ (abs.ne_zero h)]
#align complex.tan_arg Complex.tan_arg

/- warning: complex.arg_of_real_of_nonneg -> Complex.arg_of_real_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Complex.arg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Complex.arg (Complex.ofReal' x)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align complex.arg_of_real_of_nonneg Complex.arg_of_real_of_nonnegₓ'. -/
theorem arg_of_real_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arg x = 0 := by simp [arg, hx]
#align complex.arg_of_real_of_nonneg Complex.arg_of_real_of_nonneg

/- warning: complex.arg_eq_zero_iff -> Complex.arg_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, Iff (Eq.{1} Real (Complex.arg z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (And (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re z)) (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {z : Complex}, Iff (Eq.{1} Real (Complex.arg z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (And (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re z)) (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align complex.arg_eq_zero_iff Complex.arg_eq_zero_iffₓ'. -/
theorem arg_eq_zero_iff {z : ℂ} : arg z = 0 ↔ 0 ≤ z.re ∧ z.im = 0 :=
  by
  refine' ⟨fun h => _, _⟩
  · rw [← abs_mul_cos_add_sin_mul_I z, h]
    simp [abs.nonneg]
  · cases' z with x y
    rintro ⟨h, rfl : y = 0⟩
    exact arg_of_real_of_nonneg h
#align complex.arg_eq_zero_iff Complex.arg_eq_zero_iff

/- warning: complex.arg_eq_pi_iff -> Complex.arg_eq_pi_iff is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, Iff (Eq.{1} Real (Complex.arg z) Real.pi) (And (LT.lt.{0} Real Real.hasLt (Complex.re z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {z : Complex}, Iff (Eq.{1} Real (Complex.arg z) Real.pi) (And (LT.lt.{0} Real Real.instLTReal (Complex.re z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align complex.arg_eq_pi_iff Complex.arg_eq_pi_iffₓ'. -/
theorem arg_eq_pi_iff {z : ℂ} : arg z = π ↔ z.re < 0 ∧ z.im = 0 :=
  by
  by_cases h₀ : z = 0; · simp [h₀, lt_irrefl, real.pi_ne_zero.symm]
  constructor
  · intro h
    rw [← abs_mul_cos_add_sin_mul_I z, h]
    simp [h₀]
  · cases' z with x y
    rintro ⟨h : x < 0, rfl : y = 0⟩
    rw [← arg_neg_one, ← arg_real_mul (-1) (neg_pos.2 h)]
    simp [← of_real_def]
#align complex.arg_eq_pi_iff Complex.arg_eq_pi_iff

/- warning: complex.arg_lt_pi_iff -> Complex.arg_lt_pi_iff is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, Iff (LT.lt.{0} Real Real.hasLt (Complex.arg z) Real.pi) (Or (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re z)) (Ne.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {z : Complex}, Iff (LT.lt.{0} Real Real.instLTReal (Complex.arg z) Real.pi) (Or (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re z)) (Ne.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align complex.arg_lt_pi_iff Complex.arg_lt_pi_iffₓ'. -/
theorem arg_lt_pi_iff {z : ℂ} : arg z < π ↔ 0 ≤ z.re ∨ z.im ≠ 0 := by
  rw [(arg_le_pi z).lt_iff_ne, not_iff_comm, not_or, not_le, Classical.not_not, arg_eq_pi_iff]
#align complex.arg_lt_pi_iff Complex.arg_lt_pi_iff

/- warning: complex.arg_of_real_of_neg -> Complex.arg_of_real_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Complex.arg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x)) Real.pi)
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Complex.arg (Complex.ofReal' x)) Real.pi)
Case conversion may be inaccurate. Consider using '#align complex.arg_of_real_of_neg Complex.arg_of_real_of_negₓ'. -/
theorem arg_of_real_of_neg {x : ℝ} (hx : x < 0) : arg x = π :=
  arg_eq_pi_iff.2 ⟨hx, rfl⟩
#align complex.arg_of_real_of_neg Complex.arg_of_real_of_neg

/- warning: complex.arg_eq_pi_div_two_iff -> Complex.arg_eq_pi_div_two_iff is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, Iff (Eq.{1} Real (Complex.arg z) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (And (Eq.{1} Real (Complex.re z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im z)))
but is expected to have type
  forall {z : Complex}, Iff (Eq.{1} Real (Complex.arg z) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (And (Eq.{1} Real (Complex.re z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im z)))
Case conversion may be inaccurate. Consider using '#align complex.arg_eq_pi_div_two_iff Complex.arg_eq_pi_div_two_iffₓ'. -/
theorem arg_eq_pi_div_two_iff {z : ℂ} : arg z = π / 2 ↔ z.re = 0 ∧ 0 < z.im :=
  by
  by_cases h₀ : z = 0; · simp [h₀, lt_irrefl, real.pi_div_two_pos.ne]
  constructor
  · intro h
    rw [← abs_mul_cos_add_sin_mul_I z, h]
    simp [h₀]
  · cases' z with x y
    rintro ⟨rfl : x = 0, hy : 0 < y⟩
    rw [← arg_I, ← arg_real_mul I hy, of_real_mul', I_re, I_im, MulZeroClass.mul_zero, mul_one]
#align complex.arg_eq_pi_div_two_iff Complex.arg_eq_pi_div_two_iff

/- warning: complex.arg_eq_neg_pi_div_two_iff -> Complex.arg_eq_neg_pi_div_two_iff is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, Iff (Eq.{1} Real (Complex.arg z) (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (And (Eq.{1} Real (Complex.re z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {z : Complex}, Iff (Eq.{1} Real (Complex.arg z) (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (And (Eq.{1} Real (Complex.re z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align complex.arg_eq_neg_pi_div_two_iff Complex.arg_eq_neg_pi_div_two_iffₓ'. -/
theorem arg_eq_neg_pi_div_two_iff {z : ℂ} : arg z = -(π / 2) ↔ z.re = 0 ∧ z.im < 0 :=
  by
  by_cases h₀ : z = 0; · simp [h₀, lt_irrefl, Real.pi_ne_zero]
  constructor
  · intro h
    rw [← abs_mul_cos_add_sin_mul_I z, h]
    simp [h₀]
  · cases' z with x y
    rintro ⟨rfl : x = 0, hy : y < 0⟩
    rw [← arg_neg_I, ← arg_real_mul (-I) (neg_pos.2 hy), mk_eq_add_mul_I]
    simp
#align complex.arg_eq_neg_pi_div_two_iff Complex.arg_eq_neg_pi_div_two_iff

/- warning: complex.arg_of_re_nonneg -> Complex.arg_of_re_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re x)) -> (Eq.{1} Real (Complex.arg x) (Real.arcsin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.im x) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x))))
but is expected to have type
  forall {x : Complex}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re x)) -> (Eq.{1} Real (Complex.arg x) (Real.arcsin (HDiv.hDiv.{0, 0, 0} Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.im x) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x))))
Case conversion may be inaccurate. Consider using '#align complex.arg_of_re_nonneg Complex.arg_of_re_nonnegₓ'. -/
theorem arg_of_re_nonneg {x : ℂ} (hx : 0 ≤ x.re) : arg x = Real.arcsin (x.im / x.abs) :=
  if_pos hx
#align complex.arg_of_re_nonneg Complex.arg_of_re_nonneg

/- warning: complex.arg_of_re_neg_of_im_nonneg -> Complex.arg_of_re_neg_of_im_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (LT.lt.{0} Real Real.hasLt (Complex.re x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im x)) -> (Eq.{1} Real (Complex.arg x) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Real.arcsin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.im (Neg.neg.{0} Complex Complex.hasNeg x)) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x))) Real.pi))
but is expected to have type
  forall {x : Complex}, (LT.lt.{0} Real Real.instLTReal (Complex.re x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im x)) -> (Eq.{1} Real (Complex.arg x) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Real.arcsin (HDiv.hDiv.{0, 0, 0} Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.im (Neg.neg.{0} Complex Complex.instNegComplex x)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x))) Real.pi))
Case conversion may be inaccurate. Consider using '#align complex.arg_of_re_neg_of_im_nonneg Complex.arg_of_re_neg_of_im_nonnegₓ'. -/
theorem arg_of_re_neg_of_im_nonneg {x : ℂ} (hx_re : x.re < 0) (hx_im : 0 ≤ x.im) :
    arg x = Real.arcsin ((-x).im / x.abs) + π := by
  simp only [arg, hx_re.not_le, hx_im, if_true, if_false]
#align complex.arg_of_re_neg_of_im_nonneg Complex.arg_of_re_neg_of_im_nonneg

/- warning: complex.arg_of_re_neg_of_im_neg -> Complex.arg_of_re_neg_of_im_neg is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (LT.lt.{0} Real Real.hasLt (Complex.re x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} Real Real.hasLt (Complex.im x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Complex.arg x) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.arcsin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.im (Neg.neg.{0} Complex Complex.hasNeg x)) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x))) Real.pi))
but is expected to have type
  forall {x : Complex}, (LT.lt.{0} Real Real.instLTReal (Complex.re x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} Real Real.instLTReal (Complex.im x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Complex.arg x) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.arcsin (HDiv.hDiv.{0, 0, 0} Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.im (Neg.neg.{0} Complex Complex.instNegComplex x)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x))) Real.pi))
Case conversion may be inaccurate. Consider using '#align complex.arg_of_re_neg_of_im_neg Complex.arg_of_re_neg_of_im_negₓ'. -/
theorem arg_of_re_neg_of_im_neg {x : ℂ} (hx_re : x.re < 0) (hx_im : x.im < 0) :
    arg x = Real.arcsin ((-x).im / x.abs) - π := by
  simp only [arg, hx_re.not_le, hx_im.not_le, if_false]
#align complex.arg_of_re_neg_of_im_neg Complex.arg_of_re_neg_of_im_neg

/- warning: complex.arg_of_im_nonneg_of_ne_zero -> Complex.arg_of_im_nonneg_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im z)) -> (Ne.{1} Complex z (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Real (Complex.arg z) (Real.arccos (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.re z) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs z))))
but is expected to have type
  forall {z : Complex}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im z)) -> (Ne.{1} Complex z (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Real (Complex.arg z) (Real.arccos (HDiv.hDiv.{0, 0, 0} Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.re z) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs z))))
Case conversion may be inaccurate. Consider using '#align complex.arg_of_im_nonneg_of_ne_zero Complex.arg_of_im_nonneg_of_ne_zeroₓ'. -/
theorem arg_of_im_nonneg_of_ne_zero {z : ℂ} (h₁ : 0 ≤ z.im) (h₂ : z ≠ 0) :
    arg z = Real.arccos (z.re / abs z) := by
  rw [← cos_arg h₂, Real.arccos_cos (arg_nonneg_iff.2 h₁) (arg_le_pi _)]
#align complex.arg_of_im_nonneg_of_ne_zero Complex.arg_of_im_nonneg_of_ne_zero

/- warning: complex.arg_of_im_pos -> Complex.arg_of_im_pos is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im z)) -> (Eq.{1} Real (Complex.arg z) (Real.arccos (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.re z) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs z))))
but is expected to have type
  forall {z : Complex}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im z)) -> (Eq.{1} Real (Complex.arg z) (Real.arccos (HDiv.hDiv.{0, 0, 0} Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.re z) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs z))))
Case conversion may be inaccurate. Consider using '#align complex.arg_of_im_pos Complex.arg_of_im_posₓ'. -/
theorem arg_of_im_pos {z : ℂ} (hz : 0 < z.im) : arg z = Real.arccos (z.re / abs z) :=
  arg_of_im_nonneg_of_ne_zero hz.le fun h => hz.ne' <| h.symm ▸ rfl
#align complex.arg_of_im_pos Complex.arg_of_im_pos

/- warning: complex.arg_of_im_neg -> Complex.arg_of_im_neg is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, (LT.lt.{0} Real Real.hasLt (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Complex.arg z) (Neg.neg.{0} Real Real.hasNeg (Real.arccos (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.re z) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs z)))))
but is expected to have type
  forall {z : Complex}, (LT.lt.{0} Real Real.instLTReal (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Complex.arg z) (Neg.neg.{0} Real Real.instNegReal (Real.arccos (HDiv.hDiv.{0, 0, 0} Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) z) Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.re z) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs z)))))
Case conversion may be inaccurate. Consider using '#align complex.arg_of_im_neg Complex.arg_of_im_negₓ'. -/
theorem arg_of_im_neg {z : ℂ} (hz : z.im < 0) : arg z = -Real.arccos (z.re / abs z) :=
  by
  have h₀ : z ≠ 0 := mt (congr_arg im) hz.ne
  rw [← cos_arg h₀, ← Real.cos_neg, Real.arccos_cos, neg_neg]
  exacts[neg_nonneg.2 (arg_neg_iff.2 hz).le, neg_le.2 (neg_pi_lt_arg z).le]
#align complex.arg_of_im_neg Complex.arg_of_im_neg

/- warning: complex.arg_conj -> Complex.arg_conj is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Real (Complex.arg (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) x)) (ite.{1} Real (Eq.{1} Real (Complex.arg x) Real.pi) (Real.decidableEq (Complex.arg x) Real.pi) Real.pi (Neg.neg.{0} Real Real.hasNeg (Complex.arg x)))
but is expected to have type
  forall (x : Complex), Eq.{1} Real (Complex.arg (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) x)) (ite.{1} Real (Eq.{1} Real (Complex.arg x) Real.pi) (Real.decidableEq (Complex.arg x) Real.pi) Real.pi (Neg.neg.{0} Real Real.instNegReal (Complex.arg x)))
Case conversion may be inaccurate. Consider using '#align complex.arg_conj Complex.arg_conjₓ'. -/
theorem arg_conj (x : ℂ) : arg (conj x) = if arg x = π then π else -arg x :=
  by
  simp_rw [arg_eq_pi_iff, arg, neg_im, conj_im, conj_re, abs_conj, neg_div, neg_neg,
    Real.arcsin_neg, apply_ite Neg.neg, neg_add, neg_sub, neg_neg, ← sub_eq_add_neg, sub_neg_eq_add,
    add_comm π]
  rcases lt_trichotomy x.re 0 with (hr | hr | hr) <;>
    rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hr, hr.not_le, hi.le, hi.ne, not_le.2 hi]
  · simp [hr, hr.not_le, hi]
  · simp [hr, hr.not_le, hi.ne.symm, hi.le, not_le.2 hi]
  · simp [hr]
  · simp [hr]
  · simp [hr]
  · simp [hr, hr.le, hi.ne]
  · simp [hr, hr.le, hr.le.not_lt]
  · simp [hr, hr.le, hr.le.not_lt]
#align complex.arg_conj Complex.arg_conj

/- warning: complex.arg_inv -> Complex.arg_inv is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Real (Complex.arg (Inv.inv.{0} Complex Complex.hasInv x)) (ite.{1} Real (Eq.{1} Real (Complex.arg x) Real.pi) (Real.decidableEq (Complex.arg x) Real.pi) Real.pi (Neg.neg.{0} Real Real.hasNeg (Complex.arg x)))
but is expected to have type
  forall (x : Complex), Eq.{1} Real (Complex.arg (Inv.inv.{0} Complex Complex.instInvComplex x)) (ite.{1} Real (Eq.{1} Real (Complex.arg x) Real.pi) (Real.decidableEq (Complex.arg x) Real.pi) Real.pi (Neg.neg.{0} Real Real.instNegReal (Complex.arg x)))
Case conversion may be inaccurate. Consider using '#align complex.arg_inv Complex.arg_invₓ'. -/
theorem arg_inv (x : ℂ) : arg x⁻¹ = if arg x = π then π else -arg x :=
  by
  rw [← arg_conj, inv_def, mul_comm]
  by_cases hx : x = 0
  · simp [hx]
  · exact arg_real_mul (conj x) (by simp [hx])
#align complex.arg_inv Complex.arg_inv

/- warning: complex.arg_le_pi_div_two_iff -> Complex.arg_le_pi_div_two_iff is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, Iff (LE.le.{0} Real Real.hasLe (Complex.arg z) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Or (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re z)) (LT.lt.{0} Real Real.hasLt (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {z : Complex}, Iff (LE.le.{0} Real Real.instLEReal (Complex.arg z) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Or (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re z)) (LT.lt.{0} Real Real.instLTReal (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align complex.arg_le_pi_div_two_iff Complex.arg_le_pi_div_two_iffₓ'. -/
theorem arg_le_pi_div_two_iff {z : ℂ} : arg z ≤ π / 2 ↔ 0 ≤ re z ∨ im z < 0 :=
  by
  cases' le_or_lt 0 (re z) with hre hre
  · simp only [hre, arg_of_re_nonneg hre, Real.arcsin_le_pi_div_two, true_or_iff]
  simp only [hre.not_le, false_or_iff]
  cases' le_or_lt 0 (im z) with him him
  · simp only [him.not_lt]
    rw [iff_false_iff, not_le, arg_of_re_neg_of_im_nonneg hre him, ← sub_lt_iff_lt_add, half_sub,
      Real.neg_pi_div_two_lt_arcsin, neg_im, neg_div, neg_lt_neg_iff, div_lt_one, ←
      _root_.abs_of_nonneg him, abs_im_lt_abs]
    exacts[hre.ne, abs.pos <| ne_of_apply_ne re hre.ne]
  · simp only [him]
    rw [iff_true_iff, arg_of_re_neg_of_im_neg hre him]
    exact (sub_le_self _ real.pi_pos.le).trans (Real.arcsin_le_pi_div_two _)
#align complex.arg_le_pi_div_two_iff Complex.arg_le_pi_div_two_iff

/- warning: complex.neg_pi_div_two_le_arg_iff -> Complex.neg_pi_div_two_le_arg_iff is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, Iff (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Complex.arg z)) (Or (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re z)) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im z)))
but is expected to have type
  forall {z : Complex}, Iff (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Complex.arg z)) (Or (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re z)) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im z)))
Case conversion may be inaccurate. Consider using '#align complex.neg_pi_div_two_le_arg_iff Complex.neg_pi_div_two_le_arg_iffₓ'. -/
theorem neg_pi_div_two_le_arg_iff {z : ℂ} : -(π / 2) ≤ arg z ↔ 0 ≤ re z ∨ 0 ≤ im z :=
  by
  cases' le_or_lt 0 (re z) with hre hre
  · simp only [hre, arg_of_re_nonneg hre, Real.neg_pi_div_two_le_arcsin, true_or_iff]
  simp only [hre.not_le, false_or_iff]
  cases' le_or_lt 0 (im z) with him him
  · simp only [him]
    rw [iff_true_iff, arg_of_re_neg_of_im_nonneg hre him]
    exact (Real.neg_pi_div_two_le_arcsin _).trans (le_add_of_nonneg_right real.pi_pos.le)
  · simp only [him.not_le]
    rw [iff_false_iff, not_le, arg_of_re_neg_of_im_neg hre him, sub_lt_iff_lt_add', ←
      sub_eq_add_neg, sub_half, Real.arcsin_lt_pi_div_two, div_lt_one, neg_im, ← abs_of_neg him,
      abs_im_lt_abs]
    exacts[hre.ne, abs.pos <| ne_of_apply_ne re hre.ne]
#align complex.neg_pi_div_two_le_arg_iff Complex.neg_pi_div_two_le_arg_iff

/- warning: complex.abs_arg_le_pi_div_two_iff -> Complex.abs_arg_le_pi_div_two_iff is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, Iff (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Complex.arg z)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re z))
but is expected to have type
  forall {z : Complex}, Iff (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Complex.arg z)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re z))
Case conversion may be inaccurate. Consider using '#align complex.abs_arg_le_pi_div_two_iff Complex.abs_arg_le_pi_div_two_iffₓ'. -/
@[simp]
theorem abs_arg_le_pi_div_two_iff {z : ℂ} : |arg z| ≤ π / 2 ↔ 0 ≤ re z := by
  rw [abs_le, arg_le_pi_div_two_iff, neg_pi_div_two_le_arg_iff, ← or_and_left, ← not_le,
    and_not_self_iff, or_false_iff]
#align complex.abs_arg_le_pi_div_two_iff Complex.abs_arg_le_pi_div_two_iff

/- warning: complex.arg_conj_coe_angle -> Complex.arg_conj_coe_angle is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Real.Angle ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) x))) (Neg.neg.{0} Real.Angle (SubNegMonoid.toHasNeg.{0} Real.Angle (AddGroup.toSubNegMonoid.{0} Real.Angle (NormedAddGroup.toAddGroup.{0} Real.Angle (NormedAddCommGroup.toNormedAddGroup.{0} Real.Angle Real.Angle.normedAddCommGroup)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg x)))
but is expected to have type
  forall (x : Complex), Eq.{1} Real.Angle (Real.Angle.coe (Complex.arg (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) x))) (Neg.neg.{0} Real.Angle (NegZeroClass.toNeg.{0} Real.Angle (SubNegZeroMonoid.toNegZeroClass.{0} Real.Angle (SubtractionMonoid.toSubNegZeroMonoid.{0} Real.Angle (SubtractionCommMonoid.toSubtractionMonoid.{0} Real.Angle (AddCommGroup.toDivisionAddCommMonoid.{0} Real.Angle (NormedAddCommGroup.toAddCommGroup.{0} Real.Angle Real.Angle.instNormedAddCommGroupAngle)))))) (Real.Angle.coe (Complex.arg x)))
Case conversion may be inaccurate. Consider using '#align complex.arg_conj_coe_angle Complex.arg_conj_coe_angleₓ'. -/
@[simp]
theorem arg_conj_coe_angle (x : ℂ) : (arg (conj x) : Real.Angle) = -arg x := by
  by_cases h : arg x = π <;> simp [arg_conj, h]
#align complex.arg_conj_coe_angle Complex.arg_conj_coe_angle

/- warning: complex.arg_inv_coe_angle -> Complex.arg_inv_coe_angle is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Real.Angle ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg (Inv.inv.{0} Complex Complex.hasInv x))) (Neg.neg.{0} Real.Angle (SubNegMonoid.toHasNeg.{0} Real.Angle (AddGroup.toSubNegMonoid.{0} Real.Angle (NormedAddGroup.toAddGroup.{0} Real.Angle (NormedAddCommGroup.toNormedAddGroup.{0} Real.Angle Real.Angle.normedAddCommGroup)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg x)))
but is expected to have type
  forall (x : Complex), Eq.{1} Real.Angle (Real.Angle.coe (Complex.arg (Inv.inv.{0} Complex Complex.instInvComplex x))) (Neg.neg.{0} Real.Angle (NegZeroClass.toNeg.{0} Real.Angle (SubNegZeroMonoid.toNegZeroClass.{0} Real.Angle (SubtractionMonoid.toSubNegZeroMonoid.{0} Real.Angle (SubtractionCommMonoid.toSubtractionMonoid.{0} Real.Angle (AddCommGroup.toDivisionAddCommMonoid.{0} Real.Angle (NormedAddCommGroup.toAddCommGroup.{0} Real.Angle Real.Angle.instNormedAddCommGroupAngle)))))) (Real.Angle.coe (Complex.arg x)))
Case conversion may be inaccurate. Consider using '#align complex.arg_inv_coe_angle Complex.arg_inv_coe_angleₓ'. -/
@[simp]
theorem arg_inv_coe_angle (x : ℂ) : (arg x⁻¹ : Real.Angle) = -arg x := by
  by_cases h : arg x = π <;> simp [arg_inv, h]
#align complex.arg_inv_coe_angle Complex.arg_inv_coe_angle

/- warning: complex.arg_neg_eq_arg_sub_pi_of_im_pos -> Complex.arg_neg_eq_arg_sub_pi_of_im_pos is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im x)) -> (Eq.{1} Real (Complex.arg (Neg.neg.{0} Complex Complex.hasNeg x)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Complex.arg x) Real.pi))
but is expected to have type
  forall {x : Complex}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im x)) -> (Eq.{1} Real (Complex.arg (Neg.neg.{0} Complex Complex.instNegComplex x)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Complex.arg x) Real.pi))
Case conversion may be inaccurate. Consider using '#align complex.arg_neg_eq_arg_sub_pi_of_im_pos Complex.arg_neg_eq_arg_sub_pi_of_im_posₓ'. -/
theorem arg_neg_eq_arg_sub_pi_of_im_pos {x : ℂ} (hi : 0 < x.im) : arg (-x) = arg x - π :=
  by
  rw [arg_of_im_pos hi, arg_of_im_neg (show (-x).im < 0 from Left.neg_neg_iff.2 hi)]
  simp [neg_div, Real.arccos_neg]
#align complex.arg_neg_eq_arg_sub_pi_of_im_pos Complex.arg_neg_eq_arg_sub_pi_of_im_pos

/- warning: complex.arg_neg_eq_arg_add_pi_of_im_neg -> Complex.arg_neg_eq_arg_add_pi_of_im_neg is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (LT.lt.{0} Real Real.hasLt (Complex.im x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Complex.arg (Neg.neg.{0} Complex Complex.hasNeg x)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Complex.arg x) Real.pi))
but is expected to have type
  forall {x : Complex}, (LT.lt.{0} Real Real.instLTReal (Complex.im x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Complex.arg (Neg.neg.{0} Complex Complex.instNegComplex x)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Complex.arg x) Real.pi))
Case conversion may be inaccurate. Consider using '#align complex.arg_neg_eq_arg_add_pi_of_im_neg Complex.arg_neg_eq_arg_add_pi_of_im_negₓ'. -/
theorem arg_neg_eq_arg_add_pi_of_im_neg {x : ℂ} (hi : x.im < 0) : arg (-x) = arg x + π :=
  by
  rw [arg_of_im_neg hi, arg_of_im_pos (show 0 < (-x).im from Left.neg_pos_iff.2 hi)]
  simp [neg_div, Real.arccos_neg, add_comm, ← sub_eq_add_neg]
#align complex.arg_neg_eq_arg_add_pi_of_im_neg Complex.arg_neg_eq_arg_add_pi_of_im_neg

/- warning: complex.arg_neg_eq_arg_sub_pi_iff -> Complex.arg_neg_eq_arg_sub_pi_iff is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, Iff (Eq.{1} Real (Complex.arg (Neg.neg.{0} Complex Complex.hasNeg x)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Complex.arg x) Real.pi)) (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im x)) (And (Eq.{1} Real (Complex.im x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (Complex.re x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))
but is expected to have type
  forall {x : Complex}, Iff (Eq.{1} Real (Complex.arg (Neg.neg.{0} Complex Complex.instNegComplex x)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Complex.arg x) Real.pi)) (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im x)) (And (Eq.{1} Real (Complex.im x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (Complex.re x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))))
Case conversion may be inaccurate. Consider using '#align complex.arg_neg_eq_arg_sub_pi_iff Complex.arg_neg_eq_arg_sub_pi_iffₓ'. -/
theorem arg_neg_eq_arg_sub_pi_iff {x : ℂ} : arg (-x) = arg x - π ↔ 0 < x.im ∨ x.im = 0 ∧ x.re < 0 :=
  by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  ·
    simp [hi, hi.ne, hi.not_lt, arg_neg_eq_arg_add_pi_of_im_neg, sub_eq_add_neg, ←
      add_eq_zero_iff_eq_neg, Real.pi_ne_zero]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_of_real_of_neg hr, ← of_real_neg, arg_of_real_of_nonneg (Left.neg_pos_iff.2 hr).le]
      simp [hr]
    · simp [hr, hi, Real.pi_ne_zero]
    · rw [arg_of_real_of_nonneg hr.le, ← of_real_neg, arg_of_real_of_neg (Left.neg_neg_iff.2 hr)]
      simp [hr.not_lt, ← add_eq_zero_iff_eq_neg, Real.pi_ne_zero]
  · simp [hi, arg_neg_eq_arg_sub_pi_of_im_pos]
#align complex.arg_neg_eq_arg_sub_pi_iff Complex.arg_neg_eq_arg_sub_pi_iff

/- warning: complex.arg_neg_eq_arg_add_pi_iff -> Complex.arg_neg_eq_arg_add_pi_iff is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, Iff (Eq.{1} Real (Complex.arg (Neg.neg.{0} Complex Complex.hasNeg x)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Complex.arg x) Real.pi)) (Or (LT.lt.{0} Real Real.hasLt (Complex.im x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (And (Eq.{1} Real (Complex.im x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re x))))
but is expected to have type
  forall {x : Complex}, Iff (Eq.{1} Real (Complex.arg (Neg.neg.{0} Complex Complex.instNegComplex x)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Complex.arg x) Real.pi)) (Or (LT.lt.{0} Real Real.instLTReal (Complex.im x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (And (Eq.{1} Real (Complex.im x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re x))))
Case conversion may be inaccurate. Consider using '#align complex.arg_neg_eq_arg_add_pi_iff Complex.arg_neg_eq_arg_add_pi_iffₓ'. -/
theorem arg_neg_eq_arg_add_pi_iff {x : ℂ} : arg (-x) = arg x + π ↔ x.im < 0 ∨ x.im = 0 ∧ 0 < x.re :=
  by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hi, arg_neg_eq_arg_add_pi_of_im_neg]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_of_real_of_neg hr, ← of_real_neg, arg_of_real_of_nonneg (Left.neg_pos_iff.2 hr).le]
      simp [hr.not_lt, ← two_mul, Real.pi_ne_zero]
    · simp [hr, hi, real.pi_ne_zero.symm]
    · rw [arg_of_real_of_nonneg hr.le, ← of_real_neg, arg_of_real_of_neg (Left.neg_neg_iff.2 hr)]
      simp [hr]
  ·
    simp [hi, hi.ne.symm, hi.not_lt, arg_neg_eq_arg_sub_pi_of_im_pos, sub_eq_add_neg, ←
      add_eq_zero_iff_neg_eq, Real.pi_ne_zero]
#align complex.arg_neg_eq_arg_add_pi_iff Complex.arg_neg_eq_arg_add_pi_iff

/- warning: complex.arg_neg_coe_angle -> Complex.arg_neg_coe_angle is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Real.Angle ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg (Neg.neg.{0} Complex Complex.hasNeg x))) (HAdd.hAdd.{0, 0, 0} Real.Angle Real.Angle Real.Angle (instHAdd.{0} Real.Angle (AddZeroClass.toHasAdd.{0} Real.Angle (AddMonoid.toAddZeroClass.{0} Real.Angle (SubNegMonoid.toAddMonoid.{0} Real.Angle (AddGroup.toSubNegMonoid.{0} Real.Angle (NormedAddGroup.toAddGroup.{0} Real.Angle (NormedAddCommGroup.toNormedAddGroup.{0} Real.Angle Real.Angle.normedAddCommGroup))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg x)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) Real.pi)))
but is expected to have type
  forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Real.Angle (Real.Angle.coe (Complex.arg (Neg.neg.{0} Complex Complex.instNegComplex x))) (HAdd.hAdd.{0, 0, 0} Real.Angle Real.Angle Real.Angle (instHAdd.{0} Real.Angle (AddZeroClass.toAdd.{0} Real.Angle (AddMonoid.toAddZeroClass.{0} Real.Angle (SubNegMonoid.toAddMonoid.{0} Real.Angle (AddGroup.toSubNegMonoid.{0} Real.Angle (NormedAddGroup.toAddGroup.{0} Real.Angle (NormedAddCommGroup.toNormedAddGroup.{0} Real.Angle Real.Angle.instNormedAddCommGroupAngle))))))) (Real.Angle.coe (Complex.arg x)) (Real.Angle.coe Real.pi)))
Case conversion may be inaccurate. Consider using '#align complex.arg_neg_coe_angle Complex.arg_neg_coe_angleₓ'. -/
theorem arg_neg_coe_angle {x : ℂ} (hx : x ≠ 0) : (arg (-x) : Real.Angle) = arg x + π :=
  by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · rw [arg_neg_eq_arg_add_pi_of_im_neg hi, Real.Angle.coe_add]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    ·
      rw [arg_of_real_of_neg hr, ← of_real_neg, arg_of_real_of_nonneg (Left.neg_pos_iff.2 hr).le, ←
        Real.Angle.coe_add, ← two_mul, Real.Angle.coe_two_pi, Real.Angle.coe_zero]
    · exact False.elim (hx (ext hr hi))
    ·
      rw [arg_of_real_of_nonneg hr.le, ← of_real_neg, arg_of_real_of_neg (Left.neg_neg_iff.2 hr),
        Real.Angle.coe_zero, zero_add]
  · rw [arg_neg_eq_arg_sub_pi_of_im_pos hi, Real.Angle.coe_sub, Real.Angle.sub_coe_pi_eq_add_coe_pi]
#align complex.arg_neg_coe_angle Complex.arg_neg_coe_angle

/- warning: complex.arg_mul_cos_add_sin_mul_I_eq_to_Ioc_mod -> Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (forall (θ : Real), Eq.{1} Real (Complex.arg (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) r) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) θ)) Complex.I)))) (toIocMod.{0} Real Real.linearOrderedAddCommGroup Real.archimedean (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) Real.pi) Real.two_pi_pos (Neg.neg.{0} Real Real.hasNeg Real.pi) θ))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (forall (θ : Real), Eq.{1} Real (Complex.arg (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' r) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos (Complex.ofReal' θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' θ)) Complex.I)))) (toIocMod.{0} Real Real.instLinearOrderedAddCommGroupReal Real.instArchimedeanRealOrderedAddCommMonoid (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) Real.pi) Real.two_pi_pos (Neg.neg.{0} Real Real.instNegReal Real.pi) θ))
Case conversion may be inaccurate. Consider using '#align complex.arg_mul_cos_add_sin_mul_I_eq_to_Ioc_mod Complex.arg_mul_cos_add_sin_mul_I_eq_toIocModₓ'. -/
theorem arg_mul_cos_add_sin_mul_I_eq_toIocMod {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    arg (r * (cos θ + sin θ * I)) = toIocMod Real.two_pi_pos (-π) θ :=
  by
  have hi : toIocMod Real.two_pi_pos (-π) θ ∈ Ioc (-π) π :=
    by
    convert toIocMod_mem_Ioc _ _ _
    ring
  convert arg_mul_cos_add_sin_mul_I hr hi using 3
  simp [toIocMod, cos_sub_int_mul_two_pi, sin_sub_int_mul_two_pi]
#align complex.arg_mul_cos_add_sin_mul_I_eq_to_Ioc_mod Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod

/- warning: complex.arg_cos_add_sin_mul_I_eq_to_Ioc_mod -> Complex.arg_cos_add_sin_mul_I_eq_toIocMod is a dubious translation:
lean 3 declaration is
  forall (θ : Real), Eq.{1} Real (Complex.arg (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) θ)) Complex.I))) (toIocMod.{0} Real Real.linearOrderedAddCommGroup Real.archimedean (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) Real.pi) Real.two_pi_pos (Neg.neg.{0} Real Real.hasNeg Real.pi) θ)
but is expected to have type
  forall (θ : Real), Eq.{1} Real (Complex.arg (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos (Complex.ofReal' θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' θ)) Complex.I))) (toIocMod.{0} Real Real.instLinearOrderedAddCommGroupReal Real.instArchimedeanRealOrderedAddCommMonoid (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) Real.pi) Real.two_pi_pos (Neg.neg.{0} Real Real.instNegReal Real.pi) θ)
Case conversion may be inaccurate. Consider using '#align complex.arg_cos_add_sin_mul_I_eq_to_Ioc_mod Complex.arg_cos_add_sin_mul_I_eq_toIocModₓ'. -/
theorem arg_cos_add_sin_mul_I_eq_toIocMod (θ : ℝ) :
    arg (cos θ + sin θ * I) = toIocMod Real.two_pi_pos (-π) θ := by
  rw [← one_mul (_ + _), ← of_real_one, arg_mul_cos_add_sin_mul_I_eq_to_Ioc_mod zero_lt_one]
#align complex.arg_cos_add_sin_mul_I_eq_to_Ioc_mod Complex.arg_cos_add_sin_mul_I_eq_toIocMod

/- warning: complex.arg_mul_cos_add_sin_mul_I_sub -> Complex.arg_mul_cos_add_sin_mul_I_sub is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (forall (θ : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Complex.arg (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) r) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) θ)) Complex.I)))) θ) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) Real.pi) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) (Int.floor.{0} Real Real.linearOrderedRing Real.floorRing (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) Real.pi θ) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) Real.pi))))))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (forall (θ : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Complex.arg (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' r) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos (Complex.ofReal' θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' θ)) Complex.I)))) θ) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) Real.pi) (Int.cast.{0} Real Real.intCast (Int.floor.{0} Real Real.instLinearOrderedRingReal Real.instFloorRingRealInstLinearOrderedRingReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) Real.pi θ) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) Real.pi))))))
Case conversion may be inaccurate. Consider using '#align complex.arg_mul_cos_add_sin_mul_I_sub Complex.arg_mul_cos_add_sin_mul_I_subₓ'. -/
theorem arg_mul_cos_add_sin_mul_I_sub {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    arg (r * (cos θ + sin θ * I)) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ :=
  by
  rw [arg_mul_cos_add_sin_mul_I_eq_to_Ioc_mod hr, toIocMod_sub_self, toIocDiv_eq_neg_floor,
    zsmul_eq_mul]
  ring_nf
#align complex.arg_mul_cos_add_sin_mul_I_sub Complex.arg_mul_cos_add_sin_mul_I_sub

/- warning: complex.arg_cos_add_sin_mul_I_sub -> Complex.arg_cos_add_sin_mul_I_sub is a dubious translation:
lean 3 declaration is
  forall (θ : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Complex.arg (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.cos ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) θ)) Complex.I))) θ) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) Real.pi) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) (Int.floor.{0} Real Real.linearOrderedRing Real.floorRing (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) Real.pi θ) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) Real.pi)))))
but is expected to have type
  forall (θ : Real), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Complex.arg (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.cos (Complex.ofReal' θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.sin (Complex.ofReal' θ)) Complex.I))) θ) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) Real.pi) (Int.cast.{0} Real Real.intCast (Int.floor.{0} Real Real.instLinearOrderedRingReal Real.instFloorRingRealInstLinearOrderedRingReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) Real.pi θ) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) Real.pi)))))
Case conversion may be inaccurate. Consider using '#align complex.arg_cos_add_sin_mul_I_sub Complex.arg_cos_add_sin_mul_I_subₓ'. -/
theorem arg_cos_add_sin_mul_I_sub (θ : ℝ) :
    arg (cos θ + sin θ * I) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ := by
  rw [← one_mul (_ + _), ← of_real_one, arg_mul_cos_add_sin_mul_I_sub zero_lt_one]
#align complex.arg_cos_add_sin_mul_I_sub Complex.arg_cos_add_sin_mul_I_sub

/- warning: complex.arg_mul_cos_add_sin_mul_I_coe_angle -> Complex.arg_mul_cos_add_sin_mul_I_coe_angle is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (forall (θ : Real.Angle), Eq.{1} Real.Angle ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) r) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.Angle.cos θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.Angle.sin θ)) Complex.I))))) θ)
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (forall (θ : Real.Angle), Eq.{1} Real.Angle (Real.Angle.coe (Complex.arg (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' r) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.ofReal' (Real.Angle.cos θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' (Real.Angle.sin θ)) Complex.I))))) θ)
Case conversion may be inaccurate. Consider using '#align complex.arg_mul_cos_add_sin_mul_I_coe_angle Complex.arg_mul_cos_add_sin_mul_I_coe_angleₓ'. -/
theorem arg_mul_cos_add_sin_mul_I_coe_angle {r : ℝ} (hr : 0 < r) (θ : Real.Angle) :
    (arg (r * (Real.Angle.cos θ + Real.Angle.sin θ * I)) : Real.Angle) = θ :=
  by
  induction θ using Real.Angle.induction_on
  rw [Real.Angle.cos_coe, Real.Angle.sin_coe, Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  use ⌊(π - θ) / (2 * π)⌋
  exact_mod_cast arg_mul_cos_add_sin_mul_I_sub hr θ
#align complex.arg_mul_cos_add_sin_mul_I_coe_angle Complex.arg_mul_cos_add_sin_mul_I_coe_angle

/- warning: complex.arg_cos_add_sin_mul_I_coe_angle -> Complex.arg_cos_add_sin_mul_I_coe_angle is a dubious translation:
lean 3 declaration is
  forall (θ : Real.Angle), Eq.{1} Real.Angle ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.Angle.cos θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Real.Angle.sin θ)) Complex.I)))) θ
but is expected to have type
  forall (θ : Real.Angle), Eq.{1} Real.Angle (Real.Angle.coe (Complex.arg (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.ofReal' (Real.Angle.cos θ)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' (Real.Angle.sin θ)) Complex.I)))) θ
Case conversion may be inaccurate. Consider using '#align complex.arg_cos_add_sin_mul_I_coe_angle Complex.arg_cos_add_sin_mul_I_coe_angleₓ'. -/
theorem arg_cos_add_sin_mul_I_coe_angle (θ : Real.Angle) :
    (arg (Real.Angle.cos θ + Real.Angle.sin θ * I) : Real.Angle) = θ := by
  rw [← one_mul (_ + _), ← of_real_one, arg_mul_cos_add_sin_mul_I_coe_angle zero_lt_one]
#align complex.arg_cos_add_sin_mul_I_coe_angle Complex.arg_cos_add_sin_mul_I_coe_angle

/- warning: complex.arg_mul_coe_angle -> Complex.arg_mul_coe_angle is a dubious translation:
lean 3 declaration is
  forall {x : Complex} {y : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Ne.{1} Complex y (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Real.Angle ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) x y))) (HAdd.hAdd.{0, 0, 0} Real.Angle Real.Angle Real.Angle (instHAdd.{0} Real.Angle (AddZeroClass.toHasAdd.{0} Real.Angle (AddMonoid.toAddZeroClass.{0} Real.Angle (SubNegMonoid.toAddMonoid.{0} Real.Angle (AddGroup.toSubNegMonoid.{0} Real.Angle (NormedAddGroup.toAddGroup.{0} Real.Angle (NormedAddCommGroup.toNormedAddGroup.{0} Real.Angle Real.Angle.normedAddCommGroup))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg x)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg y))))
but is expected to have type
  forall {x : Complex} {y : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Ne.{1} Complex y (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Real.Angle (Real.Angle.coe (Complex.arg (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) x y))) (HAdd.hAdd.{0, 0, 0} Real.Angle Real.Angle Real.Angle (instHAdd.{0} Real.Angle (AddZeroClass.toAdd.{0} Real.Angle (AddMonoid.toAddZeroClass.{0} Real.Angle (SubNegMonoid.toAddMonoid.{0} Real.Angle (AddGroup.toSubNegMonoid.{0} Real.Angle (NormedAddGroup.toAddGroup.{0} Real.Angle (NormedAddCommGroup.toNormedAddGroup.{0} Real.Angle Real.Angle.instNormedAddCommGroupAngle))))))) (Real.Angle.coe (Complex.arg x)) (Real.Angle.coe (Complex.arg y))))
Case conversion may be inaccurate. Consider using '#align complex.arg_mul_coe_angle Complex.arg_mul_coe_angleₓ'. -/
theorem arg_mul_coe_angle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (arg (x * y) : Real.Angle) = arg x + arg y :=
  by
  convert arg_mul_cos_add_sin_mul_I_coe_angle (mul_pos (abs.pos hx) (abs.pos hy))
      (arg x + arg y : Real.Angle) using
    3
  simp_rw [← Real.Angle.coe_add, Real.Angle.sin_coe, Real.Angle.cos_coe, of_real_cos, of_real_sin,
    cos_add_sin_I, of_real_add, add_mul, exp_add, of_real_mul]
  rw [mul_assoc, mul_comm (exp _), ← mul_assoc (abs y : ℂ), abs_mul_exp_arg_mul_I, mul_comm y, ←
    mul_assoc, abs_mul_exp_arg_mul_I]
#align complex.arg_mul_coe_angle Complex.arg_mul_coe_angle

/- warning: complex.arg_div_coe_angle -> Complex.arg_div_coe_angle is a dubious translation:
lean 3 declaration is
  forall {x : Complex} {y : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Ne.{1} Complex y (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Real.Angle ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (NormedDivisionRing.toDivisionRing.{0} Complex (NormedField.toNormedDivisionRing.{0} Complex Complex.normedField))))) x y))) (HSub.hSub.{0, 0, 0} Real.Angle Real.Angle Real.Angle (instHSub.{0} Real.Angle (SubNegMonoid.toHasSub.{0} Real.Angle (AddGroup.toSubNegMonoid.{0} Real.Angle (NormedAddGroup.toAddGroup.{0} Real.Angle (NormedAddCommGroup.toNormedAddGroup.{0} Real.Angle Real.Angle.normedAddCommGroup))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg x)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg y))))
but is expected to have type
  forall {x : Complex} {y : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Ne.{1} Complex y (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Real.Angle (Real.Angle.coe (Complex.arg (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) x y))) (HSub.hSub.{0, 0, 0} Real.Angle Real.Angle Real.Angle (instHSub.{0} Real.Angle (SubNegMonoid.toSub.{0} Real.Angle (AddGroup.toSubNegMonoid.{0} Real.Angle (NormedAddGroup.toAddGroup.{0} Real.Angle (NormedAddCommGroup.toNormedAddGroup.{0} Real.Angle Real.Angle.instNormedAddCommGroupAngle))))) (Real.Angle.coe (Complex.arg x)) (Real.Angle.coe (Complex.arg y))))
Case conversion may be inaccurate. Consider using '#align complex.arg_div_coe_angle Complex.arg_div_coe_angleₓ'. -/
theorem arg_div_coe_angle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (arg (x / y) : Real.Angle) = arg x - arg y := by
  rw [div_eq_mul_inv, arg_mul_coe_angle hx (inv_ne_zero hy), arg_inv_coe_angle, sub_eq_add_neg]
#align complex.arg_div_coe_angle Complex.arg_div_coe_angle

/- warning: complex.arg_coe_angle_to_real_eq_arg -> Complex.arg_coe_angle_toReal_eq_arg is a dubious translation:
lean 3 declaration is
  forall (z : Complex), Eq.{1} Real (Real.Angle.toReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg z))) (Complex.arg z)
but is expected to have type
  forall (z : Complex), Eq.{1} Real (Real.Angle.toReal (Real.Angle.coe (Complex.arg z))) (Complex.arg z)
Case conversion may be inaccurate. Consider using '#align complex.arg_coe_angle_to_real_eq_arg Complex.arg_coe_angle_toReal_eq_argₓ'. -/
@[simp]
theorem arg_coe_angle_toReal_eq_arg (z : ℂ) : (arg z : Real.Angle).toReal = arg z :=
  by
  rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]
  exact arg_mem_Ioc _
#align complex.arg_coe_angle_to_real_eq_arg Complex.arg_coe_angle_toReal_eq_arg

/- warning: complex.arg_coe_angle_eq_iff_eq_to_real -> Complex.arg_coe_angle_eq_iff_eq_toReal is a dubious translation:
lean 3 declaration is
  forall {z : Complex} {θ : Real.Angle}, Iff (Eq.{1} Real.Angle ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg z)) θ) (Eq.{1} Real (Complex.arg z) (Real.Angle.toReal θ))
but is expected to have type
  forall {z : Complex} {θ : Real.Angle}, Iff (Eq.{1} Real.Angle (Real.Angle.coe (Complex.arg z)) θ) (Eq.{1} Real (Complex.arg z) (Real.Angle.toReal θ))
Case conversion may be inaccurate. Consider using '#align complex.arg_coe_angle_eq_iff_eq_to_real Complex.arg_coe_angle_eq_iff_eq_toRealₓ'. -/
theorem arg_coe_angle_eq_iff_eq_toReal {z : ℂ} {θ : Real.Angle} :
    (arg z : Real.Angle) = θ ↔ arg z = θ.toReal := by
  rw [← Real.Angle.toReal_inj, arg_coe_angle_to_real_eq_arg]
#align complex.arg_coe_angle_eq_iff_eq_to_real Complex.arg_coe_angle_eq_iff_eq_toReal

/- warning: complex.arg_coe_angle_eq_iff -> Complex.arg_coe_angle_eq_iff is a dubious translation:
lean 3 declaration is
  forall {x : Complex} {y : Complex}, Iff (Eq.{1} Real.Angle ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg x)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT)) (Complex.arg y))) (Eq.{1} Real (Complex.arg x) (Complex.arg y))
but is expected to have type
  forall {x : Complex} {y : Complex}, Iff (Eq.{1} Real.Angle (Real.Angle.coe (Complex.arg x)) (Real.Angle.coe (Complex.arg y))) (Eq.{1} Real (Complex.arg x) (Complex.arg y))
Case conversion may be inaccurate. Consider using '#align complex.arg_coe_angle_eq_iff Complex.arg_coe_angle_eq_iffₓ'. -/
@[simp]
theorem arg_coe_angle_eq_iff {x y : ℂ} : (arg x : Real.Angle) = arg y ↔ arg x = arg y := by
  simp_rw [← Real.Angle.toReal_inj, arg_coe_angle_to_real_eq_arg]
#align complex.arg_coe_angle_eq_iff Complex.arg_coe_angle_eq_iff

section Continuity

variable {x z : ℂ}

/- warning: complex.arg_eq_nhds_of_re_pos -> Complex.arg_eq_nhds_of_re_pos is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re x)) -> (Filter.EventuallyEq.{0, 0} Complex Real (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) x) Complex.arg (fun (x : Complex) => Real.arcsin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.im x) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x))))
but is expected to have type
  forall {x : Complex}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re x)) -> (Filter.EventuallyEq.{0, 0} Complex Real (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) x) Complex.arg (fun (x : Complex) => Real.arcsin (HDiv.hDiv.{0, 0, 0} Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.im x) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x))))
Case conversion may be inaccurate. Consider using '#align complex.arg_eq_nhds_of_re_pos Complex.arg_eq_nhds_of_re_posₓ'. -/
theorem arg_eq_nhds_of_re_pos (hx : 0 < x.re) : arg =ᶠ[𝓝 x] fun x => Real.arcsin (x.im / x.abs) :=
  ((continuous_re.Tendsto _).Eventually (lt_mem_nhds hx)).mono fun y hy => arg_of_re_nonneg hy.le
#align complex.arg_eq_nhds_of_re_pos Complex.arg_eq_nhds_of_re_pos

/- warning: complex.arg_eq_nhds_of_re_neg_of_im_pos -> Complex.arg_eq_nhds_of_re_neg_of_im_pos is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (LT.lt.{0} Real Real.hasLt (Complex.re x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im x)) -> (Filter.EventuallyEq.{0, 0} Complex Real (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) x) Complex.arg (fun (x : Complex) => HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Real.arcsin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.im (Neg.neg.{0} Complex Complex.hasNeg x)) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x))) Real.pi))
but is expected to have type
  forall {x : Complex}, (LT.lt.{0} Real Real.instLTReal (Complex.re x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im x)) -> (Filter.EventuallyEq.{0, 0} Complex Real (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) x) Complex.arg (fun (x : Complex) => HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Real.arcsin (HDiv.hDiv.{0, 0, 0} Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.im (Neg.neg.{0} Complex Complex.instNegComplex x)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x))) Real.pi))
Case conversion may be inaccurate. Consider using '#align complex.arg_eq_nhds_of_re_neg_of_im_pos Complex.arg_eq_nhds_of_re_neg_of_im_posₓ'. -/
theorem arg_eq_nhds_of_re_neg_of_im_pos (hx_re : x.re < 0) (hx_im : 0 < x.im) :
    arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / x.abs) + π :=
  by
  suffices h_forall_nhds : ∀ᶠ y : ℂ in 𝓝 x, y.re < 0 ∧ 0 < y.im
  exact h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_nonneg hy.1 hy.2.le
  refine' IsOpen.eventually_mem _ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ 0 < x.im)
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isOpen_lt continuous_zero continuous_im)
#align complex.arg_eq_nhds_of_re_neg_of_im_pos Complex.arg_eq_nhds_of_re_neg_of_im_pos

/- warning: complex.arg_eq_nhds_of_re_neg_of_im_neg -> Complex.arg_eq_nhds_of_re_neg_of_im_neg is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (LT.lt.{0} Real Real.hasLt (Complex.re x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} Real Real.hasLt (Complex.im x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.EventuallyEq.{0, 0} Complex Real (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) x) Complex.arg (fun (x : Complex) => HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.arcsin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.im (Neg.neg.{0} Complex Complex.hasNeg x)) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x))) Real.pi))
but is expected to have type
  forall {x : Complex}, (LT.lt.{0} Real Real.instLTReal (Complex.re x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} Real Real.instLTReal (Complex.im x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.EventuallyEq.{0, 0} Complex Real (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) x) Complex.arg (fun (x : Complex) => HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.arcsin (HDiv.hDiv.{0, 0, 0} Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.im (Neg.neg.{0} Complex Complex.instNegComplex x)) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x))) Real.pi))
Case conversion may be inaccurate. Consider using '#align complex.arg_eq_nhds_of_re_neg_of_im_neg Complex.arg_eq_nhds_of_re_neg_of_im_negₓ'. -/
theorem arg_eq_nhds_of_re_neg_of_im_neg (hx_re : x.re < 0) (hx_im : x.im < 0) :
    arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / x.abs) - π :=
  by
  suffices h_forall_nhds : ∀ᶠ y : ℂ in 𝓝 x, y.re < 0 ∧ y.im < 0
  exact h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_neg hy.1 hy.2
  refine' IsOpen.eventually_mem _ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ x.im < 0)
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isOpen_lt continuous_im continuous_zero)
#align complex.arg_eq_nhds_of_re_neg_of_im_neg Complex.arg_eq_nhds_of_re_neg_of_im_neg

/- warning: complex.arg_eq_nhds_of_im_pos -> Complex.arg_eq_nhds_of_im_pos is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im z)) -> (Filter.EventuallyEq.{0, 0} Complex Real (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) z) Complex.arg (fun (x : Complex) => Real.arccos (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.re x) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x))))
but is expected to have type
  forall {z : Complex}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im z)) -> (Filter.EventuallyEq.{0, 0} Complex Real (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) z) Complex.arg (fun (x : Complex) => Real.arccos (HDiv.hDiv.{0, 0, 0} Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.re x) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x))))
Case conversion may be inaccurate. Consider using '#align complex.arg_eq_nhds_of_im_pos Complex.arg_eq_nhds_of_im_posₓ'. -/
theorem arg_eq_nhds_of_im_pos (hz : 0 < im z) : arg =ᶠ[𝓝 z] fun x => Real.arccos (x.re / abs x) :=
  ((continuous_im.Tendsto _).Eventually (lt_mem_nhds hz)).mono fun x => arg_of_im_pos
#align complex.arg_eq_nhds_of_im_pos Complex.arg_eq_nhds_of_im_pos

/- warning: complex.arg_eq_nhds_of_im_neg -> Complex.arg_eq_nhds_of_im_neg is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, (LT.lt.{0} Real Real.hasLt (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.EventuallyEq.{0, 0} Complex Real (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) z) Complex.arg (fun (x : Complex) => Neg.neg.{0} Real Real.hasNeg (Real.arccos (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Complex.re x) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs x)))))
but is expected to have type
  forall {z : Complex}, (LT.lt.{0} Real Real.instLTReal (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.EventuallyEq.{0, 0} Complex Real (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) z) Complex.arg (fun (x : Complex) => Neg.neg.{0} Real Real.instNegReal (Real.arccos (HDiv.hDiv.{0, 0, 0} Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) x) Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Complex.re x) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs x)))))
Case conversion may be inaccurate. Consider using '#align complex.arg_eq_nhds_of_im_neg Complex.arg_eq_nhds_of_im_negₓ'. -/
theorem arg_eq_nhds_of_im_neg (hz : im z < 0) : arg =ᶠ[𝓝 z] fun x => -Real.arccos (x.re / abs x) :=
  ((continuous_im.Tendsto _).Eventually (gt_mem_nhds hz)).mono fun x => arg_of_im_neg
#align complex.arg_eq_nhds_of_im_neg Complex.arg_eq_nhds_of_im_neg

/- warning: complex.continuous_at_arg -> Complex.continuousAt_arg is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re x)) (Ne.{1} Real (Complex.im x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (ContinuousAt.{0, 0} Complex Real (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Complex.arg x)
but is expected to have type
  forall {x : Complex}, (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re x)) (Ne.{1} Real (Complex.im x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (ContinuousAt.{0, 0} Complex Real (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Complex.arg x)
Case conversion may be inaccurate. Consider using '#align complex.continuous_at_arg Complex.continuousAt_argₓ'. -/
theorem continuousAt_arg (h : 0 < x.re ∨ x.im ≠ 0) : ContinuousAt arg x :=
  by
  have h₀ : abs x ≠ 0 := by
    rw [abs.ne_zero_iff]
    rintro rfl
    simpa using h
  rw [← lt_or_lt_iff_ne] at h
  rcases h with (hx_re | hx_im | hx_im)
  exacts[(real.continuous_at_arcsin.comp
          (continuous_im.continuous_at.div continuous_abs.continuous_at h₀)).congr
      (arg_eq_nhds_of_re_pos hx_re).symm,
    (real.continuous_arccos.continuous_at.comp
            (continuous_re.continuous_at.div continuous_abs.continuous_at h₀)).neg.congr
      (arg_eq_nhds_of_im_neg hx_im).symm,
    (real.continuous_arccos.continuous_at.comp
          (continuous_re.continuous_at.div continuous_abs.continuous_at h₀)).congr
      (arg_eq_nhds_of_im_pos hx_im).symm]
#align complex.continuous_at_arg Complex.continuousAt_arg

/- warning: complex.tendsto_arg_nhds_within_im_neg_of_re_neg_of_im_zero -> Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, (LT.lt.{0} Real Real.hasLt (Complex.re z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Tendsto.{0, 0} Complex Real Complex.arg (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) z (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Neg.neg.{0} Real Real.hasNeg Real.pi)))
but is expected to have type
  forall {z : Complex}, (LT.lt.{0} Real Real.instLTReal (Complex.re z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Tendsto.{0, 0} Complex Real Complex.arg (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) z (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Neg.neg.{0} Real Real.instNegReal Real.pi)))
Case conversion may be inaccurate. Consider using '#align complex.tendsto_arg_nhds_within_im_neg_of_re_neg_of_im_zero Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zeroₓ'. -/
theorem tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto arg (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 (-π)) :=
  by
  suffices H :
    tendsto (fun x : ℂ => Real.arcsin ((-x).im / x.abs) - π) (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 (-π))
  · refine' H.congr' _
    have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds this]with _ him hre
    rw [arg, if_neg hre.not_le, if_neg him.not_le]
  convert(real.continuous_at_arcsin.comp_continuous_within_at
          ((continuous_im.continuous_at.comp_continuous_within_at continuousWithinAt_neg).div
            continuous_abs.continuous_within_at _)).sub
      tendsto_const_nhds
  · simp [him]
  · lift z to ℝ using him
    simpa using hre.ne
#align complex.tendsto_arg_nhds_within_im_neg_of_re_neg_of_im_zero Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero

/- warning: complex.continuous_within_at_arg_of_re_neg_of_im_zero -> Complex.continuousWithinAt_arg_of_re_neg_of_im_zero is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, (LT.lt.{0} Real Real.hasLt (Complex.re z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (ContinuousWithinAt.{0, 0} Complex Real (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Complex.arg (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im z))) z)
but is expected to have type
  forall {z : Complex}, (LT.lt.{0} Real Real.instLTReal (Complex.re z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (ContinuousWithinAt.{0, 0} Complex Real (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Complex.arg (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im z))) z)
Case conversion may be inaccurate. Consider using '#align complex.continuous_within_at_arg_of_re_neg_of_im_zero Complex.continuousWithinAt_arg_of_re_neg_of_im_zeroₓ'. -/
theorem continuousWithinAt_arg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    ContinuousWithinAt arg { z : ℂ | 0 ≤ z.im } z :=
  by
  have : arg =ᶠ[𝓝[{ z : ℂ | 0 ≤ z.im }] z] fun x => Real.arcsin ((-x).im / x.abs) + π :=
    by
    have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds this]with _ him hre
    rw [arg, if_neg hre.not_le, if_pos him]
  refine' ContinuousWithinAt.congr_of_eventuallyEq _ this _
  · refine'
      (real.continuous_at_arcsin.comp_continuous_within_at
            ((continuous_im.continuous_at.comp_continuous_within_at continuousWithinAt_neg).div
              continuous_abs.continuous_within_at _)).add
        tendsto_const_nhds
    lift z to ℝ using him
    simpa using hre.ne
  · rw [arg, if_neg hre.not_le, if_pos him.ge]
#align complex.continuous_within_at_arg_of_re_neg_of_im_zero Complex.continuousWithinAt_arg_of_re_neg_of_im_zero

/- warning: complex.tendsto_arg_nhds_within_im_nonneg_of_re_neg_of_im_zero -> Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, (LT.lt.{0} Real Real.hasLt (Complex.re z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Tendsto.{0, 0} Complex Real Complex.arg (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) z (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.im z)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.pi))
but is expected to have type
  forall {z : Complex}, (LT.lt.{0} Real Real.instLTReal (Complex.re z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Tendsto.{0, 0} Complex Real Complex.arg (nhdsWithin.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) z (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.im z)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.pi))
Case conversion may be inaccurate. Consider using '#align complex.tendsto_arg_nhds_within_im_nonneg_of_re_neg_of_im_zero Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zeroₓ'. -/
theorem tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto arg (𝓝[{ z : ℂ | 0 ≤ z.im }] z) (𝓝 π) := by
  simpa only [arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuous_within_at_arg_of_re_neg_of_im_zero hre him).Tendsto
#align complex.tendsto_arg_nhds_within_im_nonneg_of_re_neg_of_im_zero Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero

/- warning: complex.continuous_at_arg_coe_angle -> Complex.continuousAt_arg_coe_angle is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (ContinuousAt.{0, 0} Complex Real.Angle (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Real.Angle (PseudoMetricSpace.toUniformSpace.{0} Real.Angle (SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real.Angle (NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real.Angle Real.Angle.normedAddCommGroup)))) (Function.comp.{1, 1, 1} Complex Real Real.Angle ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Real.Angle (HasLiftT.mk.{1, 1} Real Real.Angle (CoeTCₓ.coe.{1, 1} Real Real.Angle Real.Angle.hasCoeT))) Complex.arg) x)
but is expected to have type
  forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (ContinuousAt.{0, 0} Complex Real.Angle (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Real.Angle (PseudoMetricSpace.toUniformSpace.{0} Real.Angle (SeminormedAddCommGroup.toPseudoMetricSpace.{0} Real.Angle (NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real.Angle Real.Angle.instNormedAddCommGroupAngle)))) (Function.comp.{1, 1, 1} Complex Real Real.Angle Real.Angle.coe Complex.arg) x)
Case conversion may be inaccurate. Consider using '#align complex.continuous_at_arg_coe_angle Complex.continuousAt_arg_coe_angleₓ'. -/
theorem continuousAt_arg_coe_angle (h : x ≠ 0) : ContinuousAt (coe ∘ arg : ℂ → Real.Angle) x :=
  by
  by_cases hs : 0 < x.re ∨ x.im ≠ 0
  · exact real.angle.continuous_coe.continuous_at.comp (continuous_at_arg hs)
  · rw [← Function.comp.right_id (coe ∘ arg),
      (Function.funext_iff.2 fun _ => (neg_neg _).symm : (id : ℂ → ℂ) = Neg.neg ∘ Neg.neg), ←
      Function.comp.assoc]
    refine' ContinuousAt.comp _ continuous_neg.continuous_at
    suffices ContinuousAt (Function.update ((coe ∘ arg) ∘ Neg.neg : ℂ → Real.Angle) 0 π) (-x) by
      rwa [continuousAt_update_of_ne (neg_ne_zero.2 h)] at this
    have ha :
      Function.update ((coe ∘ arg) ∘ Neg.neg : ℂ → Real.Angle) 0 π = fun z =>
        (arg z : Real.Angle) + π :=
      by
      rw [Function.update_eq_iff]
      exact ⟨by simp, fun z hz => arg_neg_coe_angle hz⟩
    rw [ha]
    push_neg  at hs
    refine'
      (real.angle.continuous_coe.continuous_at.comp (continuous_at_arg (Or.inl _))).add
        continuousAt_const
    rw [neg_re, neg_pos]
    exact hs.1.lt_of_ne fun h0 => h (ext_iff.2 ⟨h0, hs.2⟩)
#align complex.continuous_at_arg_coe_angle Complex.continuousAt_arg_coe_angle

end Continuity

end Complex

