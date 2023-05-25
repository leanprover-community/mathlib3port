/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler

! This file was ported from Lean 3 source module analysis.special_functions.pow.asymptotics
! leanprover-community/mathlib commit 0b9eaaa7686280fad8cce467f5c3c57ee6ce77f8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Pow.Nnreal

/-!
# Limits and asymptotics of power functions at `+∞`

This file contains results about the limiting behaviour of power functions at `+∞`. For convenience
some results on asymptotics as `x → 0` (those which are not just continuity statements) are also
located here.
-/


noncomputable section

open Classical Real Topology NNReal ENNReal Filter BigOperators ComplexConjugate

open Filter Finset Set

/-!
## Limits at `+∞`
-/


section Limits

open Real Filter

/- warning: tendsto_rpow_at_top -> tendsto_rpow_atTop is a dubious translation:
lean 3 declaration is
  forall {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y) (Filter.atTop.{0} Real Real.preorder) (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  forall {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y) (Filter.atTop.{0} Real Real.instPreorderReal) (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align tendsto_rpow_at_top tendsto_rpow_atTopₓ'. -/
/-- The function `x ^ y` tends to `+∞` at `+∞` for any positive real `y`. -/
theorem tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) : Tendsto (fun x : ℝ => x ^ y) atTop atTop :=
  by
  rw [tendsto_at_top_at_top]
  intro b
  use max b 0 ^ (1 / y)
  intro x hx
  exact
    le_of_max_le_left
      (by
        convert rpow_le_rpow (rpow_nonneg_of_nonneg (le_max_right b 0) (1 / y)) hx (le_of_lt hy)
        rw [← rpow_mul (le_max_right b 0), (eq_div_iff (ne_of_gt hy)).mp rfl, rpow_one])
#align tendsto_rpow_at_top tendsto_rpow_atTop

/- warning: tendsto_rpow_neg_at_top -> tendsto_rpow_neg_atTop is a dubious translation:
lean 3 declaration is
  forall {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (Neg.neg.{0} Real Real.hasNeg y)) (Filter.atTop.{0} Real Real.preorder) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (Neg.neg.{0} Real Real.instNegReal y)) (Filter.atTop.{0} Real Real.instPreorderReal) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_rpow_neg_at_top tendsto_rpow_neg_atTopₓ'. -/
/-- The function `x ^ (-y)` tends to `0` at `+∞` for any positive real `y`. -/
theorem tendsto_rpow_neg_atTop {y : ℝ} (hy : 0 < y) : Tendsto (fun x : ℝ => x ^ (-y)) atTop (𝓝 0) :=
  Tendsto.congr' (eventuallyEq_of_mem (Ioi_mem_atTop 0) fun x hx => (rpow_neg (le_of_lt hx) y).symm)
    (tendsto_rpow_atTop hy).inv_tendsto_atTop
#align tendsto_rpow_neg_at_top tendsto_rpow_neg_atTop

/- warning: tendsto_rpow_div_mul_add -> tendsto_rpow_div_mul_add is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real) (c : Real), (Ne.{1} Real (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) a (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) b x) c))) (Filter.atTop.{0} Real Real.preorder) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall (a : Real) (b : Real) (c : Real), (Ne.{1} Real (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) a (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) b x) c))) (Filter.atTop.{0} Real Real.instPreorderReal) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_rpow_div_mul_add tendsto_rpow_div_mul_addₓ'. -/
/-- The function `x ^ (a / (b * x + c))` tends to `1` at `+∞`, for any real numbers `a`, `b`, and
`c` such that `b` is nonzero. -/
theorem tendsto_rpow_div_mul_add (a b c : ℝ) (hb : 0 ≠ b) :
    Tendsto (fun x => x ^ (a / (b * x + c))) atTop (𝓝 1) :=
  by
  refine'
    tendsto.congr' _
      ((tendsto_exp_nhds_0_nhds_1.comp
            (by
              simpa only [MulZeroClass.mul_zero, pow_one] using
                (@tendsto_const_nhds _ _ _ a _).mul
                  (tendsto_div_pow_mul_exp_add_at_top b c 1 hb))).comp
        tendsto_log_at_top)
  apply eventually_eq_of_mem (Ioi_mem_at_top (0 : ℝ))
  intro x hx
  simp only [Set.mem_Ioi, Function.comp_apply] at hx⊢
  rw [exp_log hx, ← exp_log (rpow_pos_of_pos hx (a / (b * x + c))), log_rpow hx (a / (b * x + c))]
  field_simp
#align tendsto_rpow_div_mul_add tendsto_rpow_div_mul_add

/- warning: tendsto_rpow_div -> tendsto_rpow_div is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x)) (Filter.atTop.{0} Real Real.preorder) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x)) (Filter.atTop.{0} Real Real.instPreorderReal) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align tendsto_rpow_div tendsto_rpow_divₓ'. -/
/-- The function `x ^ (1 / x)` tends to `1` at `+∞`. -/
theorem tendsto_rpow_div : Tendsto (fun x => x ^ ((1 : ℝ) / x)) atTop (𝓝 1) :=
  by
  convert tendsto_rpow_div_mul_add (1 : ℝ) _ (0 : ℝ) zero_ne_one
  funext
  congr 2
  ring
#align tendsto_rpow_div tendsto_rpow_div

/- warning: tendsto_rpow_neg_div -> tendsto_rpow_neg_div is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) x)) (Filter.atTop.{0} Real Real.preorder) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x)) (Filter.atTop.{0} Real Real.instPreorderReal) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align tendsto_rpow_neg_div tendsto_rpow_neg_divₓ'. -/
/-- The function `x ^ (-1 / x)` tends to `1` at `+∞`. -/
theorem tendsto_rpow_neg_div : Tendsto (fun x => x ^ (-(1 : ℝ) / x)) atTop (𝓝 1) :=
  by
  convert tendsto_rpow_div_mul_add (-(1 : ℝ)) _ (0 : ℝ) zero_ne_one
  funext
  congr 2
  ring
#align tendsto_rpow_neg_div tendsto_rpow_neg_div

/- warning: tendsto_exp_div_rpow_at_top -> tendsto_exp_div_rpow_atTop is a dubious translation:
lean 3 declaration is
  forall (s : Real), Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.exp x) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x s)) (Filter.atTop.{0} Real Real.preorder) (Filter.atTop.{0} Real Real.preorder)
but is expected to have type
  forall (s : Real), Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.exp x) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x s)) (Filter.atTop.{0} Real Real.instPreorderReal) (Filter.atTop.{0} Real Real.instPreorderReal)
Case conversion may be inaccurate. Consider using '#align tendsto_exp_div_rpow_at_top tendsto_exp_div_rpow_atTopₓ'. -/
/-- The function `exp(x) / x ^ s` tends to `+∞` at `+∞`, for any real number `s`. -/
theorem tendsto_exp_div_rpow_atTop (s : ℝ) : Tendsto (fun x : ℝ => exp x / x ^ s) atTop atTop :=
  by
  cases' archimedean_iff_nat_lt.1 Real.instArchimedean s with n hn
  refine' tendsto_at_top_mono' _ _ (tendsto_exp_div_pow_at_top n)
  filter_upwards [eventually_gt_at_top (0 : ℝ), eventually_ge_at_top (1 : ℝ)]with x hx₀ hx₁
  rw [div_le_div_left (exp_pos _) (pow_pos hx₀ _) (rpow_pos_of_pos hx₀ _), ← rpow_nat_cast]
  exact rpow_le_rpow_of_exponent_le hx₁ hn.le
#align tendsto_exp_div_rpow_at_top tendsto_exp_div_rpow_atTop

/- warning: tendsto_exp_mul_div_rpow_at_top -> tendsto_exp_mul_div_rpow_atTop is a dubious translation:
lean 3 declaration is
  forall (s : Real) (b : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) b x)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x s)) (Filter.atTop.{0} Real Real.preorder) (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  forall (s : Real) (b : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) b x)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x s)) (Filter.atTop.{0} Real Real.instPreorderReal) (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align tendsto_exp_mul_div_rpow_at_top tendsto_exp_mul_div_rpow_atTopₓ'. -/
/-- The function `exp (b * x) / x ^ s` tends to `+∞` at `+∞`, for any real `s` and `b > 0`. -/
theorem tendsto_exp_mul_div_rpow_atTop (s : ℝ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => exp (b * x) / x ^ s) atTop atTop :=
  by
  refine' ((tendsto_rpow_atTop hb).comp (tendsto_exp_div_rpow_atTop (s / b))).congr' _
  filter_upwards [eventually_ge_at_top (0 : ℝ)]with x hx₀
  simp [div_rpow, (exp_pos x).le, rpow_nonneg_of_nonneg, ← rpow_mul, ← exp_mul, mul_comm x, hb.ne',
    *]
#align tendsto_exp_mul_div_rpow_at_top tendsto_exp_mul_div_rpow_atTop

/- warning: tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0 -> tendsto_rpow_mul_exp_neg_mul_atTop_nhds_0 is a dubious translation:
lean 3 declaration is
  forall (s : Real) (b : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x s) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Neg.neg.{0} Real Real.hasNeg b) x))) (Filter.atTop.{0} Real Real.preorder) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall (s : Real) (b : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x s) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Neg.neg.{0} Real Real.instNegReal b) x))) (Filter.atTop.{0} Real Real.instPreorderReal) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0 tendsto_rpow_mul_exp_neg_mul_atTop_nhds_0ₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:38: in filter_upwards #[[], ["with", ident x],
  ["using", expr by simp [] [] [] ["[", expr exp_neg, ",", expr inv_div, ",", expr div_eq_mul_inv _
    (exp _), "]"] [] []]]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error @ arg 0: next failed, no more args -/
/-- The function `x ^ s * exp (-b * x)` tends to `0` at `+∞`, for any real `s` and `b > 0`. -/
theorem tendsto_rpow_mul_exp_neg_mul_atTop_nhds_0 (s : ℝ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ s * exp (-b * x)) atTop (𝓝 0) :=
  by
  refine' (tendsto_exp_mul_div_rpow_atTop s b hb).inv_tendsto_atTop.congr' _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:38: in filter_upwards #[[], [\"with\", ident x],\n  [\"using\", expr by simp [] [] [] [\"[\", expr exp_neg, \",\", expr inv_div, \",\", expr div_eq_mul_inv _\n    (exp _), \"]\"] [] []]]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error @ arg 0: next failed, no more args"
#align tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0 tendsto_rpow_mul_exp_neg_mul_atTop_nhds_0

/- warning: nnreal.tendsto_rpow_at_top -> NNReal.tendsto_rpow_atTop is a dubious translation:
lean 3 declaration is
  forall {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Filter.Tendsto.{0, 0} NNReal NNReal (fun (x : NNReal) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y) (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))
but is expected to have type
  forall {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Filter.Tendsto.{0, 0} NNReal Real (fun (x : NNReal) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (NNReal.toReal x) y) (Filter.atTop.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align nnreal.tendsto_rpow_at_top NNReal.tendsto_rpow_atTopₓ'. -/
theorem NNReal.tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ≥0 => x ^ y) atTop atTop :=
  by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨c, hc⟩ := tendsto_at_top_at_top.mp (tendsto_rpow_atTop hy) b
  use c.to_nnreal
  intro a ha
  exact_mod_cast hc a (real.to_nnreal_le_iff_le_coe.mp ha)
#align nnreal.tendsto_rpow_at_top NNReal.tendsto_rpow_atTop

/- warning: ennreal.tendsto_rpow_at_top -> ENNReal.tendsto_rpow_at_top is a dubious translation:
lean 3 declaration is
  forall {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Filter.Tendsto.{0, 0} ENNReal ENNReal (fun (x : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y) (nhds.{0} ENNReal ENNReal.topologicalSpace (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (nhds.{0} ENNReal ENNReal.topologicalSpace (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Filter.Tendsto.{0, 0} ENNReal ENNReal (fun (x : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_rpow_at_top ENNReal.tendsto_rpow_at_topₓ'. -/
theorem ENNReal.tendsto_rpow_at_top {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ≥0∞ => x ^ y) (𝓝 ⊤) (𝓝 ⊤) :=
  by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro x
  obtain ⟨c, _, hc⟩ :=
    (at_top_basis_Ioi.tendsto_iff at_top_basis_Ioi).mp (NNReal.tendsto_rpow_atTop hy) x trivial
  have hc' : Set.Ioi ↑c ∈ 𝓝 (⊤ : ℝ≥0∞) := Ioi_mem_nhds ENNReal.coe_lt_top
  refine' eventually_of_mem hc' _
  intro a ha
  by_cases ha' : a = ⊤
  · simp [ha', hy]
  lift a to ℝ≥0 using ha'
  change ↑c < ↑a at ha
  rw [ENNReal.coe_rpow_of_nonneg _ hy.le]
  exact_mod_cast hc a (by exact_mod_cast ha)
#align ennreal.tendsto_rpow_at_top ENNReal.tendsto_rpow_at_top

end Limits

/-!
## Asymptotic results: `is_O`, `is_o` and `is_Theta`
-/


namespace Complex

section

variable {α : Type _} {l : Filter α} {f g : α → ℂ}

open Asymptotics

/- warning: complex.is_Theta_exp_arg_mul_im -> Complex.isTheta_exp_arg_mul_im is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {g : α -> Complex}, (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Complex.im (g x)))) -> (Asymptotics.IsTheta.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Complex.arg (f x)) (Complex.im (g x)))) (fun (x : α) => OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {g : α -> Complex}, (Filter.IsBoundedUnder.{0, u1} Real α (fun (x._@.Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics._hyg.1401 : Real) (x._@.Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics._hyg.1403 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics._hyg.1401 x._@.Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics._hyg.1403) l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Complex.im (g x)))) -> (Asymptotics.IsTheta.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Complex.arg (f x)) (Complex.im (g x)))) (fun (x : α) => OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align complex.is_Theta_exp_arg_mul_im Complex.isTheta_exp_arg_mul_imₓ'. -/
theorem isTheta_exp_arg_mul_im (hl : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|) :
    (fun x => Real.exp (arg (f x) * im (g x))) =Θ[l] fun x => (1 : ℝ) :=
  by
  rcases hl with ⟨b, hb⟩
  refine' Real.isTheta_exp_comp_one.2 ⟨π * b, _⟩
  rw [eventually_map] at hb⊢
  refine' hb.mono fun x hx => _
  erw [abs_mul]
  exact mul_le_mul (abs_arg_le_pi _) hx (abs_nonneg _) real.pi_pos.le
#align complex.is_Theta_exp_arg_mul_im Complex.isTheta_exp_arg_mul_im

/- warning: complex.is_O_cpow_rpow -> Complex.isBigO_cpow_rpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {g : α -> Complex}, (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Complex.im (g x)))) -> (Asymptotics.IsBigO.{u1, 0, 0} α Complex Real Complex.hasNorm Real.hasNorm l (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (f x) (g x)) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (f x)) (Complex.re (g x))))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {g : α -> Complex}, (Filter.IsBoundedUnder.{0, u1} Real α (fun (x._@.Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics._hyg.1582 : Real) (x._@.Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics._hyg.1584 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics._hyg.1582 x._@.Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics._hyg.1584) l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Complex.im (g x)))) -> (Asymptotics.IsBigO.{u1, 0, 0} α Complex Real Complex.instNormComplex Real.norm l (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (f x) (g x)) (fun (x : α) => HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (f x)) Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (f x)) (instHPow.{0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (f x)) Real Real.instPowReal) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs (f x)) (Complex.re (g x))))
Case conversion may be inaccurate. Consider using '#align complex.is_O_cpow_rpow Complex.isBigO_cpow_rpowₓ'. -/
theorem isBigO_cpow_rpow (hl : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|) :
    (fun x => f x ^ g x) =O[l] fun x => abs (f x) ^ (g x).re :=
  calc
    (fun x => f x ^ g x) =O[l] fun x => abs (f x) ^ (g x).re / Real.exp (arg (f x) * im (g x)) :=
      isBigO_of_le _ fun x => (abs_cpow_le _ _).trans (le_abs_self _)
    _ =Θ[l] fun x => abs (f x) ^ (g x).re / (1 : ℝ) :=
      ((isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl))
    _ =ᶠ[l] fun x => abs (f x) ^ (g x).re := by simp only [of_real_one, div_one]
    
#align complex.is_O_cpow_rpow Complex.isBigO_cpow_rpow

/- warning: complex.is_Theta_cpow_rpow -> Complex.isTheta_cpow_rpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {g : α -> Complex}, (Filter.IsBoundedUnder.{0, u1} Real α (LE.le.{0} Real Real.hasLe) l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Complex.im (g x)))) -> (Filter.Eventually.{u1} α (fun (x : α) => (Eq.{1} Complex (f x) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Real (Complex.re (g x)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Complex (g x) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))))) l) -> (Asymptotics.IsTheta.{u1, 0, 0} α Complex Real Complex.hasNorm Real.hasNorm l (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (f x) (g x)) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (f x)) (Complex.re (g x))))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {g : α -> Complex}, (Filter.IsBoundedUnder.{0, u1} Real α (fun (x._@.Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics._hyg.1857 : Real) (x._@.Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics._hyg.1859 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics._hyg.1857 x._@.Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics._hyg.1859) l (fun (x : α) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Complex.im (g x)))) -> (Filter.Eventually.{u1} α (fun (x : α) => (Eq.{1} Complex (f x) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Real (Complex.re (g x)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Complex (g x) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)))) l) -> (Asymptotics.IsTheta.{u1, 0, 0} α Complex Real Complex.instNormComplex Real.norm l (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (f x) (g x)) (fun (x : α) => HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (f x)) Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (f x)) (instHPow.{0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (f x)) Real Real.instPowReal) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs (f x)) (Complex.re (g x))))
Case conversion may be inaccurate. Consider using '#align complex.is_Theta_cpow_rpow Complex.isTheta_cpow_rpowₓ'. -/
theorem isTheta_cpow_rpow (hl_im : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|)
    (hl : ∀ᶠ x in l, f x = 0 → re (g x) = 0 → g x = 0) :
    (fun x => f x ^ g x) =Θ[l] fun x => abs (f x) ^ (g x).re :=
  calc
    (fun x => f x ^ g x) =Θ[l] fun x => abs (f x) ^ (g x).re / Real.exp (arg (f x) * im (g x)) :=
      isTheta_of_norm_eventuallyEq' <| hl.mono fun x => abs_cpow_of_imp
    _ =Θ[l] fun x => abs (f x) ^ (g x).re / (1 : ℝ) :=
      ((isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl_im))
    _ =ᶠ[l] fun x => abs (f x) ^ (g x).re := by simp only [of_real_one, div_one]
    
#align complex.is_Theta_cpow_rpow Complex.isTheta_cpow_rpow

/- warning: complex.is_Theta_cpow_const_rpow -> Complex.isTheta_cpow_const_rpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {b : Complex}, ((Eq.{1} Real (Complex.re b) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Filter.Eventually.{u1} α (fun (x : α) => Ne.{1} Complex (f x) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) l)) -> (Asymptotics.IsTheta.{u1, 0, 0} α Complex Real Complex.hasNorm Real.hasNorm l (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (f x) b) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (f x)) (Complex.re b)))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {b : Complex}, ((Eq.{1} Real (Complex.re b) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Filter.Eventually.{u1} α (fun (x : α) => Ne.{1} Complex (f x) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) l)) -> (Asymptotics.IsTheta.{u1, 0, 0} α Complex Real Complex.instNormComplex Real.norm l (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (f x) b) (fun (x : α) => HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (f x)) Real ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (f x)) (instHPow.{0, 0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (f x)) Real Real.instPowReal) (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs (f x)) (Complex.re b)))
Case conversion may be inaccurate. Consider using '#align complex.is_Theta_cpow_const_rpow Complex.isTheta_cpow_const_rpowₓ'. -/
theorem isTheta_cpow_const_rpow {b : ℂ} (hl : b.re = 0 → b ≠ 0 → ∀ᶠ x in l, f x ≠ 0) :
    (fun x => f x ^ b) =Θ[l] fun x => abs (f x) ^ b.re :=
  isTheta_cpow_rpow isBoundedUnder_const <| by
    simpa only [eventually_imp_distrib_right, Ne.def, ← not_frequently, not_imp_not, Imp.swap] using
      hl
#align complex.is_Theta_cpow_const_rpow Complex.isTheta_cpow_const_rpow

end

end Complex

open Real

namespace Asymptotics

variable {α : Type _} {r c : ℝ} {l : Filter α} {f g : α → ℝ}

/- warning: asymptotics.is_O_with.rpow -> Asymptotics.IsBigOWith.rpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : Real} {c : Real} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real}, (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm c l f g) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Filter.EventuallyLE.{u1, 0} α Real Real.hasLe l (OfNat.ofNat.{u1} (α -> Real) 0 (OfNat.mk.{u1} (α -> Real) 0 (Zero.zero.{u1} (α -> Real) (Pi.instZero.{u1, 0} α (fun (ᾰ : α) => Real) (fun (i : α) => Real.hasZero))))) g) -> (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) c r) l (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (f x) r) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (g x) r))
but is expected to have type
  forall {α : Type.{u1}} {r : Real} {c : Real} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real}, (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.norm Real.norm c l f g) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Filter.EventuallyLE.{u1, 0} α Real Real.instLEReal l (OfNat.ofNat.{u1} (α -> Real) 0 (Zero.toOfNat0.{u1} (α -> Real) (Pi.instZero.{u1, 0} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.21854 : α) => Real) (fun (i : α) => Real.instZeroReal)))) g) -> (Asymptotics.IsBigOWith.{u1, 0, 0} α Real Real Real.norm Real.norm (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) c r) l (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (f x) r) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (g x) r))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O_with.rpow Asymptotics.IsBigOWith.rpowₓ'. -/
theorem IsBigOWith.rpow (h : IsBigOWith c l f g) (hc : 0 ≤ c) (hr : 0 ≤ r) (hg : 0 ≤ᶠ[l] g) :
    IsBigOWith (c ^ r) l (fun x => f x ^ r) fun x => g x ^ r :=
  by
  apply is_O_with.of_bound
  filter_upwards [hg, h.bound]with x hgx hx
  calc
    |f x ^ r| ≤ |f x| ^ r := abs_rpow_le_abs_rpow _ _
    _ ≤ (c * |g x|) ^ r := (rpow_le_rpow (abs_nonneg _) hx hr)
    _ = c ^ r * |g x ^ r| := by rw [mul_rpow hc (abs_nonneg _), abs_rpow_of_nonneg hgx]
    
#align asymptotics.is_O_with.rpow Asymptotics.IsBigOWith.rpow

/- warning: asymptotics.is_O.rpow -> Asymptotics.IsBigO.rpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : Real} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Filter.EventuallyLE.{u1, 0} α Real Real.hasLe l (OfNat.ofNat.{u1} (α -> Real) 0 (OfNat.mk.{u1} (α -> Real) 0 (Zero.zero.{u1} (α -> Real) (Pi.instZero.{u1, 0} α (fun (ᾰ : α) => Real) (fun (i : α) => Real.hasZero))))) g) -> (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l f g) -> (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (f x) r) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (g x) r))
but is expected to have type
  forall {α : Type.{u1}} {r : Real} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Filter.EventuallyLE.{u1, 0} α Real Real.instLEReal l (OfNat.ofNat.{u1} (α -> Real) 0 (Zero.toOfNat0.{u1} (α -> Real) (Pi.instZero.{u1, 0} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.21854 : α) => Real) (fun (i : α) => Real.instZeroReal)))) g) -> (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.norm Real.norm l f g) -> (Asymptotics.IsBigO.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (f x) r) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (g x) r))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_O.rpow Asymptotics.IsBigO.rpowₓ'. -/
theorem IsBigO.rpow (hr : 0 ≤ r) (hg : 0 ≤ᶠ[l] g) (h : f =O[l] g) :
    (fun x => f x ^ r) =O[l] fun x => g x ^ r :=
  let ⟨c, hc, h'⟩ := h.exists_nonneg
  (h'.rpow hc hr hg).IsBigO
#align asymptotics.is_O.rpow Asymptotics.IsBigO.rpow

/- warning: asymptotics.is_o.rpow -> Asymptotics.IsLittleO.rpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : Real} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Filter.EventuallyLE.{u1, 0} α Real Real.hasLe l (OfNat.ofNat.{u1} (α -> Real) 0 (OfNat.mk.{u1} (α -> Real) 0 (Zero.zero.{u1} (α -> Real) (Pi.instZero.{u1, 0} α (fun (ᾰ : α) => Real) (fun (i : α) => Real.hasZero))))) g) -> (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l f g) -> (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.hasNorm Real.hasNorm l (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (f x) r) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (g x) r))
but is expected to have type
  forall {α : Type.{u1}} {r : Real} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Filter.EventuallyLE.{u1, 0} α Real Real.instLEReal l (OfNat.ofNat.{u1} (α -> Real) 0 (Zero.toOfNat0.{u1} (α -> Real) (Pi.instZero.{u1, 0} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.21854 : α) => Real) (fun (i : α) => Real.instZeroReal)))) g) -> (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.norm Real.norm l f g) -> (Asymptotics.IsLittleO.{u1, 0, 0} α Real Real Real.norm Real.norm l (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (f x) r) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (g x) r))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.rpow Asymptotics.IsLittleO.rpowₓ'. -/
theorem IsLittleO.rpow (hr : 0 < r) (hg : 0 ≤ᶠ[l] g) (h : f =o[l] g) :
    (fun x => f x ^ r) =o[l] fun x => g x ^ r :=
  IsLittleO.of_isBigOWith fun c hc =>
    ((h.forall_isBigOWith (rpow_pos_of_pos hc r⁻¹)).rpow (rpow_nonneg_of_nonneg hc.le _) hr.le
          hg).congr_const
      (by rw [← rpow_mul hc.le, inv_mul_cancel hr.ne', rpow_one])
#align asymptotics.is_o.rpow Asymptotics.IsLittleO.rpow

end Asymptotics

open Asymptotics

/- warning: is_o_rpow_exp_pos_mul_at_top -> isLittleO_rpow_exp_pos_mul_atTop is a dubious translation:
lean 3 declaration is
  forall (s : Real) {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Real Real.preorder) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x s) (fun (x : Real) => Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) b x)))
but is expected to have type
  forall (s : Real) {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm (Filter.atTop.{0} Real Real.instPreorderReal) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x s) (fun (x : Real) => Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) b x)))
Case conversion may be inaccurate. Consider using '#align is_o_rpow_exp_pos_mul_at_top isLittleO_rpow_exp_pos_mul_atTopₓ'. -/
/-- `x ^ s = o(exp(b * x))` as `x → ∞` for any real `s` and positive `b`. -/
theorem isLittleO_rpow_exp_pos_mul_atTop (s : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ s) =o[atTop] fun x => exp (b * x) :=
  Iff.mpr (isLittleO_iff_tendsto fun x h => absurd h (exp_pos _).ne') <| by
    simpa only [div_eq_mul_inv, exp_neg, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_0 s b hb
#align is_o_rpow_exp_pos_mul_at_top isLittleO_rpow_exp_pos_mul_atTop

/- warning: is_o_zpow_exp_pos_mul_at_top -> isLittleO_zpow_exp_pos_mul_atTop is a dubious translation:
lean 3 declaration is
  forall (k : Int) {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Real Real.preorder) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x k) (fun (x : Real) => Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) b x)))
but is expected to have type
  forall (k : Int) {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm (Filter.atTop.{0} Real Real.instPreorderReal) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (Int.cast.{0} Real Real.intCast k)) (fun (x : Real) => Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) b x)))
Case conversion may be inaccurate. Consider using '#align is_o_zpow_exp_pos_mul_at_top isLittleO_zpow_exp_pos_mul_atTopₓ'. -/
/-- `x ^ k = o(exp(b * x))` as `x → ∞` for any integer `k` and positive `b`. -/
theorem isLittleO_zpow_exp_pos_mul_atTop (k : ℤ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ k) =o[atTop] fun x => exp (b * x) := by
  simpa only [rpow_int_cast] using isLittleO_rpow_exp_pos_mul_atTop k hb
#align is_o_zpow_exp_pos_mul_at_top isLittleO_zpow_exp_pos_mul_atTop

/- warning: is_o_pow_exp_pos_mul_at_top -> isLittleO_pow_exp_pos_mul_atTop is a dubious translation:
lean 3 declaration is
  forall (k : Nat) {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Real Real.preorder) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x k) (fun (x : Real) => Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) b x)))
but is expected to have type
  forall (k : Nat) {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm (Filter.atTop.{0} Real Real.instPreorderReal) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x (Nat.cast.{0} Real Real.natCast k)) (fun (x : Real) => Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) b x)))
Case conversion may be inaccurate. Consider using '#align is_o_pow_exp_pos_mul_at_top isLittleO_pow_exp_pos_mul_atTopₓ'. -/
/-- `x ^ k = o(exp(b * x))` as `x → ∞` for any natural `k` and positive `b`. -/
theorem isLittleO_pow_exp_pos_mul_atTop (k : ℕ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ k) =o[atTop] fun x => exp (b * x) := by
  simpa using isLittleO_zpow_exp_pos_mul_atTop k hb
#align is_o_pow_exp_pos_mul_at_top isLittleO_pow_exp_pos_mul_atTop

/- warning: is_o_rpow_exp_at_top -> isLittleO_rpow_exp_atTop is a dubious translation:
lean 3 declaration is
  forall (s : Real), Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Real Real.preorder) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x s) Real.exp
but is expected to have type
  forall (s : Real), Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm (Filter.atTop.{0} Real Real.instPreorderReal) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x s) Real.exp
Case conversion may be inaccurate. Consider using '#align is_o_rpow_exp_at_top isLittleO_rpow_exp_atTopₓ'. -/
/-- `x ^ s = o(exp x)` as `x → ∞` for any real `s`. -/
theorem isLittleO_rpow_exp_atTop (s : ℝ) : (fun x : ℝ => x ^ s) =o[atTop] exp := by
  simpa only [one_mul] using isLittleO_rpow_exp_pos_mul_atTop s one_pos
#align is_o_rpow_exp_at_top isLittleO_rpow_exp_atTop

/- warning: is_o_exp_neg_mul_rpow_at_top -> isLittleO_exp_neg_mul_rpow_atTop is a dubious translation:
lean 3 declaration is
  forall {a : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) a) -> (forall (b : Real), Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Real Real.preorder) (fun (x : Real) => Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Neg.neg.{0} Real Real.hasNeg a) x)) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x b))
but is expected to have type
  forall {a : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) a) -> (forall (b : Real), Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm (Filter.atTop.{0} Real Real.instPreorderReal) (fun (x : Real) => Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Neg.neg.{0} Real Real.instNegReal a) x)) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x b))
Case conversion may be inaccurate. Consider using '#align is_o_exp_neg_mul_rpow_at_top isLittleO_exp_neg_mul_rpow_atTopₓ'. -/
/-- `exp (-a * x) = o(x ^ s)` as `x → ∞`, for any positive `a` and real `s`. -/
theorem isLittleO_exp_neg_mul_rpow_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IsLittleO atTop (fun x : ℝ => exp (-a * x)) fun x : ℝ => x ^ b :=
  by
  apply is_o_of_tendsto'
  · refine' (eventually_gt_at_top 0).mp (eventually_of_forall fun t ht h => _)
    rw [rpow_eq_zero_iff_of_nonneg ht.le] at h
    exact (ht.ne' h.1).elim
  · refine' (tendsto_exp_mul_div_rpow_atTop (-b) a ha).inv_tendsto_atTop.congr' _
    refine' (eventually_ge_at_top 0).mp (eventually_of_forall fun t ht => _)
    dsimp only
    rw [Pi.inv_apply, inv_div, ← inv_div_inv, neg_mul, Real.exp_neg, rpow_neg ht, inv_inv]
#align is_o_exp_neg_mul_rpow_at_top isLittleO_exp_neg_mul_rpow_atTop

/- warning: is_o_log_rpow_at_top -> isLittleO_log_rpow_atTop is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Real Real.preorder) Real.log (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x r))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm (Filter.atTop.{0} Real Real.instPreorderReal) Real.log (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x r))
Case conversion may be inaccurate. Consider using '#align is_o_log_rpow_at_top isLittleO_log_rpow_atTopₓ'. -/
theorem isLittleO_log_rpow_atTop {r : ℝ} (hr : 0 < r) : log =o[atTop] fun x => x ^ r :=
  calc
    log =O[atTop] fun x => r * log x := isBigO_self_const_mul _ hr.ne' _ _
    _ =ᶠ[atTop] fun x => log (x ^ r) :=
      ((eventually_gt_atTop 0).mono fun x hx => (log_rpow hx _).symm)
    _ =o[atTop] fun x => x ^ r := isLittleO_log_id_atTop.comp_tendsto (tendsto_rpow_atTop hr)
    
#align is_o_log_rpow_at_top isLittleO_log_rpow_atTop

/- warning: is_o_log_rpow_rpow_at_top -> isLittleO_log_rpow_rpow_atTop is a dubious translation:
lean 3 declaration is
  forall {s : Real} (r : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) s) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Real Real.preorder) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Real.log x) r) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x s))
but is expected to have type
  forall {s : Real} (r : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) s) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm (Filter.atTop.{0} Real Real.instPreorderReal) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Real.log x) r) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x s))
Case conversion may be inaccurate. Consider using '#align is_o_log_rpow_rpow_at_top isLittleO_log_rpow_rpow_atTopₓ'. -/
theorem isLittleO_log_rpow_rpow_atTop {s : ℝ} (r : ℝ) (hs : 0 < s) :
    (fun x => log x ^ r) =o[atTop] fun x => x ^ s :=
  let r' := max r 1
  have hr : 0 < r' := lt_max_iff.2 <| Or.inr one_pos
  have H : 0 < s / r' := div_pos hs hr
  calc
    (fun x => log x ^ r) =O[atTop] fun x => log x ^ r' :=
      IsBigO.of_bound 1 <|
        (tendsto_log_atTop.eventually_ge_atTop 1).mono fun x hx =>
          by
          have hx₀ : 0 ≤ log x := zero_le_one.trans hx
          simp [norm_eq_abs, abs_rpow_of_nonneg, abs_rpow_of_nonneg hx₀,
            rpow_le_rpow_of_exponent_le (hx.trans (le_abs_self _))]
    _ =o[atTop] fun x => (x ^ (s / r')) ^ r' :=
      ((isLittleO_log_rpow_atTop H).rpow hr <|
        (tendsto_rpow_atTop H).Eventually <| eventually_ge_atTop 0)
    _ =ᶠ[atTop] fun x => x ^ s :=
      (eventually_ge_atTop 0).mono fun x hx => by simp only [← rpow_mul hx, div_mul_cancel _ hr.ne']
    
#align is_o_log_rpow_rpow_at_top isLittleO_log_rpow_rpow_atTop

/- warning: is_o_abs_log_rpow_rpow_nhds_zero -> isLittleO_abs_log_rpow_rpow_nhds_zero is a dubious translation:
lean 3 declaration is
  forall {s : Real} (r : Real), (LT.lt.{0} Real Real.hasLt s (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.hasNorm Real.hasNorm (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Real.log x)) r) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x s))
but is expected to have type
  forall {s : Real} (r : Real), (LT.lt.{0} Real Real.instLTReal s (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Real.log x)) r) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x s))
Case conversion may be inaccurate. Consider using '#align is_o_abs_log_rpow_rpow_nhds_zero isLittleO_abs_log_rpow_rpow_nhds_zeroₓ'. -/
theorem isLittleO_abs_log_rpow_rpow_nhds_zero {s : ℝ} (r : ℝ) (hs : s < 0) :
    (fun x => |log x| ^ r) =o[𝓝[>] 0] fun x => x ^ s :=
  ((isLittleO_log_rpow_rpow_atTop r (neg_pos.2 hs)).comp_tendsto tendsto_inv_zero_atTop).congr'
    (mem_of_superset (Icc_mem_nhdsWithin_Ioi <| Set.left_mem_Ico.2 one_pos) fun x hx => by
      simp [abs_of_nonpos, log_nonpos hx.1 hx.2])
    (eventually_mem_nhdsWithin.mono fun x hx => by
      rw [Function.comp_apply, inv_rpow hx.out.le, rpow_neg hx.out.le, inv_inv])
#align is_o_abs_log_rpow_rpow_nhds_zero isLittleO_abs_log_rpow_rpow_nhds_zero

/- warning: is_o_log_rpow_nhds_zero -> isLittleO_log_rpow_nhds_zero is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.hasNorm Real.hasNorm (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real.log (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x r))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real.log (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x r))
Case conversion may be inaccurate. Consider using '#align is_o_log_rpow_nhds_zero isLittleO_log_rpow_nhds_zeroₓ'. -/
theorem isLittleO_log_rpow_nhds_zero {r : ℝ} (hr : r < 0) : log =o[𝓝[>] 0] fun x => x ^ r :=
  (isLittleO_abs_log_rpow_rpow_nhds_zero 1 hr).neg_left.congr'
    (mem_of_superset (Icc_mem_nhdsWithin_Ioi <| Set.left_mem_Ico.2 one_pos) fun x hx => by
      simp [abs_of_nonpos (log_nonpos hx.1 hx.2)])
    EventuallyEq.rfl
#align is_o_log_rpow_nhds_zero isLittleO_log_rpow_nhds_zero

/- warning: tendsto_log_div_rpow_nhds_zero -> tendsto_log_div_rpow_nhds_zero is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.log x) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x r)) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.log x) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x r)) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_log_div_rpow_nhds_zero tendsto_log_div_rpow_nhds_zeroₓ'. -/
theorem tendsto_log_div_rpow_nhds_zero {r : ℝ} (hr : r < 0) :
    Tendsto (fun x => log x / x ^ r) (𝓝[>] 0) (𝓝 0) :=
  (isLittleO_log_rpow_nhds_zero hr).tendsto_div_nhds_zero
#align tendsto_log_div_rpow_nhds_zero tendsto_log_div_rpow_nhds_zero

/- warning: tendsto_log_mul_rpow_nhds_zero -> tendsto_log_mul_rpow_nhds_zero is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.log x) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x r)) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.log x) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x r)) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_log_mul_rpow_nhds_zero tendsto_log_mul_rpow_nhds_zeroₓ'. -/
theorem tendsto_log_mul_rpow_nhds_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x => log x * x ^ r) (𝓝[>] 0) (𝓝 0) :=
  (tendsto_log_div_rpow_nhds_zero <| neg_lt_zero.2 hr).congr' <|
    eventually_mem_nhdsWithin.mono fun x hx => by rw [rpow_neg hx.out.le, div_inv_eq_mul]
#align tendsto_log_mul_rpow_nhds_zero tendsto_log_mul_rpow_nhds_zero

