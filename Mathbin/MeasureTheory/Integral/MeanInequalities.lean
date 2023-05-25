/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.integral.mean_inequalities
! leanprover-community/mathlib commit 13bf7613c96a9fd66a81b9020a82cad9a6ea1fcf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Integral.Lebesgue
import Mathbin.Analysis.MeanInequalities
import Mathbin.Analysis.MeanInequalitiesPow
import Mathbin.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Mean value inequalities for integrals

In this file we prove several inequalities on integrals, notably the Hölder inequality and
the Minkowski inequality. The versions for finite sums are in `analysis.mean_inequalities`.

## Main results

Hölder's inequality for the Lebesgue integral of `ℝ≥0∞` and `ℝ≥0` functions: we prove
`∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q` conjugate real exponents
and `α→(e)nnreal` functions in two cases,
* `ennreal.lintegral_mul_le_Lp_mul_Lq` : ℝ≥0∞ functions,
* `nnreal.lintegral_mul_le_Lp_mul_Lq`  : ℝ≥0 functions.

Minkowski's inequality for the Lebesgue integral of measurable functions with `ℝ≥0∞` values:
we prove `(∫ (f + g)^p ∂μ) ^ (1/p) ≤ (∫ f^p ∂μ) ^ (1/p) + (∫ g^p ∂μ) ^ (1/p)` for `1 ≤ p`.
-/


section Lintegral

/-!
### Hölder's inequality for the Lebesgue integral of ℝ≥0∞ and nnreal functions

We prove `∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q`
conjugate real exponents and `α→(e)nnreal` functions in several cases, the first two being useful
only to prove the more general results:
* `ennreal.lintegral_mul_le_one_of_lintegral_rpow_eq_one` : ℝ≥0∞ functions for which the
    integrals on the right are equal to 1,
* `ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top` : ℝ≥0∞ functions for which the
    integrals on the right are neither ⊤ nor 0,
* `ennreal.lintegral_mul_le_Lp_mul_Lq` : ℝ≥0∞ functions,
* `nnreal.lintegral_mul_le_Lp_mul_Lq`  : nnreal functions.
-/


noncomputable section

open Classical BigOperators NNReal ENNReal

open MeasureTheory

variable {α : Type _} [MeasurableSpace α] {μ : Measure α}

namespace ENNReal

/- warning: ennreal.lintegral_mul_le_one_of_lintegral_rpow_eq_one -> ENNReal.lintegral_mul_le_one_of_lintegral_rpow_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) q)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) q)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) f g a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))
Case conversion may be inaccurate. Consider using '#align ennreal.lintegral_mul_le_one_of_lintegral_rpow_eq_one ENNReal.lintegral_mul_le_one_of_lintegral_rpow_eq_oneₓ'. -/
theorem lintegral_mul_le_one_of_lintegral_rpow_eq_one {p q : ℝ} (hpq : p.IsConjugateExponent q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_norm : (∫⁻ a, f a ^ p ∂μ) = 1)
    (hg_norm : (∫⁻ a, g a ^ q ∂μ) = 1) : (∫⁻ a, (f * g) a ∂μ) ≤ 1 := by
  calc
    (∫⁻ a : α, (f * g) a ∂μ) ≤
        ∫⁻ a : α, f a ^ p / ENNReal.ofReal p + g a ^ q / ENNReal.ofReal q ∂μ :=
      lintegral_mono fun a => young_inequality (f a) (g a) hpq
    _ = 1 := by
      simp only [div_eq_mul_inv]
      rw [lintegral_add_left']
      · rw [lintegral_mul_const'' _ (hf.pow_const p), lintegral_mul_const', hf_norm, hg_norm, ←
          div_eq_mul_inv, ← div_eq_mul_inv, hpq.inv_add_inv_conj_ennreal]
        simp [hpq.symm.pos]
      · exact (hf.pow_const _).mul_const _
    
#align ennreal.lintegral_mul_le_one_of_lintegral_rpow_eq_one ENNReal.lintegral_mul_le_one_of_lintegral_rpow_eq_one

#print ENNReal.funMulInvSnorm /-
/-- Function multiplied by the inverse of its p-seminorm `(∫⁻ f^p ∂μ) ^ 1/p`-/
def funMulInvSnorm (f : α → ℝ≥0∞) (p : ℝ) (μ : Measure α) : α → ℝ≥0∞ := fun a =>
  f a * ((∫⁻ c, f c ^ p ∂μ) ^ (1 / p))⁻¹
#align ennreal.fun_mul_inv_snorm ENNReal.funMulInvSnorm
-/

/- warning: ennreal.fun_eq_fun_mul_inv_snorm_mul_snorm -> ENNReal.fun_eq_funMulInvSnorm_mul_snorm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} (f : α -> ENNReal), (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {a : α}, Eq.{1} ENNReal (f a) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (ENNReal.funMulInvSnorm.{u1} α _inst_1 f p μ a) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (c : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f c) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} (f : α -> ENNReal), (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {a : α}, Eq.{1} ENNReal (f a) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.funMulInvSnorm.{u1} α _inst_1 f p μ a) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (c : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f c) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p))))
Case conversion may be inaccurate. Consider using '#align ennreal.fun_eq_fun_mul_inv_snorm_mul_snorm ENNReal.fun_eq_funMulInvSnorm_mul_snormₓ'. -/
theorem fun_eq_funMulInvSnorm_mul_snorm {p : ℝ} (f : α → ℝ≥0∞) (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0)
    (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) {a : α} :
    f a = funMulInvSnorm f p μ a * (∫⁻ c, f c ^ p ∂μ) ^ (1 / p) := by
  simp [fun_mul_inv_snorm, mul_assoc, ENNReal.inv_mul_cancel, hf_nonzero, hf_top]
#align ennreal.fun_eq_fun_mul_inv_snorm_mul_snorm ENNReal.fun_eq_funMulInvSnorm_mul_snorm

/- warning: ennreal.fun_mul_inv_snorm_rpow -> ENNReal.funMulInvSnorm_rpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (forall {f : α -> ENNReal} {a : α}, Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (ENNReal.funMulInvSnorm.{u1} α _inst_1 f p μ a) p) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p) (Inv.inv.{0} ENNReal ENNReal.hasInv (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (c : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f c) p)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (forall {f : α -> ENNReal} {a : α}, Eq.{1} ENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (ENNReal.funMulInvSnorm.{u1} α _inst_1 f p μ a) p) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p) (Inv.inv.{0} ENNReal ENNReal.instInvENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (c : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f c) p)))))
Case conversion may be inaccurate. Consider using '#align ennreal.fun_mul_inv_snorm_rpow ENNReal.funMulInvSnorm_rpowₓ'. -/
theorem funMulInvSnorm_rpow {p : ℝ} (hp0 : 0 < p) {f : α → ℝ≥0∞} {a : α} :
    funMulInvSnorm f p μ a ^ p = f a ^ p * (∫⁻ c, f c ^ p ∂μ)⁻¹ :=
  by
  rw [fun_mul_inv_snorm, mul_rpow_of_nonneg _ _ (le_of_lt hp0)]
  suffices h_inv_rpow : ((∫⁻ c : α, f c ^ p ∂μ) ^ (1 / p))⁻¹ ^ p = (∫⁻ c : α, f c ^ p ∂μ)⁻¹
  · rw [h_inv_rpow]
  rw [inv_rpow, ← rpow_mul, one_div_mul_cancel hp0.ne', rpow_one]
#align ennreal.fun_mul_inv_snorm_rpow ENNReal.funMulInvSnorm_rpow

/- warning: ennreal.lintegral_rpow_fun_mul_inv_snorm_eq_one -> ENNReal.lintegral_rpow_funMulInvSnorm_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (forall {f : α -> ENNReal}, (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (c : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (ENNReal.funMulInvSnorm.{u1} α _inst_1 f p μ c) p)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (forall {f : α -> ENNReal}, (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (c : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (ENNReal.funMulInvSnorm.{u1} α _inst_1 f p μ c) p)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))
Case conversion may be inaccurate. Consider using '#align ennreal.lintegral_rpow_fun_mul_inv_snorm_eq_one ENNReal.lintegral_rpow_funMulInvSnorm_eq_oneₓ'. -/
theorem lintegral_rpow_funMulInvSnorm_eq_one {p : ℝ} (hp0_lt : 0 < p) {f : α → ℝ≥0∞}
    (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0) (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) :
    (∫⁻ c, funMulInvSnorm f p μ c ^ p ∂μ) = 1 :=
  by
  simp_rw [fun_mul_inv_snorm_rpow hp0_lt]
  rw [lintegral_mul_const', ENNReal.mul_inv_cancel hf_nonzero hf_top]
  rwa [inv_ne_top]
#align ennreal.lintegral_rpow_fun_mul_inv_snorm_eq_one ENNReal.lintegral_rpow_funMulInvSnorm_eq_one

/- warning: ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top -> ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) q)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) q)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) q)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) q)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) q)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) q)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) f g a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) q)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) q)))))
Case conversion may be inaccurate. Consider using '#align ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_topₓ'. -/
/-- Hölder's inequality in case of finite non-zero integrals -/
theorem lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top {p q : ℝ} (hpq : p.IsConjugateExponent q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_nontop : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤)
    (hg_nontop : (∫⁻ a, g a ^ q ∂μ) ≠ ⊤) (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0)
    (hg_nonzero : (∫⁻ a, g a ^ q ∂μ) ≠ 0) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) :=
  by
  let npf := (∫⁻ c : α, f c ^ p ∂μ) ^ (1 / p)
  let nqg := (∫⁻ c : α, g c ^ q ∂μ) ^ (1 / q)
  calc
    (∫⁻ a : α, (f * g) a ∂μ) =
        ∫⁻ a : α, (fun_mul_inv_snorm f p μ * fun_mul_inv_snorm g q μ) a * (npf * nqg) ∂μ :=
      by
      refine' lintegral_congr fun a => _
      rw [Pi.mul_apply, fun_eq_fun_mul_inv_snorm_mul_snorm f hf_nonzero hf_nontop,
        fun_eq_fun_mul_inv_snorm_mul_snorm g hg_nonzero hg_nontop, Pi.mul_apply]
      ring
    _ ≤ npf * nqg :=
      by
      rw [lintegral_mul_const' (npf * nqg) _
          (by simp [hf_nontop, hg_nontop, hf_nonzero, hg_nonzero, ENNReal.mul_eq_top])]
      refine' mul_le_of_le_one_left' _
      have hf1 := lintegral_rpow_fun_mul_inv_snorm_eq_one hpq.pos hf_nonzero hf_nontop
      have hg1 := lintegral_rpow_fun_mul_inv_snorm_eq_one hpq.symm.pos hg_nonzero hg_nontop
      exact lintegral_mul_le_one_of_lintegral_rpow_eq_one hpq (hf.mul_const _) hf1 hg1
    
#align ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top

/- warning: ennreal.ae_eq_zero_of_lintegral_rpow_eq_zero -> ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (forall {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Filter.EventuallyEq.{u1, 0} α ENNReal (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) f (OfNat.ofNat.{u1} (α -> ENNReal) 0 (OfNat.mk.{u1} (α -> ENNReal) 0 (Zero.zero.{u1} (α -> ENNReal) (Pi.instZero.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => ENNReal.hasZero)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (forall {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Filter.EventuallyEq.{u1, 0} α ENNReal (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) f (OfNat.ofNat.{u1} (α -> ENNReal) 0 (Zero.toOfNat0.{u1} (α -> ENNReal) (Pi.instZero.{u1, 0} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19136 : α) => ENNReal) (fun (i : α) => instENNRealZero))))))
Case conversion may be inaccurate. Consider using '#align ennreal.ae_eq_zero_of_lintegral_rpow_eq_zero ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zeroₓ'. -/
theorem ae_eq_zero_of_lintegral_rpow_eq_zero {p : ℝ} (hp0 : 0 ≤ p) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_zero : (∫⁻ a, f a ^ p ∂μ) = 0) : f =ᵐ[μ] 0 :=
  by
  rw [lintegral_eq_zero_iff' (hf.pow_const p)] at hf_zero
  refine' Filter.Eventually.mp hf_zero (Filter.eventually_of_forall fun x => _)
  dsimp only
  rw [Pi.zero_apply, ← not_imp_not]
  exact fun hx => (rpow_pos_of_nonneg (pos_iff_ne_zero.2 hx) hp0).ne'
#align ennreal.ae_eq_zero_of_lintegral_rpow_eq_zero ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero

/- warning: ennreal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero -> ENNReal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) f g a)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align ennreal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero ENNReal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zeroₓ'. -/
theorem lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero {p : ℝ} (hp0 : 0 ≤ p) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_zero : (∫⁻ a, f a ^ p ∂μ) = 0) : (∫⁻ a, (f * g) a ∂μ) = 0 :=
  by
  rw [← @lintegral_zero_fun α _ μ]
  refine' lintegral_congr_ae _
  suffices h_mul_zero : f * g =ᵐ[μ] 0 * g
  · rwa [MulZeroClass.zero_mul] at h_mul_zero
  have hf_eq_zero : f =ᵐ[μ] 0 := ae_eq_zero_of_lintegral_rpow_eq_zero hp0 hf hf_zero
  exact hf_eq_zero.mul (ae_eq_refl g)
#align ennreal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero ENNReal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero

/- warning: ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top -> ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {q : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) q) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) q)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) q)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) q)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {q : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) q) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) q)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) f g a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) q)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) q)))))
Case conversion may be inaccurate. Consider using '#align ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_topₓ'. -/
theorem lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top {p q : ℝ} (hp0_lt : 0 < p) (hq0 : 0 ≤ q)
    {f g : α → ℝ≥0∞} (hf_top : (∫⁻ a, f a ^ p ∂μ) = ⊤) (hg_nonzero : (∫⁻ a, g a ^ q ∂μ) ≠ 0) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) :=
  by
  refine' le_trans le_top (le_of_eq _)
  have hp0_inv_lt : 0 < 1 / p := by simp [hp0_lt]
  rw [hf_top, ENNReal.top_rpow_of_pos hp0_inv_lt]
  simp [hq0, hg_nonzero]
#align ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top

/- warning: ennreal.lintegral_mul_le_Lp_mul_Lq -> ENNReal.lintegral_mul_le_Lp_mul_Lq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_1) {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 g μ) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) q)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) q)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_1) {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 g μ) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) f g a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) q)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) q)))))
Case conversion may be inaccurate. Consider using '#align ennreal.lintegral_mul_le_Lp_mul_Lq ENNReal.lintegral_mul_le_Lp_mul_Lqₓ'. -/
/-- Hölder's inequality for functions `α → ℝ≥0∞`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem lintegral_mul_le_Lp_mul_Lq (μ : Measure α) {p q : ℝ} (hpq : p.IsConjugateExponent q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) :=
  by
  by_cases hf_zero : (∫⁻ a, f a ^ p ∂μ) = 0
  · refine' Eq.trans_le _ (zero_le _)
    exact lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.nonneg hf hf_zero
  by_cases hg_zero : (∫⁻ a, g a ^ q ∂μ) = 0
  · refine' Eq.trans_le _ (zero_le _)
    rw [mul_comm]
    exact lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.symm.nonneg hg hg_zero
  by_cases hf_top : (∫⁻ a, f a ^ p ∂μ) = ⊤
  · exact lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.pos hpq.symm.nonneg hf_top hg_zero
  by_cases hg_top : (∫⁻ a, g a ^ q ∂μ) = ⊤
  · rw [mul_comm, mul_comm ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p))]
    exact lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.symm.pos hpq.nonneg hg_top hf_zero
  -- non-⊤ non-zero case
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top hpq hf hf_top hg_top hf_zero hg_zero
#align ennreal.lintegral_mul_le_Lp_mul_Lq ENNReal.lintegral_mul_le_Lp_mul_Lq

/- warning: ennreal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top -> ENNReal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) p)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (HAdd.hAdd.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHAdd.{u1} (α -> ENNReal) (Pi.instAdd.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a) p)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) p)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (HAdd.hAdd.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHAdd.{u1} (α -> ENNReal) (Pi.instAdd.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))))) f g a) p)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ennreal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top ENNReal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_topₓ'. -/
theorem lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top {p : ℝ} {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_top : (∫⁻ a, f a ^ p ∂μ) < ⊤) (hg_top : (∫⁻ a, g a ^ p ∂μ) < ⊤)
    (hp1 : 1 ≤ p) : (∫⁻ a, (f + g) a ^ p ∂μ) < ⊤ :=
  by
  have hp0_lt : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hp0 : 0 ≤ p := le_of_lt hp0_lt
  calc
    (∫⁻ a : α, (f a + g a) ^ p ∂μ) ≤
        ∫⁻ a, (2 : ℝ≥0∞) ^ (p - 1) * f a ^ p + (2 : ℝ≥0∞) ^ (p - 1) * g a ^ p ∂μ :=
      by
      refine' lintegral_mono fun a => _
      dsimp only
      have h_zero_lt_half_rpow : (0 : ℝ≥0∞) < (1 / 2) ^ p :=
        by
        rw [← ENNReal.zero_rpow_of_pos hp0_lt]
        exact ENNReal.rpow_lt_rpow (by simp [zero_lt_one]) hp0_lt
      have h_rw : (1 / 2) ^ p * (2 : ℝ≥0∞) ^ (p - 1) = 1 / 2 := by
        rw [sub_eq_add_neg, ENNReal.rpow_add _ _ two_ne_zero ENNReal.coe_ne_top, ← mul_assoc, ←
          ENNReal.mul_rpow_of_nonneg _ _ hp0, one_div,
          ENNReal.inv_mul_cancel two_ne_zero ENNReal.coe_ne_top, ENNReal.one_rpow, one_mul,
          ENNReal.rpow_neg_one]
      rw [← ENNReal.mul_le_mul_left (ne_of_lt h_zero_lt_half_rpow).symm _]
      · rw [mul_add, ← mul_assoc, ← mul_assoc, h_rw, ← ENNReal.mul_rpow_of_nonneg _ _ hp0, mul_add]
        refine'
          ENNReal.rpow_arith_mean_le_arith_mean2_rpow (1 / 2 : ℝ≥0∞) (1 / 2 : ℝ≥0∞) (f a) (g a) _
            hp1
        rw [ENNReal.div_add_div_same, one_add_one_eq_two,
          ENNReal.div_self two_ne_zero ENNReal.coe_ne_top]
      · rw [← lt_top_iff_ne_top]
        refine' ENNReal.rpow_lt_top_of_nonneg hp0 _
        rw [one_div, ENNReal.inv_ne_top]
        exact two_ne_zero
    _ < ⊤ :=
      by
      have h_two : (2 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by simp [hp1]) ENNReal.coe_ne_top
      rw [lintegral_add_left', lintegral_const_mul'' _ (hf.pow_const p),
        lintegral_const_mul' _ _ h_two, ENNReal.add_lt_top]
      · exact ⟨ENNReal.mul_lt_top h_two hf_top.ne, ENNReal.mul_lt_top h_two hg_top.ne⟩
      · exact (hf.pow_const p).const_mul _
    
#align ennreal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top ENNReal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top

/- warning: ennreal.lintegral_Lp_mul_le_Lq_mul_Lr -> ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} α] {p : Real} {q : Real} {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (LT.lt.{0} Real Real.hasLt p q) -> (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) q) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) r))) -> (forall (μ : MeasureTheory.Measure.{u1} α _inst_2) {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_2 f μ) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_2 g μ) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_2 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_2 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) q)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) q)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_2 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) r)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) r)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} α] {p : Real} {q : Real} {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (LT.lt.{0} Real Real.instLTReal p q) -> (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) q) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) r))) -> (forall (μ : MeasureTheory.Measure.{u1} α _inst_2) {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_2 f μ) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_2 g μ) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_2 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) f g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_2 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) q)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) q)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_2 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) r)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) r)))))
Case conversion may be inaccurate. Consider using '#align ennreal.lintegral_Lp_mul_le_Lq_mul_Lr ENNReal.lintegral_Lp_mul_le_Lq_mul_Lrₓ'. -/
theorem lintegral_Lp_mul_le_Lq_mul_Lr {α} [MeasurableSpace α] {p q r : ℝ} (hp0_lt : 0 < p)
    (hpq : p < q) (hpqr : 1 / p = 1 / q + 1 / r) (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, (f * g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ q ∂μ) ^ (1 / q) * (∫⁻ a, g a ^ r ∂μ) ^ (1 / r) :=
  by
  have hp0_ne : p ≠ 0 := (ne_of_lt hp0_lt).symm
  have hp0 : 0 ≤ p := le_of_lt hp0_lt
  have hq0_lt : 0 < q := lt_of_le_of_lt hp0 hpq
  have hq0_ne : q ≠ 0 := (ne_of_lt hq0_lt).symm
  have h_one_div_r : 1 / r = 1 / p - 1 / q := by simp [hpqr]
  have hr0_ne : r ≠ 0 :=
    by
    have hr_inv_pos : 0 < 1 / r := by rwa [h_one_div_r, sub_pos, one_div_lt_one_div hq0_lt hp0_lt]
    rw [one_div, _root_.inv_pos] at hr_inv_pos
    exact (ne_of_lt hr_inv_pos).symm
  let p2 := q / p
  let q2 := p2.conjugate_exponent
  have hp2q2 : p2.is_conjugate_exponent q2 :=
    Real.isConjugateExponent_conjugateExponent (by simp [lt_div_iff, hpq, hp0_lt])
  calc
    (∫⁻ a : α, (f * g) a ^ p ∂μ) ^ (1 / p) = (∫⁻ a : α, f a ^ p * g a ^ p ∂μ) ^ (1 / p) := by
      simp_rw [Pi.mul_apply, ENNReal.mul_rpow_of_nonneg _ _ hp0]
    _ ≤ ((∫⁻ a, f a ^ (p * p2) ∂μ) ^ (1 / p2) * (∫⁻ a, g a ^ (p * q2) ∂μ) ^ (1 / q2)) ^ (1 / p) :=
      by
      refine' ENNReal.rpow_le_rpow _ (by simp [hp0])
      simp_rw [ENNReal.rpow_mul]
      exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hp2q2 (hf.pow_const _) (hg.pow_const _)
    _ = (∫⁻ a : α, f a ^ q ∂μ) ^ (1 / q) * (∫⁻ a : α, g a ^ r ∂μ) ^ (1 / r) :=
      by
      rw [@ENNReal.mul_rpow_of_nonneg _ _ (1 / p) (by simp [hp0]), ← ENNReal.rpow_mul, ←
        ENNReal.rpow_mul]
      have hpp2 : p * p2 = q := by
        symm
        rw [mul_comm, ← div_eq_iff hp0_ne]
      have hpq2 : p * q2 = r :=
        by
        rw [← inv_inv r, ← one_div, ← one_div, h_one_div_r]
        field_simp [q2, Real.conjugateExponent, p2, hp0_ne, hq0_ne]
      simp_rw [div_mul_div_comm, mul_one, mul_comm p2, mul_comm q2, hpp2, hpq2]
    
#align ennreal.lintegral_Lp_mul_le_Lq_mul_Lr ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr

/- warning: ennreal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow -> ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 g μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) p (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) q)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 g μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f a) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) p (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) q)))))
Case conversion may be inaccurate. Consider using '#align ennreal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpowₓ'. -/
theorem lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow {p q : ℝ}
    (hpq : p.IsConjugateExponent q) {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) :
    (∫⁻ a, f a * g a ^ (p - 1) ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ p ∂μ) ^ (1 / q) :=
  by
  refine' le_trans (ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf (hg.pow_const _)) _
  by_cases hf_zero_rpow : (∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) = 0
  · rw [hf_zero_rpow, MulZeroClass.zero_mul]
    exact zero_le _
  have hf_top_rpow : (∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) ≠ ⊤ :=
    by
    by_contra h
    refine' hf_top _
    have hp_not_neg : ¬p < 0 := by simp [hpq.nonneg]
    simpa [hpq.pos, hp_not_neg] using h
  refine' (ENNReal.mul_le_mul_left hf_zero_rpow hf_top_rpow).mpr (le_of_eq _)
  congr
  ext1 a
  rw [← ENNReal.rpow_mul, hpq.sub_one_mul_conj]
#align ennreal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow

/- warning: ennreal.lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add -> ENNReal.lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 g μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) p)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (HAdd.hAdd.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHAdd.{u1} (α -> ENNReal) (Pi.instAdd.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a) p)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (g a)) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) q)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (forall {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 g μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) p)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (HAdd.hAdd.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHAdd.{u1} (α -> ENNReal) (Pi.instAdd.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))))) f g a) p)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f a) (g a)) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) q)))))
Case conversion may be inaccurate. Consider using '#align ennreal.lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add ENNReal.lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_addₓ'. -/
theorem lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add {p q : ℝ}
    (hpq : p.IsConjugateExponent q) {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) (hg : AEMeasurable g μ) (hg_top : (∫⁻ a, g a ^ p ∂μ) ≠ ⊤) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ≤
      ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) *
        (∫⁻ a, (f a + g a) ^ p ∂μ) ^ (1 / q) :=
  by
  calc
    (∫⁻ a, (f + g) a ^ p ∂μ) ≤ ∫⁻ a, (f + g) a * (f + g) a ^ (p - 1) ∂μ :=
      by
      refine' lintegral_mono fun a => _
      dsimp only
      by_cases h_zero : (f + g) a = 0
      · rw [h_zero, ENNReal.zero_rpow_of_pos hpq.pos]
        exact zero_le _
      by_cases h_top : (f + g) a = ⊤
      · rw [h_top, ENNReal.top_rpow_of_pos hpq.sub_one_pos, ENNReal.top_mul_top]
        exact le_top
      refine' le_of_eq _
      nth_rw 2 [← ENNReal.rpow_one ((f + g) a)]
      rw [← ENNReal.rpow_add _ _ h_zero h_top, add_sub_cancel'_right]
    _ = (∫⁻ a : α, f a * (f + g) a ^ (p - 1) ∂μ) + ∫⁻ a : α, g a * (f + g) a ^ (p - 1) ∂μ :=
      by
      have h_add_m : AEMeasurable (fun a : α => (f + g) a ^ (p - 1)) μ := (hf.add hg).pow_const _
      have h_add_apply :
        (∫⁻ a : α, (f + g) a * (f + g) a ^ (p - 1) ∂μ) =
          ∫⁻ a : α, (f a + g a) * (f + g) a ^ (p - 1) ∂μ :=
        rfl
      simp_rw [h_add_apply, add_mul]
      rw [lintegral_add_left' (hf.mul h_add_m)]
    _ ≤
        ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) *
          (∫⁻ a, (f a + g a) ^ p ∂μ) ^ (1 / q) :=
      by
      rw [add_mul]
      exact
        add_le_add
          (lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq hf (hf.add hg) hf_top)
          (lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq hg (hf.add hg) hg_top)
    
#align ennreal.lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add ENNReal.lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add

private theorem lintegral_Lp_add_le_aux {p q : ℝ} (hpq : p.IsConjugateExponent q) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) (hg : AEMeasurable g μ)
    (hg_top : (∫⁻ a, g a ^ p ∂μ) ≠ ⊤) (h_add_zero : (∫⁻ a, (f + g) a ^ p ∂μ) ≠ 0)
    (h_add_top : (∫⁻ a, (f + g) a ^ p ∂μ) ≠ ⊤) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p) :=
  by
  have hp_not_nonpos : ¬p ≤ 0 := by simp [hpq.pos]
  have htop_rpow : (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≠ ⊤ :=
    by
    by_contra h
    exact h_add_top (@ENNReal.rpow_eq_top_of_nonneg _ (1 / p) (by simp [hpq.nonneg]) h)
  have h0_rpow : (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≠ 0 := by
    simp [h_add_zero, h_add_top, hpq.nonneg, hp_not_nonpos, -Pi.add_apply]
  suffices h :
    1 ≤
      (∫⁻ a : α, (f + g) a ^ p ∂μ) ^ (-(1 / p)) *
        ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a : α, g a ^ p ∂μ) ^ (1 / p))
  ·
    rwa [← mul_le_mul_left h0_rpow htop_rpow, ← mul_assoc, ← rpow_add _ _ h_add_zero h_add_top, ←
      sub_eq_add_neg, _root_.sub_self, rpow_zero, one_mul, mul_one] at h
  have h :
    (∫⁻ a : α, (f + g) a ^ p ∂μ) ≤
      ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a : α, g a ^ p ∂μ) ^ (1 / p)) *
        (∫⁻ a : α, (f + g) a ^ p ∂μ) ^ (1 / q) :=
    lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add hpq hf hf_top hg hg_top
  have h_one_div_q : 1 / q = 1 - 1 / p :=
    by
    nth_rw 2 [← hpq.inv_add_inv_conj]
    ring
  simp_rw [h_one_div_q, sub_eq_add_neg 1 (1 / p), ENNReal.rpow_add _ _ h_add_zero h_add_top,
    rpow_one] at h
  nth_rw 2 [mul_comm] at h
  nth_rw 1 [← one_mul (∫⁻ a : α, (f + g) a ^ p ∂μ)] at h
  rwa [← mul_assoc, ENNReal.mul_le_mul_right h_add_zero h_add_top, mul_comm] at h
#align ennreal.lintegral_Lp_add_le_aux ennreal.lintegral_Lp_add_le_aux

/- warning: ennreal.lintegral_Lp_add_le -> ENNReal.lintegral_Lp_add_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 g μ) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (HAdd.hAdd.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHAdd.{u1} (α -> ENNReal) (Pi.instAdd.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 g μ) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (HAdd.hAdd.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHAdd.{u1} (α -> ENNReal) (Pi.instAdd.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))))) f g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p))))
Case conversion may be inaccurate. Consider using '#align ennreal.lintegral_Lp_add_le ENNReal.lintegral_Lp_add_leₓ'. -/
/-- Minkowski's inequality for functions `α → ℝ≥0∞`: the `ℒp` seminorm of the sum of two
functions is bounded by the sum of their `ℒp` seminorms. -/
theorem lintegral_Lp_add_le {p : ℝ} {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hp1 : 1 ≤ p) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p) :=
  by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  by_cases hf_top : (∫⁻ a, f a ^ p ∂μ) = ⊤
  · simp [hf_top, hp_pos]
  by_cases hg_top : (∫⁻ a, g a ^ p ∂μ) = ⊤
  · simp [hg_top, hp_pos]
  by_cases h1 : p = 1
  · refine' le_of_eq _
    simp_rw [h1, one_div_one, ENNReal.rpow_one]
    exact lintegral_add_left' hf _
  have hp1_lt : 1 < p := by
    refine' lt_of_le_of_ne hp1 _
    symm
    exact h1
  have hpq := Real.isConjugateExponent_conjugateExponent hp1_lt
  by_cases h0 : (∫⁻ a, (f + g) a ^ p ∂μ) = 0
  · rw [h0, @ENNReal.zero_rpow_of_pos (1 / p) (by simp [lt_of_lt_of_le zero_lt_one hp1])]
    exact zero_le _
  have htop : (∫⁻ a, (f + g) a ^ p ∂μ) ≠ ⊤ :=
    by
    rw [← Ne.def] at hf_top hg_top
    rw [← lt_top_iff_ne_top] at hf_top hg_top⊢
    exact lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top hf hf_top hg_top hp1
  exact lintegral_Lp_add_le_aux hpq hf hf_top hg hg_top h0 htop
#align ennreal.lintegral_Lp_add_le ENNReal.lintegral_Lp_add_le

/- warning: ennreal.lintegral_Lp_add_le_of_le_one -> ENNReal.lintegral_Lp_add_le_of_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (LE.le.{0} Real Real.hasLe p (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (HAdd.hAdd.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHAdd.{u1} (α -> ENNReal) (Pi.instAdd.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (OfNat.ofNat.{0} ENNReal 2 (OfNat.mk.{0} ENNReal 2 (bit0.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_1 f μ) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (LE.le.{0} Real Real.instLEReal p (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (HAdd.hAdd.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHAdd.{u1} (α -> ENNReal) (Pi.instAdd.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))))) f g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (OfNat.ofNat.{0} ENNReal 2 (instOfNat.{0} ENNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (f a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (g a) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)))))
Case conversion may be inaccurate. Consider using '#align ennreal.lintegral_Lp_add_le_of_le_one ENNReal.lintegral_Lp_add_le_of_le_oneₓ'. -/
/-- Variant of Minkowski's inequality for functions `α → ℝ≥0∞` in `ℒp` with `p ≤ 1`: the `ℒp`
seminorm of the sum of two functions is bounded by a constant multiple of the sum
of their `ℒp` seminorms. -/
theorem lintegral_Lp_add_le_of_le_one {p : ℝ} {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      2 ^ (1 / p - 1) * ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) :=
  by
  rcases eq_or_lt_of_le hp0 with (rfl | hp)
  · simp only [Pi.add_apply, rpow_zero, lintegral_one, _root_.div_zero, zero_sub]
    norm_num
    rw [rpow_neg, rpow_one, ENNReal.inv_mul_cancel two_ne_zero two_ne_top]
    exact le_rfl
  calc
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤ ((∫⁻ a, f a ^ p ∂μ) + ∫⁻ a, g a ^ p ∂μ) ^ (1 / p) :=
      by
      apply rpow_le_rpow _ (div_nonneg zero_le_one hp0)
      rw [← lintegral_add_left' (hf.pow_const p)]
      exact lintegral_mono fun a => rpow_add_le_add_rpow _ _ hp0 hp1
    _ ≤ 2 ^ (1 / p - 1) * ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) :=
      rpow_add_le_mul_rpow_add_rpow _ _ ((one_le_div hp).2 hp1)
    
#align ennreal.lintegral_Lp_add_le_of_le_one ENNReal.lintegral_Lp_add_le_of_le_one

end ENNReal

/- warning: nnreal.lintegral_mul_le_Lp_mul_Lq -> NNReal.lintegral_mul_le_Lp_mul_Lq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (forall {f : α -> NNReal} {g : α -> NNReal}, (AEMeasurable.{u1, 0} α NNReal NNReal.measurableSpace _inst_1 f μ) -> (AEMeasurable.{u1, 0} α NNReal NNReal.measurableSpace _inst_1 g μ) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (HMul.hMul.{u1, u1, u1} (α -> NNReal) (α -> NNReal) (α -> NNReal) (instHMul.{u1} (α -> NNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => NNReal) (fun (i : α) => Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))) f g a))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f a)) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (g a)) q)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) q)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : Real} {q : Real}, (Real.IsConjugateExponent p q) -> (forall {f : α -> NNReal} {g : α -> NNReal}, (AEMeasurable.{u1, 0} α NNReal NNReal.measurableSpace _inst_1 f μ) -> (AEMeasurable.{u1, 0} α NNReal NNReal.measurableSpace _inst_1 g μ) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => ENNReal.some (HMul.hMul.{u1, u1, u1} (α -> NNReal) (α -> NNReal) (α -> NNReal) (instHMul.{u1} (α -> NNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => NNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring))) f g a))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (ENNReal.some (f a)) p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (ENNReal.some (g a)) q)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) q)))))
Case conversion may be inaccurate. Consider using '#align nnreal.lintegral_mul_le_Lp_mul_Lq NNReal.lintegral_mul_le_Lp_mul_Lqₓ'. -/
/-- Hölder's inequality for functions `α → ℝ≥0`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem NNReal.lintegral_mul_le_Lp_mul_Lq {p q : ℝ} (hpq : p.IsConjugateExponent q) {f g : α → ℝ≥0}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) :=
  by
  simp_rw [Pi.mul_apply, ENNReal.coe_mul]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.coe_nnreal_ennreal hg.coe_nnreal_ennreal
#align nnreal.lintegral_mul_le_Lp_mul_Lq NNReal.lintegral_mul_le_Lp_mul_Lq

end Lintegral

