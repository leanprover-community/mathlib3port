/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler

! This file was ported from Lean 3 source module analysis.special_functions.pow.continuity
! leanprover-community/mathlib commit 0b9eaaa7686280fad8cce467f5c3c57ee6ce77f8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Continuity of power functions

This file contains lemmas about continuity of the power functions on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`.
-/


noncomputable section

open Classical Real Topology NNReal ENNReal Filter BigOperators ComplexConjugate

open Filter Finset Set

section CpowLimits

/-!
## Continuity for complex powers
-/


open Complex

variable {α : Type _}

/- warning: zero_cpow_eq_nhds -> zero_cpow_eq_nhds is a dubious translation:
lean 3 declaration is
  forall {b : Complex}, (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Filter.EventuallyEq.{0, 0} Complex Complex (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) b) (fun (x : Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))) x) (OfNat.ofNat.{0} (Complex -> Complex) 0 (OfNat.mk.{0} (Complex -> Complex) 0 (Zero.zero.{0} (Complex -> Complex) (Pi.instZero.{0, 0} Complex (fun (ᾰ : Complex) => Complex) (fun (i : Complex) => Complex.hasZero))))))
but is expected to have type
  forall {b : Complex}, (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Filter.EventuallyEq.{0, 0} Complex Complex (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) b) (fun (x : Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)) x) (OfNat.ofNat.{0} (Complex -> Complex) 0 (Zero.toOfNat0.{0} (Complex -> Complex) (Pi.instZero.{0, 0} Complex (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19136 : Complex) => Complex) (fun (i : Complex) => Complex.instZeroComplex)))))
Case conversion may be inaccurate. Consider using '#align zero_cpow_eq_nhds zero_cpow_eq_nhdsₓ'. -/
theorem zero_cpow_eq_nhds {b : ℂ} (hb : b ≠ 0) : (fun x : ℂ => (0 : ℂ) ^ x) =ᶠ[𝓝 b] 0 :=
  by
  suffices : ∀ᶠ x : ℂ in 𝓝 b, x ≠ 0
  exact
    this.mono fun x hx => by
      dsimp only
      rw [zero_cpow hx, Pi.zero_apply]
  exact IsOpen.eventually_mem isOpen_ne hb
#align zero_cpow_eq_nhds zero_cpow_eq_nhds

/- warning: cpow_eq_nhds -> cpow_eq_nhds is a dubious translation:
lean 3 declaration is
  forall {a : Complex} {b : Complex}, (Ne.{1} Complex a (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Filter.EventuallyEq.{0, 0} Complex Complex (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) a) (fun (x : Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x b) (fun (x : Complex) => Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.log x) b)))
but is expected to have type
  forall {a : Complex} {b : Complex}, (Ne.{1} Complex a (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Filter.EventuallyEq.{0, 0} Complex Complex (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) a) (fun (x : Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x b) (fun (x : Complex) => Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.log x) b)))
Case conversion may be inaccurate. Consider using '#align cpow_eq_nhds cpow_eq_nhdsₓ'. -/
theorem cpow_eq_nhds {a b : ℂ} (ha : a ≠ 0) : (fun x => x ^ b) =ᶠ[𝓝 a] fun x => exp (log x * b) :=
  by
  suffices : ∀ᶠ x : ℂ in 𝓝 a, x ≠ 0
  exact
    this.mono fun x hx => by
      dsimp only
      rw [cpow_def_of_ne_zero hx]
  exact IsOpen.eventually_mem isOpen_ne ha
#align cpow_eq_nhds cpow_eq_nhds

/- warning: cpow_eq_nhds' -> cpow_eq_nhds' is a dubious translation:
lean 3 declaration is
  forall {p : Prod.{0, 0} Complex Complex}, (Ne.{1} Complex (Prod.fst.{0, 0} Complex Complex p) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Filter.EventuallyEq.{0, 0} (Prod.{0, 0} Complex Complex) Complex (nhds.{0} (Prod.{0, 0} Complex Complex) (Prod.topologicalSpace.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField))))))) p) (fun (x : Prod.{0, 0} Complex Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (Prod.fst.{0, 0} Complex Complex x) (Prod.snd.{0, 0} Complex Complex x)) (fun (x : Prod.{0, 0} Complex Complex) => Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.log (Prod.fst.{0, 0} Complex Complex x)) (Prod.snd.{0, 0} Complex Complex x))))
but is expected to have type
  forall {p : Prod.{0, 0} Complex Complex}, (Ne.{1} Complex (Prod.fst.{0, 0} Complex Complex p) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Filter.EventuallyEq.{0, 0} (Prod.{0, 0} Complex Complex) Complex (nhds.{0} (Prod.{0, 0} Complex Complex) (instTopologicalSpaceProd.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex))))))) p) (fun (x : Prod.{0, 0} Complex Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Prod.fst.{0, 0} Complex Complex x) (Prod.snd.{0, 0} Complex Complex x)) (fun (x : Prod.{0, 0} Complex Complex) => Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.log (Prod.fst.{0, 0} Complex Complex x)) (Prod.snd.{0, 0} Complex Complex x))))
Case conversion may be inaccurate. Consider using '#align cpow_eq_nhds' cpow_eq_nhds'ₓ'. -/
theorem cpow_eq_nhds' {p : ℂ × ℂ} (hp_fst : p.fst ≠ 0) :
    (fun x => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
  by
  suffices : ∀ᶠ x : ℂ × ℂ in 𝓝 p, x.1 ≠ 0
  exact
    this.mono fun x hx => by
      dsimp only
      rw [cpow_def_of_ne_zero hx]
  refine' IsOpen.eventually_mem _ hp_fst
  change IsOpen ({ x : ℂ × ℂ | x.1 = 0 }ᶜ)
  rw [isOpen_compl_iff]
  exact isClosed_eq continuous_fst continuous_const
#align cpow_eq_nhds' cpow_eq_nhds'

/- warning: continuous_at_const_cpow -> continuousAt_const_cpow is a dubious translation:
lean 3 declaration is
  forall {a : Complex} {b : Complex}, (Ne.{1} Complex a (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (ContinuousAt.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) a x) b)
but is expected to have type
  forall {a : Complex} {b : Complex}, (Ne.{1} Complex a (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (ContinuousAt.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) a x) b)
Case conversion may be inaccurate. Consider using '#align continuous_at_const_cpow continuousAt_const_cpowₓ'. -/
-- Continuity of `λ x, a ^ x`: union of these two lemmas is optimal.
theorem continuousAt_const_cpow {a b : ℂ} (ha : a ≠ 0) : ContinuousAt (fun x => a ^ x) b :=
  by
  have cpow_eq : (fun x : ℂ => a ^ x) = fun x => exp (log a * x) :=
    by
    ext1 b
    rw [cpow_def_of_ne_zero ha]
  rw [cpow_eq]
  exact continuous_exp.continuous_at.comp (ContinuousAt.mul continuousAt_const continuousAt_id)
#align continuous_at_const_cpow continuousAt_const_cpow

/- warning: continuous_at_const_cpow' -> continuousAt_const_cpow' is a dubious translation:
lean 3 declaration is
  forall {a : Complex} {b : Complex}, (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (ContinuousAt.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) a x) b)
but is expected to have type
  forall {a : Complex} {b : Complex}, (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (ContinuousAt.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) a x) b)
Case conversion may be inaccurate. Consider using '#align continuous_at_const_cpow' continuousAt_const_cpow'ₓ'. -/
theorem continuousAt_const_cpow' {a b : ℂ} (h : b ≠ 0) : ContinuousAt (fun x => a ^ x) b :=
  by
  by_cases ha : a = 0
  · rw [ha, continuousAt_congr (zero_cpow_eq_nhds h)]
    exact continuousAt_const
  · exact continuousAt_const_cpow ha
#align continuous_at_const_cpow' continuousAt_const_cpow'

/- warning: continuous_at_cpow -> continuousAt_cpow is a dubious translation:
lean 3 declaration is
  forall {p : Prod.{0, 0} Complex Complex}, (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re (Prod.fst.{0, 0} Complex Complex p))) (Ne.{1} Real (Complex.im (Prod.fst.{0, 0} Complex Complex p)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Complex Complex) Complex (Prod.topologicalSpace.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField))))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : Prod.{0, 0} Complex Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (Prod.fst.{0, 0} Complex Complex x) (Prod.snd.{0, 0} Complex Complex x)) p)
but is expected to have type
  forall {p : Prod.{0, 0} Complex Complex}, (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re (Prod.fst.{0, 0} Complex Complex p))) (Ne.{1} Real (Complex.im (Prod.fst.{0, 0} Complex Complex p)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Complex Complex) Complex (instTopologicalSpaceProd.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex))))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : Prod.{0, 0} Complex Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Prod.fst.{0, 0} Complex Complex x) (Prod.snd.{0, 0} Complex Complex x)) p)
Case conversion may be inaccurate. Consider using '#align continuous_at_cpow continuousAt_cpowₓ'. -/
/-- The function `z ^ w` is continuous in `(z, w)` provided that `z` does not belong to the interval
`(-∞, 0]` on the real line. See also `complex.continuous_at_cpow_zero_of_re_pos` for a version that
works for `z = 0` but assumes `0 < re w`. -/
theorem continuousAt_cpow {p : ℂ × ℂ} (hp_fst : 0 < p.fst.re ∨ p.fst.im ≠ 0) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) p :=
  by
  have hp_fst_ne_zero : p.fst ≠ 0 := by
    intro h
    cases hp_fst <;>
      · rw [h] at hp_fst
        simpa using hp_fst
  rw [continuousAt_congr (cpow_eq_nhds' hp_fst_ne_zero)]
  refine' continuous_exp.continuous_at.comp _
  refine'
    ContinuousAt.mul (ContinuousAt.comp _ continuous_fst.continuous_at) continuous_snd.continuous_at
  exact continuousAt_clog hp_fst
#align continuous_at_cpow continuousAt_cpow

/- warning: continuous_at_cpow_const -> continuousAt_cpow_const is a dubious translation:
lean 3 declaration is
  forall {a : Complex} {b : Complex}, (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re a)) (Ne.{1} Real (Complex.im a) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (ContinuousAt.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : Complex) => Complex.cpow x b) a)
but is expected to have type
  forall {a : Complex} {b : Complex}, (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re a)) (Ne.{1} Real (Complex.im a) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (ContinuousAt.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : Complex) => Complex.cpow x b) a)
Case conversion may be inaccurate. Consider using '#align continuous_at_cpow_const continuousAt_cpow_constₓ'. -/
theorem continuousAt_cpow_const {a b : ℂ} (ha : 0 < a.re ∨ a.im ≠ 0) :
    ContinuousAt (fun x => cpow x b) a :=
  Tendsto.comp (@continuousAt_cpow (a, b) ha) (continuousAt_id.Prod continuousAt_const)
#align continuous_at_cpow_const continuousAt_cpow_const

/- warning: filter.tendsto.cpow -> Filter.Tendsto.cpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {g : α -> Complex} {a : Complex} {b : Complex}, (Filter.Tendsto.{u1, 0} α Complex f l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) a)) -> (Filter.Tendsto.{u1, 0} α Complex g l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) b)) -> (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re a)) (Ne.{1} Real (Complex.im a) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Filter.Tendsto.{u1, 0} α Complex (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (f x) (g x)) l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) a b)))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {g : α -> Complex} {a : Complex} {b : Complex}, (Filter.Tendsto.{u1, 0} α Complex f l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) a)) -> (Filter.Tendsto.{u1, 0} α Complex g l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) b)) -> (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re a)) (Ne.{1} Real (Complex.im a) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Filter.Tendsto.{u1, 0} α Complex (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (f x) (g x)) l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) a b)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.cpow Filter.Tendsto.cpowₓ'. -/
theorem Filter.Tendsto.cpow {l : Filter α} {f g : α → ℂ} {a b : ℂ} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (ha : 0 < a.re ∨ a.im ≠ 0) :
    Tendsto (fun x => f x ^ g x) l (𝓝 (a ^ b)) :=
  (@continuousAt_cpow (a, b) ha).Tendsto.comp (hf.prod_mk_nhds hg)
#align filter.tendsto.cpow Filter.Tendsto.cpow

/- warning: filter.tendsto.const_cpow -> Filter.Tendsto.const_cpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {a : Complex} {b : Complex}, (Filter.Tendsto.{u1, 0} α Complex f l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) b)) -> (Or (Ne.{1} Complex a (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))))) -> (Filter.Tendsto.{u1, 0} α Complex (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) a (f x)) l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) a b)))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Complex} {a : Complex} {b : Complex}, (Filter.Tendsto.{u1, 0} α Complex f l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) b)) -> (Or (Ne.{1} Complex a (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)))) -> (Filter.Tendsto.{u1, 0} α Complex (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) a (f x)) l (nhds.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) a b)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.const_cpow Filter.Tendsto.const_cpowₓ'. -/
theorem Filter.Tendsto.const_cpow {l : Filter α} {f : α → ℂ} {a b : ℂ} (hf : Tendsto f l (𝓝 b))
    (h : a ≠ 0 ∨ b ≠ 0) : Tendsto (fun x => a ^ f x) l (𝓝 (a ^ b)) :=
  by
  cases h
  · exact (continuousAt_const_cpow h).Tendsto.comp hf
  · exact (continuousAt_const_cpow' h).Tendsto.comp hf
#align filter.tendsto.const_cpow Filter.Tendsto.const_cpow

variable [TopologicalSpace α] {f g : α → ℂ} {s : Set α} {a : α}

/- warning: continuous_within_at.cpow -> ContinuousWithinAt.cpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {g : α -> Complex} {s : Set.{u1} α} {a : α}, (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f s a) -> (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) g s a) -> (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re (f a))) (Ne.{1} Real (Complex.im (f a)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (f x) (g x)) s a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {g : α -> Complex} {s : Set.{u1} α} {a : α}, (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f s a) -> (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) g s a) -> (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re (f a))) (Ne.{1} Real (Complex.im (f a)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (f x) (g x)) s a)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.cpow ContinuousWithinAt.cpowₓ'. -/
theorem ContinuousWithinAt.cpow (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a)
    (h0 : 0 < (f a).re ∨ (f a).im ≠ 0) : ContinuousWithinAt (fun x => f x ^ g x) s a :=
  hf.cpow hg h0
#align continuous_within_at.cpow ContinuousWithinAt.cpow

/- warning: continuous_within_at.const_cpow -> ContinuousWithinAt.const_cpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α} {a : α} {b : Complex}, (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f s a) -> (Or (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (Ne.{1} Complex (f a) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))))) -> (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) b (f x)) s a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α} {a : α} {b : Complex}, (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f s a) -> (Or (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (Ne.{1} Complex (f a) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)))) -> (ContinuousWithinAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) b (f x)) s a)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.const_cpow ContinuousWithinAt.const_cpowₓ'. -/
theorem ContinuousWithinAt.const_cpow {b : ℂ} (hf : ContinuousWithinAt f s a)
    (h : b ≠ 0 ∨ f a ≠ 0) : ContinuousWithinAt (fun x => b ^ f x) s a :=
  hf.const_cpow h
#align continuous_within_at.const_cpow ContinuousWithinAt.const_cpow

/- warning: continuous_at.cpow -> ContinuousAt.cpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {g : α -> Complex} {a : α}, (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f a) -> (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) g a) -> (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re (f a))) (Ne.{1} Real (Complex.im (f a)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (f x) (g x)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {g : α -> Complex} {a : α}, (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f a) -> (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) g a) -> (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re (f a))) (Ne.{1} Real (Complex.im (f a)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (f x) (g x)) a)
Case conversion may be inaccurate. Consider using '#align continuous_at.cpow ContinuousAt.cpowₓ'. -/
theorem ContinuousAt.cpow (hf : ContinuousAt f a) (hg : ContinuousAt g a)
    (h0 : 0 < (f a).re ∨ (f a).im ≠ 0) : ContinuousAt (fun x => f x ^ g x) a :=
  hf.cpow hg h0
#align continuous_at.cpow ContinuousAt.cpow

/- warning: continuous_at.const_cpow -> ContinuousAt.const_cpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {a : α} {b : Complex}, (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f a) -> (Or (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (Ne.{1} Complex (f a) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))))) -> (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) b (f x)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {a : α} {b : Complex}, (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f a) -> (Or (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (Ne.{1} Complex (f a) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)))) -> (ContinuousAt.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) b (f x)) a)
Case conversion may be inaccurate. Consider using '#align continuous_at.const_cpow ContinuousAt.const_cpowₓ'. -/
theorem ContinuousAt.const_cpow {b : ℂ} (hf : ContinuousAt f a) (h : b ≠ 0 ∨ f a ≠ 0) :
    ContinuousAt (fun x => b ^ f x) a :=
  hf.const_cpow h
#align continuous_at.const_cpow ContinuousAt.const_cpow

/- warning: continuous_on.cpow -> ContinuousOn.cpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {g : α -> Complex} {s : Set.{u1} α}, (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f s) -> (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) g s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re (f a))) (Ne.{1} Real (Complex.im (f a)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) -> (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {g : α -> Complex} {s : Set.{u1} α}, (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f s) -> (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) g s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re (f a))) (Ne.{1} Real (Complex.im (f a)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) -> (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.cpow ContinuousOn.cpowₓ'. -/
theorem ContinuousOn.cpow (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h0 : ∀ a ∈ s, 0 < (f a).re ∨ (f a).im ≠ 0) : ContinuousOn (fun x => f x ^ g x) s := fun a ha =>
  (hf a ha).cpow (hg a ha) (h0 a ha)
#align continuous_on.cpow ContinuousOn.cpow

/- warning: continuous_on.const_cpow -> ContinuousOn.const_cpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α} {b : Complex}, (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f s) -> (Or (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Ne.{1} Complex (f a) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))))) -> (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) b (f x)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α} {b : Complex}, (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f s) -> (Or (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (Ne.{1} Complex (f a) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))))) -> (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) b (f x)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.const_cpow ContinuousOn.const_cpowₓ'. -/
theorem ContinuousOn.const_cpow {b : ℂ} (hf : ContinuousOn f s) (h : b ≠ 0 ∨ ∀ a ∈ s, f a ≠ 0) :
    ContinuousOn (fun x => b ^ f x) s := fun a ha => (hf a ha).const_cpow (h.imp id fun h => h a ha)
#align continuous_on.const_cpow ContinuousOn.const_cpow

/- warning: continuous.cpow -> Continuous.cpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {g : α -> Complex}, (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f) -> (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) g) -> (forall (a : α), Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re (f a))) (Ne.{1} Real (Complex.im (f a)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {g : α -> Complex}, (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f) -> (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) g) -> (forall (a : α), Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re (f a))) (Ne.{1} Real (Complex.im (f a)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align continuous.cpow Continuous.cpowₓ'. -/
theorem Continuous.cpow (hf : Continuous f) (hg : Continuous g)
    (h0 : ∀ a, 0 < (f a).re ∨ (f a).im ≠ 0) : Continuous fun x => f x ^ g x :=
  continuous_iff_continuousAt.2 fun a => hf.ContinuousAt.cpow hg.ContinuousAt (h0 a)
#align continuous.cpow Continuous.cpow

/- warning: continuous.const_cpow -> Continuous.const_cpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {b : Complex}, (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f) -> (Or (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (forall (a : α), Ne.{1} Complex (f a) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))))) -> (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) b (f x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {b : Complex}, (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f) -> (Or (Ne.{1} Complex b (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (forall (a : α), Ne.{1} Complex (f a) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)))) -> (Continuous.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) b (f x)))
Case conversion may be inaccurate. Consider using '#align continuous.const_cpow Continuous.const_cpowₓ'. -/
theorem Continuous.const_cpow {b : ℂ} (hf : Continuous f) (h : b ≠ 0 ∨ ∀ a, f a ≠ 0) :
    Continuous fun x => b ^ f x :=
  continuous_iff_continuousAt.2 fun a => hf.ContinuousAt.const_cpow <| h.imp id fun h => h a
#align continuous.const_cpow Continuous.const_cpow

/- warning: continuous_on.cpow_const -> ContinuousOn.cpow_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α} {b : Complex}, (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) f s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re (f a))) (Ne.{1} Real (Complex.im (f a)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) -> (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (f x) b) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Complex} {s : Set.{u1} α} {b : Complex}, (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) f s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re (f a))) (Ne.{1} Real (Complex.im (f a)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) -> (ContinuousOn.{u1, 0} α Complex _inst_1 (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : α) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (f x) b) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.cpow_const ContinuousOn.cpow_constₓ'. -/
theorem ContinuousOn.cpow_const {b : ℂ} (hf : ContinuousOn f s)
    (h : ∀ a : α, a ∈ s → 0 < (f a).re ∨ (f a).im ≠ 0) : ContinuousOn (fun x => f x ^ b) s :=
  hf.cpow continuousOn_const h
#align continuous_on.cpow_const ContinuousOn.cpow_const

end CpowLimits

section RpowLimits

/-!
## Continuity for real powers
-/


namespace Real

/- warning: real.continuous_at_const_rpow -> Real.continuousAt_const_rpow is a dubious translation:
lean 3 declaration is
  forall {a : Real} {b : Real}, (Ne.{1} Real a (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (ContinuousAt.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Real.rpow a) b)
but is expected to have type
  forall {a : Real} {b : Real}, (Ne.{1} Real a (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (ContinuousAt.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Real.rpow a) b)
Case conversion may be inaccurate. Consider using '#align real.continuous_at_const_rpow Real.continuousAt_const_rpowₓ'. -/
theorem continuousAt_const_rpow {a b : ℝ} (h : a ≠ 0) : ContinuousAt (rpow a) b :=
  by
  have : rpow a = fun x : ℝ => ((a : ℂ) ^ (x : ℂ)).re :=
    by
    ext1 x
    rw [rpow_eq_pow, rpow_def]
  rw [this]
  refine' complex.continuous_re.continuous_at.comp _
  refine' (continuousAt_const_cpow _).comp complex.continuous_of_real.continuous_at
  norm_cast
  exact h
#align real.continuous_at_const_rpow Real.continuousAt_const_rpow

/- warning: real.continuous_at_const_rpow' -> Real.continuousAt_const_rpow' is a dubious translation:
lean 3 declaration is
  forall {a : Real} {b : Real}, (Ne.{1} Real b (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (ContinuousAt.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Real.rpow a) b)
but is expected to have type
  forall {a : Real} {b : Real}, (Ne.{1} Real b (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (ContinuousAt.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Real.rpow a) b)
Case conversion may be inaccurate. Consider using '#align real.continuous_at_const_rpow' Real.continuousAt_const_rpow'ₓ'. -/
theorem continuousAt_const_rpow' {a b : ℝ} (h : b ≠ 0) : ContinuousAt (rpow a) b :=
  by
  have : rpow a = fun x : ℝ => ((a : ℂ) ^ (x : ℂ)).re :=
    by
    ext1 x
    rw [rpow_eq_pow, rpow_def]
  rw [this]
  refine' complex.continuous_re.continuous_at.comp _
  refine' (continuousAt_const_cpow' _).comp complex.continuous_of_real.continuous_at
  norm_cast
  exact h
#align real.continuous_at_const_rpow' Real.continuousAt_const_rpow'

/- warning: real.rpow_eq_nhds_of_neg -> Real.rpow_eq_nhds_of_neg is a dubious translation:
lean 3 declaration is
  forall {p : Prod.{0, 0} Real Real}, (LT.lt.{0} Real Real.hasLt (Prod.fst.{0, 0} Real Real p) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.EventuallyEq.{0, 0} (Prod.{0, 0} Real Real) Real (nhds.{0} (Prod.{0, 0} Real Real) (Prod.topologicalSpace.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) p) (fun (x : Prod.{0, 0} Real Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Prod.fst.{0, 0} Real Real x) (Prod.snd.{0, 0} Real Real x)) (fun (x : Prod.{0, 0} Real Real) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.log (Prod.fst.{0, 0} Real Real x)) (Prod.snd.{0, 0} Real Real x))) (Real.cos (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Prod.snd.{0, 0} Real Real x) Real.pi))))
but is expected to have type
  forall {p : Prod.{0, 0} Real Real}, (LT.lt.{0} Real Real.instLTReal (Prod.fst.{0, 0} Real Real p) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.EventuallyEq.{0, 0} (Prod.{0, 0} Real Real) Real (nhds.{0} (Prod.{0, 0} Real Real) (instTopologicalSpaceProd.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) p) (fun (x : Prod.{0, 0} Real Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Prod.fst.{0, 0} Real Real x) (Prod.snd.{0, 0} Real Real x)) (fun (x : Prod.{0, 0} Real Real) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.log (Prod.fst.{0, 0} Real Real x)) (Prod.snd.{0, 0} Real Real x))) (Real.cos (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Prod.snd.{0, 0} Real Real x) Real.pi))))
Case conversion may be inaccurate. Consider using '#align real.rpow_eq_nhds_of_neg Real.rpow_eq_nhds_of_negₓ'. -/
theorem rpow_eq_nhds_of_neg {p : ℝ × ℝ} (hp_fst : p.fst < 0) :
    (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) :=
  by
  suffices : ∀ᶠ x : ℝ × ℝ in 𝓝 p, x.1 < 0
  exact
    this.mono fun x hx => by
      dsimp only
      rw [rpow_def_of_neg hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_fst continuous_const) hp_fst
#align real.rpow_eq_nhds_of_neg Real.rpow_eq_nhds_of_neg

/- warning: real.rpow_eq_nhds_of_pos -> Real.rpow_eq_nhds_of_pos is a dubious translation:
lean 3 declaration is
  forall {p : Prod.{0, 0} Real Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Prod.fst.{0, 0} Real Real p)) -> (Filter.EventuallyEq.{0, 0} (Prod.{0, 0} Real Real) Real (nhds.{0} (Prod.{0, 0} Real Real) (Prod.topologicalSpace.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) p) (fun (x : Prod.{0, 0} Real Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Prod.fst.{0, 0} Real Real x) (Prod.snd.{0, 0} Real Real x)) (fun (x : Prod.{0, 0} Real Real) => Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.log (Prod.fst.{0, 0} Real Real x)) (Prod.snd.{0, 0} Real Real x))))
but is expected to have type
  forall {p : Prod.{0, 0} Real Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Prod.fst.{0, 0} Real Real p)) -> (Filter.EventuallyEq.{0, 0} (Prod.{0, 0} Real Real) Real (nhds.{0} (Prod.{0, 0} Real Real) (instTopologicalSpaceProd.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) p) (fun (x : Prod.{0, 0} Real Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Prod.fst.{0, 0} Real Real x) (Prod.snd.{0, 0} Real Real x)) (fun (x : Prod.{0, 0} Real Real) => Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.log (Prod.fst.{0, 0} Real Real x)) (Prod.snd.{0, 0} Real Real x))))
Case conversion may be inaccurate. Consider using '#align real.rpow_eq_nhds_of_pos Real.rpow_eq_nhds_of_posₓ'. -/
theorem rpow_eq_nhds_of_pos {p : ℝ × ℝ} (hp_fst : 0 < p.fst) :
    (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
  by
  suffices : ∀ᶠ x : ℝ × ℝ in 𝓝 p, 0 < x.1
  exact
    this.mono fun x hx => by
      dsimp only
      rw [rpow_def_of_pos hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_const continuous_fst) hp_fst
#align real.rpow_eq_nhds_of_pos Real.rpow_eq_nhds_of_pos

/- warning: real.continuous_at_rpow_of_ne -> Real.continuousAt_rpow_of_ne is a dubious translation:
lean 3 declaration is
  forall (p : Prod.{0, 0} Real Real), (Ne.{1} Real (Prod.fst.{0, 0} Real Real p) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Real Real) Real (Prod.topologicalSpace.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (p : Prod.{0, 0} Real Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Prod.fst.{0, 0} Real Real p) (Prod.snd.{0, 0} Real Real p)) p)
but is expected to have type
  forall (p : Prod.{0, 0} Real Real), (Ne.{1} Real (Prod.fst.{0, 0} Real Real p) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Real Real) Real (instTopologicalSpaceProd.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (p : Prod.{0, 0} Real Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Prod.fst.{0, 0} Real Real p) (Prod.snd.{0, 0} Real Real p)) p)
Case conversion may be inaccurate. Consider using '#align real.continuous_at_rpow_of_ne Real.continuousAt_rpow_of_neₓ'. -/
theorem continuousAt_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) p :=
  by
  rw [ne_iff_lt_or_gt] at hp
  cases hp
  · rw [continuousAt_congr (rpow_eq_nhds_of_neg hp)]
    refine' ContinuousAt.mul _ (continuous_cos.continuous_at.comp _)
    · refine' continuous_exp.continuous_at.comp (ContinuousAt.mul _ continuous_snd.continuous_at)
      refine' (continuous_at_log _).comp continuous_fst.continuous_at
      exact hp.ne
    · exact continuous_snd.continuous_at.mul continuousAt_const
  · rw [continuousAt_congr (rpow_eq_nhds_of_pos hp)]
    refine' continuous_exp.continuous_at.comp (ContinuousAt.mul _ continuous_snd.continuous_at)
    refine' (continuous_at_log _).comp continuous_fst.continuous_at
    exact hp.lt.ne.symm
#align real.continuous_at_rpow_of_ne Real.continuousAt_rpow_of_ne

/- warning: real.continuous_at_rpow_of_pos -> Real.continuousAt_rpow_of_pos is a dubious translation:
lean 3 declaration is
  forall (p : Prod.{0, 0} Real Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Prod.snd.{0, 0} Real Real p)) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Real Real) Real (Prod.topologicalSpace.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (p : Prod.{0, 0} Real Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Prod.fst.{0, 0} Real Real p) (Prod.snd.{0, 0} Real Real p)) p)
but is expected to have type
  forall (p : Prod.{0, 0} Real Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Prod.snd.{0, 0} Real Real p)) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Real Real) Real (instTopologicalSpaceProd.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (p : Prod.{0, 0} Real Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Prod.fst.{0, 0} Real Real p) (Prod.snd.{0, 0} Real Real p)) p)
Case conversion may be inaccurate. Consider using '#align real.continuous_at_rpow_of_pos Real.continuousAt_rpow_of_posₓ'. -/
theorem continuousAt_rpow_of_pos (p : ℝ × ℝ) (hp : 0 < p.2) :
    ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) p :=
  by
  cases' p with x y
  obtain hx | rfl := ne_or_eq x 0
  · exact continuous_at_rpow_of_ne (x, y) hx
  have A : tendsto (fun p : ℝ × ℝ => exp (log p.1 * p.2)) (𝓝[≠] 0 ×ᶠ 𝓝 y) (𝓝 0) :=
    tendsto_exp_at_bot.comp
      ((tendsto_log_nhds_within_zero.comp tendsto_fst).atBot_mul hp tendsto_snd)
  have B : tendsto (fun p : ℝ × ℝ => p.1 ^ p.2) (𝓝[≠] 0 ×ᶠ 𝓝 y) (𝓝 0) :=
    squeeze_zero_norm (fun p => abs_rpow_le_exp_log_mul p.1 p.2) A
  have C : tendsto (fun p : ℝ × ℝ => p.1 ^ p.2) (𝓝[{0}] 0 ×ᶠ 𝓝 y) (pure 0) :=
    by
    rw [nhdsWithin_singleton, tendsto_pure, pure_prod, eventually_map]
    exact (lt_mem_nhds hp).mono fun y hy => zero_rpow hy.ne'
  simpa only [← sup_prod, ← nhdsWithin_union, compl_union_self, nhdsWithin_univ, nhds_prod_eq,
    ContinuousAt, zero_rpow hp.ne'] using B.sup (C.mono_right (pure_le_nhds _))
#align real.continuous_at_rpow_of_pos Real.continuousAt_rpow_of_pos

/- warning: real.continuous_at_rpow -> Real.continuousAt_rpow is a dubious translation:
lean 3 declaration is
  forall (p : Prod.{0, 0} Real Real), (Or (Ne.{1} Real (Prod.fst.{0, 0} Real Real p) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Prod.snd.{0, 0} Real Real p))) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Real Real) Real (Prod.topologicalSpace.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (p : Prod.{0, 0} Real Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Prod.fst.{0, 0} Real Real p) (Prod.snd.{0, 0} Real Real p)) p)
but is expected to have type
  forall (p : Prod.{0, 0} Real Real), (Or (Ne.{1} Real (Prod.fst.{0, 0} Real Real p) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Prod.snd.{0, 0} Real Real p))) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Real Real) Real (instTopologicalSpaceProd.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (p : Prod.{0, 0} Real Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Prod.fst.{0, 0} Real Real p) (Prod.snd.{0, 0} Real Real p)) p)
Case conversion may be inaccurate. Consider using '#align real.continuous_at_rpow Real.continuousAt_rpowₓ'. -/
theorem continuousAt_rpow (p : ℝ × ℝ) (h : p.1 ≠ 0 ∨ 0 < p.2) :
    ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) p :=
  h.elim (fun h => continuousAt_rpow_of_ne p h) fun h => continuousAt_rpow_of_pos p h
#align real.continuous_at_rpow Real.continuousAt_rpow

/- warning: real.continuous_at_rpow_const -> Real.continuousAt_rpow_const is a dubious translation:
lean 3 declaration is
  forall (x : Real) (q : Real), (Or (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) q)) -> (ContinuousAt.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x q) x)
but is expected to have type
  forall (x : Real) (q : Real), (Or (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) q)) -> (ContinuousAt.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x q) x)
Case conversion may be inaccurate. Consider using '#align real.continuous_at_rpow_const Real.continuousAt_rpow_constₓ'. -/
theorem continuousAt_rpow_const (x : ℝ) (q : ℝ) (h : x ≠ 0 ∨ 0 < q) :
    ContinuousAt (fun x : ℝ => x ^ q) x :=
  by
  change ContinuousAt ((fun p : ℝ × ℝ => p.1 ^ p.2) ∘ fun y : ℝ => (y, q)) x
  apply ContinuousAt.comp
  · exact continuous_at_rpow (x, q) h
  · exact (continuous_id'.prod_mk continuous_const).ContinuousAt
#align real.continuous_at_rpow_const Real.continuousAt_rpow_const

end Real

section

variable {α : Type _}

/- warning: filter.tendsto.rpow -> Filter.Tendsto.rpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real} {x : Real} {y : Real}, (Filter.Tendsto.{u1, 0} α Real f l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) x)) -> (Filter.Tendsto.{u1, 0} α Real g l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) y)) -> (Or (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y)) -> (Filter.Tendsto.{u1, 0} α Real (fun (t : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (f t) (g t)) l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x y)))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real} {g : α -> Real} {x : Real} {y : Real}, (Filter.Tendsto.{u1, 0} α Real f l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) x)) -> (Filter.Tendsto.{u1, 0} α Real g l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) y)) -> (Or (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y)) -> (Filter.Tendsto.{u1, 0} α Real (fun (t : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (f t) (g t)) l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x y)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.rpow Filter.Tendsto.rpowₓ'. -/
theorem Filter.Tendsto.rpow {l : Filter α} {f g : α → ℝ} {x y : ℝ} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) (h : x ≠ 0 ∨ 0 < y) : Tendsto (fun t => f t ^ g t) l (𝓝 (x ^ y)) :=
  (Real.continuousAt_rpow (x, y) h).Tendsto.comp (hf.prod_mk_nhds hg)
#align filter.tendsto.rpow Filter.Tendsto.rpow

/- warning: filter.tendsto.rpow_const -> Filter.Tendsto.rpow_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real} {x : Real} {p : Real}, (Filter.Tendsto.{u1, 0} α Real f l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) x)) -> (Or (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p)) -> (Filter.Tendsto.{u1, 0} α Real (fun (a : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (f a) p) l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x p)))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {f : α -> Real} {x : Real} {p : Real}, (Filter.Tendsto.{u1, 0} α Real f l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) x)) -> (Or (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p)) -> (Filter.Tendsto.{u1, 0} α Real (fun (a : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (f a) p) l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x p)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.rpow_const Filter.Tendsto.rpow_constₓ'. -/
theorem Filter.Tendsto.rpow_const {l : Filter α} {f : α → ℝ} {x p : ℝ} (hf : Tendsto f l (𝓝 x))
    (h : x ≠ 0 ∨ 0 ≤ p) : Tendsto (fun a => f a ^ p) l (𝓝 (x ^ p)) :=
  if h0 : 0 = p then h0 ▸ by simp [tendsto_const_nhds]
  else hf.rpow tendsto_const_nhds (h.imp id fun h' => h'.lt_of_ne h0)
#align filter.tendsto.rpow_const Filter.Tendsto.rpow_const

variable [TopologicalSpace α] {f g : α → ℝ} {s : Set α} {x : α} {p : ℝ}

/- warning: continuous_at.rpow -> ContinuousAt.rpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {g : α -> Real} {x : α}, (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f x) -> (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g x) -> (Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (g x))) -> (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (t : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (f t) (g t)) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {g : α -> Real} {x : α}, (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f x) -> (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g x) -> (Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (g x))) -> (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (t : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (f t) (g t)) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.rpow ContinuousAt.rpowₓ'. -/
theorem ContinuousAt.rpow (hf : ContinuousAt f x) (hg : ContinuousAt g x) (h : f x ≠ 0 ∨ 0 < g x) :
    ContinuousAt (fun t => f t ^ g t) x :=
  hf.rpow hg h
#align continuous_at.rpow ContinuousAt.rpow

/- warning: continuous_within_at.rpow -> ContinuousWithinAt.rpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {g : α -> Real} {s : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f s x) -> (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g s x) -> (Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (g x))) -> (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (t : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (f t) (g t)) s x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {g : α -> Real} {s : Set.{u1} α} {x : α}, (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f s x) -> (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g s x) -> (Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (g x))) -> (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (t : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (f t) (g t)) s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.rpow ContinuousWithinAt.rpowₓ'. -/
theorem ContinuousWithinAt.rpow (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
    (h : f x ≠ 0 ∨ 0 < g x) : ContinuousWithinAt (fun t => f t ^ g t) s x :=
  hf.rpow hg h
#align continuous_within_at.rpow ContinuousWithinAt.rpow

/- warning: continuous_on.rpow -> ContinuousOn.rpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {g : α -> Real} {s : Set.{u1} α}, (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f s) -> (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (g x)))) -> (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (t : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (f t) (g t)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {g : α -> Real} {s : Set.{u1} α}, (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f s) -> (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g s) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (g x)))) -> (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (t : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (f t) (g t)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.rpow ContinuousOn.rpowₓ'. -/
theorem ContinuousOn.rpow (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h : ∀ x ∈ s, f x ≠ 0 ∨ 0 < g x) : ContinuousOn (fun t => f t ^ g t) s := fun t ht =>
  (hf t ht).rpow (hg t ht) (h t ht)
#align continuous_on.rpow ContinuousOn.rpow

/- warning: continuous.rpow -> Continuous.rpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {g : α -> Real}, (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (forall (x : α), Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (g x))) -> (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {g : α -> Real}, (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (forall (x : α), Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (g x))) -> (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align continuous.rpow Continuous.rpowₓ'. -/
theorem Continuous.rpow (hf : Continuous f) (hg : Continuous g) (h : ∀ x, f x ≠ 0 ∨ 0 < g x) :
    Continuous fun x => f x ^ g x :=
  continuous_iff_continuousAt.2 fun x => hf.ContinuousAt.rpow hg.ContinuousAt (h x)
#align continuous.rpow Continuous.rpow

/- warning: continuous_within_at.rpow_const -> ContinuousWithinAt.rpow_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {s : Set.{u1} α} {x : α} {p : Real}, (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f s x) -> (Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p)) -> (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (f x) p) s x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {s : Set.{u1} α} {x : α} {p : Real}, (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f s x) -> (Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p)) -> (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (f x) p) s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.rpow_const ContinuousWithinAt.rpow_constₓ'. -/
theorem ContinuousWithinAt.rpow_const (hf : ContinuousWithinAt f s x) (h : f x ≠ 0 ∨ 0 ≤ p) :
    ContinuousWithinAt (fun x => f x ^ p) s x :=
  hf.rpow_const h
#align continuous_within_at.rpow_const ContinuousWithinAt.rpow_const

/- warning: continuous_at.rpow_const -> ContinuousAt.rpow_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {x : α} {p : Real}, (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f x) -> (Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p)) -> (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (f x) p) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {x : α} {p : Real}, (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f x) -> (Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p)) -> (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (f x) p) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.rpow_const ContinuousAt.rpow_constₓ'. -/
theorem ContinuousAt.rpow_const (hf : ContinuousAt f x) (h : f x ≠ 0 ∨ 0 ≤ p) :
    ContinuousAt (fun x => f x ^ p) x :=
  hf.rpow_const h
#align continuous_at.rpow_const ContinuousAt.rpow_const

/- warning: continuous_on.rpow_const -> ContinuousOn.rpow_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {s : Set.{u1} α} {p : Real}, (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p))) -> (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (f x) p) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {s : Set.{u1} α} {p : Real}, (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f s) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p))) -> (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (f x) p) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.rpow_const ContinuousOn.rpow_constₓ'. -/
theorem ContinuousOn.rpow_const (hf : ContinuousOn f s) (h : ∀ x ∈ s, f x ≠ 0 ∨ 0 ≤ p) :
    ContinuousOn (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const (h x hx)
#align continuous_on.rpow_const ContinuousOn.rpow_const

/- warning: continuous.rpow_const -> Continuous.rpow_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {p : Real}, (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (forall (x : α), Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p)) -> (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (f x) p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {p : Real}, (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (forall (x : α), Or (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p)) -> (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (f x) p))
Case conversion may be inaccurate. Consider using '#align continuous.rpow_const Continuous.rpow_constₓ'. -/
theorem Continuous.rpow_const (hf : Continuous f) (h : ∀ x, f x ≠ 0 ∨ 0 ≤ p) :
    Continuous fun x => f x ^ p :=
  continuous_iff_continuousAt.2 fun x => hf.ContinuousAt.rpow_const (h x)
#align continuous.rpow_const Continuous.rpow_const

end

end RpowLimits

/-! ## Continuity results for `cpow`, part II

These results involve relating real and complex powers, so cannot be done higher up.
-/


section CpowLimits2

namespace Complex

/- warning: complex.continuous_at_cpow_zero_of_re_pos -> Complex.continuousAt_cpow_zero_of_re_pos is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re z)) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Complex Complex) Complex (Prod.topologicalSpace.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField))))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : Prod.{0, 0} Complex Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (Prod.fst.{0, 0} Complex Complex x) (Prod.snd.{0, 0} Complex Complex x)) (Prod.mk.{0, 0} Complex Complex (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))) z))
but is expected to have type
  forall {z : Complex}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re z)) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Complex Complex) Complex (instTopologicalSpaceProd.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex))))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : Prod.{0, 0} Complex Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Prod.fst.{0, 0} Complex Complex x) (Prod.snd.{0, 0} Complex Complex x)) (Prod.mk.{0, 0} Complex Complex (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)) z))
Case conversion may be inaccurate. Consider using '#align complex.continuous_at_cpow_zero_of_re_pos Complex.continuousAt_cpow_zero_of_re_posₓ'. -/
/-- See also `continuous_at_cpow` and `complex.continuous_at_cpow_of_re_pos`. -/
theorem continuousAt_cpow_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) (0, z) :=
  by
  have hz₀ : z ≠ 0 := ne_of_apply_ne re hz.ne'
  rw [ContinuousAt, zero_cpow hz₀, tendsto_zero_iff_norm_tendsto_zero]
  refine' squeeze_zero (fun _ => norm_nonneg _) (fun _ => abs_cpow_le _ _) _
  simp only [div_eq_mul_inv, ← Real.exp_neg]
  refine' tendsto.zero_mul_is_bounded_under_le _ _
  ·
    convert(continuous_fst.norm.tendsto _).rpow ((continuous_re.comp continuous_snd).Tendsto _)
          _ <;>
      simp [hz, Real.zero_rpow hz.ne']
  · simp only [(· ∘ ·), Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases exists_gt (|im z|) with ⟨C, hC⟩
    refine' ⟨Real.exp (π * C), eventually_map.2 _⟩
    refine'
      (((continuous_im.comp continuous_snd).abs.Tendsto (_, z)).Eventually (gt_mem_nhds hC)).mono
        fun z hz => Real.exp_le_exp.2 <| (neg_le_abs_self _).trans _
    rw [_root_.abs_mul]
    exact
      mul_le_mul (abs_le.2 ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩) hz.le (_root_.abs_nonneg _)
        real.pi_pos.le
#align complex.continuous_at_cpow_zero_of_re_pos Complex.continuousAt_cpow_zero_of_re_pos

/- warning: complex.continuous_at_cpow_of_re_pos -> Complex.continuousAt_cpow_of_re_pos is a dubious translation:
lean 3 declaration is
  forall {p : Prod.{0, 0} Complex Complex}, (Or (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re (Prod.fst.{0, 0} Complex Complex p))) (Ne.{1} Real (Complex.im (Prod.fst.{0, 0} Complex Complex p)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re (Prod.snd.{0, 0} Complex Complex p))) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Complex Complex) Complex (Prod.topologicalSpace.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField))))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : Prod.{0, 0} Complex Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (Prod.fst.{0, 0} Complex Complex x) (Prod.snd.{0, 0} Complex Complex x)) p)
but is expected to have type
  forall {p : Prod.{0, 0} Complex Complex}, (Or (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re (Prod.fst.{0, 0} Complex Complex p))) (Ne.{1} Real (Complex.im (Prod.fst.{0, 0} Complex Complex p)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re (Prod.snd.{0, 0} Complex Complex p))) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Complex Complex) Complex (instTopologicalSpaceProd.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex))))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : Prod.{0, 0} Complex Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Prod.fst.{0, 0} Complex Complex x) (Prod.snd.{0, 0} Complex Complex x)) p)
Case conversion may be inaccurate. Consider using '#align complex.continuous_at_cpow_of_re_pos Complex.continuousAt_cpow_of_re_posₓ'. -/
/-- See also `continuous_at_cpow` for a version that assumes `p.1 ≠ 0` but makes no
assumptions about `p.2`. -/
theorem continuousAt_cpow_of_re_pos {p : ℂ × ℂ} (h₁ : 0 ≤ p.1.re ∨ p.1.im ≠ 0) (h₂ : 0 < p.2.re) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) p :=
  by
  cases' p with z w
  rw [← not_lt_zero_iff, lt_iff_le_and_ne, not_and_or, Ne.def, Classical.not_not,
    not_le_zero_iff] at h₁
  rcases h₁ with (h₁ | (rfl : z = 0))
  exacts[continuousAt_cpow h₁, continuous_at_cpow_zero_of_re_pos h₂]
#align complex.continuous_at_cpow_of_re_pos Complex.continuousAt_cpow_of_re_pos

/- warning: complex.continuous_at_cpow_const_of_re_pos -> Complex.continuousAt_cpow_const_of_re_pos is a dubious translation:
lean 3 declaration is
  forall {z : Complex} {w : Complex}, (Or (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re z)) (Ne.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re w)) -> (ContinuousAt.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x w) z)
but is expected to have type
  forall {z : Complex} {w : Complex}, (Or (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re z)) (Ne.{1} Real (Complex.im z) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re w)) -> (ContinuousAt.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x w) z)
Case conversion may be inaccurate. Consider using '#align complex.continuous_at_cpow_const_of_re_pos Complex.continuousAt_cpow_const_of_re_posₓ'. -/
/-- See also `continuous_at_cpow_const` for a version that assumes `z ≠ 0` but makes no
assumptions about `w`. -/
theorem continuousAt_cpow_const_of_re_pos {z w : ℂ} (hz : 0 ≤ re z ∨ im z ≠ 0) (hw : 0 < re w) :
    ContinuousAt (fun x => x ^ w) z :=
  Tendsto.comp (@continuousAt_cpow_of_re_pos (z, w) hz hw) (continuousAt_id.Prod continuousAt_const)
#align complex.continuous_at_cpow_const_of_re_pos Complex.continuousAt_cpow_const_of_re_pos

/- warning: complex.continuous_at_of_real_cpow -> Complex.continuousAt_of_real_cpow is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Complex), (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re y)) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Real Complex) Complex (Prod.topologicalSpace.{0, 0} Real Complex (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField))))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (p : Prod.{0, 0} Real Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) (Prod.fst.{0, 0} Real Complex p)) (Prod.snd.{0, 0} Real Complex p)) (Prod.mk.{0, 0} Real Complex x y))
but is expected to have type
  forall (x : Real) (y : Complex), (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re y)) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (ContinuousAt.{0, 0} (Prod.{0, 0} Real Complex) Complex (instTopologicalSpaceProd.{0, 0} Real Complex (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex))))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (p : Prod.{0, 0} Real Complex) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Complex.ofReal' (Prod.fst.{0, 0} Real Complex p)) (Prod.snd.{0, 0} Real Complex p)) (Prod.mk.{0, 0} Real Complex x y))
Case conversion may be inaccurate. Consider using '#align complex.continuous_at_of_real_cpow Complex.continuousAt_of_real_cpowₓ'. -/
/-- Continuity of `(x, y) ↦ x ^ y` as a function on `ℝ × ℂ`. -/
theorem continuousAt_of_real_cpow (x : ℝ) (y : ℂ) (h : 0 < y.re ∨ x ≠ 0) :
    ContinuousAt (fun p => ↑p.1 ^ p.2 : ℝ × ℂ → ℂ) (x, y) :=
  by
  rcases lt_trichotomy 0 x with (hx | rfl | hx)
  · -- x > 0 : easy case
    have : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) (x, y) :=
      continuous_of_real.continuous_at.prod_map continuousAt_id
    refine' (continuousAt_cpow (Or.inl _)).comp this
    rwa [of_real_re]
  · -- x = 0 : reduce to continuous_at_cpow_zero_of_re_pos
    have A : ContinuousAt (fun p => p.1 ^ p.2 : ℂ × ℂ → ℂ) ⟨↑(0 : ℝ), y⟩ :=
      by
      rw [of_real_zero]
      apply continuous_at_cpow_zero_of_re_pos
      tauto
    have B : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) ⟨0, y⟩ :=
      continuous_of_real.continuous_at.prod_map continuousAt_id
    exact @ContinuousAt.comp (ℝ × ℂ) (ℂ × ℂ) ℂ _ _ _ _ (fun p => ⟨↑p.1, p.2⟩) ⟨0, y⟩ A B
  · -- x < 0 : difficult case
    suffices ContinuousAt (fun p => (-↑p.1) ^ p.2 * exp (π * I * p.2) : ℝ × ℂ → ℂ) (x, y)
      by
      refine' this.congr (eventually_of_mem (prod_mem_nhds (Iio_mem_nhds hx) univ_mem) _)
      exact fun p hp => (of_real_cpow_of_nonpos (le_of_lt hp.1) p.2).symm
    have A : ContinuousAt (fun p => ⟨-↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) (x, y) :=
      ContinuousAt.prod_map continuous_of_real.continuous_at.neg continuousAt_id
    apply ContinuousAt.mul
    · refine' (continuousAt_cpow (Or.inl _)).comp A
      rwa [neg_re, of_real_re, neg_pos]
    · exact (continuous_exp.comp (continuous_const.mul continuous_snd)).ContinuousAt
#align complex.continuous_at_of_real_cpow Complex.continuousAt_of_real_cpow

/- warning: complex.continuous_at_of_real_cpow_const -> Complex.continuousAt_of_real_cpow_const is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Complex), (Or (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re y)) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (ContinuousAt.{0, 0} Real Complex (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (a : Real) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) a) y) x)
but is expected to have type
  forall (x : Real) (y : Complex), (Or (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re y)) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (ContinuousAt.{0, 0} Real Complex (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (a : Real) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Complex.ofReal' a) y) x)
Case conversion may be inaccurate. Consider using '#align complex.continuous_at_of_real_cpow_const Complex.continuousAt_of_real_cpow_constₓ'. -/
theorem continuousAt_of_real_cpow_const (x : ℝ) (y : ℂ) (h : 0 < y.re ∨ x ≠ 0) :
    ContinuousAt (fun a => a ^ y : ℝ → ℂ) x :=
  @ContinuousAt.comp _ _ _ _ _ _ _ _ x (continuousAt_of_real_cpow x y h)
    (continuous_id.prod_mk continuous_const).ContinuousAt
#align complex.continuous_at_of_real_cpow_const Complex.continuousAt_of_real_cpow_const

/- warning: complex.continuous_of_real_cpow_const -> Complex.continuous_of_real_cpow_const is a dubious translation:
lean 3 declaration is
  forall {y : Complex}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Complex.re y)) -> (Continuous.{0, 0} Real Complex (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (fun (x : Real) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) x) y))
but is expected to have type
  forall {y : Complex}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Complex.re y)) -> (Continuous.{0, 0} Real Complex (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (fun (x : Real) => HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Complex.ofReal' x) y))
Case conversion may be inaccurate. Consider using '#align complex.continuous_of_real_cpow_const Complex.continuous_of_real_cpow_constₓ'. -/
theorem continuous_of_real_cpow_const {y : ℂ} (hs : 0 < y.re) :
    Continuous (fun x => x ^ y : ℝ → ℂ) :=
  continuous_iff_continuousAt.mpr fun x => continuousAt_of_real_cpow_const x y (Or.inl hs)
#align complex.continuous_of_real_cpow_const Complex.continuous_of_real_cpow_const

end Complex

end CpowLimits2

/-! ## Limits and continuity for `ℝ≥0` powers -/


namespace NNReal

/- warning: nnreal.continuous_at_rpow -> NNReal.continuousAt_rpow is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : Real}, (Or (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y)) -> (ContinuousAt.{0, 0} (Prod.{0, 0} NNReal Real) NNReal (Prod.topologicalSpace.{0, 0} NNReal Real NNReal.topologicalSpace (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) NNReal.topologicalSpace (fun (p : Prod.{0, 0} NNReal Real) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) (Prod.fst.{0, 0} NNReal Real p) (Prod.snd.{0, 0} NNReal Real p)) (Prod.mk.{0, 0} NNReal Real x y))
but is expected to have type
  forall {x : NNReal} {y : Real}, (Or (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y)) -> (ContinuousAt.{0, 0} (Prod.{0, 0} NNReal Real) NNReal (instTopologicalSpaceProd.{0, 0} NNReal Real NNReal.instTopologicalSpaceNNReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) NNReal.instTopologicalSpaceNNReal (fun (p : Prod.{0, 0} NNReal Real) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) (Prod.fst.{0, 0} NNReal Real p) (Prod.snd.{0, 0} NNReal Real p)) (Prod.mk.{0, 0} NNReal Real x y))
Case conversion may be inaccurate. Consider using '#align nnreal.continuous_at_rpow NNReal.continuousAt_rpowₓ'. -/
theorem continuousAt_rpow {x : ℝ≥0} {y : ℝ} (h : x ≠ 0 ∨ 0 < y) :
    ContinuousAt (fun p : ℝ≥0 × ℝ => p.1 ^ p.2) (x, y) :=
  by
  have :
    (fun p : ℝ≥0 × ℝ => p.1 ^ p.2) =
      Real.toNNReal ∘ (fun p : ℝ × ℝ => p.1 ^ p.2) ∘ fun p : ℝ≥0 × ℝ => (p.1.1, p.2) :=
    by
    ext p
    rw [coe_rpow, Real.coe_toNNReal _ (Real.rpow_nonneg_of_nonneg p.1.2 _)]
    rfl
  rw [this]
  refine' continuous_real_to_nnreal.continuous_at.comp (ContinuousAt.comp _ _)
  · apply Real.continuousAt_rpow
    simp only [Ne.def] at h
    rw [← NNReal.coe_eq_zero x] at h
    exact h
  · exact ((continuous_subtype_val.comp continuous_fst).prod_mk continuous_snd).ContinuousAt
#align nnreal.continuous_at_rpow NNReal.continuousAt_rpow

/- warning: nnreal.eventually_pow_one_div_le -> NNReal.eventually_pow_one_div_le is a dubious translation:
lean 3 declaration is
  forall (x : NNReal) {y : NNReal}, (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) y) -> (Filter.Eventually.{0} Nat (fun (n : Nat) => LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))) y) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))))
but is expected to have type
  forall (x : NNReal) {y : NNReal}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) y) -> (Filter.Eventually.{0} Nat (fun (n : Nat) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Nat.cast.{0} Real Real.natCast n))) y) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))))
Case conversion may be inaccurate. Consider using '#align nnreal.eventually_pow_one_div_le NNReal.eventually_pow_one_div_leₓ'. -/
theorem eventually_pow_one_div_le (x : ℝ≥0) {y : ℝ≥0} (hy : 1 < y) :
    ∀ᶠ n : ℕ in atTop, x ^ (1 / n : ℝ) ≤ y :=
  by
  obtain ⟨m, hm⟩ := add_one_pow_unbounded_of_pos x (tsub_pos_of_lt hy)
  rw [tsub_add_cancel_of_le hy.le] at hm
  refine' eventually_at_top.2 ⟨m + 1, fun n hn => _⟩
  simpa only [NNReal.rpow_one_div_le_iff (Nat.cast_pos.2 <| m.succ_pos.trans_le hn),
    NNReal.rpow_nat_cast] using hm.le.trans (pow_le_pow hy.le (m.le_succ.trans hn))
#align nnreal.eventually_pow_one_div_le NNReal.eventually_pow_one_div_le

end NNReal

open Filter

/- warning: filter.tendsto.nnrpow -> Filter.Tendsto.nnrpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {u : α -> NNReal} {v : α -> Real} {x : NNReal} {y : Real}, (Filter.Tendsto.{u1, 0} α NNReal u f (nhds.{0} NNReal NNReal.topologicalSpace x)) -> (Filter.Tendsto.{u1, 0} α Real v f (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) y)) -> (Or (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y)) -> (Filter.Tendsto.{u1, 0} α NNReal (fun (a : α) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) (u a) (v a)) f (nhds.{0} NNReal NNReal.topologicalSpace (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {u : α -> NNReal} {v : α -> Real} {x : NNReal} {y : Real}, (Filter.Tendsto.{u1, 0} α NNReal u f (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal x)) -> (Filter.Tendsto.{u1, 0} α Real v f (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) y)) -> (Or (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y)) -> (Filter.Tendsto.{u1, 0} α NNReal (fun (a : α) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) (u a) (v a)) f (nhds.{0} NNReal NNReal.instTopologicalSpaceNNReal (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.nnrpow Filter.Tendsto.nnrpowₓ'. -/
theorem Filter.Tendsto.nnrpow {α : Type _} {f : Filter α} {u : α → ℝ≥0} {v : α → ℝ} {x : ℝ≥0}
    {y : ℝ} (hx : Tendsto u f (𝓝 x)) (hy : Tendsto v f (𝓝 y)) (h : x ≠ 0 ∨ 0 < y) :
    Tendsto (fun a => u a ^ v a) f (𝓝 (x ^ y)) :=
  Tendsto.comp (NNReal.continuousAt_rpow h) (hx.prod_mk_nhds hy)
#align filter.tendsto.nnrpow Filter.Tendsto.nnrpow

namespace NNReal

/- warning: nnreal.continuous_at_rpow_const -> NNReal.continuousAt_rpow_const is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : Real}, (Or (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y)) -> (ContinuousAt.{0, 0} NNReal NNReal NNReal.topologicalSpace NNReal.topologicalSpace (fun (z : NNReal) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) z y) x)
but is expected to have type
  forall {x : NNReal} {y : Real}, (Or (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y)) -> (ContinuousAt.{0, 0} NNReal NNReal NNReal.instTopologicalSpaceNNReal NNReal.instTopologicalSpaceNNReal (fun (z : NNReal) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) z y) x)
Case conversion may be inaccurate. Consider using '#align nnreal.continuous_at_rpow_const NNReal.continuousAt_rpow_constₓ'. -/
theorem continuousAt_rpow_const {x : ℝ≥0} {y : ℝ} (h : x ≠ 0 ∨ 0 ≤ y) :
    ContinuousAt (fun z => z ^ y) x :=
  h.elim (fun h => tendsto_id.nnrpow tendsto_const_nhds (Or.inl h)) fun h =>
    h.eq_or_lt.elim (fun h => h ▸ by simp only [rpow_zero, continuousAt_const]) fun h =>
      tendsto_id.nnrpow tendsto_const_nhds (Or.inr h)
#align nnreal.continuous_at_rpow_const NNReal.continuousAt_rpow_const

/- warning: nnreal.continuous_rpow_const -> NNReal.continuous_rpow_const is a dubious translation:
lean 3 declaration is
  forall {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Continuous.{0, 0} NNReal NNReal NNReal.topologicalSpace NNReal.topologicalSpace (fun (x : NNReal) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) x y))
but is expected to have type
  forall {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Continuous.{0, 0} NNReal NNReal NNReal.instTopologicalSpaceNNReal NNReal.instTopologicalSpaceNNReal (fun (x : NNReal) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) x y))
Case conversion may be inaccurate. Consider using '#align nnreal.continuous_rpow_const NNReal.continuous_rpow_constₓ'. -/
theorem continuous_rpow_const {y : ℝ} (h : 0 ≤ y) : Continuous fun x : ℝ≥0 => x ^ y :=
  continuous_iff_continuousAt.2 fun x => continuousAt_rpow_const (Or.inr h)
#align nnreal.continuous_rpow_const NNReal.continuous_rpow_const

end NNReal

/-! ## Continuity for `ℝ≥0∞` powers -/


namespace ENNReal

/- warning: ennreal.eventually_pow_one_div_le -> ENNReal.eventually_pow_one_div_le is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {y : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) y) -> (Filter.Eventually.{0} Nat (fun (n : Nat) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))) y) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))))
but is expected to have type
  forall {x : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {y : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) y) -> (Filter.Eventually.{0} Nat (fun (n : Nat) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Nat.cast.{0} Real Real.natCast n))) y) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))))
Case conversion may be inaccurate. Consider using '#align ennreal.eventually_pow_one_div_le ENNReal.eventually_pow_one_div_leₓ'. -/
theorem eventually_pow_one_div_le {x : ℝ≥0∞} (hx : x ≠ ∞) {y : ℝ≥0∞} (hy : 1 < y) :
    ∀ᶠ n : ℕ in atTop, x ^ (1 / n : ℝ) ≤ y :=
  by
  lift x to ℝ≥0 using hx
  by_cases y = ∞
  · exact eventually_of_forall fun n => h.symm ▸ le_top
  · lift y to ℝ≥0 using h
    have := NNReal.eventually_pow_one_div_le x (by exact_mod_cast hy : 1 < y)
    refine' this.congr (eventually_of_forall fun n => _)
    rw [coe_rpow_of_nonneg x (by positivity : 0 ≤ (1 / n : ℝ)), coe_le_coe]
#align ennreal.eventually_pow_one_div_le ENNReal.eventually_pow_one_div_le

private theorem continuous_at_rpow_const_of_pos {x : ℝ≥0∞} {y : ℝ} (h : 0 < y) :
    ContinuousAt (fun a : ℝ≥0∞ => a ^ y) x :=
  by
  by_cases hx : x = ⊤
  · rw [hx, ContinuousAt]
    convert tendsto_rpow_atTop h
    simp [h]
  lift x to ℝ≥0 using hx
  rw [continuous_at_coe_iff]
  convert continuous_coe.continuous_at.comp (NNReal.continuousAt_rpow_const (Or.inr h.le)) using 1
  ext1 x
  simp [coe_rpow_of_nonneg _ h.le]
#align ennreal.continuous_at_rpow_const_of_pos ennreal.continuous_at_rpow_const_of_pos

/- warning: ennreal.continuous_rpow_const -> ENNReal.continuous_rpow_const is a dubious translation:
lean 3 declaration is
  forall {y : Real}, Continuous.{0, 0} ENNReal ENNReal ENNReal.topologicalSpace ENNReal.topologicalSpace (fun (a : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) a y)
but is expected to have type
  forall {y : Real}, Continuous.{0, 0} ENNReal ENNReal ENNReal.instTopologicalSpaceENNReal ENNReal.instTopologicalSpaceENNReal (fun (a : ENNReal) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) a y)
Case conversion may be inaccurate. Consider using '#align ennreal.continuous_rpow_const ENNReal.continuous_rpow_constₓ'. -/
@[continuity]
theorem continuous_rpow_const {y : ℝ} : Continuous fun a : ℝ≥0∞ => a ^ y :=
  by
  apply continuous_iff_continuousAt.2 fun x => _
  rcases lt_trichotomy 0 y with (hy | rfl | hy)
  · exact continuous_at_rpow_const_of_pos hy
  · simp only [rpow_zero]
    exact continuousAt_const
  · obtain ⟨z, hz⟩ : ∃ z, y = -z := ⟨-y, (neg_neg _).symm⟩
    have z_pos : 0 < z := by simpa [hz] using hy
    simp_rw [hz, rpow_neg]
    exact continuous_inv.continuous_at.comp (continuous_at_rpow_const_of_pos z_pos)
#align ennreal.continuous_rpow_const ENNReal.continuous_rpow_const

/- warning: ennreal.tendsto_const_mul_rpow_nhds_zero_of_pos -> ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos is a dubious translation:
lean 3 declaration is
  forall {c : ENNReal}, (Ne.{1} ENNReal c (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Filter.Tendsto.{0, 0} ENNReal ENNReal (fun (x : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) c (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) x y)) (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))))
but is expected to have type
  forall {c : ENNReal}, (Ne.{1} ENNReal c (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Filter.Tendsto.{0, 0} ENNReal ENNReal (fun (x : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) c (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) x y)) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))))
Case conversion may be inaccurate. Consider using '#align ennreal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.tendsto_const_mul_rpow_nhds_zero_of_posₓ'. -/
theorem tendsto_const_mul_rpow_nhds_zero_of_pos {c : ℝ≥0∞} (hc : c ≠ ∞) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ≥0∞ => c * x ^ y) (𝓝 0) (𝓝 0) :=
  by
  convert ENNReal.Tendsto.const_mul (ennreal.continuous_rpow_const.tendsto 0) _
  · simp [hy]
  · exact Or.inr hc
#align ennreal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos

end ENNReal

/- warning: filter.tendsto.ennrpow_const -> Filter.Tendsto.ennrpow_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal} (r : Real), (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.topologicalSpace a)) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (x : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (m x) r) f (nhds.{0} ENNReal ENNReal.topologicalSpace (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) a r)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {m : α -> ENNReal} {a : ENNReal} (r : Real), (Filter.Tendsto.{u1, 0} α ENNReal m f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal a)) -> (Filter.Tendsto.{u1, 0} α ENNReal (fun (x : α) => HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (m x) r) f (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) a r)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.ennrpow_const Filter.Tendsto.ennrpow_constₓ'. -/
theorem Filter.Tendsto.ennrpow_const {α : Type _} {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} (r : ℝ)
    (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ r) f (𝓝 (a ^ r)) :=
  (ENNReal.continuous_rpow_const.Tendsto a).comp hm
#align filter.tendsto.ennrpow_const Filter.Tendsto.ennrpow_const

