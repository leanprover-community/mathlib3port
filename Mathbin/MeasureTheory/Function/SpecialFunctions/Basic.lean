/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.function.special_functions.basic
! leanprover-community/mathlib commit 198161d833f2c01498c39c266b0b3dbe2c7a8c07
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Pow
import Mathbin.MeasureTheory.Constructions.BorelSpace

/-!
# Measurability of real and complex functions

We show that most standard real and complex functions are measurable, notably `exp`, `cos`, `sin`,
`cosh`, `sinh`, `log`, `pow`, `arcsin`, `arccos`.

See also `measure_theory.function.special_functions.arctan` and
`measure_theory.function.special_functions.inner`, which have been split off to minimize imports.
-/


noncomputable section

open Nnreal Ennreal

namespace Real

@[measurability]
theorem measurableExp : Measurable exp :=
  continuous_exp.Measurable
#align real.measurable_exp Real.measurableExp

@[measurability]
theorem measurableLog : Measurable log :=
  measurableOfMeasurableOnComplSingleton 0 <|
    Continuous.measurable <| continuous_on_iff_continuous_restrict.1 continuous_on_log
#align real.measurable_log Real.measurableLog

@[measurability]
theorem measurableSin : Measurable sin :=
  continuous_sin.Measurable
#align real.measurable_sin Real.measurableSin

@[measurability]
theorem measurableCos : Measurable cos :=
  continuous_cos.Measurable
#align real.measurable_cos Real.measurableCos

@[measurability]
theorem measurableSinh : Measurable sinh :=
  continuous_sinh.Measurable
#align real.measurable_sinh Real.measurableSinh

@[measurability]
theorem measurableCosh : Measurable cosh :=
  continuous_cosh.Measurable
#align real.measurable_cosh Real.measurableCosh

@[measurability]
theorem measurableArcsin : Measurable arcsin :=
  continuous_arcsin.Measurable
#align real.measurable_arcsin Real.measurableArcsin

@[measurability]
theorem measurableArccos : Measurable arccos :=
  continuous_arccos.Measurable
#align real.measurable_arccos Real.measurableArccos

end Real

namespace Complex

@[measurability]
theorem measurableRe : Measurable re :=
  continuous_re.Measurable
#align complex.measurable_re Complex.measurableRe

@[measurability]
theorem measurableIm : Measurable im :=
  continuous_im.Measurable
#align complex.measurable_im Complex.measurableIm

@[measurability]
theorem measurableOfReal : Measurable (coe : ℝ → ℂ) :=
  continuous_of_real.Measurable
#align complex.measurable_of_real Complex.measurableOfReal

@[measurability]
theorem measurableExp : Measurable exp :=
  continuous_exp.Measurable
#align complex.measurable_exp Complex.measurableExp

@[measurability]
theorem measurableSin : Measurable sin :=
  continuous_sin.Measurable
#align complex.measurable_sin Complex.measurableSin

@[measurability]
theorem measurableCos : Measurable cos :=
  continuous_cos.Measurable
#align complex.measurable_cos Complex.measurableCos

@[measurability]
theorem measurableSinh : Measurable sinh :=
  continuous_sinh.Measurable
#align complex.measurable_sinh Complex.measurableSinh

@[measurability]
theorem measurableCosh : Measurable cosh :=
  continuous_cosh.Measurable
#align complex.measurable_cosh Complex.measurableCosh

@[measurability]
theorem measurableArg : Measurable arg :=
  have A : Measurable fun x : ℂ => Real.arcsin (x.im / x.abs) :=
    Real.measurableArcsin.comp (measurableIm.div measurableNorm)
  have B : Measurable fun x : ℂ => Real.arcsin ((-x).im / x.abs) :=
    Real.measurableArcsin.comp ((measurableIm.comp measurableNeg).div measurableNorm)
  Measurable.ite (isClosedLe continuous_const continuous_re).MeasurableSet A <|
    Measurable.ite (isClosedLe continuous_const continuous_im).MeasurableSet (B.AddConst _)
      (B.sub_const _)
#align complex.measurable_arg Complex.measurableArg

@[measurability]
theorem measurableLog : Measurable log :=
  (measurableOfReal.comp <| Real.measurableLog.comp measurableNorm).add <|
    (measurableOfReal.comp measurableArg).mul_const i
#align complex.measurable_log Complex.measurableLog

end Complex

namespace IsROrC

variable {𝕜 : Type _} [IsROrC 𝕜]

@[measurability]
theorem measurableRe : Measurable (re : 𝕜 → ℝ) :=
  continuous_re.Measurable
#align is_R_or_C.measurable_re IsROrC.measurableRe

@[measurability]
theorem measurableIm : Measurable (im : 𝕜 → ℝ) :=
  continuous_im.Measurable
#align is_R_or_C.measurable_im IsROrC.measurableIm

end IsROrC

section RealComposition

open Real

variable {α : Type _} {m : MeasurableSpace α} {f : α → ℝ} (hf : Measurable f)

@[measurability]
theorem Measurable.exp : Measurable fun x => Real.exp (f x) :=
  Real.measurableExp.comp hf
#align measurable.exp Measurable.exp

@[measurability]
theorem Measurable.log : Measurable fun x => log (f x) :=
  measurableLog.comp hf
#align measurable.log Measurable.log

@[measurability]
theorem Measurable.cos : Measurable fun x => Real.cos (f x) :=
  Real.measurableCos.comp hf
#align measurable.cos Measurable.cos

@[measurability]
theorem Measurable.sin : Measurable fun x => Real.sin (f x) :=
  Real.measurableSin.comp hf
#align measurable.sin Measurable.sin

@[measurability]
theorem Measurable.cosh : Measurable fun x => Real.cosh (f x) :=
  Real.measurableCosh.comp hf
#align measurable.cosh Measurable.cosh

@[measurability]
theorem Measurable.sinh : Measurable fun x => Real.sinh (f x) :=
  Real.measurableSinh.comp hf
#align measurable.sinh Measurable.sinh

@[measurability]
theorem Measurable.sqrt : Measurable fun x => sqrt (f x) :=
  continuous_sqrt.Measurable.comp hf
#align measurable.sqrt Measurable.sqrt

end RealComposition

section ComplexComposition

open Complex

variable {α : Type _} {m : MeasurableSpace α} {f : α → ℂ} (hf : Measurable f)

@[measurability]
theorem Measurable.cexp : Measurable fun x => Complex.exp (f x) :=
  Complex.measurableExp.comp hf
#align measurable.cexp Measurable.cexp

@[measurability]
theorem Measurable.ccos : Measurable fun x => Complex.cos (f x) :=
  Complex.measurableCos.comp hf
#align measurable.ccos Measurable.ccos

@[measurability]
theorem Measurable.csin : Measurable fun x => Complex.sin (f x) :=
  Complex.measurableSin.comp hf
#align measurable.csin Measurable.csin

@[measurability]
theorem Measurable.ccosh : Measurable fun x => Complex.cosh (f x) :=
  Complex.measurableCosh.comp hf
#align measurable.ccosh Measurable.ccosh

@[measurability]
theorem Measurable.csinh : Measurable fun x => Complex.sinh (f x) :=
  Complex.measurableSinh.comp hf
#align measurable.csinh Measurable.csinh

@[measurability]
theorem Measurable.carg : Measurable fun x => arg (f x) :=
  measurableArg.comp hf
#align measurable.carg Measurable.carg

@[measurability]
theorem Measurable.clog : Measurable fun x => log (f x) :=
  measurableLog.comp hf
#align measurable.clog Measurable.clog

end ComplexComposition

section IsROrCComposition

variable {α 𝕜 : Type _} [IsROrC 𝕜] {m : MeasurableSpace α} {f : α → 𝕜} {μ : MeasureTheory.Measure α}

include m

@[measurability]
theorem Measurable.re (hf : Measurable f) : Measurable fun x => IsROrC.re (f x) :=
  IsROrC.measurableRe.comp hf
#align measurable.re Measurable.re

@[measurability]
theorem AeMeasurable.re (hf : AeMeasurable f μ) : AeMeasurable (fun x => IsROrC.re (f x)) μ :=
  IsROrC.measurableRe.compAeMeasurable hf
#align ae_measurable.re AeMeasurable.re

@[measurability]
theorem Measurable.im (hf : Measurable f) : Measurable fun x => IsROrC.im (f x) :=
  IsROrC.measurableIm.comp hf
#align measurable.im Measurable.im

@[measurability]
theorem AeMeasurable.im (hf : AeMeasurable f μ) : AeMeasurable (fun x => IsROrC.im (f x)) μ :=
  IsROrC.measurableIm.compAeMeasurable hf
#align ae_measurable.im AeMeasurable.im

omit m

end IsROrCComposition

section

variable {α 𝕜 : Type _} [IsROrC 𝕜] [MeasurableSpace α] {f : α → 𝕜} {μ : MeasureTheory.Measure α}

@[measurability]
theorem IsROrC.measurableOfReal : Measurable (coe : ℝ → 𝕜) :=
  IsROrC.continuous_of_real.Measurable
#align is_R_or_C.measurable_of_real IsROrC.measurableOfReal

theorem measurableOfReIm (hre : Measurable fun x => IsROrC.re (f x))
    (him : Measurable fun x => IsROrC.im (f x)) : Measurable f := by
  convert
    (is_R_or_C.measurable_of_real.comp hre).add
      ((is_R_or_C.measurable_of_real.comp him).mul_const IsROrC.i)
  · ext1 x
    exact (IsROrC.re_add_im _).symm
  all_goals infer_instance
#align measurable_of_re_im measurableOfReIm

theorem aeMeasurableOfReIm (hre : AeMeasurable (fun x => IsROrC.re (f x)) μ)
    (him : AeMeasurable (fun x => IsROrC.im (f x)) μ) : AeMeasurable f μ := by
  convert
    (is_R_or_C.measurable_of_real.comp_ae_measurable hre).add
      ((is_R_or_C.measurable_of_real.comp_ae_measurable him).mul_const IsROrC.i)
  · ext1 x
    exact (IsROrC.re_add_im _).symm
  all_goals infer_instance
#align ae_measurable_of_re_im aeMeasurableOfReIm

end

section PowInstances

instance Complex.hasMeasurablePow : HasMeasurablePow ℂ ℂ :=
  ⟨Measurable.ite (measurableFst (measurableSetSingleton 0))
      (Measurable.ite (measurableSnd (measurableSetSingleton 0)) measurableOne measurableZero)
      (measurableFst.clog.mul measurableSnd).cexp⟩
#align complex.has_measurable_pow Complex.hasMeasurablePow

instance Real.hasMeasurablePow : HasMeasurablePow ℝ ℝ :=
  ⟨Complex.measurableRe.comp <|
      (Complex.measurableOfReal.comp measurableFst).pow
        (Complex.measurableOfReal.comp measurableSnd)⟩
#align real.has_measurable_pow Real.hasMeasurablePow

instance Nnreal.hasMeasurablePow : HasMeasurablePow ℝ≥0 ℝ :=
  ⟨(measurableFst.coeNnrealReal.pow measurableSnd).subtype_mk⟩
#align nnreal.has_measurable_pow Nnreal.hasMeasurablePow

instance Ennreal.hasMeasurablePow : HasMeasurablePow ℝ≥0∞ ℝ := by
  refine' ⟨Ennreal.measurableOfMeasurableNnrealProd _ _⟩
  · simp_rw [Ennreal.coe_rpow_def]
    refine' Measurable.ite _ measurableConst (measurable_fst.pow measurableSnd).coeNnrealEnnreal
    exact
      MeasurableSet.inter (measurableFst (measurable_set_singleton 0))
        (measurableSnd measurableSetIio)
  · simp_rw [Ennreal.top_rpow_def]
    refine' Measurable.ite measurableSetIoi measurableConst _
    exact Measurable.ite (measurable_set_singleton 0) measurableConst measurableConst
#align ennreal.has_measurable_pow Ennreal.hasMeasurablePow

end PowInstances

/- ./././Mathport/Syntax/Translate/Command.lean:719:14: unsupported user command assert_not_exists -/
/- ./././Mathport/Syntax/Translate/Command.lean:719:14: unsupported user command assert_not_exists -/
-- Guard against import creep:
