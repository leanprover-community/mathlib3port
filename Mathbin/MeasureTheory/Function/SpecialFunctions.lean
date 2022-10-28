/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.SpecialFunctions.Pow
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.MeasureTheory.Constructions.BorelSpace

/-!
# Measurability of real and complex functions

We show that most standard real and complex functions are measurable, notably `exp`, `cos`, `sin`,
`cosh`, `sinh`, `log`, `pow`, `arcsin`, `arccos`, `arctan`, and scalar products.
-/


noncomputable section

open Nnreal Ennreal

namespace Real

@[measurability]
theorem measurableExp : Measurable exp :=
  continuous_exp.Measurable

@[measurability]
theorem measurableLog : Measurable log :=
  measurableOfMeasurableOnComplSingleton 0 <|
    Continuous.measurable <| continuous_on_iff_continuous_restrict.1 continuous_on_log

@[measurability]
theorem measurableSin : Measurable sin :=
  continuous_sin.Measurable

@[measurability]
theorem measurableCos : Measurable cos :=
  continuous_cos.Measurable

@[measurability]
theorem measurableSinh : Measurable sinh :=
  continuous_sinh.Measurable

@[measurability]
theorem measurableCosh : Measurable cosh :=
  continuous_cosh.Measurable

@[measurability]
theorem measurableArcsin : Measurable arcsin :=
  continuous_arcsin.Measurable

@[measurability]
theorem measurableArccos : Measurable arccos :=
  continuous_arccos.Measurable

@[measurability]
theorem measurableArctan : Measurable arctan :=
  continuous_arctan.Measurable

end Real

namespace Complex

@[measurability]
theorem measurableRe : Measurable re :=
  continuous_re.Measurable

@[measurability]
theorem measurableIm : Measurable im :=
  continuous_im.Measurable

@[measurability]
theorem measurableOfReal : Measurable (coe : ℝ → ℂ) :=
  continuous_of_real.Measurable

@[measurability]
theorem measurableExp : Measurable exp :=
  continuous_exp.Measurable

@[measurability]
theorem measurableSin : Measurable sin :=
  continuous_sin.Measurable

@[measurability]
theorem measurableCos : Measurable cos :=
  continuous_cos.Measurable

@[measurability]
theorem measurableSinh : Measurable sinh :=
  continuous_sinh.Measurable

@[measurability]
theorem measurableCosh : Measurable cosh :=
  continuous_cosh.Measurable

@[measurability]
theorem measurableArg : Measurable arg :=
  have A : Measurable fun x : ℂ => Real.arcsin (x.im / x.abs) :=
    Real.measurableArcsin.comp (measurableIm.div measurableNorm)
  have B : Measurable fun x : ℂ => Real.arcsin ((-x).im / x.abs) :=
    Real.measurableArcsin.comp ((measurableIm.comp measurableNeg).div measurableNorm)
  Measurable.ite (isClosedLe continuous_const continuous_re).MeasurableSet A <|
    Measurable.ite (isClosedLe continuous_const continuous_im).MeasurableSet (B.AddConst _) (B.sub_const _)

@[measurability]
theorem measurableLog : Measurable log :=
  (measurableOfReal.comp <| Real.measurableLog.comp measurableNorm).add <|
    (measurableOfReal.comp measurableArg).mul_const i

end Complex

namespace IsROrC

variable {𝕜 : Type _} [IsROrC 𝕜]

@[measurability]
theorem measurableRe : Measurable (re : 𝕜 → ℝ) :=
  continuous_re.Measurable

@[measurability]
theorem measurableIm : Measurable (im : 𝕜 → ℝ) :=
  continuous_im.Measurable

end IsROrC

section RealComposition

open Real

variable {α : Type _} {m : MeasurableSpace α} {f : α → ℝ} (hf : Measurable f)

@[measurability]
theorem Measurable.exp : Measurable fun x => Real.exp (f x) :=
  Real.measurableExp.comp hf

@[measurability]
theorem Measurable.log : Measurable fun x => log (f x) :=
  measurableLog.comp hf

@[measurability]
theorem Measurable.cos : Measurable fun x => Real.cos (f x) :=
  Real.measurableCos.comp hf

@[measurability]
theorem Measurable.sin : Measurable fun x => Real.sin (f x) :=
  Real.measurableSin.comp hf

@[measurability]
theorem Measurable.cosh : Measurable fun x => Real.cosh (f x) :=
  Real.measurableCosh.comp hf

@[measurability]
theorem Measurable.sinh : Measurable fun x => Real.sinh (f x) :=
  Real.measurableSinh.comp hf

@[measurability]
theorem Measurable.arctan : Measurable fun x => arctan (f x) :=
  measurableArctan.comp hf

@[measurability]
theorem Measurable.sqrt : Measurable fun x => sqrt (f x) :=
  continuous_sqrt.Measurable.comp hf

end RealComposition

section ComplexComposition

open Complex

variable {α : Type _} {m : MeasurableSpace α} {f : α → ℂ} (hf : Measurable f)

@[measurability]
theorem Measurable.cexp : Measurable fun x => Complex.exp (f x) :=
  Complex.measurableExp.comp hf

@[measurability]
theorem Measurable.ccos : Measurable fun x => Complex.cos (f x) :=
  Complex.measurableCos.comp hf

@[measurability]
theorem Measurable.csin : Measurable fun x => Complex.sin (f x) :=
  Complex.measurableSin.comp hf

@[measurability]
theorem Measurable.ccosh : Measurable fun x => Complex.cosh (f x) :=
  Complex.measurableCosh.comp hf

@[measurability]
theorem Measurable.csinh : Measurable fun x => Complex.sinh (f x) :=
  Complex.measurableSinh.comp hf

@[measurability]
theorem Measurable.carg : Measurable fun x => arg (f x) :=
  measurableArg.comp hf

@[measurability]
theorem Measurable.clog : Measurable fun x => log (f x) :=
  measurableLog.comp hf

end ComplexComposition

section IsROrCComposition

variable {α 𝕜 : Type _} [IsROrC 𝕜] {m : MeasurableSpace α} {f : α → 𝕜} {μ : MeasureTheory.Measure α}

include m

@[measurability]
theorem Measurable.re (hf : Measurable f) : Measurable fun x => IsROrC.re (f x) :=
  IsROrC.measurableRe.comp hf

@[measurability]
theorem AeMeasurable.re (hf : AeMeasurable f μ) : AeMeasurable (fun x => IsROrC.re (f x)) μ :=
  IsROrC.measurableRe.compAeMeasurable hf

@[measurability]
theorem Measurable.im (hf : Measurable f) : Measurable fun x => IsROrC.im (f x) :=
  IsROrC.measurableIm.comp hf

@[measurability]
theorem AeMeasurable.im (hf : AeMeasurable f μ) : AeMeasurable (fun x => IsROrC.im (f x)) μ :=
  IsROrC.measurableIm.compAeMeasurable hf

omit m

end IsROrCComposition

section

variable {α 𝕜 : Type _} [IsROrC 𝕜] [MeasurableSpace α] {f : α → 𝕜} {μ : MeasureTheory.Measure α}

@[measurability]
theorem IsROrC.measurableOfReal : Measurable (coe : ℝ → 𝕜) :=
  IsROrC.continuous_of_real.Measurable

theorem measurableOfReIm (hre : Measurable fun x => IsROrC.re (f x)) (him : Measurable fun x => IsROrC.im (f x)) :
    Measurable f := by
  convert (is_R_or_C.measurable_of_real.comp hre).add ((is_R_or_C.measurable_of_real.comp him).mul_const IsROrC.i)
  · ext1 x
    exact (IsROrC.re_add_im _).symm
    
  all_goals infer_instance

theorem aeMeasurableOfReIm (hre : AeMeasurable (fun x => IsROrC.re (f x)) μ)
    (him : AeMeasurable (fun x => IsROrC.im (f x)) μ) : AeMeasurable f μ := by
  convert
    (is_R_or_C.measurable_of_real.comp_ae_measurable hre).add
      ((is_R_or_C.measurable_of_real.comp_ae_measurable him).mul_const IsROrC.i)
  · ext1 x
    exact (IsROrC.re_add_im _).symm
    
  all_goals infer_instance

end

section PowInstances

instance Complex.hasMeasurablePow : HasMeasurablePow ℂ ℂ :=
  ⟨Measurable.ite (measurableFst (measurableSetSingleton 0))
      (Measurable.ite (measurableSnd (measurableSetSingleton 0)) measurableOne measurableZero)
      (measurableFst.clog.mul measurableSnd).cexp⟩

instance Real.hasMeasurablePow : HasMeasurablePow ℝ ℝ :=
  ⟨Complex.measurableRe.comp <|
      (Complex.measurableOfReal.comp measurableFst).pow (Complex.measurableOfReal.comp measurableSnd)⟩

instance Nnreal.hasMeasurablePow : HasMeasurablePow ℝ≥0 ℝ :=
  ⟨(measurableFst.coeNnrealReal.pow measurableSnd).subtype_mk⟩

instance Ennreal.hasMeasurablePow : HasMeasurablePow ℝ≥0∞ ℝ := by
  refine' ⟨Ennreal.measurableOfMeasurableNnrealProd _ _⟩
  · simp_rw [Ennreal.coe_rpow_def]
    refine' Measurable.ite _ measurableConst (measurable_fst.pow measurableSnd).coeNnrealEnnreal
    exact MeasurableSet.inter (measurableFst (measurable_set_singleton 0)) (measurableSnd measurableSetIio)
    
  · simp_rw [Ennreal.top_rpow_def]
    refine' Measurable.ite measurableSetIoi measurableConst _
    exact Measurable.ite (measurable_set_singleton 0) measurableConst measurableConst
    

end PowInstances

section

variable {α : Type _} {𝕜 : Type _} {E : Type _} [IsROrC 𝕜] [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

@[measurability]
theorem Measurable.inner {m : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace.SecondCountableTopology E] {f g : α → E} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun t => ⟪f t, g t⟫ :=
  Continuous.measurable2 continuous_inner hf hg

@[measurability]
theorem AeMeasurable.inner {m : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace.SecondCountableTopology E] {μ : MeasureTheory.Measure α} {f g : α → E} (hf : AeMeasurable f μ)
    (hg : AeMeasurable g μ) : AeMeasurable (fun x => ⟪f x, g x⟫) μ := by
  refine' ⟨fun x => ⟪hf.mk f x, hg.mk g x⟫, hf.measurable_mk.inner hg.measurable_mk, _⟩
  refine' hf.ae_eq_mk.mp (hg.ae_eq_mk.mono fun x hxg hxf => _)
  dsimp only
  congr
  exacts[hxf, hxg]

end

