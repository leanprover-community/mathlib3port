/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module measure_theory.constructions.borel_space.continuous_linear_map
! leanprover-community/mathlib commit 4280f5f32e16755ec7985ce11e189b6cd6ff6735
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.FiniteDimension
import Mathbin.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurable functions in normed spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


open MeasureTheory

variable {α : Type _} [MeasurableSpace α]

namespace ContinuousLinearMap

variable {𝕜 : Type _} [NormedField 𝕜]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [MeasurableSpace F]
  [BorelSpace F]

/- warning: continuous_linear_map.measurable -> ContinuousLinearMap.measurable is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.measurable ContinuousLinearMap.measurableₓ'. -/
@[measurability]
protected theorem measurable (L : E →L[𝕜] F) : Measurable L :=
  L.Continuous.Measurable
#align continuous_linear_map.measurable ContinuousLinearMap.measurable

/- warning: continuous_linear_map.measurable_comp -> ContinuousLinearMap.measurable_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.measurable_comp ContinuousLinearMap.measurable_compₓ'. -/
theorem measurable_comp (L : E →L[𝕜] F) {φ : α → E} (φ_meas : Measurable φ) :
    Measurable fun a : α => L (φ a) :=
  L.Measurable.comp φ_meas
#align continuous_linear_map.measurable_comp ContinuousLinearMap.measurable_comp

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

instance : MeasurableSpace (E →L[𝕜] F) :=
  borel _

instance : BorelSpace (E →L[𝕜] F) :=
  ⟨rfl⟩

/- warning: continuous_linear_map.measurable_apply -> ContinuousLinearMap.measurable_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.measurable_apply ContinuousLinearMap.measurable_applyₓ'. -/
@[measurability]
theorem measurable_apply [MeasurableSpace F] [BorelSpace F] (x : E) :
    Measurable fun f : E →L[𝕜] F => f x :=
  (apply 𝕜 F x).Continuous.Measurable
#align continuous_linear_map.measurable_apply ContinuousLinearMap.measurable_apply

/- warning: continuous_linear_map.measurable_apply' -> ContinuousLinearMap.measurable_apply' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.measurable_apply' ContinuousLinearMap.measurable_apply'ₓ'. -/
@[measurability]
theorem measurable_apply' [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace F]
    [BorelSpace F] : Measurable fun (x : E) (f : E →L[𝕜] F) => f x :=
  measurable_pi_lambda _ fun f => f.Measurable
#align continuous_linear_map.measurable_apply' ContinuousLinearMap.measurable_apply'

/- warning: continuous_linear_map.measurable_coe -> ContinuousLinearMap.measurable_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.measurable_coe ContinuousLinearMap.measurable_coeₓ'. -/
@[measurability]
theorem measurable_coe [MeasurableSpace F] [BorelSpace F] :
    Measurable fun (f : E →L[𝕜] F) (x : E) => f x :=
  measurable_pi_lambda _ measurable_apply
#align continuous_linear_map.measurable_coe ContinuousLinearMap.measurable_coe

end ContinuousLinearMap

section ContinuousLinearMapNontriviallyNormedField

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]
  {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/- warning: measurable.apply_continuous_linear_map -> Measurable.apply_continuousLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measurable.apply_continuous_linear_map Measurable.apply_continuousLinearMapₓ'. -/
@[measurability]
theorem Measurable.apply_continuousLinearMap {φ : α → F →L[𝕜] E} (hφ : Measurable φ) (v : F) :
    Measurable fun a => φ a v :=
  (ContinuousLinearMap.apply 𝕜 E v).Measurable.comp hφ
#align measurable.apply_continuous_linear_map Measurable.apply_continuousLinearMap

/- warning: ae_measurable.apply_continuous_linear_map -> AEMeasurable.apply_continuousLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ae_measurable.apply_continuous_linear_map AEMeasurable.apply_continuousLinearMapₓ'. -/
@[measurability]
theorem AEMeasurable.apply_continuousLinearMap {φ : α → F →L[𝕜] E} {μ : Measure α}
    (hφ : AEMeasurable φ μ) (v : F) : AEMeasurable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply 𝕜 E v).Measurable.comp_aemeasurable hφ
#align ae_measurable.apply_continuous_linear_map AEMeasurable.apply_continuousLinearMap

end ContinuousLinearMapNontriviallyNormedField

section NormedSpace

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [MeasurableSpace 𝕜]

variable [BorelSpace 𝕜] {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E]
  [BorelSpace E]

/- warning: measurable_smul_const -> measurable_smul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measurable_smul_const measurable_smul_constₓ'. -/
theorem measurable_smul_const {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
    (Measurable fun x => f x • c) ↔ Measurable f :=
  (closedEmbedding_smul_left hc).MeasurableEmbedding.measurable_comp_iff
#align measurable_smul_const measurable_smul_const

/- warning: ae_measurable_smul_const -> aemeasurable_smul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ae_measurable_smul_const aemeasurable_smul_constₓ'. -/
theorem aemeasurable_smul_const {f : α → 𝕜} {μ : Measure α} {c : E} (hc : c ≠ 0) :
    AEMeasurable (fun x => f x • c) μ ↔ AEMeasurable f μ :=
  (closedEmbedding_smul_left hc).MeasurableEmbedding.aemeasurable_comp_iff
#align ae_measurable_smul_const aemeasurable_smul_const

end NormedSpace

