/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.function.special_functions.inner
! leanprover-community/mathlib commit bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurability of scalar products
-/


variable {α : Type _} {𝕜 : Type _} {E : Type _}

variable [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/- warning: measurable.inner -> Measurable.inner is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} {E : Type.{u3}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : InnerProductSpace.{u2, u3} 𝕜 E _inst_1 _inst_2] {m : MeasurableSpace.{u1} α} [_inst_4 : MeasurableSpace.{u3} E] [_inst_5 : OpensMeasurableSpace.{u3} E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)))) _inst_4] [_inst_6 : TopologicalSpace.SecondCountableTopology.{u3} E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2))))] {f : α -> E} {g : α -> E}, (Measurable.{u1, u3} α E m _inst_4 f) -> (Measurable.{u1, u3} α E m _inst_4 g) -> (Measurable.{u1, u2} α 𝕜 m (IsROrC.measurableSpace.{u2} 𝕜 _inst_1) (fun (t : α) => Inner.inner.{u2, u3} 𝕜 E (InnerProductSpace.toHasInner.{u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3) (f t) (g t)))
but is expected to have type
  forall {α : Type.{u3}} {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {m : MeasurableSpace.{u3} α} [_inst_4 : MeasurableSpace.{u2} E] [_inst_5 : OpensMeasurableSpace.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) _inst_4] [_inst_6 : TopologicalSpace.SecondCountableTopology.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))] {f : α -> E} {g : α -> E}, (Measurable.{u3, u2} α E m _inst_4 f) -> (Measurable.{u3, u2} α E m _inst_4 g) -> (Measurable.{u3, u1} α 𝕜 m (IsROrC.measurableSpace.{u1} 𝕜 _inst_1) (fun (t : α) => Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (f t) (g t)))
Case conversion may be inaccurate. Consider using '#align measurable.inner Measurable.innerₓ'. -/
@[measurability]
theorem Measurable.inner {m : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace.SecondCountableTopology E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun t => ⟪f t, g t⟫ :=
  Continuous.measurable2 continuous_inner hf hg
#align measurable.inner Measurable.inner

/- warning: ae_measurable.inner -> AEMeasurable.inner is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} {E : Type.{u3}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : InnerProductSpace.{u2, u3} 𝕜 E _inst_1 _inst_2] {m : MeasurableSpace.{u1} α} [_inst_4 : MeasurableSpace.{u3} E] [_inst_5 : OpensMeasurableSpace.{u3} E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)))) _inst_4] [_inst_6 : TopologicalSpace.SecondCountableTopology.{u3} E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2))))] {μ : MeasureTheory.Measure.{u1} α m} {f : α -> E} {g : α -> E}, (AEMeasurable.{u1, u3} α E _inst_4 m f μ) -> (AEMeasurable.{u1, u3} α E _inst_4 m g μ) -> (AEMeasurable.{u1, u2} α 𝕜 (IsROrC.measurableSpace.{u2} 𝕜 _inst_1) m (fun (x : α) => Inner.inner.{u2, u3} 𝕜 E (InnerProductSpace.toHasInner.{u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3) (f x) (g x)) μ)
but is expected to have type
  forall {α : Type.{u3}} {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {m : MeasurableSpace.{u3} α} [_inst_4 : MeasurableSpace.{u2} E] [_inst_5 : OpensMeasurableSpace.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) _inst_4] [_inst_6 : TopologicalSpace.SecondCountableTopology.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))] {μ : MeasureTheory.Measure.{u3} α m} {f : α -> E} {g : α -> E}, (AEMeasurable.{u3, u2} α E _inst_4 m f μ) -> (AEMeasurable.{u3, u2} α E _inst_4 m g μ) -> (AEMeasurable.{u3, u1} α 𝕜 (IsROrC.measurableSpace.{u1} 𝕜 _inst_1) m (fun (x : α) => Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (f x) (g x)) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.inner AEMeasurable.innerₓ'. -/
@[measurability]
theorem AEMeasurable.inner {m : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace.SecondCountableTopology E] {μ : MeasureTheory.Measure α} {f g : α → E}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => ⟪f x, g x⟫) μ :=
  by
  refine' ⟨fun x => ⟪hf.mk f x, hg.mk g x⟫, hf.measurable_mk.inner hg.measurable_mk, _⟩
  refine' hf.ae_eq_mk.mp (hg.ae_eq_mk.mono fun x hxg hxf => _)
  dsimp only
  congr
  exacts[hxf, hxg]
#align ae_measurable.inner AEMeasurable.inner

