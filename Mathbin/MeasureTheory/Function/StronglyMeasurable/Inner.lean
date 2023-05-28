/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.function.strongly_measurable.inner
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathbin.Analysis.InnerProductSpace.Basic

/-!
# Inner products of strongly measurable functions are strongly measurable.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


variable {α : Type _}

namespace MeasureTheory

/-! ## Strongly measurable functions -/


namespace StronglyMeasurable

/- warning: measure_theory.strongly_measurable.inner -> MeasureTheory.StronglyMeasurable.inner is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} {E : Type.{u3}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : InnerProductSpace.{u2, u3} 𝕜 E _inst_1 _inst_2] {m : MeasurableSpace.{u1} α} {f : α -> E} {g : α -> E}, (MeasureTheory.StronglyMeasurable.{u1, u3} α E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)))) m f) -> (MeasureTheory.StronglyMeasurable.{u1, u3} α E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)))) m g) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) m (fun (t : α) => Inner.inner.{u2, u3} 𝕜 E (InnerProductSpace.toHasInner.{u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3) (f t) (g t)))
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u3}} {E : Type.{u2}} [_inst_1 : IsROrC.{u3} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u3, u2} 𝕜 E _inst_1 _inst_2] {m : MeasurableSpace.{u1} α} {f : α -> E} {g : α -> E}, (MeasureTheory.StronglyMeasurable.{u1, u2} α E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) m f) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) m g) -> (MeasureTheory.StronglyMeasurable.{u1, u3} α 𝕜 (UniformSpace.toTopologicalSpace.{u3} 𝕜 (PseudoMetricSpace.toUniformSpace.{u3} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u3} 𝕜 (SeminormedCommRing.toSeminormedRing.{u3} 𝕜 (NormedCommRing.toSeminormedCommRing.{u3} 𝕜 (NormedField.toNormedCommRing.{u3} 𝕜 (DenselyNormedField.toNormedField.{u3} 𝕜 (IsROrC.toDenselyNormedField.{u3} 𝕜 _inst_1)))))))) m (fun (t : α) => Inner.inner.{u3, u2} 𝕜 E (InnerProductSpace.toInner.{u3, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (f t) (g t)))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.inner MeasureTheory.StronglyMeasurable.innerₓ'. -/
protected theorem inner {𝕜 : Type _} {E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {m : MeasurableSpace α} {f g : α → E} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable fun t => @inner 𝕜 _ _ (f t) (g t) :=
  Continuous.comp_stronglyMeasurable continuous_inner (hf.prod_mk hg)
#align measure_theory.strongly_measurable.inner MeasureTheory.StronglyMeasurable.inner

end StronglyMeasurable

namespace AeStronglyMeasurable

variable {m : MeasurableSpace α} {μ : Measure α} {𝕜 : Type _} {E : Type _} [IsROrC 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/- warning: measure_theory.ae_strongly_measurable.re -> MeasureTheory.AEStronglyMeasurable.re is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.re MeasureTheory.AEStronglyMeasurable.reₓ'. -/
protected theorem re {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => IsROrC.re (f x)) μ :=
  IsROrC.continuous_re.comp_aestronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.re MeasureTheory.AEStronglyMeasurable.re

/- warning: measure_theory.ae_strongly_measurable.im -> MeasureTheory.AEStronglyMeasurable.im is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.im MeasureTheory.AEStronglyMeasurable.imₓ'. -/
protected theorem im {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => IsROrC.im (f x)) μ :=
  IsROrC.continuous_im.comp_aestronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.im MeasureTheory.AEStronglyMeasurable.im

/- warning: measure_theory.ae_strongly_measurable.inner -> MeasureTheory.AEStronglyMeasurable.inner is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} {E : Type.{u3}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : InnerProductSpace.{u2, u3} 𝕜 E _inst_1 _inst_2] {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> E} {g : α -> E}, (MeasureTheory.AEStronglyMeasurable.{u1, u3} α E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)))) m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u3} α E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)))) m g μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) m (fun (x : α) => Inner.inner.{u2, u3} 𝕜 E (InnerProductSpace.toHasInner.{u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3) (f x) (g x)) μ)
but is expected to have type
  forall {α : Type.{u3}} {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {m : MeasurableSpace.{u3} α} {μ : MeasureTheory.Measure.{u3} α m} {f : α -> E} {g : α -> E}, (MeasureTheory.AEStronglyMeasurable.{u3, u2} α E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u3, u2} α E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) m g μ) -> (MeasureTheory.AEStronglyMeasurable.{u3, u1} α 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) m (fun (x : α) => Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (f x) (g x)) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.inner MeasureTheory.AEStronglyMeasurable.innerₓ'. -/
protected theorem inner {m : MeasurableSpace α} {μ : Measure α} {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => ⟪f x, g x⟫) μ :=
  continuous_inner.comp_aestronglyMeasurable (hf.prod_mk hg)
#align measure_theory.ae_strongly_measurable.inner MeasureTheory.AEStronglyMeasurable.inner

end AeStronglyMeasurable

end MeasureTheory

