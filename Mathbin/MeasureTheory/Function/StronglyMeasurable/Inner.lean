/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.function.strongly_measurable.inner
! leanprover-community/mathlib commit 6cb77a8eaff0ddd100e87b1591c6d3ad319514ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathbin.Analysis.InnerProductSpace.Basic

/-!
# Inner products of strongly measurable functions are strongly measurable.

-/


variable {α : Type _}

namespace MeasureTheory

/-! ## Strongly measurable functions -/


namespace StronglyMeasurable

protected theorem inner {𝕜 : Type _} {E : Type _} [IsROrC 𝕜] [InnerProductSpace 𝕜 E]
    {m : MeasurableSpace α} {f g : α → E} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun t => @inner 𝕜 _ _ (f t) (g t) :=
  Continuous.comp_strongly_measurable continuous_inner (hf.prod_mk hg)
#align measure_theory.strongly_measurable.inner MeasureTheory.StronglyMeasurable.inner

end StronglyMeasurable

namespace AeStronglyMeasurable

variable {m : MeasurableSpace α} {μ : Measure α} {𝕜 : Type _} {E : Type _} [IsROrC 𝕜]
  [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

protected theorem re {f : α → 𝕜} (hf : AeStronglyMeasurable f μ) :
    AeStronglyMeasurable (fun x => IsROrC.re (f x)) μ :=
  IsROrC.continuous_re.compAeStronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.re MeasureTheory.AeStronglyMeasurable.re

protected theorem im {f : α → 𝕜} (hf : AeStronglyMeasurable f μ) :
    AeStronglyMeasurable (fun x => IsROrC.im (f x)) μ :=
  IsROrC.continuous_im.compAeStronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.im MeasureTheory.AeStronglyMeasurable.im

protected theorem inner {m : MeasurableSpace α} {μ : Measure α} {f g : α → E}
    (hf : AeStronglyMeasurable f μ) (hg : AeStronglyMeasurable g μ) :
    AeStronglyMeasurable (fun x => ⟪f x, g x⟫) μ :=
  continuous_inner.compAeStronglyMeasurable (hf.prod_mk hg)
#align measure_theory.ae_strongly_measurable.inner MeasureTheory.AeStronglyMeasurable.inner

end AeStronglyMeasurable

end MeasureTheory

