/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Analysis.InnerProductSpace.Basic
import MeasureTheory.Constructions.BorelSpace.Complex

#align_import measure_theory.function.special_functions.inner from "leanprover-community/mathlib"@"0b7c740e25651db0ba63648fbae9f9d6f941e31b"

/-!
# Measurability of scalar products

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _} {𝕜 : Type _} {E : Type _}

variable [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

#print Measurable.inner /-
@[measurability]
theorem Measurable.inner {m : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace.SecondCountableTopology E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun t => ⟪f t, g t⟫ :=
  Continuous.measurable2 continuous_inner hf hg
#align measurable.inner Measurable.inner
-/

#print AEMeasurable.inner /-
@[measurability]
theorem AEMeasurable.inner {m : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace.SecondCountableTopology E] {μ : MeasureTheory.Measure α} {f g : α → E}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => ⟪f x, g x⟫) μ :=
  by
  refine' ⟨fun x => ⟪hf.mk f x, hg.mk g x⟫, hf.measurable_mk.inner hg.measurable_mk, _⟩
  refine' hf.ae_eq_mk.mp (hg.ae_eq_mk.mono fun x hxg hxf => _)
  dsimp only
  congr
  exacts [hxf, hxg]
#align ae_measurable.inner AEMeasurable.inner
-/

