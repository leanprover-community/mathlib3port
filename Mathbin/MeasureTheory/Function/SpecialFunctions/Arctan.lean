/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathbin.MeasureTheory.Constructions.BorelSpace

/-!
# Measurability of arctan

-/


namespace Real

@[measurability]
theorem measurableArctan : Measurable arctan :=
  continuous_arctan.Measurable
#align real.measurable_arctan Real.measurableArctan

end Real

section RealComposition

open Real

variable {α : Type _} {m : MeasurableSpace α} {f : α → ℝ} (hf : Measurable f)

@[measurability]
theorem Measurable.arctan : Measurable fun x => arctan (f x) :=
  measurableArctan.comp hf
#align measurable.arctan Measurable.arctan

end RealComposition

