/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Analysis.SpecialFunctions.Trigonometric.Arctan
import MeasureTheory.Constructions.BorelSpace.Basic

#align_import measure_theory.function.special_functions.arctan from "leanprover-community/mathlib"@"7e5137f579de09a059a5ce98f364a04e221aabf0"

/-!
# Measurability of arctan

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


namespace Real

#print Real.measurable_arctan /-
@[measurability]
theorem measurable_arctan : Measurable arctan :=
  continuous_arctan.Measurable
#align real.measurable_arctan Real.measurable_arctan
-/

end Real

section RealComposition

open Real

variable {α : Type _} {m : MeasurableSpace α} {f : α → ℝ} (hf : Measurable f)

#print Measurable.arctan /-
@[measurability]
theorem Measurable.arctan : Measurable fun x => arctan (f x) :=
  measurable_arctan.comp hf
#align measurable.arctan Measurable.arctan
-/

end RealComposition

