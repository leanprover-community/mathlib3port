/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.function.special_functions.arctan
! leanprover-community/mathlib commit b3f25363ae62cb169e72cd6b8b1ac97bacf21ca7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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

