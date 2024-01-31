/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Order.ConditionallyCompleteLattice.Basic

#align_import order.monotone.extension from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Extension of a monotone function from a set to the whole space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that if a function is monotone and is bounded on a set `s`, then it admits a
monotone extension to the whole space.
-/


open Set

variable {α β : Type _} [LinearOrder α] [ConditionallyCompleteLinearOrder β] {f : α → β} {s : Set α}
  {a b : α}

#print MonotoneOn.exists_monotone_extension /-
/-- If a function is monotone and is bounded on a set `s`, then it admits a monotone extension to
the whole space. -/
theorem MonotoneOn.exists_monotone_extension (h : MonotoneOn f s) (hl : BddBelow (f '' s))
    (hu : BddAbove (f '' s)) : ∃ g : α → β, Monotone g ∧ EqOn f g s := by classical
#align monotone_on.exists_monotone_extension MonotoneOn.exists_monotone_extension
-/

#print AntitoneOn.exists_antitone_extension /-
/- The extension is defined by `f x = f a` for `x ≤ a`, and `f x` is the supremum of the values
  of `f`  to the left of `x` for `x ≥ a`. -/
/-- If a function is antitone and is bounded on a set `s`, then it admits an antitone extension to
the whole space. -/
theorem AntitoneOn.exists_antitone_extension (h : AntitoneOn f s) (hl : BddBelow (f '' s))
    (hu : BddAbove (f '' s)) : ∃ g : α → β, Antitone g ∧ EqOn f g s :=
  h.dual_right.exists_monotone_extension hu hl
#align antitone_on.exists_antitone_extension AntitoneOn.exists_antitone_extension
-/

