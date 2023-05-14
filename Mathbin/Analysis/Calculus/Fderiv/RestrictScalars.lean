/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.calculus.fderiv.restrict_scalars
! leanprover-community/mathlib commit e3fb84046afd187b710170887195d50bada934ee
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Fderiv.Basic

/-!
# The derivative of the scalar restriction of a linear map

For detailed documentation of the Fréchet derivative,
see the module docstring of `analysis/calculus/fderiv/basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
the scalar restriction of a linear map.
-/


open Filter Asymptotics ContinuousLinearMap Set Metric

open Topology Classical NNReal Filter Asymptotics ENNReal

noncomputable section

section RestrictScalars

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is differentiable over `ℂ`, then it is differentiable over `ℝ`. In this paragraph,
we give variants of this statement, in the general situation where `ℂ` and `ℝ` are replaced
respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra over `𝕜`.
-/


variable (𝕜 : Type _) [NontriviallyNormedField 𝕜]

variable {𝕜' : Type _} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]

variable [IsScalarTower 𝕜 𝕜' E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]

variable [IsScalarTower 𝕜 𝕜' F]

variable {f : E → F} {f' : E →L[𝕜'] F} {s : Set E} {x : E}

theorem HasStrictFderivAt.restrictScalars (h : HasStrictFderivAt f f' x) :
    HasStrictFderivAt f (f'.restrictScalars 𝕜) x :=
  h
#align has_strict_fderiv_at.restrict_scalars HasStrictFderivAt.restrictScalars

theorem HasFderivAtFilter.restrictScalars {L} (h : HasFderivAtFilter f f' x L) :
    HasFderivAtFilter f (f'.restrictScalars 𝕜) x L :=
  h
#align has_fderiv_at_filter.restrict_scalars HasFderivAtFilter.restrictScalars

theorem HasFderivAt.restrictScalars (h : HasFderivAt f f' x) :
    HasFderivAt f (f'.restrictScalars 𝕜) x :=
  h
#align has_fderiv_at.restrict_scalars HasFderivAt.restrictScalars

theorem HasFderivWithinAt.restrictScalars (h : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt f (f'.restrictScalars 𝕜) s x :=
  h
#align has_fderiv_within_at.restrict_scalars HasFderivWithinAt.restrictScalars

theorem DifferentiableAt.restrict_scalars (h : DifferentiableAt 𝕜' f x) : DifferentiableAt 𝕜 f x :=
  (h.HasFderivAt.restrictScalars 𝕜).DifferentiableAt
#align differentiable_at.restrict_scalars DifferentiableAt.restrict_scalars

theorem DifferentiableWithinAt.restrict_scalars (h : DifferentiableWithinAt 𝕜' f s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  (h.HasFderivWithinAt.restrictScalars 𝕜).DifferentiableWithinAt
#align differentiable_within_at.restrict_scalars DifferentiableWithinAt.restrict_scalars

theorem DifferentiableOn.restrict_scalars (h : DifferentiableOn 𝕜' f s) : DifferentiableOn 𝕜 f s :=
  fun x hx => (h x hx).restrictScalars 𝕜
#align differentiable_on.restrict_scalars DifferentiableOn.restrict_scalars

theorem Differentiable.restrict_scalars (h : Differentiable 𝕜' f) : Differentiable 𝕜 f := fun x =>
  (h x).restrictScalars 𝕜
#align differentiable.restrict_scalars Differentiable.restrict_scalars

theorem hasFderivWithinAt_of_restrictScalars {g' : E →L[𝕜] F} (h : HasFderivWithinAt f g' s x)
    (H : f'.restrictScalars 𝕜 = g') : HasFderivWithinAt f f' s x :=
  by
  rw [← H] at h
  exact h
#align has_fderiv_within_at_of_restrict_scalars hasFderivWithinAt_of_restrictScalars

theorem hasFderivAt_of_restrictScalars {g' : E →L[𝕜] F} (h : HasFderivAt f g' x)
    (H : f'.restrictScalars 𝕜 = g') : HasFderivAt f f' x :=
  by
  rw [← H] at h
  exact h
#align has_fderiv_at_of_restrict_scalars hasFderivAt_of_restrictScalars

theorem DifferentiableAt.fderiv_restrictScalars (h : DifferentiableAt 𝕜' f x) :
    fderiv 𝕜 f x = (fderiv 𝕜' f x).restrictScalars 𝕜 :=
  (h.HasFderivAt.restrictScalars 𝕜).fderiv
#align differentiable_at.fderiv_restrict_scalars DifferentiableAt.fderiv_restrictScalars

theorem differentiableWithinAt_iff_restrictScalars (hf : DifferentiableWithinAt 𝕜 f s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    DifferentiableWithinAt 𝕜' f s x ↔
      ∃ g' : E →L[𝕜'] F, g'.restrictScalars 𝕜 = fderivWithin 𝕜 f s x :=
  by
  constructor
  · rintro ⟨g', hg'⟩
    exact ⟨g', hs.eq (hg'.restrict_scalars 𝕜) hf.has_fderiv_within_at⟩
  · rintro ⟨f', hf'⟩
    exact ⟨f', hasFderivWithinAt_of_restrictScalars 𝕜 hf.has_fderiv_within_at hf'⟩
#align differentiable_within_at_iff_restrict_scalars differentiableWithinAt_iff_restrictScalars

theorem differentiableAt_iff_restrictScalars (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜' f x ↔ ∃ g' : E →L[𝕜'] F, g'.restrictScalars 𝕜 = fderiv 𝕜 f x :=
  by
  rw [← differentiableWithinAt_univ, ← fderivWithin_univ]
  exact
    differentiableWithinAt_iff_restrictScalars 𝕜 hf.differentiable_within_at uniqueDiffWithinAt_univ
#align differentiable_at_iff_restrict_scalars differentiableAt_iff_restrictScalars

end RestrictScalars

