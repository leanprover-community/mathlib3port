/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.calculus.fderiv.mul
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Fderiv.Bilinear

/-!
# Multiplicative operations on derivatives

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For detailed documentation of the Fréchet derivative,
see the module docstring of `analysis/calculus/fderiv/basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* multiplication of a function by a scalar function
* multiplication of two scalar functions
* inverse function (assuming that it exists; the inverse function theorem is in `../inverse.lean`)
-/


open Filter Asymptotics ContinuousLinearMap Set Metric

open Topology Classical NNReal Filter Asymptotics ENNReal

noncomputable section

section

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {G' : Type _} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

variable {f f₀ f₁ g : E → F}

variable {f' f₀' f₁' g' : E →L[𝕜] F}

variable (e : E →L[𝕜] F)

variable {x : E}

variable {s t : Set E}

variable {L L₁ L₂ : Filter E}

section ClmCompApply

/-! ### Derivative of the pointwise composition/application of continuous linear maps -/


variable {H : Type _} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {c : E → G →L[𝕜] H}
  {c' : E →L[𝕜] G →L[𝕜] H} {d : E → F →L[𝕜] G} {d' : E →L[𝕜] F →L[𝕜] G} {u : E → G} {u' : E →L[𝕜] G}

/- warning: has_strict_fderiv_at.clm_comp -> HasStrictFDerivAt.clm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.clm_comp HasStrictFDerivAt.clm_compₓ'. -/
theorem HasStrictFDerivAt.clm_comp (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
    HasStrictFDerivAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
  (isBoundedBilinearMapComp.HasStrictFDerivAt (c x, d x)).comp x <| hc.Prod hd
#align has_strict_fderiv_at.clm_comp HasStrictFDerivAt.clm_comp

/- warning: has_fderiv_within_at.clm_comp -> HasFDerivWithinAt.clm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.clm_comp HasFDerivWithinAt.clm_compₓ'. -/
theorem HasFDerivWithinAt.clm_comp (hc : HasFDerivWithinAt c c' s x)
    (hd : HasFDerivWithinAt d d' s x) :
    HasFDerivWithinAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') s x :=
  (isBoundedBilinearMapComp.HasFDerivAt (c x, d x)).comp_hasFDerivWithinAt x <| hc.Prod hd
#align has_fderiv_within_at.clm_comp HasFDerivWithinAt.clm_comp

/- warning: has_fderiv_at.clm_comp -> HasFDerivAt.clm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.clm_comp HasFDerivAt.clm_compₓ'. -/
theorem HasFDerivAt.clm_comp (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
    HasFDerivAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
  (isBoundedBilinearMapComp.HasFDerivAt (c x, d x)).comp x <| hc.Prod hd
#align has_fderiv_at.clm_comp HasFDerivAt.clm_comp

/- warning: differentiable_within_at.clm_comp -> DifferentiableWithinAt.clm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.clm_comp DifferentiableWithinAt.clm_compₓ'. -/
theorem DifferentiableWithinAt.clm_comp (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    DifferentiableWithinAt 𝕜 (fun y => (c y).comp (d y)) s x :=
  (hc.HasFDerivWithinAt.clm_comp hd.HasFDerivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.clm_comp DifferentiableWithinAt.clm_comp

/- warning: differentiable_at.clm_comp -> DifferentiableAt.clm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_at.clm_comp DifferentiableAt.clm_compₓ'. -/
theorem DifferentiableAt.clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    DifferentiableAt 𝕜 (fun y => (c y).comp (d y)) x :=
  (hc.HasFDerivAt.clm_comp hd.HasFDerivAt).DifferentiableAt
#align differentiable_at.clm_comp DifferentiableAt.clm_comp

/- warning: differentiable_on.clm_comp -> DifferentiableOn.clm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_on.clm_comp DifferentiableOn.clm_compₓ'. -/
theorem DifferentiableOn.clm_comp (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s) :
    DifferentiableOn 𝕜 (fun y => (c y).comp (d y)) s := fun x hx => (hc x hx).clm_comp (hd x hx)
#align differentiable_on.clm_comp DifferentiableOn.clm_comp

/- warning: differentiable.clm_comp -> Differentiable.clm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable.clm_comp Differentiable.clm_compₓ'. -/
theorem Differentiable.clm_comp (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) :
    Differentiable 𝕜 fun y => (c y).comp (d y) := fun x => (hc x).clm_comp (hd x)
#align differentiable.clm_comp Differentiable.clm_comp

/- warning: fderiv_within_clm_comp -> fderivWithin_clm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_clm_comp fderivWithin_clm_compₓ'. -/
theorem fderivWithin_clm_comp (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (fun y => (c y).comp (d y)) s x =
      (compL 𝕜 F G H (c x)).comp (fderivWithin 𝕜 d s x) +
        ((compL 𝕜 F G H).flip (d x)).comp (fderivWithin 𝕜 c s x) :=
  (hc.HasFDerivWithinAt.clm_comp hd.HasFDerivWithinAt).fderivWithin hxs
#align fderiv_within_clm_comp fderivWithin_clm_comp

/- warning: fderiv_clm_comp -> fderiv_clm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_clm_comp fderiv_clm_compₓ'. -/
theorem fderiv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => (c y).comp (d y)) x =
      (compL 𝕜 F G H (c x)).comp (fderiv 𝕜 d x) +
        ((compL 𝕜 F G H).flip (d x)).comp (fderiv 𝕜 c x) :=
  (hc.HasFDerivAt.clm_comp hd.HasFDerivAt).fderiv
#align fderiv_clm_comp fderiv_clm_comp

/- warning: has_strict_fderiv_at.clm_apply -> HasStrictFDerivAt.clm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.clm_apply HasStrictFDerivAt.clm_applyₓ'. -/
theorem HasStrictFDerivAt.clm_apply (hc : HasStrictFDerivAt c c' x)
    (hu : HasStrictFDerivAt u u' x) :
    HasStrictFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
  (isBoundedBilinearMapApply.HasStrictFDerivAt (c x, u x)).comp x (hc.Prod hu)
#align has_strict_fderiv_at.clm_apply HasStrictFDerivAt.clm_apply

/- warning: has_fderiv_within_at.clm_apply -> HasFDerivWithinAt.clm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.clm_apply HasFDerivWithinAt.clm_applyₓ'. -/
theorem HasFDerivWithinAt.clm_apply (hc : HasFDerivWithinAt c c' s x)
    (hu : HasFDerivWithinAt u u' s x) :
    HasFDerivWithinAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) s x :=
  (isBoundedBilinearMapApply.HasFDerivAt (c x, u x)).comp_hasFDerivWithinAt x (hc.Prod hu)
#align has_fderiv_within_at.clm_apply HasFDerivWithinAt.clm_apply

/- warning: has_fderiv_at.clm_apply -> HasFDerivAt.clm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.clm_apply HasFDerivAt.clm_applyₓ'. -/
theorem HasFDerivAt.clm_apply (hc : HasFDerivAt c c' x) (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
  (isBoundedBilinearMapApply.HasFDerivAt (c x, u x)).comp x (hc.Prod hu)
#align has_fderiv_at.clm_apply HasFDerivAt.clm_apply

/- warning: differentiable_within_at.clm_apply -> DifferentiableWithinAt.clm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.clm_apply DifferentiableWithinAt.clm_applyₓ'. -/
theorem DifferentiableWithinAt.clm_apply (hc : DifferentiableWithinAt 𝕜 c s x)
    (hu : DifferentiableWithinAt 𝕜 u s x) : DifferentiableWithinAt 𝕜 (fun y => (c y) (u y)) s x :=
  (hc.HasFDerivWithinAt.clm_apply hu.HasFDerivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.clm_apply DifferentiableWithinAt.clm_apply

/- warning: differentiable_at.clm_apply -> DifferentiableAt.clm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_at.clm_apply DifferentiableAt.clm_applyₓ'. -/
theorem DifferentiableAt.clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    DifferentiableAt 𝕜 (fun y => (c y) (u y)) x :=
  (hc.HasFDerivAt.clm_apply hu.HasFDerivAt).DifferentiableAt
#align differentiable_at.clm_apply DifferentiableAt.clm_apply

/- warning: differentiable_on.clm_apply -> DifferentiableOn.clm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_on.clm_apply DifferentiableOn.clm_applyₓ'. -/
theorem DifferentiableOn.clm_apply (hc : DifferentiableOn 𝕜 c s) (hu : DifferentiableOn 𝕜 u s) :
    DifferentiableOn 𝕜 (fun y => (c y) (u y)) s := fun x hx => (hc x hx).clm_apply (hu x hx)
#align differentiable_on.clm_apply DifferentiableOn.clm_apply

/- warning: differentiable.clm_apply -> Differentiable.clm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable.clm_apply Differentiable.clm_applyₓ'. -/
theorem Differentiable.clm_apply (hc : Differentiable 𝕜 c) (hu : Differentiable 𝕜 u) :
    Differentiable 𝕜 fun y => (c y) (u y) := fun x => (hc x).clm_apply (hu x)
#align differentiable.clm_apply Differentiable.clm_apply

/- warning: fderiv_within_clm_apply -> fderivWithin_clm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_clm_apply fderivWithin_clm_applyₓ'. -/
theorem fderivWithin_clm_apply (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s x) :
    fderivWithin 𝕜 (fun y => (c y) (u y)) s x =
      (c x).comp (fderivWithin 𝕜 u s x) + (fderivWithin 𝕜 c s x).flip (u x) :=
  (hc.HasFDerivWithinAt.clm_apply hu.HasFDerivWithinAt).fderivWithin hxs
#align fderiv_within_clm_apply fderivWithin_clm_apply

/- warning: fderiv_clm_apply -> fderiv_clm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_clm_apply fderiv_clm_applyₓ'. -/
theorem fderiv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    fderiv 𝕜 (fun y => (c y) (u y)) x = (c x).comp (fderiv 𝕜 u x) + (fderiv 𝕜 c x).flip (u x) :=
  (hc.HasFDerivAt.clm_apply hu.HasFDerivAt).fderiv
#align fderiv_clm_apply fderiv_clm_apply

end ClmCompApply

section Smul

/-! ### Derivative of the product of a scalar-valued function and a vector-valued function

If `c` is a differentiable scalar-valued function and `f` is a differentiable vector-valued
function, then `λ x, c x • f x` is differentiable as well. Lemmas in this section works for
function `c` taking values in the base field, as well as in a normed algebra over the base
field: e.g., they work for `c : E → ℂ` and `f : E → F` provided that `F` is a complex
normed vector space.
-/


variable {𝕜' : Type _} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]

variable {c : E → 𝕜'} {c' : E →L[𝕜] 𝕜'}

/- warning: has_strict_fderiv_at.smul -> HasStrictFDerivAt.smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.smul HasStrictFDerivAt.smulₓ'. -/
theorem HasStrictFDerivAt.smul (hc : HasStrictFDerivAt c c' x) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun y => c y • f y) (c x • f' + c'.smul_right (f x)) x :=
  (isBoundedBilinearMapSmul.HasStrictFDerivAt (c x, f x)).comp x <| hc.Prod hf
#align has_strict_fderiv_at.smul HasStrictFDerivAt.smul

/- warning: has_fderiv_within_at.smul -> HasFDerivWithinAt.smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.smul HasFDerivWithinAt.smulₓ'. -/
theorem HasFDerivWithinAt.smul (hc : HasFDerivWithinAt c c' s x) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun y => c y • f y) (c x • f' + c'.smul_right (f x)) s x :=
  (isBoundedBilinearMapSmul.HasFDerivAt (c x, f x)).comp_hasFDerivWithinAt x <| hc.Prod hf
#align has_fderiv_within_at.smul HasFDerivWithinAt.smul

/- warning: has_fderiv_at.smul -> HasFDerivAt.smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.smul HasFDerivAt.smulₓ'. -/
theorem HasFDerivAt.smul (hc : HasFDerivAt c c' x) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => c y • f y) (c x • f' + c'.smul_right (f x)) x :=
  (isBoundedBilinearMapSmul.HasFDerivAt (c x, f x)).comp x <| hc.Prod hf
#align has_fderiv_at.smul HasFDerivAt.smul

/- warning: differentiable_within_at.smul -> DifferentiableWithinAt.smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.smul DifferentiableWithinAt.smulₓ'. -/
theorem DifferentiableWithinAt.smul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (fun y => c y • f y) s x :=
  (hc.HasFDerivWithinAt.smul hf.HasFDerivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.smul DifferentiableWithinAt.smul

/- warning: differentiable_at.smul -> DifferentiableAt.smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_at.smul DifferentiableAt.smulₓ'. -/
@[simp]
theorem DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y => c y • f y) x :=
  (hc.HasFDerivAt.smul hf.HasFDerivAt).DifferentiableAt
#align differentiable_at.smul DifferentiableAt.smul

/- warning: differentiable_on.smul -> DifferentiableOn.smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_on.smul DifferentiableOn.smulₓ'. -/
theorem DifferentiableOn.smul (hc : DifferentiableOn 𝕜 c s) (hf : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y => c y • f y) s := fun x hx => (hc x hx).smul (hf x hx)
#align differentiable_on.smul DifferentiableOn.smul

/- warning: differentiable.smul -> Differentiable.smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable.smul Differentiable.smulₓ'. -/
@[simp]
theorem Differentiable.smul (hc : Differentiable 𝕜 c) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun y => c y • f y := fun x => (hc x).smul (hf x)
#align differentiable.smul Differentiable.smul

/- warning: fderiv_within_smul -> fderivWithin_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_smul fderivWithin_smulₓ'. -/
theorem fderivWithin_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (fun y => c y • f y) s x =
      c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smul_right (f x) :=
  (hc.HasFDerivWithinAt.smul hf.HasFDerivWithinAt).fderivWithin hxs
#align fderiv_within_smul fderivWithin_smul

/- warning: fderiv_smul -> fderiv_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_smul fderiv_smulₓ'. -/
theorem fderiv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun y => c y • f y) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smul_right (f x) :=
  (hc.HasFDerivAt.smul hf.HasFDerivAt).fderiv
#align fderiv_smul fderiv_smul

/- warning: has_strict_fderiv_at.smul_const -> HasStrictFDerivAt.smul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.smul_const HasStrictFDerivAt.smul_constₓ'. -/
theorem HasStrictFDerivAt.smul_const (hc : HasStrictFDerivAt c c' x) (f : F) :
    HasStrictFDerivAt (fun y => c y • f) (c'.smul_right f) x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasStrictFDerivAt_const f x)
#align has_strict_fderiv_at.smul_const HasStrictFDerivAt.smul_const

/- warning: has_fderiv_within_at.smul_const -> HasFDerivWithinAt.smul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.smul_const HasFDerivWithinAt.smul_constₓ'. -/
theorem HasFDerivWithinAt.smul_const (hc : HasFDerivWithinAt c c' s x) (f : F) :
    HasFDerivWithinAt (fun y => c y • f) (c'.smul_right f) s x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasFDerivWithinAt_const f x s)
#align has_fderiv_within_at.smul_const HasFDerivWithinAt.smul_const

/- warning: has_fderiv_at.smul_const -> HasFDerivAt.smul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.smul_const HasFDerivAt.smul_constₓ'. -/
theorem HasFDerivAt.smul_const (hc : HasFDerivAt c c' x) (f : F) :
    HasFDerivAt (fun y => c y • f) (c'.smul_right f) x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasFDerivAt_const f x)
#align has_fderiv_at.smul_const HasFDerivAt.smul_const

/- warning: differentiable_within_at.smul_const -> DifferentiableWithinAt.smul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.smul_const DifferentiableWithinAt.smul_constₓ'. -/
theorem DifferentiableWithinAt.smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    DifferentiableWithinAt 𝕜 (fun y => c y • f) s x :=
  (hc.HasFDerivWithinAt.smul_const f).DifferentiableWithinAt
#align differentiable_within_at.smul_const DifferentiableWithinAt.smul_const

/- warning: differentiable_at.smul_const -> DifferentiableAt.smul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_at.smul_const DifferentiableAt.smul_constₓ'. -/
theorem DifferentiableAt.smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    DifferentiableAt 𝕜 (fun y => c y • f) x :=
  (hc.HasFDerivAt.smul_const f).DifferentiableAt
#align differentiable_at.smul_const DifferentiableAt.smul_const

/- warning: differentiable_on.smul_const -> DifferentiableOn.smul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_on.smul_const DifferentiableOn.smul_constₓ'. -/
theorem DifferentiableOn.smul_const (hc : DifferentiableOn 𝕜 c s) (f : F) :
    DifferentiableOn 𝕜 (fun y => c y • f) s := fun x hx => (hc x hx).smul_const f
#align differentiable_on.smul_const DifferentiableOn.smul_const

/- warning: differentiable.smul_const -> Differentiable.smul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable.smul_const Differentiable.smul_constₓ'. -/
theorem Differentiable.smul_const (hc : Differentiable 𝕜 c) (f : F) :
    Differentiable 𝕜 fun y => c y • f := fun x => (hc x).smul_const f
#align differentiable.smul_const Differentiable.smul_const

/- warning: fderiv_within_smul_const -> fderivWithin_smul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_smul_const fderivWithin_smul_constₓ'. -/
theorem fderivWithin_smul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    fderivWithin 𝕜 (fun y => c y • f) s x = (fderivWithin 𝕜 c s x).smul_right f :=
  (hc.HasFDerivWithinAt.smul_const f).fderivWithin hxs
#align fderiv_within_smul_const fderivWithin_smul_const

/- warning: fderiv_smul_const -> fderiv_smul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_smul_const fderiv_smul_constₓ'. -/
theorem fderiv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    fderiv 𝕜 (fun y => c y • f) x = (fderiv 𝕜 c x).smul_right f :=
  (hc.HasFDerivAt.smul_const f).fderiv
#align fderiv_smul_const fderiv_smul_const

end Smul

section Mul

/-! ### Derivative of the product of two functions -/


variable {𝔸 𝔸' : Type _} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸] [NormedAlgebra 𝕜 𝔸']
  {a b : E → 𝔸} {a' b' : E →L[𝕜] 𝔸} {c d : E → 𝔸'} {c' d' : E →L[𝕜] 𝔸'}

/- warning: has_strict_fderiv_at.mul' -> HasStrictFDerivAt.mul' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.mul' HasStrictFDerivAt.mul'ₓ'. -/
theorem HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x)
    (hb : HasStrictFDerivAt b b' x) :
    HasStrictFDerivAt (fun y => a y * b y) (a x • b' + a'.smul_right (b x)) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).IsBoundedBilinearMap.HasStrictFDerivAt (a x, b x)).comp x
    (ha.Prod hb)
#align has_strict_fderiv_at.mul' HasStrictFDerivAt.mul'

/- warning: has_strict_fderiv_at.mul -> HasStrictFDerivAt.mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.mul HasStrictFDerivAt.mulₓ'. -/
theorem HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
    HasStrictFDerivAt (fun y => c y * d y) (c x • d' + d x • c') x := by convert hc.mul' hd; ext z;
  apply mul_comm
#align has_strict_fderiv_at.mul HasStrictFDerivAt.mul

/- warning: has_fderiv_within_at.mul' -> HasFDerivWithinAt.mul' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.mul' HasFDerivWithinAt.mul'ₓ'. -/
theorem HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a a' s x) (hb : HasFDerivWithinAt b b' s x) :
    HasFDerivWithinAt (fun y => a y * b y) (a x • b' + a'.smul_right (b x)) s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).IsBoundedBilinearMap.HasFDerivAt (a x, b x)).comp_hasFDerivWithinAt
    x (ha.Prod hb)
#align has_fderiv_within_at.mul' HasFDerivWithinAt.mul'

/- warning: has_fderiv_within_at.mul -> HasFDerivWithinAt.mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.mul HasFDerivWithinAt.mulₓ'. -/
theorem HasFDerivWithinAt.mul (hc : HasFDerivWithinAt c c' s x) (hd : HasFDerivWithinAt d d' s x) :
    HasFDerivWithinAt (fun y => c y * d y) (c x • d' + d x • c') s x := by convert hc.mul' hd;
  ext z; apply mul_comm
#align has_fderiv_within_at.mul HasFDerivWithinAt.mul

/- warning: has_fderiv_at.mul' -> HasFDerivAt.mul' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.mul' HasFDerivAt.mul'ₓ'. -/
theorem HasFDerivAt.mul' (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
    HasFDerivAt (fun y => a y * b y) (a x • b' + a'.smul_right (b x)) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).IsBoundedBilinearMap.HasFDerivAt (a x, b x)).comp x (ha.Prod hb)
#align has_fderiv_at.mul' HasFDerivAt.mul'

/- warning: has_fderiv_at.mul -> HasFDerivAt.mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.mul HasFDerivAt.mulₓ'. -/
theorem HasFDerivAt.mul (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
    HasFDerivAt (fun y => c y * d y) (c x • d' + d x • c') x := by convert hc.mul' hd; ext z;
  apply mul_comm
#align has_fderiv_at.mul HasFDerivAt.mul

/- warning: differentiable_within_at.mul -> DifferentiableWithinAt.mul is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {s : Set.{u2} E} {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸} {b : E -> 𝔸}, (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s x) -> (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) b s x) -> (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u3, u3, u3} 𝔸 𝔸 𝔸 (instHMul.{u3} 𝔸 (Distrib.toHasMul.{u3} 𝔸 (Ring.toDistrib.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) (a y) (b y)) s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {s : Set.{u2} E} {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸} {b : E -> 𝔸}, (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s x) -> (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) b s x) -> (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u1, u1, u1} 𝔸 𝔸 𝔸 (instHMul.{u1} 𝔸 (NonUnitalNonAssocRing.toMul.{u1} 𝔸 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝔸 (Ring.toNonAssocRing.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10))))) (a y) (b y)) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.mul DifferentiableWithinAt.mulₓ'. -/
theorem DifferentiableWithinAt.mul (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) : DifferentiableWithinAt 𝕜 (fun y => a y * b y) s x :=
  (ha.HasFDerivWithinAt.mul' hb.HasFDerivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.mul DifferentiableWithinAt.mul

/- warning: differentiable_at.mul -> DifferentiableAt.mul is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸} {b : E -> 𝔸}, (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a x) -> (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) b x) -> (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u3, u3, u3} 𝔸 𝔸 𝔸 (instHMul.{u3} 𝔸 (Distrib.toHasMul.{u3} 𝔸 (Ring.toDistrib.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) (a y) (b y)) x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸} {b : E -> 𝔸}, (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a x) -> (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) b x) -> (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u1, u1, u1} 𝔸 𝔸 𝔸 (instHMul.{u1} 𝔸 (NonUnitalNonAssocRing.toMul.{u1} 𝔸 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝔸 (Ring.toNonAssocRing.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10))))) (a y) (b y)) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.mul DifferentiableAt.mulₓ'. -/
@[simp]
theorem DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    DifferentiableAt 𝕜 (fun y => a y * b y) x :=
  (ha.HasFDerivAt.mul' hb.HasFDerivAt).DifferentiableAt
#align differentiable_at.mul DifferentiableAt.mul

/- warning: differentiable_on.mul -> DifferentiableOn.mul is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {s : Set.{u2} E} {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸} {b : E -> 𝔸}, (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s) -> (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) b s) -> (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u3, u3, u3} 𝔸 𝔸 𝔸 (instHMul.{u3} 𝔸 (Distrib.toHasMul.{u3} 𝔸 (Ring.toDistrib.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) (a y) (b y)) s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {s : Set.{u2} E} {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸} {b : E -> 𝔸}, (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s) -> (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) b s) -> (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u1, u1, u1} 𝔸 𝔸 𝔸 (instHMul.{u1} 𝔸 (NonUnitalNonAssocRing.toMul.{u1} 𝔸 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝔸 (Ring.toNonAssocRing.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10))))) (a y) (b y)) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.mul DifferentiableOn.mulₓ'. -/
theorem DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s) (hb : DifferentiableOn 𝕜 b s) :
    DifferentiableOn 𝕜 (fun y => a y * b y) s := fun x hx => (ha x hx).mul (hb x hx)
#align differentiable_on.mul DifferentiableOn.mul

/- warning: differentiable.mul -> Differentiable.mul is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸} {b : E -> 𝔸}, (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a) -> (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) b) -> (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u3, u3, u3} 𝔸 𝔸 𝔸 (instHMul.{u3} 𝔸 (Distrib.toHasMul.{u3} 𝔸 (Ring.toDistrib.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) (a y) (b y)))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸} {b : E -> 𝔸}, (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a) -> (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) b) -> (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u1, u1, u1} 𝔸 𝔸 𝔸 (instHMul.{u1} 𝔸 (NonUnitalNonAssocRing.toMul.{u1} 𝔸 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝔸 (Ring.toNonAssocRing.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10))))) (a y) (b y)))
Case conversion may be inaccurate. Consider using '#align differentiable.mul Differentiable.mulₓ'. -/
@[simp]
theorem Differentiable.mul (ha : Differentiable 𝕜 a) (hb : Differentiable 𝕜 b) :
    Differentiable 𝕜 fun y => a y * b y := fun x => (ha x).mul (hb x)
#align differentiable.mul Differentiable.mul

/- warning: differentiable_within_at.pow -> DifferentiableWithinAt.pow is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {s : Set.{u2} E} {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s x) -> (forall (n : Nat), DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (x : E) => HPow.hPow.{u3, 0, u3} 𝔸 Nat 𝔸 (instHPow.{u3, 0} 𝔸 Nat (Monoid.Pow.{u3} 𝔸 (Ring.toMonoid.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) (a x) n) s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {s : Set.{u2} E} {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s x) -> (forall (n : Nat), DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (x : E) => HPow.hPow.{u1, 0, u1} 𝔸 Nat 𝔸 (instHPow.{u1, 0} 𝔸 Nat (Monoid.Pow.{u1} 𝔸 (MonoidWithZero.toMonoid.{u1} 𝔸 (Semiring.toMonoidWithZero.{u1} 𝔸 (Ring.toSemiring.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10)))))) (a x) n) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.pow DifferentiableWithinAt.powₓ'. -/
theorem DifferentiableWithinAt.pow (ha : DifferentiableWithinAt 𝕜 a s x) :
    ∀ n : ℕ, DifferentiableWithinAt 𝕜 (fun x => a x ^ n) s x
  | 0 => by simp only [pow_zero, differentiableWithinAt_const]
  | n + 1 => by simp only [pow_succ, DifferentiableWithinAt.pow n, ha.mul]
#align differentiable_within_at.pow DifferentiableWithinAt.pow

/- warning: differentiable_at.pow -> DifferentiableAt.pow is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a x) -> (forall (n : Nat), DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (x : E) => HPow.hPow.{u3, 0, u3} 𝔸 Nat 𝔸 (instHPow.{u3, 0} 𝔸 Nat (Monoid.Pow.{u3} 𝔸 (Ring.toMonoid.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) (a x) n) x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a x) -> (forall (n : Nat), DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (x : E) => HPow.hPow.{u1, 0, u1} 𝔸 Nat 𝔸 (instHPow.{u1, 0} 𝔸 Nat (Monoid.Pow.{u1} 𝔸 (MonoidWithZero.toMonoid.{u1} 𝔸 (Semiring.toMonoidWithZero.{u1} 𝔸 (Ring.toSemiring.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10)))))) (a x) n) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.pow DifferentiableAt.powₓ'. -/
@[simp]
theorem DifferentiableAt.pow (ha : DifferentiableAt 𝕜 a x) (n : ℕ) :
    DifferentiableAt 𝕜 (fun x => a x ^ n) x :=
  differentiableWithinAt_univ.mp <| ha.DifferentiableWithinAt.pow n
#align differentiable_at.pow DifferentiableAt.pow

/- warning: differentiable_on.pow -> DifferentiableOn.pow is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {s : Set.{u2} E} {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s) -> (forall (n : Nat), DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (x : E) => HPow.hPow.{u3, 0, u3} 𝔸 Nat 𝔸 (instHPow.{u3, 0} 𝔸 Nat (Monoid.Pow.{u3} 𝔸 (Ring.toMonoid.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) (a x) n) s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {s : Set.{u2} E} {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s) -> (forall (n : Nat), DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (x : E) => HPow.hPow.{u1, 0, u1} 𝔸 Nat 𝔸 (instHPow.{u1, 0} 𝔸 Nat (Monoid.Pow.{u1} 𝔸 (MonoidWithZero.toMonoid.{u1} 𝔸 (Semiring.toMonoidWithZero.{u1} 𝔸 (Ring.toSemiring.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10)))))) (a x) n) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.pow DifferentiableOn.powₓ'. -/
theorem DifferentiableOn.pow (ha : DifferentiableOn 𝕜 a s) (n : ℕ) :
    DifferentiableOn 𝕜 (fun x => a x ^ n) s := fun x h => (ha x h).pow n
#align differentiable_on.pow DifferentiableOn.pow

/- warning: differentiable.pow -> Differentiable.pow is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸}, (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a) -> (forall (n : Nat), Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (x : E) => HPow.hPow.{u3, 0, u3} 𝔸 Nat 𝔸 (instHPow.{u3, 0} 𝔸 Nat (Monoid.Pow.{u3} 𝔸 (Ring.toMonoid.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) (a x) n))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸}, (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a) -> (forall (n : Nat), Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (x : E) => HPow.hPow.{u1, 0, u1} 𝔸 Nat 𝔸 (instHPow.{u1, 0} 𝔸 Nat (Monoid.Pow.{u1} 𝔸 (MonoidWithZero.toMonoid.{u1} 𝔸 (Semiring.toMonoidWithZero.{u1} 𝔸 (Ring.toSemiring.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10)))))) (a x) n))
Case conversion may be inaccurate. Consider using '#align differentiable.pow Differentiable.powₓ'. -/
@[simp]
theorem Differentiable.pow (ha : Differentiable 𝕜 a) (n : ℕ) : Differentiable 𝕜 fun x => a x ^ n :=
  fun x => (ha x).pow n
#align differentiable.pow Differentiable.pow

/- warning: fderiv_within_mul' -> fderivWithin_mul' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_mul' fderivWithin_mul'ₓ'. -/
theorem fderivWithin_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) :
    fderivWithin 𝕜 (fun y => a y * b y) s x =
      a x • fderivWithin 𝕜 b s x + (fderivWithin 𝕜 a s x).smul_right (b x) :=
  (ha.HasFDerivWithinAt.mul' hb.HasFDerivWithinAt).fderivWithin hxs
#align fderiv_within_mul' fderivWithin_mul'

/- warning: fderiv_within_mul -> fderivWithin_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_mul fderivWithin_mulₓ'. -/
theorem fderivWithin_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (fun y => c y * d y) s x =
      c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x :=
  (hc.HasFDerivWithinAt.mul hd.HasFDerivWithinAt).fderivWithin hxs
#align fderiv_within_mul fderivWithin_mul

/- warning: fderiv_mul' -> fderiv_mul' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_mul' fderiv_mul'ₓ'. -/
theorem fderiv_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    fderiv 𝕜 (fun y => a y * b y) x = a x • fderiv 𝕜 b x + (fderiv 𝕜 a x).smul_right (b x) :=
  (ha.HasFDerivAt.mul' hb.HasFDerivAt).fderiv
#align fderiv_mul' fderiv_mul'

/- warning: fderiv_mul -> fderiv_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_mul fderiv_mulₓ'. -/
theorem fderiv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => c y * d y) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  (hc.HasFDerivAt.mul hd.HasFDerivAt).fderiv
#align fderiv_mul fderiv_mul

/- warning: has_strict_fderiv_at.mul_const' -> HasStrictFDerivAt.mul_const' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.mul_const' HasStrictFDerivAt.mul_const'ₓ'. -/
theorem HasStrictFDerivAt.mul_const' (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
    HasStrictFDerivAt (fun y => a y * b) (a'.smul_right b) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).HasStrictFDerivAt.comp x ha
#align has_strict_fderiv_at.mul_const' HasStrictFDerivAt.mul_const'

/- warning: has_strict_fderiv_at.mul_const -> HasStrictFDerivAt.mul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.mul_const HasStrictFDerivAt.mul_constₓ'. -/
theorem HasStrictFDerivAt.mul_const (hc : HasStrictFDerivAt c c' x) (d : 𝔸') :
    HasStrictFDerivAt (fun y => c y * d) (d • c') x := by convert hc.mul_const' d; ext z;
  apply mul_comm
#align has_strict_fderiv_at.mul_const HasStrictFDerivAt.mul_const

/- warning: has_fderiv_within_at.mul_const' -> HasFDerivWithinAt.mul_const' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.mul_const' HasFDerivWithinAt.mul_const'ₓ'. -/
theorem HasFDerivWithinAt.mul_const' (ha : HasFDerivWithinAt a a' s x) (b : 𝔸) :
    HasFDerivWithinAt (fun y => a y * b) (a'.smul_right b) s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).HasFDerivAt.comp_hasFDerivWithinAt x ha
#align has_fderiv_within_at.mul_const' HasFDerivWithinAt.mul_const'

/- warning: has_fderiv_within_at.mul_const -> HasFDerivWithinAt.mul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.mul_const HasFDerivWithinAt.mul_constₓ'. -/
theorem HasFDerivWithinAt.mul_const (hc : HasFDerivWithinAt c c' s x) (d : 𝔸') :
    HasFDerivWithinAt (fun y => c y * d) (d • c') s x := by convert hc.mul_const' d; ext z;
  apply mul_comm
#align has_fderiv_within_at.mul_const HasFDerivWithinAt.mul_const

/- warning: has_fderiv_at.mul_const' -> HasFDerivAt.mul_const' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.mul_const' HasFDerivAt.mul_const'ₓ'. -/
theorem HasFDerivAt.mul_const' (ha : HasFDerivAt a a' x) (b : 𝔸) :
    HasFDerivAt (fun y => a y * b) (a'.smul_right b) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).HasFDerivAt.comp x ha
#align has_fderiv_at.mul_const' HasFDerivAt.mul_const'

/- warning: has_fderiv_at.mul_const -> HasFDerivAt.mul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.mul_const HasFDerivAt.mul_constₓ'. -/
theorem HasFDerivAt.mul_const (hc : HasFDerivAt c c' x) (d : 𝔸') :
    HasFDerivAt (fun y => c y * d) (d • c') x := by convert hc.mul_const' d; ext z; apply mul_comm
#align has_fderiv_at.mul_const HasFDerivAt.mul_const

/- warning: differentiable_within_at.mul_const -> DifferentiableWithinAt.mul_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {s : Set.{u2} E} {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s x) -> (forall (b : 𝔸), DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u3, u3, u3} 𝔸 𝔸 𝔸 (instHMul.{u3} 𝔸 (Distrib.toHasMul.{u3} 𝔸 (Ring.toDistrib.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) (a y) b) s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {s : Set.{u2} E} {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s x) -> (forall (b : 𝔸), DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u1, u1, u1} 𝔸 𝔸 𝔸 (instHMul.{u1} 𝔸 (NonUnitalNonAssocRing.toMul.{u1} 𝔸 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝔸 (Ring.toNonAssocRing.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10))))) (a y) b) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.mul_const DifferentiableWithinAt.mul_constₓ'. -/
theorem DifferentiableWithinAt.mul_const (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => a y * b) s x :=
  (ha.HasFDerivWithinAt.mul_const' b).DifferentiableWithinAt
#align differentiable_within_at.mul_const DifferentiableWithinAt.mul_const

/- warning: differentiable_at.mul_const -> DifferentiableAt.mul_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a x) -> (forall (b : 𝔸), DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u3, u3, u3} 𝔸 𝔸 𝔸 (instHMul.{u3} 𝔸 (Distrib.toHasMul.{u3} 𝔸 (Ring.toDistrib.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) (a y) b) x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a x) -> (forall (b : 𝔸), DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u1, u1, u1} 𝔸 𝔸 𝔸 (instHMul.{u1} 𝔸 (NonUnitalNonAssocRing.toMul.{u1} 𝔸 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝔸 (Ring.toNonAssocRing.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10))))) (a y) b) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.mul_const DifferentiableAt.mul_constₓ'. -/
theorem DifferentiableAt.mul_const (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => a y * b) x :=
  (ha.HasFDerivAt.mul_const' b).DifferentiableAt
#align differentiable_at.mul_const DifferentiableAt.mul_const

/- warning: differentiable_on.mul_const -> DifferentiableOn.mul_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {s : Set.{u2} E} {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s) -> (forall (b : 𝔸), DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u3, u3, u3} 𝔸 𝔸 𝔸 (instHMul.{u3} 𝔸 (Distrib.toHasMul.{u3} 𝔸 (Ring.toDistrib.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) (a y) b) s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {s : Set.{u2} E} {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s) -> (forall (b : 𝔸), DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u1, u1, u1} 𝔸 𝔸 𝔸 (instHMul.{u1} 𝔸 (NonUnitalNonAssocRing.toMul.{u1} 𝔸 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝔸 (Ring.toNonAssocRing.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10))))) (a y) b) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.mul_const DifferentiableOn.mul_constₓ'. -/
theorem DifferentiableOn.mul_const (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => a y * b) s := fun x hx => (ha x hx).mul_const b
#align differentiable_on.mul_const DifferentiableOn.mul_const

/- warning: differentiable.mul_const -> Differentiable.mul_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸}, (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a) -> (forall (b : 𝔸), Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u3, u3, u3} 𝔸 𝔸 𝔸 (instHMul.{u3} 𝔸 (Distrib.toHasMul.{u3} 𝔸 (Ring.toDistrib.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) (a y) b))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸}, (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a) -> (forall (b : 𝔸), Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u1, u1, u1} 𝔸 𝔸 𝔸 (instHMul.{u1} 𝔸 (NonUnitalNonAssocRing.toMul.{u1} 𝔸 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝔸 (Ring.toNonAssocRing.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10))))) (a y) b))
Case conversion may be inaccurate. Consider using '#align differentiable.mul_const Differentiable.mul_constₓ'. -/
theorem Differentiable.mul_const (ha : Differentiable 𝕜 a) (b : 𝔸) :
    Differentiable 𝕜 fun y => a y * b := fun x => (ha x).mul_const b
#align differentiable.mul_const Differentiable.mul_const

/- warning: fderiv_within_mul_const' -> fderivWithin_mul_const' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_mul_const' fderivWithin_mul_const'ₓ'. -/
theorem fderivWithin_mul_const' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => a y * b) s x = (fderivWithin 𝕜 a s x).smul_right b :=
  (ha.HasFDerivWithinAt.mul_const' b).fderivWithin hxs
#align fderiv_within_mul_const' fderivWithin_mul_const'

/- warning: fderiv_within_mul_const -> fderivWithin_mul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_mul_const fderivWithin_mul_constₓ'. -/
theorem fderivWithin_mul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸') :
    fderivWithin 𝕜 (fun y => c y * d) s x = d • fderivWithin 𝕜 c s x :=
  (hc.HasFDerivWithinAt.mul_const d).fderivWithin hxs
#align fderiv_within_mul_const fderivWithin_mul_const

/- warning: fderiv_mul_const' -> fderiv_mul_const' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_mul_const' fderiv_mul_const'ₓ'. -/
theorem fderiv_mul_const' (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => a y * b) x = (fderiv 𝕜 a x).smul_right b :=
  (ha.HasFDerivAt.mul_const' b).fderiv
#align fderiv_mul_const' fderiv_mul_const'

/- warning: fderiv_mul_const -> fderiv_mul_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_mul_const fderiv_mul_constₓ'. -/
theorem fderiv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸') :
    fderiv 𝕜 (fun y => c y * d) x = d • fderiv 𝕜 c x :=
  (hc.HasFDerivAt.mul_const d).fderiv
#align fderiv_mul_const fderiv_mul_const

/- warning: has_strict_fderiv_at.const_mul -> HasStrictFDerivAt.const_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.const_mul HasStrictFDerivAt.const_mulₓ'. -/
theorem HasStrictFDerivAt.const_mul (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
    HasStrictFDerivAt (fun y => b * a y) (b • a') x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).HasStrictFDerivAt.comp x ha
#align has_strict_fderiv_at.const_mul HasStrictFDerivAt.const_mul

/- warning: has_fderiv_within_at.const_mul -> HasFDerivWithinAt.const_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.const_mul HasFDerivWithinAt.const_mulₓ'. -/
theorem HasFDerivWithinAt.const_mul (ha : HasFDerivWithinAt a a' s x) (b : 𝔸) :
    HasFDerivWithinAt (fun y => b * a y) (b • a') s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).HasFDerivAt.comp_hasFDerivWithinAt x ha
#align has_fderiv_within_at.const_mul HasFDerivWithinAt.const_mul

/- warning: has_fderiv_at.const_mul -> HasFDerivAt.const_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.const_mul HasFDerivAt.const_mulₓ'. -/
theorem HasFDerivAt.const_mul (ha : HasFDerivAt a a' x) (b : 𝔸) :
    HasFDerivAt (fun y => b * a y) (b • a') x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).HasFDerivAt.comp x ha
#align has_fderiv_at.const_mul HasFDerivAt.const_mul

/- warning: differentiable_within_at.const_mul -> DifferentiableWithinAt.const_mul is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {s : Set.{u2} E} {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s x) -> (forall (b : 𝔸), DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u3, u3, u3} 𝔸 𝔸 𝔸 (instHMul.{u3} 𝔸 (Distrib.toHasMul.{u3} 𝔸 (Ring.toDistrib.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) b (a y)) s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {s : Set.{u2} E} {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s x) -> (forall (b : 𝔸), DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u1, u1, u1} 𝔸 𝔸 𝔸 (instHMul.{u1} 𝔸 (NonUnitalNonAssocRing.toMul.{u1} 𝔸 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝔸 (Ring.toNonAssocRing.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10))))) b (a y)) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.const_mul DifferentiableWithinAt.const_mulₓ'. -/
theorem DifferentiableWithinAt.const_mul (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => b * a y) s x :=
  (ha.HasFDerivWithinAt.const_mul b).DifferentiableWithinAt
#align differentiable_within_at.const_mul DifferentiableWithinAt.const_mul

/- warning: differentiable_at.const_mul -> DifferentiableAt.const_mul is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a x) -> (forall (b : 𝔸), DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u3, u3, u3} 𝔸 𝔸 𝔸 (instHMul.{u3} 𝔸 (Distrib.toHasMul.{u3} 𝔸 (Ring.toDistrib.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) b (a y)) x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a x) -> (forall (b : 𝔸), DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u1, u1, u1} 𝔸 𝔸 𝔸 (instHMul.{u1} 𝔸 (NonUnitalNonAssocRing.toMul.{u1} 𝔸 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝔸 (Ring.toNonAssocRing.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10))))) b (a y)) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.const_mul DifferentiableAt.const_mulₓ'. -/
theorem DifferentiableAt.const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => b * a y) x :=
  (ha.HasFDerivAt.const_mul b).DifferentiableAt
#align differentiable_at.const_mul DifferentiableAt.const_mul

/- warning: differentiable_on.const_mul -> DifferentiableOn.const_mul is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {s : Set.{u2} E} {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s) -> (forall (b : 𝔸), DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u3, u3, u3} 𝔸 𝔸 𝔸 (instHMul.{u3} 𝔸 (Distrib.toHasMul.{u3} 𝔸 (Ring.toDistrib.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) b (a y)) s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {s : Set.{u2} E} {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸}, (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a s) -> (forall (b : 𝔸), DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u1, u1, u1} 𝔸 𝔸 𝔸 (instHMul.{u1} 𝔸 (NonUnitalNonAssocRing.toMul.{u1} 𝔸 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝔸 (Ring.toNonAssocRing.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10))))) b (a y)) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.const_mul DifferentiableOn.const_mulₓ'. -/
theorem DifferentiableOn.const_mul (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => b * a y) s := fun x hx => (ha x hx).const_mul b
#align differentiable_on.const_mul DifferentiableOn.const_mul

/- warning: differentiable.const_mul -> Differentiable.const_mul is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {𝔸 : Type.{u3}} [_inst_10 : NormedRing.{u3} 𝔸] [_inst_12 : NormedAlgebra.{u1, u3} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u3} 𝔸 _inst_10)] {a : E -> 𝔸}, (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a) -> (forall (b : 𝔸), Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u3} 𝔸 (NormedRing.toNonUnitalNormedRing.{u3} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u3, u3, u3} 𝔸 𝔸 𝔸 (instHMul.{u3} 𝔸 (Distrib.toHasMul.{u3} 𝔸 (Ring.toDistrib.{u3} 𝔸 (NormedRing.toRing.{u3} 𝔸 _inst_10)))) b (a y)))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {𝔸 : Type.{u1}} [_inst_10 : NormedRing.{u1} 𝔸] [_inst_12 : NormedAlgebra.{u3, u1} 𝕜 𝔸 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u1} 𝔸 _inst_10)] {a : E -> 𝔸}, (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) a) -> (forall (b : 𝔸), Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 𝔸 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝔸 (NormedRing.toNonUnitalNormedRing.{u1} 𝔸 _inst_10)) (NormedAlgebra.toNormedSpace'.{u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) 𝔸 _inst_10 _inst_12) (fun (y : E) => HMul.hMul.{u1, u1, u1} 𝔸 𝔸 𝔸 (instHMul.{u1} 𝔸 (NonUnitalNonAssocRing.toMul.{u1} 𝔸 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝔸 (Ring.toNonAssocRing.{u1} 𝔸 (NormedRing.toRing.{u1} 𝔸 _inst_10))))) b (a y)))
Case conversion may be inaccurate. Consider using '#align differentiable.const_mul Differentiable.const_mulₓ'. -/
theorem Differentiable.const_mul (ha : Differentiable 𝕜 a) (b : 𝔸) :
    Differentiable 𝕜 fun y => b * a y := fun x => (ha x).const_mul b
#align differentiable.const_mul Differentiable.const_mul

/- warning: fderiv_within_const_mul -> fderivWithin_const_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_const_mul fderivWithin_const_mulₓ'. -/
theorem fderivWithin_const_mul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => b * a y) s x = b • fderivWithin 𝕜 a s x :=
  (ha.HasFDerivWithinAt.const_mul b).fderivWithin hxs
#align fderiv_within_const_mul fderivWithin_const_mul

/- warning: fderiv_const_mul -> fderiv_const_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_const_mul fderiv_const_mulₓ'. -/
theorem fderiv_const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => b * a y) x = b • fderiv 𝕜 a x :=
  (ha.HasFDerivAt.const_mul b).fderiv
#align fderiv_const_mul fderiv_const_mul

end Mul

section AlgebraInverse

variable {R : Type _} [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]

open NormedRing ContinuousLinearMap Ring

/- warning: has_fderiv_at_ring_inverse -> hasFDerivAt_ring_inverse is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_ring_inverse hasFDerivAt_ring_inverseₓ'. -/
/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `λ t, - x⁻¹ * t * x⁻¹`. -/
theorem hasFDerivAt_ring_inverse (x : Rˣ) :
    HasFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x :=
  by
  have h_is_o : (fun t : R => inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =o[𝓝 0] fun t : R => t :=
    by
    refine' (inverse_add_norm_diff_second_order x).trans_isLittleO (is_o_norm_norm.mp _)
    simp only [norm_pow, norm_norm]
    have h12 : 1 < 2 := by norm_num
    convert(Asymptotics.isLittleO_pow_pow h12).comp_tendsto tendsto_norm_zero
    ext; simp
  have h_lim : tendsto (fun y : R => y - x) (𝓝 x) (𝓝 0) :=
    by
    refine' tendsto_zero_iff_norm_tendsto_zero.mpr _
    exact tendsto_iff_norm_tendsto_zero.mp tendsto_id
  simp only [HasFDerivAt, HasFDerivAtFilter]
  convert h_is_o.comp_tendsto h_lim
  ext y
  simp only [coe_comp', Function.comp_apply, mul_left_right_apply, neg_apply, inverse_unit x,
    Units.inv_mul, add_sub_cancel'_right, mul_sub, sub_mul, one_mul, sub_neg_eq_add]
#align has_fderiv_at_ring_inverse hasFDerivAt_ring_inverse

/- warning: differentiable_at_inverse -> differentiableAt_inverse is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {R : Type.{u2}} [_inst_10 : NormedRing.{u2} R] [_inst_11 : NormedAlgebra.{u1, u2} 𝕜 R (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u2} R _inst_10)] [_inst_12 : CompleteSpace.{u2} R (PseudoMetricSpace.toUniformSpace.{u2} R (SeminormedRing.toPseudoMetricSpace.{u2} R (NormedRing.toSeminormedRing.{u2} R _inst_10)))] (x : Units.{u2} R (Ring.toMonoid.{u2} R (NormedRing.toRing.{u2} R _inst_10))), DifferentiableAt.{u1, u2, u2} 𝕜 _inst_1 R (NonUnitalNormedRing.toNormedAddCommGroup.{u2} R (NormedRing.toNonUnitalNormedRing.{u2} R _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) R _inst_10 _inst_11) R (NonUnitalNormedRing.toNormedAddCommGroup.{u2} R (NormedRing.toNonUnitalNormedRing.{u2} R _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) R _inst_10 _inst_11) (Ring.inverse.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (NormedRing.toRing.{u2} R _inst_10)))) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} R (Ring.toMonoid.{u2} R (NormedRing.toRing.{u2} R _inst_10))) R (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} R (Ring.toMonoid.{u2} R (NormedRing.toRing.{u2} R _inst_10))) R (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} R (Ring.toMonoid.{u2} R (NormedRing.toRing.{u2} R _inst_10))) R (coeBase.{succ u2, succ u2} (Units.{u2} R (Ring.toMonoid.{u2} R (NormedRing.toRing.{u2} R _inst_10))) R (Units.hasCoe.{u2} R (Ring.toMonoid.{u2} R (NormedRing.toRing.{u2} R _inst_10)))))) x)
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {R : Type.{u2}} [_inst_10 : NormedRing.{u2} R] [_inst_11 : NormedAlgebra.{u1, u2} 𝕜 R (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedRing.toSeminormedRing.{u2} R _inst_10)] [_inst_12 : CompleteSpace.{u2} R (PseudoMetricSpace.toUniformSpace.{u2} R (SeminormedRing.toPseudoMetricSpace.{u2} R (NormedRing.toSeminormedRing.{u2} R _inst_10)))] (x : Units.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (NormedRing.toRing.{u2} R _inst_10))))), DifferentiableAt.{u1, u2, u2} 𝕜 _inst_1 R (NonUnitalNormedRing.toNormedAddCommGroup.{u2} R (NormedRing.toNonUnitalNormedRing.{u2} R _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) R _inst_10 _inst_11) R (NonUnitalNormedRing.toNormedAddCommGroup.{u2} R (NormedRing.toNonUnitalNormedRing.{u2} R _inst_10)) (NormedAlgebra.toNormedSpace'.{u1, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) R _inst_10 _inst_11) (Ring.inverse.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (NormedRing.toRing.{u2} R _inst_10)))) (Units.val.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (NormedRing.toRing.{u2} R _inst_10)))) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at_inverse differentiableAt_inverseₓ'. -/
theorem differentiableAt_inverse (x : Rˣ) : DifferentiableAt 𝕜 (@Ring.inverse R _) x :=
  (hasFDerivAt_ring_inverse x).DifferentiableAt
#align differentiable_at_inverse differentiableAt_inverse

/- warning: fderiv_inverse -> fderiv_inverse is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_inverse fderiv_inverseₓ'. -/
theorem fderiv_inverse (x : Rˣ) : fderiv 𝕜 (@Ring.inverse R _) x = -mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹ :=
  (hasFDerivAt_ring_inverse x).fderiv
#align fderiv_inverse fderiv_inverse

end AlgebraInverse

end

