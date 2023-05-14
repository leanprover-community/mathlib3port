/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.calculus.fderiv.mul
! leanprover-community/mathlib commit e3fb84046afd187b710170887195d50bada934ee
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Fderiv.Bilinear

/-!
# Multiplicative operations on derivatives

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

theorem HasStrictFderivAt.clm_comp (hc : HasStrictFderivAt c c' x) (hd : HasStrictFderivAt d d' x) :
    HasStrictFderivAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
  (isBoundedBilinearMapComp.HasStrictFderivAt (c x, d x)).comp x <| hc.Prod hd
#align has_strict_fderiv_at.clm_comp HasStrictFderivAt.clm_comp

theorem HasFderivWithinAt.clm_comp (hc : HasFderivWithinAt c c' s x)
    (hd : HasFderivWithinAt d d' s x) :
    HasFderivWithinAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') s x :=
  (isBoundedBilinearMapComp.HasFderivAt (c x, d x)).comp_hasFderivWithinAt x <| hc.Prod hd
#align has_fderiv_within_at.clm_comp HasFderivWithinAt.clm_comp

theorem HasFderivAt.clm_comp (hc : HasFderivAt c c' x) (hd : HasFderivAt d d' x) :
    HasFderivAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
  (isBoundedBilinearMapComp.HasFderivAt (c x, d x)).comp x <| hc.Prod hd
#align has_fderiv_at.clm_comp HasFderivAt.clm_comp

theorem DifferentiableWithinAt.clm_comp (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    DifferentiableWithinAt 𝕜 (fun y => (c y).comp (d y)) s x :=
  (hc.HasFderivWithinAt.clm_comp hd.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.clm_comp DifferentiableWithinAt.clm_comp

theorem DifferentiableAt.clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    DifferentiableAt 𝕜 (fun y => (c y).comp (d y)) x :=
  (hc.HasFderivAt.clm_comp hd.HasFderivAt).DifferentiableAt
#align differentiable_at.clm_comp DifferentiableAt.clm_comp

theorem DifferentiableOn.clm_comp (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s) :
    DifferentiableOn 𝕜 (fun y => (c y).comp (d y)) s := fun x hx => (hc x hx).clm_comp (hd x hx)
#align differentiable_on.clm_comp DifferentiableOn.clm_comp

theorem Differentiable.clm_comp (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) :
    Differentiable 𝕜 fun y => (c y).comp (d y) := fun x => (hc x).clm_comp (hd x)
#align differentiable.clm_comp Differentiable.clm_comp

theorem fderivWithin_clm_comp (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (fun y => (c y).comp (d y)) s x =
      (compL 𝕜 F G H (c x)).comp (fderivWithin 𝕜 d s x) +
        ((compL 𝕜 F G H).flip (d x)).comp (fderivWithin 𝕜 c s x) :=
  (hc.HasFderivWithinAt.clm_comp hd.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_clm_comp fderivWithin_clm_comp

theorem fderiv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => (c y).comp (d y)) x =
      (compL 𝕜 F G H (c x)).comp (fderiv 𝕜 d x) +
        ((compL 𝕜 F G H).flip (d x)).comp (fderiv 𝕜 c x) :=
  (hc.HasFderivAt.clm_comp hd.HasFderivAt).fderiv
#align fderiv_clm_comp fderiv_clm_comp

theorem HasStrictFderivAt.clm_apply (hc : HasStrictFderivAt c c' x)
    (hu : HasStrictFderivAt u u' x) :
    HasStrictFderivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
  (isBoundedBilinearMapApply.HasStrictFderivAt (c x, u x)).comp x (hc.Prod hu)
#align has_strict_fderiv_at.clm_apply HasStrictFderivAt.clm_apply

theorem HasFderivWithinAt.clm_apply (hc : HasFderivWithinAt c c' s x)
    (hu : HasFderivWithinAt u u' s x) :
    HasFderivWithinAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) s x :=
  (isBoundedBilinearMapApply.HasFderivAt (c x, u x)).comp_hasFderivWithinAt x (hc.Prod hu)
#align has_fderiv_within_at.clm_apply HasFderivWithinAt.clm_apply

theorem HasFderivAt.clm_apply (hc : HasFderivAt c c' x) (hu : HasFderivAt u u' x) :
    HasFderivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
  (isBoundedBilinearMapApply.HasFderivAt (c x, u x)).comp x (hc.Prod hu)
#align has_fderiv_at.clm_apply HasFderivAt.clm_apply

theorem DifferentiableWithinAt.clm_apply (hc : DifferentiableWithinAt 𝕜 c s x)
    (hu : DifferentiableWithinAt 𝕜 u s x) : DifferentiableWithinAt 𝕜 (fun y => (c y) (u y)) s x :=
  (hc.HasFderivWithinAt.clm_apply hu.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.clm_apply DifferentiableWithinAt.clm_apply

theorem DifferentiableAt.clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    DifferentiableAt 𝕜 (fun y => (c y) (u y)) x :=
  (hc.HasFderivAt.clm_apply hu.HasFderivAt).DifferentiableAt
#align differentiable_at.clm_apply DifferentiableAt.clm_apply

theorem DifferentiableOn.clm_apply (hc : DifferentiableOn 𝕜 c s) (hu : DifferentiableOn 𝕜 u s) :
    DifferentiableOn 𝕜 (fun y => (c y) (u y)) s := fun x hx => (hc x hx).clm_apply (hu x hx)
#align differentiable_on.clm_apply DifferentiableOn.clm_apply

theorem Differentiable.clm_apply (hc : Differentiable 𝕜 c) (hu : Differentiable 𝕜 u) :
    Differentiable 𝕜 fun y => (c y) (u y) := fun x => (hc x).clm_apply (hu x)
#align differentiable.clm_apply Differentiable.clm_apply

theorem fderivWithin_clm_apply (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s x) :
    fderivWithin 𝕜 (fun y => (c y) (u y)) s x =
      (c x).comp (fderivWithin 𝕜 u s x) + (fderivWithin 𝕜 c s x).flip (u x) :=
  (hc.HasFderivWithinAt.clm_apply hu.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_clm_apply fderivWithin_clm_apply

theorem fderiv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    fderiv 𝕜 (fun y => (c y) (u y)) x = (c x).comp (fderiv 𝕜 u x) + (fderiv 𝕜 c x).flip (u x) :=
  (hc.HasFderivAt.clm_apply hu.HasFderivAt).fderiv
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

theorem HasStrictFderivAt.smul (hc : HasStrictFderivAt c c' x) (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun y => c y • f y) (c x • f' + c'.smul_right (f x)) x :=
  (isBoundedBilinearMapSmul.HasStrictFderivAt (c x, f x)).comp x <| hc.Prod hf
#align has_strict_fderiv_at.smul HasStrictFderivAt.smul

theorem HasFderivWithinAt.smul (hc : HasFderivWithinAt c c' s x) (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun y => c y • f y) (c x • f' + c'.smul_right (f x)) s x :=
  (isBoundedBilinearMapSmul.HasFderivAt (c x, f x)).comp_hasFderivWithinAt x <| hc.Prod hf
#align has_fderiv_within_at.smul HasFderivWithinAt.smul

theorem HasFderivAt.smul (hc : HasFderivAt c c' x) (hf : HasFderivAt f f' x) :
    HasFderivAt (fun y => c y • f y) (c x • f' + c'.smul_right (f x)) x :=
  (isBoundedBilinearMapSmul.HasFderivAt (c x, f x)).comp x <| hc.Prod hf
#align has_fderiv_at.smul HasFderivAt.smul

theorem DifferentiableWithinAt.smul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (fun y => c y • f y) s x :=
  (hc.HasFderivWithinAt.smul hf.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.smul DifferentiableWithinAt.smul

@[simp]
theorem DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y => c y • f y) x :=
  (hc.HasFderivAt.smul hf.HasFderivAt).DifferentiableAt
#align differentiable_at.smul DifferentiableAt.smul

theorem DifferentiableOn.smul (hc : DifferentiableOn 𝕜 c s) (hf : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y => c y • f y) s := fun x hx => (hc x hx).smul (hf x hx)
#align differentiable_on.smul DifferentiableOn.smul

@[simp]
theorem Differentiable.smul (hc : Differentiable 𝕜 c) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun y => c y • f y := fun x => (hc x).smul (hf x)
#align differentiable.smul Differentiable.smul

theorem fderivWithin_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (fun y => c y • f y) s x =
      c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smul_right (f x) :=
  (hc.HasFderivWithinAt.smul hf.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_smul fderivWithin_smul

theorem fderiv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun y => c y • f y) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smul_right (f x) :=
  (hc.HasFderivAt.smul hf.HasFderivAt).fderiv
#align fderiv_smul fderiv_smul

theorem HasStrictFderivAt.smul_const (hc : HasStrictFderivAt c c' x) (f : F) :
    HasStrictFderivAt (fun y => c y • f) (c'.smul_right f) x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasStrictFderivAt_const f x)
#align has_strict_fderiv_at.smul_const HasStrictFderivAt.smul_const

theorem HasFderivWithinAt.smul_const (hc : HasFderivWithinAt c c' s x) (f : F) :
    HasFderivWithinAt (fun y => c y • f) (c'.smul_right f) s x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasFderivWithinAt_const f x s)
#align has_fderiv_within_at.smul_const HasFderivWithinAt.smul_const

theorem HasFderivAt.smul_const (hc : HasFderivAt c c' x) (f : F) :
    HasFderivAt (fun y => c y • f) (c'.smul_right f) x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasFderivAt_const f x)
#align has_fderiv_at.smul_const HasFderivAt.smul_const

theorem DifferentiableWithinAt.smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    DifferentiableWithinAt 𝕜 (fun y => c y • f) s x :=
  (hc.HasFderivWithinAt.smul_const f).DifferentiableWithinAt
#align differentiable_within_at.smul_const DifferentiableWithinAt.smul_const

theorem DifferentiableAt.smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    DifferentiableAt 𝕜 (fun y => c y • f) x :=
  (hc.HasFderivAt.smul_const f).DifferentiableAt
#align differentiable_at.smul_const DifferentiableAt.smul_const

theorem DifferentiableOn.smul_const (hc : DifferentiableOn 𝕜 c s) (f : F) :
    DifferentiableOn 𝕜 (fun y => c y • f) s := fun x hx => (hc x hx).smul_const f
#align differentiable_on.smul_const DifferentiableOn.smul_const

theorem Differentiable.smul_const (hc : Differentiable 𝕜 c) (f : F) :
    Differentiable 𝕜 fun y => c y • f := fun x => (hc x).smul_const f
#align differentiable.smul_const Differentiable.smul_const

theorem fderivWithin_smul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    fderivWithin 𝕜 (fun y => c y • f) s x = (fderivWithin 𝕜 c s x).smul_right f :=
  (hc.HasFderivWithinAt.smul_const f).fderivWithin hxs
#align fderiv_within_smul_const fderivWithin_smul_const

theorem fderiv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    fderiv 𝕜 (fun y => c y • f) x = (fderiv 𝕜 c x).smul_right f :=
  (hc.HasFderivAt.smul_const f).fderiv
#align fderiv_smul_const fderiv_smul_const

end Smul

section Mul

/-! ### Derivative of the product of two functions -/


variable {𝔸 𝔸' : Type _} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸] [NormedAlgebra 𝕜 𝔸']
  {a b : E → 𝔸} {a' b' : E →L[𝕜] 𝔸} {c d : E → 𝔸'} {c' d' : E →L[𝕜] 𝔸'}

theorem HasStrictFderivAt.mul' {x : E} (ha : HasStrictFderivAt a a' x)
    (hb : HasStrictFderivAt b b' x) :
    HasStrictFderivAt (fun y => a y * b y) (a x • b' + a'.smul_right (b x)) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).IsBoundedBilinearMap.HasStrictFderivAt (a x, b x)).comp x
    (ha.Prod hb)
#align has_strict_fderiv_at.mul' HasStrictFderivAt.mul'

theorem HasStrictFderivAt.mul (hc : HasStrictFderivAt c c' x) (hd : HasStrictFderivAt d d' x) :
    HasStrictFderivAt (fun y => c y * d y) (c x • d' + d x • c') x :=
  by
  convert hc.mul' hd
  ext z
  apply mul_comm
#align has_strict_fderiv_at.mul HasStrictFderivAt.mul

theorem HasFderivWithinAt.mul' (ha : HasFderivWithinAt a a' s x) (hb : HasFderivWithinAt b b' s x) :
    HasFderivWithinAt (fun y => a y * b y) (a x • b' + a'.smul_right (b x)) s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).IsBoundedBilinearMap.HasFderivAt (a x, b x)).comp_hasFderivWithinAt
    x (ha.Prod hb)
#align has_fderiv_within_at.mul' HasFderivWithinAt.mul'

theorem HasFderivWithinAt.mul (hc : HasFderivWithinAt c c' s x) (hd : HasFderivWithinAt d d' s x) :
    HasFderivWithinAt (fun y => c y * d y) (c x • d' + d x • c') s x :=
  by
  convert hc.mul' hd
  ext z
  apply mul_comm
#align has_fderiv_within_at.mul HasFderivWithinAt.mul

theorem HasFderivAt.mul' (ha : HasFderivAt a a' x) (hb : HasFderivAt b b' x) :
    HasFderivAt (fun y => a y * b y) (a x • b' + a'.smul_right (b x)) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).IsBoundedBilinearMap.HasFderivAt (a x, b x)).comp x (ha.Prod hb)
#align has_fderiv_at.mul' HasFderivAt.mul'

theorem HasFderivAt.mul (hc : HasFderivAt c c' x) (hd : HasFderivAt d d' x) :
    HasFderivAt (fun y => c y * d y) (c x • d' + d x • c') x :=
  by
  convert hc.mul' hd
  ext z
  apply mul_comm
#align has_fderiv_at.mul HasFderivAt.mul

theorem DifferentiableWithinAt.mul (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) : DifferentiableWithinAt 𝕜 (fun y => a y * b y) s x :=
  (ha.HasFderivWithinAt.mul' hb.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.mul DifferentiableWithinAt.mul

@[simp]
theorem DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    DifferentiableAt 𝕜 (fun y => a y * b y) x :=
  (ha.HasFderivAt.mul' hb.HasFderivAt).DifferentiableAt
#align differentiable_at.mul DifferentiableAt.mul

theorem DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s) (hb : DifferentiableOn 𝕜 b s) :
    DifferentiableOn 𝕜 (fun y => a y * b y) s := fun x hx => (ha x hx).mul (hb x hx)
#align differentiable_on.mul DifferentiableOn.mul

@[simp]
theorem Differentiable.mul (ha : Differentiable 𝕜 a) (hb : Differentiable 𝕜 b) :
    Differentiable 𝕜 fun y => a y * b y := fun x => (ha x).mul (hb x)
#align differentiable.mul Differentiable.mul

theorem DifferentiableWithinAt.pow (ha : DifferentiableWithinAt 𝕜 a s x) :
    ∀ n : ℕ, DifferentiableWithinAt 𝕜 (fun x => a x ^ n) s x
  | 0 => by simp only [pow_zero, differentiableWithinAt_const]
  | n + 1 => by simp only [pow_succ, DifferentiableWithinAt.pow n, ha.mul]
#align differentiable_within_at.pow DifferentiableWithinAt.pow

@[simp]
theorem DifferentiableAt.pow (ha : DifferentiableAt 𝕜 a x) (n : ℕ) :
    DifferentiableAt 𝕜 (fun x => a x ^ n) x :=
  differentiableWithinAt_univ.mp <| ha.DifferentiableWithinAt.pow n
#align differentiable_at.pow DifferentiableAt.pow

theorem DifferentiableOn.pow (ha : DifferentiableOn 𝕜 a s) (n : ℕ) :
    DifferentiableOn 𝕜 (fun x => a x ^ n) s := fun x h => (ha x h).pow n
#align differentiable_on.pow DifferentiableOn.pow

@[simp]
theorem Differentiable.pow (ha : Differentiable 𝕜 a) (n : ℕ) : Differentiable 𝕜 fun x => a x ^ n :=
  fun x => (ha x).pow n
#align differentiable.pow Differentiable.pow

theorem fderivWithin_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) :
    fderivWithin 𝕜 (fun y => a y * b y) s x =
      a x • fderivWithin 𝕜 b s x + (fderivWithin 𝕜 a s x).smul_right (b x) :=
  (ha.HasFderivWithinAt.mul' hb.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_mul' fderivWithin_mul'

theorem fderivWithin_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (fun y => c y * d y) s x =
      c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x :=
  (hc.HasFderivWithinAt.mul hd.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_mul fderivWithin_mul

theorem fderiv_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    fderiv 𝕜 (fun y => a y * b y) x = a x • fderiv 𝕜 b x + (fderiv 𝕜 a x).smul_right (b x) :=
  (ha.HasFderivAt.mul' hb.HasFderivAt).fderiv
#align fderiv_mul' fderiv_mul'

theorem fderiv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => c y * d y) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  (hc.HasFderivAt.mul hd.HasFderivAt).fderiv
#align fderiv_mul fderiv_mul

theorem HasStrictFderivAt.mul_const' (ha : HasStrictFderivAt a a' x) (b : 𝔸) :
    HasStrictFderivAt (fun y => a y * b) (a'.smul_right b) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).HasStrictFderivAt.comp x ha
#align has_strict_fderiv_at.mul_const' HasStrictFderivAt.mul_const'

theorem HasStrictFderivAt.mul_const (hc : HasStrictFderivAt c c' x) (d : 𝔸') :
    HasStrictFderivAt (fun y => c y * d) (d • c') x :=
  by
  convert hc.mul_const' d
  ext z
  apply mul_comm
#align has_strict_fderiv_at.mul_const HasStrictFderivAt.mul_const

theorem HasFderivWithinAt.mul_const' (ha : HasFderivWithinAt a a' s x) (b : 𝔸) :
    HasFderivWithinAt (fun y => a y * b) (a'.smul_right b) s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).HasFderivAt.comp_hasFderivWithinAt x ha
#align has_fderiv_within_at.mul_const' HasFderivWithinAt.mul_const'

theorem HasFderivWithinAt.mul_const (hc : HasFderivWithinAt c c' s x) (d : 𝔸') :
    HasFderivWithinAt (fun y => c y * d) (d • c') s x :=
  by
  convert hc.mul_const' d
  ext z
  apply mul_comm
#align has_fderiv_within_at.mul_const HasFderivWithinAt.mul_const

theorem HasFderivAt.mul_const' (ha : HasFderivAt a a' x) (b : 𝔸) :
    HasFderivAt (fun y => a y * b) (a'.smul_right b) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).HasFderivAt.comp x ha
#align has_fderiv_at.mul_const' HasFderivAt.mul_const'

theorem HasFderivAt.mul_const (hc : HasFderivAt c c' x) (d : 𝔸') :
    HasFderivAt (fun y => c y * d) (d • c') x :=
  by
  convert hc.mul_const' d
  ext z
  apply mul_comm
#align has_fderiv_at.mul_const HasFderivAt.mul_const

theorem DifferentiableWithinAt.mul_const (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => a y * b) s x :=
  (ha.HasFderivWithinAt.mul_const' b).DifferentiableWithinAt
#align differentiable_within_at.mul_const DifferentiableWithinAt.mul_const

theorem DifferentiableAt.mul_const (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => a y * b) x :=
  (ha.HasFderivAt.mul_const' b).DifferentiableAt
#align differentiable_at.mul_const DifferentiableAt.mul_const

theorem DifferentiableOn.mul_const (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => a y * b) s := fun x hx => (ha x hx).mul_const b
#align differentiable_on.mul_const DifferentiableOn.mul_const

theorem Differentiable.mul_const (ha : Differentiable 𝕜 a) (b : 𝔸) :
    Differentiable 𝕜 fun y => a y * b := fun x => (ha x).mul_const b
#align differentiable.mul_const Differentiable.mul_const

theorem fderivWithin_mul_const' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => a y * b) s x = (fderivWithin 𝕜 a s x).smul_right b :=
  (ha.HasFderivWithinAt.mul_const' b).fderivWithin hxs
#align fderiv_within_mul_const' fderivWithin_mul_const'

theorem fderivWithin_mul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸') :
    fderivWithin 𝕜 (fun y => c y * d) s x = d • fderivWithin 𝕜 c s x :=
  (hc.HasFderivWithinAt.mul_const d).fderivWithin hxs
#align fderiv_within_mul_const fderivWithin_mul_const

theorem fderiv_mul_const' (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => a y * b) x = (fderiv 𝕜 a x).smul_right b :=
  (ha.HasFderivAt.mul_const' b).fderiv
#align fderiv_mul_const' fderiv_mul_const'

theorem fderiv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸') :
    fderiv 𝕜 (fun y => c y * d) x = d • fderiv 𝕜 c x :=
  (hc.HasFderivAt.mul_const d).fderiv
#align fderiv_mul_const fderiv_mul_const

theorem HasStrictFderivAt.const_mul (ha : HasStrictFderivAt a a' x) (b : 𝔸) :
    HasStrictFderivAt (fun y => b * a y) (b • a') x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).HasStrictFderivAt.comp x ha
#align has_strict_fderiv_at.const_mul HasStrictFderivAt.const_mul

theorem HasFderivWithinAt.const_mul (ha : HasFderivWithinAt a a' s x) (b : 𝔸) :
    HasFderivWithinAt (fun y => b * a y) (b • a') s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).HasFderivAt.comp_hasFderivWithinAt x ha
#align has_fderiv_within_at.const_mul HasFderivWithinAt.const_mul

theorem HasFderivAt.const_mul (ha : HasFderivAt a a' x) (b : 𝔸) :
    HasFderivAt (fun y => b * a y) (b • a') x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).HasFderivAt.comp x ha
#align has_fderiv_at.const_mul HasFderivAt.const_mul

theorem DifferentiableWithinAt.const_mul (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => b * a y) s x :=
  (ha.HasFderivWithinAt.const_mul b).DifferentiableWithinAt
#align differentiable_within_at.const_mul DifferentiableWithinAt.const_mul

theorem DifferentiableAt.const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => b * a y) x :=
  (ha.HasFderivAt.const_mul b).DifferentiableAt
#align differentiable_at.const_mul DifferentiableAt.const_mul

theorem DifferentiableOn.const_mul (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => b * a y) s := fun x hx => (ha x hx).const_mul b
#align differentiable_on.const_mul DifferentiableOn.const_mul

theorem Differentiable.const_mul (ha : Differentiable 𝕜 a) (b : 𝔸) :
    Differentiable 𝕜 fun y => b * a y := fun x => (ha x).const_mul b
#align differentiable.const_mul Differentiable.const_mul

theorem fderivWithin_const_mul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => b * a y) s x = b • fderivWithin 𝕜 a s x :=
  (ha.HasFderivWithinAt.const_mul b).fderivWithin hxs
#align fderiv_within_const_mul fderivWithin_const_mul

theorem fderiv_const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => b * a y) x = b • fderiv 𝕜 a x :=
  (ha.HasFderivAt.const_mul b).fderiv
#align fderiv_const_mul fderiv_const_mul

end Mul

section AlgebraInverse

variable {R : Type _} [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]

open NormedRing ContinuousLinearMap Ring

/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `λ t, - x⁻¹ * t * x⁻¹`. -/
theorem hasFderivAt_ring_inverse (x : Rˣ) :
    HasFderivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x :=
  by
  have h_is_o : (fun t : R => inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =o[𝓝 0] fun t : R => t :=
    by
    refine' (inverse_add_norm_diff_second_order x).trans_isLittleO (is_o_norm_norm.mp _)
    simp only [norm_pow, norm_norm]
    have h12 : 1 < 2 := by norm_num
    convert(Asymptotics.isLittleO_pow_pow h12).comp_tendsto tendsto_norm_zero
    ext
    simp
  have h_lim : tendsto (fun y : R => y - x) (𝓝 x) (𝓝 0) :=
    by
    refine' tendsto_zero_iff_norm_tendsto_zero.mpr _
    exact tendsto_iff_norm_tendsto_zero.mp tendsto_id
  simp only [HasFderivAt, HasFderivAtFilter]
  convert h_is_o.comp_tendsto h_lim
  ext y
  simp only [coe_comp', Function.comp_apply, mul_left_right_apply, neg_apply, inverse_unit x,
    Units.inv_mul, add_sub_cancel'_right, mul_sub, sub_mul, one_mul, sub_neg_eq_add]
#align has_fderiv_at_ring_inverse hasFderivAt_ring_inverse

theorem differentiableAt_inverse (x : Rˣ) : DifferentiableAt 𝕜 (@Ring.inverse R _) x :=
  (hasFderivAt_ring_inverse x).DifferentiableAt
#align differentiable_at_inverse differentiableAt_inverse

theorem fderiv_inverse (x : Rˣ) : fderiv 𝕜 (@Ring.inverse R _) x = -mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹ :=
  (hasFderivAt_ring_inverse x).fderiv
#align fderiv_inverse fderiv_inverse

end AlgebraInverse

end

