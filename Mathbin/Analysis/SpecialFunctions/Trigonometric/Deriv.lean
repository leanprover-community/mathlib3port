/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson

! This file was ported from Lean 3 source module analysis.special_functions.trigonometric.deriv
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Monotone.Odd
import Mathbin.Analysis.SpecialFunctions.ExpDeriv
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathbin.Data.Set.Intervals.Monotone

/-!
# Differentiability of trigonometric functions

## Main statements

The differentiability of the usual trigonometric functions is proved, and their derivatives are
computed.

## Tags

sin, cos, tan, angle
-/


noncomputable section

open Classical TopologicalSpace Filter

open Set Filter

namespace Complex

/-- The complex sine function is everywhere strictly differentiable, with the derivative `cos x`. -/
theorem has_strict_deriv_at_sin (x : ℂ) : HasStrictDerivAt sin (cos x) x :=
  by
  simp only [cos, div_eq_mul_inv]
  convert
    ((((has_strict_deriv_at_id x).neg.mul_const I).cexp.sub
              ((has_strict_deriv_at_id x).mul_const I).cexp).mul_const
          I).mul_const
      (2 : ℂ)⁻¹
  simp only [Function.comp, id]
  rw [sub_mul, mul_assoc, mul_assoc, I_mul_I, neg_one_mul, neg_neg, mul_one, one_mul, mul_assoc,
    I_mul_I, mul_neg_one, sub_neg_eq_add, add_comm]
#align complex.has_strict_deriv_at_sin Complex.has_strict_deriv_at_sin

/-- The complex sine function is everywhere differentiable, with the derivative `cos x`. -/
theorem has_deriv_at_sin (x : ℂ) : HasDerivAt sin (cos x) x :=
  (has_strict_deriv_at_sin x).HasDerivAt
#align complex.has_deriv_at_sin Complex.has_deriv_at_sin

theorem cont_diff_sin {n} : ContDiff ℂ n sin :=
  (((cont_diff_neg.mul cont_diff_const).cexp.sub (cont_diff_id.mul cont_diff_const).cexp).mul
      cont_diff_const).div_const
#align complex.cont_diff_sin Complex.cont_diff_sin

theorem differentiable_sin : Differentiable ℂ sin := fun x => (has_deriv_at_sin x).DifferentiableAt
#align complex.differentiable_sin Complex.differentiable_sin

theorem differentiable_at_sin {x : ℂ} : DifferentiableAt ℂ sin x :=
  differentiable_sin x
#align complex.differentiable_at_sin Complex.differentiable_at_sin

@[simp]
theorem deriv_sin : deriv sin = cos :=
  funext fun x => (has_deriv_at_sin x).deriv
#align complex.deriv_sin Complex.deriv_sin

/-- The complex cosine function is everywhere strictly differentiable, with the derivative
`-sin x`. -/
theorem has_strict_deriv_at_cos (x : ℂ) : HasStrictDerivAt cos (-sin x) x :=
  by
  simp only [sin, div_eq_mul_inv, neg_mul_eq_neg_mul]
  convert
    (((has_strict_deriv_at_id x).mul_const I).cexp.add
          ((has_strict_deriv_at_id x).neg.mul_const I).cexp).mul_const
      (2 : ℂ)⁻¹
  simp only [Function.comp, id]
  ring
#align complex.has_strict_deriv_at_cos Complex.has_strict_deriv_at_cos

/-- The complex cosine function is everywhere differentiable, with the derivative `-sin x`. -/
theorem has_deriv_at_cos (x : ℂ) : HasDerivAt cos (-sin x) x :=
  (has_strict_deriv_at_cos x).HasDerivAt
#align complex.has_deriv_at_cos Complex.has_deriv_at_cos

theorem cont_diff_cos {n} : ContDiff ℂ n cos :=
  ((cont_diff_id.mul cont_diff_const).cexp.add (cont_diff_neg.mul cont_diff_const).cexp).div_const
#align complex.cont_diff_cos Complex.cont_diff_cos

theorem differentiable_cos : Differentiable ℂ cos := fun x => (has_deriv_at_cos x).DifferentiableAt
#align complex.differentiable_cos Complex.differentiable_cos

theorem differentiable_at_cos {x : ℂ} : DifferentiableAt ℂ cos x :=
  differentiable_cos x
#align complex.differentiable_at_cos Complex.differentiable_at_cos

theorem deriv_cos {x : ℂ} : deriv cos x = -sin x :=
  (has_deriv_at_cos x).deriv
#align complex.deriv_cos Complex.deriv_cos

@[simp]
theorem deriv_cos' : deriv cos = fun x => -sin x :=
  funext fun x => deriv_cos
#align complex.deriv_cos' Complex.deriv_cos'

/-- The complex hyperbolic sine function is everywhere strictly differentiable, with the derivative
`cosh x`. -/
theorem has_strict_deriv_at_sinh (x : ℂ) : HasStrictDerivAt sinh (cosh x) x :=
  by
  simp only [cosh, div_eq_mul_inv]
  convert ((has_strict_deriv_at_exp x).sub (has_strict_deriv_at_id x).neg.cexp).mul_const (2 : ℂ)⁻¹
  rw [id, mul_neg_one, sub_eq_add_neg, neg_neg]
#align complex.has_strict_deriv_at_sinh Complex.has_strict_deriv_at_sinh

/-- The complex hyperbolic sine function is everywhere differentiable, with the derivative
`cosh x`. -/
theorem has_deriv_at_sinh (x : ℂ) : HasDerivAt sinh (cosh x) x :=
  (has_strict_deriv_at_sinh x).HasDerivAt
#align complex.has_deriv_at_sinh Complex.has_deriv_at_sinh

theorem cont_diff_sinh {n} : ContDiff ℂ n sinh :=
  (cont_diff_exp.sub cont_diff_neg.cexp).div_const
#align complex.cont_diff_sinh Complex.cont_diff_sinh

theorem differentiable_sinh : Differentiable ℂ sinh := fun x =>
  (has_deriv_at_sinh x).DifferentiableAt
#align complex.differentiable_sinh Complex.differentiable_sinh

theorem differentiable_at_sinh {x : ℂ} : DifferentiableAt ℂ sinh x :=
  differentiable_sinh x
#align complex.differentiable_at_sinh Complex.differentiable_at_sinh

@[simp]
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (has_deriv_at_sinh x).deriv
#align complex.deriv_sinh Complex.deriv_sinh

/-- The complex hyperbolic cosine function is everywhere strictly differentiable, with the
derivative `sinh x`. -/
theorem has_strict_deriv_at_cosh (x : ℂ) : HasStrictDerivAt cosh (sinh x) x :=
  by
  simp only [sinh, div_eq_mul_inv]
  convert ((has_strict_deriv_at_exp x).add (has_strict_deriv_at_id x).neg.cexp).mul_const (2 : ℂ)⁻¹
  rw [id, mul_neg_one, sub_eq_add_neg]
#align complex.has_strict_deriv_at_cosh Complex.has_strict_deriv_at_cosh

/-- The complex hyperbolic cosine function is everywhere differentiable, with the derivative
`sinh x`. -/
theorem has_deriv_at_cosh (x : ℂ) : HasDerivAt cosh (sinh x) x :=
  (has_strict_deriv_at_cosh x).HasDerivAt
#align complex.has_deriv_at_cosh Complex.has_deriv_at_cosh

theorem cont_diff_cosh {n} : ContDiff ℂ n cosh :=
  (cont_diff_exp.add cont_diff_neg.cexp).div_const
#align complex.cont_diff_cosh Complex.cont_diff_cosh

theorem differentiable_cosh : Differentiable ℂ cosh := fun x =>
  (has_deriv_at_cosh x).DifferentiableAt
#align complex.differentiable_cosh Complex.differentiable_cosh

theorem differentiable_at_cosh {x : ℂ} : DifferentiableAt ℂ cosh x :=
  differentiable_cosh x
#align complex.differentiable_at_cosh Complex.differentiable_at_cosh

@[simp]
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (has_deriv_at_cosh x).deriv
#align complex.deriv_cosh Complex.deriv_cosh

end Complex

section

/-! ### Simp lemmas for derivatives of `λ x, complex.cos (f x)` etc., `f : ℂ → ℂ` -/


variable {f : ℂ → ℂ} {f' x : ℂ} {s : Set ℂ}

/-! #### `complex.cos` -/


theorem HasStrictDerivAt.ccos (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') x :=
  (Complex.has_strict_deriv_at_cos (f x)).comp x hf
#align has_strict_deriv_at.ccos HasStrictDerivAt.ccos

theorem HasDerivAt.ccos (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') x :=
  (Complex.has_deriv_at_cos (f x)).comp x hf
#align has_deriv_at.ccos HasDerivAt.ccos

theorem HasDerivWithinAt.ccos (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') s x :=
  (Complex.has_deriv_at_cos (f x)).comp_has_deriv_within_at x hf
#align has_deriv_within_at.ccos HasDerivWithinAt.ccos

theorem deriv_within_ccos (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.cos (f x)) s x = -Complex.sin (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.ccos.derivWithin hxs
#align deriv_within_ccos deriv_within_ccos

@[simp]
theorem deriv_ccos (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.cos (f x)) x = -Complex.sin (f x) * deriv f x :=
  hc.HasDerivAt.ccos.deriv
#align deriv_ccos deriv_ccos

/-! #### `complex.sin` -/


theorem HasStrictDerivAt.csin (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') x :=
  (Complex.has_strict_deriv_at_sin (f x)).comp x hf
#align has_strict_deriv_at.csin HasStrictDerivAt.csin

theorem HasDerivAt.csin (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') x :=
  (Complex.has_deriv_at_sin (f x)).comp x hf
#align has_deriv_at.csin HasDerivAt.csin

theorem HasDerivWithinAt.csin (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') s x :=
  (Complex.has_deriv_at_sin (f x)).comp_has_deriv_within_at x hf
#align has_deriv_within_at.csin HasDerivWithinAt.csin

theorem deriv_within_csin (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.sin (f x)) s x = Complex.cos (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.csin.derivWithin hxs
#align deriv_within_csin deriv_within_csin

@[simp]
theorem deriv_csin (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.sin (f x)) x = Complex.cos (f x) * deriv f x :=
  hc.HasDerivAt.csin.deriv
#align deriv_csin deriv_csin

/-! #### `complex.cosh` -/


theorem HasStrictDerivAt.ccosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.has_strict_deriv_at_cosh (f x)).comp x hf
#align has_strict_deriv_at.ccosh HasStrictDerivAt.ccosh

theorem HasDerivAt.ccosh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.has_deriv_at_cosh (f x)).comp x hf
#align has_deriv_at.ccosh HasDerivAt.ccosh

theorem HasDerivWithinAt.ccosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') s x :=
  (Complex.has_deriv_at_cosh (f x)).comp_has_deriv_within_at x hf
#align has_deriv_within_at.ccosh HasDerivWithinAt.ccosh

theorem deriv_within_ccosh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.ccosh.derivWithin hxs
#align deriv_within_ccosh deriv_within_ccosh

@[simp]
theorem deriv_ccosh (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) * deriv f x :=
  hc.HasDerivAt.ccosh.deriv
#align deriv_ccosh deriv_ccosh

/-! #### `complex.sinh` -/


theorem HasStrictDerivAt.csinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.has_strict_deriv_at_sinh (f x)).comp x hf
#align has_strict_deriv_at.csinh HasStrictDerivAt.csinh

theorem HasDerivAt.csinh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.has_deriv_at_sinh (f x)).comp x hf
#align has_deriv_at.csinh HasDerivAt.csinh

theorem HasDerivWithinAt.csinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') s x :=
  (Complex.has_deriv_at_sinh (f x)).comp_has_deriv_within_at x hf
#align has_deriv_within_at.csinh HasDerivWithinAt.csinh

theorem deriv_within_csinh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.csinh.derivWithin hxs
#align deriv_within_csinh deriv_within_csinh

@[simp]
theorem deriv_csinh (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) * deriv f x :=
  hc.HasDerivAt.csinh.deriv
#align deriv_csinh deriv_csinh

end

section

/-! ### Simp lemmas for derivatives of `λ x, complex.cos (f x)` etc., `f : E → ℂ` -/


variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E}
  {s : Set E}

/-! #### `complex.cos` -/


theorem HasStrictFderivAt.ccos (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x :=
  (Complex.has_strict_deriv_at_cos (f x)).compHasStrictFderivAt x hf
#align has_strict_fderiv_at.ccos HasStrictFderivAt.ccos

theorem HasFderivAt.ccos (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x :=
  (Complex.has_deriv_at_cos (f x)).compHasFderivAt x hf
#align has_fderiv_at.ccos HasFderivAt.ccos

theorem HasFderivWithinAt.ccos (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') s x :=
  (Complex.has_deriv_at_cos (f x)).compHasFderivWithinAt x hf
#align has_fderiv_within_at.ccos HasFderivWithinAt.ccos

theorem DifferentiableWithinAt.ccos (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.cos (f x)) s x :=
  hf.HasFderivWithinAt.ccos.DifferentiableWithinAt
#align differentiable_within_at.ccos DifferentiableWithinAt.ccos

@[simp]
theorem DifferentiableAt.ccos (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.cos (f x)) x :=
  hc.HasFderivAt.ccos.DifferentiableAt
#align differentiable_at.ccos DifferentiableAt.ccos

theorem DifferentiableOn.ccos (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.cos (f x)) s := fun x h => (hc x h).ccos
#align differentiable_on.ccos DifferentiableOn.ccos

@[simp]
theorem Differentiable.ccos (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.cos (f x) := fun x => (hc x).ccos
#align differentiable.ccos Differentiable.ccos

theorem fderiv_within_ccos (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.cos (f x)) s x = -Complex.sin (f x) • fderivWithin ℂ f s x :=
  hf.HasFderivWithinAt.ccos.fderivWithin hxs
#align fderiv_within_ccos fderiv_within_ccos

@[simp]
theorem fderiv_ccos (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.cos (f x)) x = -Complex.sin (f x) • fderiv ℂ f x :=
  hc.HasFderivAt.ccos.fderiv
#align fderiv_ccos fderiv_ccos

theorem ContDiff.ccos {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.cos (f x) :=
  Complex.cont_diff_cos.comp h
#align cont_diff.ccos ContDiff.ccos

theorem ContDiffAt.ccos {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.cos (f x)) x :=
  Complex.cont_diff_cos.ContDiffAt.comp x hf
#align cont_diff_at.ccos ContDiffAt.ccos

theorem ContDiffOn.ccos {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.cos (f x)) s :=
  Complex.cont_diff_cos.comp_cont_diff_on hf
#align cont_diff_on.ccos ContDiffOn.ccos

theorem ContDiffWithinAt.ccos {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.cos (f x)) s x :=
  Complex.cont_diff_cos.ContDiffAt.comp_cont_diff_within_at x hf
#align cont_diff_within_at.ccos ContDiffWithinAt.ccos

/-! #### `complex.sin` -/


theorem HasStrictFderivAt.csin (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x :=
  (Complex.has_strict_deriv_at_sin (f x)).compHasStrictFderivAt x hf
#align has_strict_fderiv_at.csin HasStrictFderivAt.csin

theorem HasFderivAt.csin (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x :=
  (Complex.has_deriv_at_sin (f x)).compHasFderivAt x hf
#align has_fderiv_at.csin HasFderivAt.csin

theorem HasFderivWithinAt.csin (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') s x :=
  (Complex.has_deriv_at_sin (f x)).compHasFderivWithinAt x hf
#align has_fderiv_within_at.csin HasFderivWithinAt.csin

theorem DifferentiableWithinAt.csin (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.sin (f x)) s x :=
  hf.HasFderivWithinAt.csin.DifferentiableWithinAt
#align differentiable_within_at.csin DifferentiableWithinAt.csin

@[simp]
theorem DifferentiableAt.csin (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.sin (f x)) x :=
  hc.HasFderivAt.csin.DifferentiableAt
#align differentiable_at.csin DifferentiableAt.csin

theorem DifferentiableOn.csin (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.sin (f x)) s := fun x h => (hc x h).csin
#align differentiable_on.csin DifferentiableOn.csin

@[simp]
theorem Differentiable.csin (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.sin (f x) := fun x => (hc x).csin
#align differentiable.csin Differentiable.csin

theorem fderiv_within_csin (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.sin (f x)) s x = Complex.cos (f x) • fderivWithin ℂ f s x :=
  hf.HasFderivWithinAt.csin.fderivWithin hxs
#align fderiv_within_csin fderiv_within_csin

@[simp]
theorem fderiv_csin (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.sin (f x)) x = Complex.cos (f x) • fderiv ℂ f x :=
  hc.HasFderivAt.csin.fderiv
#align fderiv_csin fderiv_csin

theorem ContDiff.csin {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.sin (f x) :=
  Complex.cont_diff_sin.comp h
#align cont_diff.csin ContDiff.csin

theorem ContDiffAt.csin {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.sin (f x)) x :=
  Complex.cont_diff_sin.ContDiffAt.comp x hf
#align cont_diff_at.csin ContDiffAt.csin

theorem ContDiffOn.csin {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.sin (f x)) s :=
  Complex.cont_diff_sin.comp_cont_diff_on hf
#align cont_diff_on.csin ContDiffOn.csin

theorem ContDiffWithinAt.csin {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.sin (f x)) s x :=
  Complex.cont_diff_sin.ContDiffAt.comp_cont_diff_within_at x hf
#align cont_diff_within_at.csin ContDiffWithinAt.csin

/-! #### `complex.cosh` -/


theorem HasStrictFderivAt.ccosh (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.has_strict_deriv_at_cosh (f x)).compHasStrictFderivAt x hf
#align has_strict_fderiv_at.ccosh HasStrictFderivAt.ccosh

theorem HasFderivAt.ccosh (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.has_deriv_at_cosh (f x)).compHasFderivAt x hf
#align has_fderiv_at.ccosh HasFderivAt.ccosh

theorem HasFderivWithinAt.ccosh (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') s x :=
  (Complex.has_deriv_at_cosh (f x)).compHasFderivWithinAt x hf
#align has_fderiv_within_at.ccosh HasFderivWithinAt.ccosh

theorem DifferentiableWithinAt.ccosh (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.cosh (f x)) s x :=
  hf.HasFderivWithinAt.ccosh.DifferentiableWithinAt
#align differentiable_within_at.ccosh DifferentiableWithinAt.ccosh

@[simp]
theorem DifferentiableAt.ccosh (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.cosh (f x)) x :=
  hc.HasFderivAt.ccosh.DifferentiableAt
#align differentiable_at.ccosh DifferentiableAt.ccosh

theorem DifferentiableOn.ccosh (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.cosh (f x)) s := fun x h => (hc x h).ccosh
#align differentiable_on.ccosh DifferentiableOn.ccosh

@[simp]
theorem Differentiable.ccosh (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.cosh (f x) := fun x => (hc x).ccosh
#align differentiable.ccosh Differentiable.ccosh

theorem fderiv_within_ccosh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) • fderivWithin ℂ f s x :=
  hf.HasFderivWithinAt.ccosh.fderivWithin hxs
#align fderiv_within_ccosh fderiv_within_ccosh

@[simp]
theorem fderiv_ccosh (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) • fderiv ℂ f x :=
  hc.HasFderivAt.ccosh.fderiv
#align fderiv_ccosh fderiv_ccosh

theorem ContDiff.ccosh {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.cosh (f x) :=
  Complex.cont_diff_cosh.comp h
#align cont_diff.ccosh ContDiff.ccosh

theorem ContDiffAt.ccosh {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.cosh (f x)) x :=
  Complex.cont_diff_cosh.ContDiffAt.comp x hf
#align cont_diff_at.ccosh ContDiffAt.ccosh

theorem ContDiffOn.ccosh {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.cosh (f x)) s :=
  Complex.cont_diff_cosh.comp_cont_diff_on hf
#align cont_diff_on.ccosh ContDiffOn.ccosh

theorem ContDiffWithinAt.ccosh {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.cosh (f x)) s x :=
  Complex.cont_diff_cosh.ContDiffAt.comp_cont_diff_within_at x hf
#align cont_diff_within_at.ccosh ContDiffWithinAt.ccosh

/-! #### `complex.sinh` -/


theorem HasStrictFderivAt.csinh (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.has_strict_deriv_at_sinh (f x)).compHasStrictFderivAt x hf
#align has_strict_fderiv_at.csinh HasStrictFderivAt.csinh

theorem HasFderivAt.csinh (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.has_deriv_at_sinh (f x)).compHasFderivAt x hf
#align has_fderiv_at.csinh HasFderivAt.csinh

theorem HasFderivWithinAt.csinh (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') s x :=
  (Complex.has_deriv_at_sinh (f x)).compHasFderivWithinAt x hf
#align has_fderiv_within_at.csinh HasFderivWithinAt.csinh

theorem DifferentiableWithinAt.csinh (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.sinh (f x)) s x :=
  hf.HasFderivWithinAt.csinh.DifferentiableWithinAt
#align differentiable_within_at.csinh DifferentiableWithinAt.csinh

@[simp]
theorem DifferentiableAt.csinh (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.sinh (f x)) x :=
  hc.HasFderivAt.csinh.DifferentiableAt
#align differentiable_at.csinh DifferentiableAt.csinh

theorem DifferentiableOn.csinh (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.sinh (f x)) s := fun x h => (hc x h).csinh
#align differentiable_on.csinh DifferentiableOn.csinh

@[simp]
theorem Differentiable.csinh (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.sinh (f x) := fun x => (hc x).csinh
#align differentiable.csinh Differentiable.csinh

theorem fderiv_within_csinh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) • fderivWithin ℂ f s x :=
  hf.HasFderivWithinAt.csinh.fderivWithin hxs
#align fderiv_within_csinh fderiv_within_csinh

@[simp]
theorem fderiv_csinh (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) • fderiv ℂ f x :=
  hc.HasFderivAt.csinh.fderiv
#align fderiv_csinh fderiv_csinh

theorem ContDiff.csinh {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.sinh (f x) :=
  Complex.cont_diff_sinh.comp h
#align cont_diff.csinh ContDiff.csinh

theorem ContDiffAt.csinh {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.sinh (f x)) x :=
  Complex.cont_diff_sinh.ContDiffAt.comp x hf
#align cont_diff_at.csinh ContDiffAt.csinh

theorem ContDiffOn.csinh {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.sinh (f x)) s :=
  Complex.cont_diff_sinh.comp_cont_diff_on hf
#align cont_diff_on.csinh ContDiffOn.csinh

theorem ContDiffWithinAt.csinh {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.sinh (f x)) s x :=
  Complex.cont_diff_sinh.ContDiffAt.comp_cont_diff_within_at x hf
#align cont_diff_within_at.csinh ContDiffWithinAt.csinh

end

namespace Real

variable {x y z : ℝ}

theorem has_strict_deriv_at_sin (x : ℝ) : HasStrictDerivAt sin (cos x) x :=
  (Complex.has_strict_deriv_at_sin x).real_of_complex
#align real.has_strict_deriv_at_sin Real.has_strict_deriv_at_sin

theorem has_deriv_at_sin (x : ℝ) : HasDerivAt sin (cos x) x :=
  (has_strict_deriv_at_sin x).HasDerivAt
#align real.has_deriv_at_sin Real.has_deriv_at_sin

theorem cont_diff_sin {n} : ContDiff ℝ n sin :=
  Complex.cont_diff_sin.real_of_complex
#align real.cont_diff_sin Real.cont_diff_sin

theorem differentiable_sin : Differentiable ℝ sin := fun x => (has_deriv_at_sin x).DifferentiableAt
#align real.differentiable_sin Real.differentiable_sin

theorem differentiable_at_sin : DifferentiableAt ℝ sin x :=
  differentiable_sin x
#align real.differentiable_at_sin Real.differentiable_at_sin

@[simp]
theorem deriv_sin : deriv sin = cos :=
  funext fun x => (has_deriv_at_sin x).deriv
#align real.deriv_sin Real.deriv_sin

theorem has_strict_deriv_at_cos (x : ℝ) : HasStrictDerivAt cos (-sin x) x :=
  (Complex.has_strict_deriv_at_cos x).real_of_complex
#align real.has_strict_deriv_at_cos Real.has_strict_deriv_at_cos

theorem has_deriv_at_cos (x : ℝ) : HasDerivAt cos (-sin x) x :=
  (Complex.has_deriv_at_cos x).real_of_complex
#align real.has_deriv_at_cos Real.has_deriv_at_cos

theorem cont_diff_cos {n} : ContDiff ℝ n cos :=
  Complex.cont_diff_cos.real_of_complex
#align real.cont_diff_cos Real.cont_diff_cos

theorem differentiable_cos : Differentiable ℝ cos := fun x => (has_deriv_at_cos x).DifferentiableAt
#align real.differentiable_cos Real.differentiable_cos

theorem differentiable_at_cos : DifferentiableAt ℝ cos x :=
  differentiable_cos x
#align real.differentiable_at_cos Real.differentiable_at_cos

theorem deriv_cos : deriv cos x = -sin x :=
  (has_deriv_at_cos x).deriv
#align real.deriv_cos Real.deriv_cos

@[simp]
theorem deriv_cos' : deriv cos = fun x => -sin x :=
  funext fun _ => deriv_cos
#align real.deriv_cos' Real.deriv_cos'

theorem has_strict_deriv_at_sinh (x : ℝ) : HasStrictDerivAt sinh (cosh x) x :=
  (Complex.has_strict_deriv_at_sinh x).real_of_complex
#align real.has_strict_deriv_at_sinh Real.has_strict_deriv_at_sinh

theorem has_deriv_at_sinh (x : ℝ) : HasDerivAt sinh (cosh x) x :=
  (Complex.has_deriv_at_sinh x).real_of_complex
#align real.has_deriv_at_sinh Real.has_deriv_at_sinh

theorem cont_diff_sinh {n} : ContDiff ℝ n sinh :=
  Complex.cont_diff_sinh.real_of_complex
#align real.cont_diff_sinh Real.cont_diff_sinh

theorem differentiable_sinh : Differentiable ℝ sinh := fun x =>
  (has_deriv_at_sinh x).DifferentiableAt
#align real.differentiable_sinh Real.differentiable_sinh

theorem differentiable_at_sinh : DifferentiableAt ℝ sinh x :=
  differentiable_sinh x
#align real.differentiable_at_sinh Real.differentiable_at_sinh

@[simp]
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (has_deriv_at_sinh x).deriv
#align real.deriv_sinh Real.deriv_sinh

theorem has_strict_deriv_at_cosh (x : ℝ) : HasStrictDerivAt cosh (sinh x) x :=
  (Complex.has_strict_deriv_at_cosh x).real_of_complex
#align real.has_strict_deriv_at_cosh Real.has_strict_deriv_at_cosh

theorem has_deriv_at_cosh (x : ℝ) : HasDerivAt cosh (sinh x) x :=
  (Complex.has_deriv_at_cosh x).real_of_complex
#align real.has_deriv_at_cosh Real.has_deriv_at_cosh

theorem cont_diff_cosh {n} : ContDiff ℝ n cosh :=
  Complex.cont_diff_cosh.real_of_complex
#align real.cont_diff_cosh Real.cont_diff_cosh

theorem differentiable_cosh : Differentiable ℝ cosh := fun x =>
  (has_deriv_at_cosh x).DifferentiableAt
#align real.differentiable_cosh Real.differentiable_cosh

theorem differentiable_at_cosh : DifferentiableAt ℝ cosh x :=
  differentiable_cosh x
#align real.differentiable_at_cosh Real.differentiable_at_cosh

@[simp]
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (has_deriv_at_cosh x).deriv
#align real.deriv_cosh Real.deriv_cosh

/-- `sinh` is strictly monotone. -/
theorem sinh_strict_mono : StrictMono sinh :=
  strict_mono_of_deriv_pos <| by
    rw [Real.deriv_sinh]
    exact cosh_pos
#align real.sinh_strict_mono Real.sinh_strict_mono

/-- `sinh` is injective, `∀ a b, sinh a = sinh b → a = b`. -/
theorem sinh_injective : Function.Injective sinh :=
  sinh_strict_mono.Injective
#align real.sinh_injective Real.sinh_injective

@[simp]
theorem sinh_inj : sinh x = sinh y ↔ x = y :=
  sinh_injective.eq_iff
#align real.sinh_inj Real.sinh_inj

@[simp]
theorem sinh_le_sinh : sinh x ≤ sinh y ↔ x ≤ y :=
  sinh_strict_mono.le_iff_le
#align real.sinh_le_sinh Real.sinh_le_sinh

@[simp]
theorem sinh_lt_sinh : sinh x < sinh y ↔ x < y :=
  sinh_strict_mono.lt_iff_lt
#align real.sinh_lt_sinh Real.sinh_lt_sinh

@[simp]
theorem sinh_pos_iff : 0 < sinh x ↔ 0 < x := by simpa only [sinh_zero] using @sinh_lt_sinh 0 x
#align real.sinh_pos_iff Real.sinh_pos_iff

@[simp]
theorem sinh_nonpos_iff : sinh x ≤ 0 ↔ x ≤ 0 := by simpa only [sinh_zero] using @sinh_le_sinh x 0
#align real.sinh_nonpos_iff Real.sinh_nonpos_iff

@[simp]
theorem sinh_neg_iff : sinh x < 0 ↔ x < 0 := by simpa only [sinh_zero] using @sinh_lt_sinh x 0
#align real.sinh_neg_iff Real.sinh_neg_iff

@[simp]
theorem sinh_nonneg_iff : 0 ≤ sinh x ↔ 0 ≤ x := by simpa only [sinh_zero] using @sinh_le_sinh 0 x
#align real.sinh_nonneg_iff Real.sinh_nonneg_iff

theorem abs_sinh (x : ℝ) : |sinh x| = sinh (|x|) := by
  cases le_total x 0 <;> simp [abs_of_nonneg, abs_of_nonpos, *]
#align real.abs_sinh Real.abs_sinh

theorem cosh_strict_mono_on : StrictMonoOn cosh (Ici 0) :=
  (convex_Ici _).strict_mono_on_of_deriv_pos continuous_cosh.ContinuousOn fun x hx =>
    by
    rw [interior_Ici, mem_Ioi] at hx
    rwa [deriv_cosh, sinh_pos_iff]
#align real.cosh_strict_mono_on Real.cosh_strict_mono_on

@[simp]
theorem cosh_le_cosh : cosh x ≤ cosh y ↔ |x| ≤ |y| :=
  cosh_abs x ▸ cosh_abs y ▸ cosh_strict_mono_on.le_iff_le (abs_nonneg x) (abs_nonneg y)
#align real.cosh_le_cosh Real.cosh_le_cosh

@[simp]
theorem cosh_lt_cosh : cosh x < cosh y ↔ |x| < |y| :=
  lt_iff_lt_of_le_iff_le cosh_le_cosh
#align real.cosh_lt_cosh Real.cosh_lt_cosh

@[simp]
theorem one_le_cosh (x : ℝ) : 1 ≤ cosh x :=
  cosh_zero ▸ cosh_le_cosh.2 (by simp only [_root_.abs_zero, _root_.abs_nonneg])
#align real.one_le_cosh Real.one_le_cosh

@[simp]
theorem one_lt_cosh : 1 < cosh x ↔ x ≠ 0 :=
  cosh_zero ▸ cosh_lt_cosh.trans (by simp only [_root_.abs_zero, abs_pos])
#align real.one_lt_cosh Real.one_lt_cosh

theorem sinh_sub_id_strict_mono : StrictMono fun x => sinh x - x :=
  by
  refine' strictMono_of_odd_strictMono_on_nonneg (fun x => by simp) _
  refine' (convex_Ici _).strict_mono_on_of_deriv_pos _ fun x hx => _
  · exact (continuous_sinh.sub continuous_id).ContinuousOn
  · rw [interior_Ici, mem_Ioi] at hx
    rw [deriv_sub, deriv_sinh, deriv_id'', sub_pos, one_lt_cosh]
    exacts[hx.ne', differentiable_at_sinh, differentiable_at_id]
#align real.sinh_sub_id_strict_mono Real.sinh_sub_id_strict_mono

@[simp]
theorem self_le_sinh_iff : x ≤ sinh x ↔ 0 ≤ x :=
  calc
    x ≤ sinh x ↔ sinh 0 - 0 ≤ sinh x - x := by simp
    _ ↔ 0 ≤ x := sinh_sub_id_strict_mono.le_iff_le
    
#align real.self_le_sinh_iff Real.self_le_sinh_iff

@[simp]
theorem sinh_le_self_iff : sinh x ≤ x ↔ x ≤ 0 :=
  calc
    sinh x ≤ x ↔ sinh x - x ≤ sinh 0 - 0 := by simp
    _ ↔ x ≤ 0 := sinh_sub_id_strict_mono.le_iff_le
    
#align real.sinh_le_self_iff Real.sinh_le_self_iff

@[simp]
theorem self_lt_sinh_iff : x < sinh x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le sinh_le_self_iff
#align real.self_lt_sinh_iff Real.self_lt_sinh_iff

@[simp]
theorem sinh_lt_self_iff : sinh x < x ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le self_le_sinh_iff
#align real.sinh_lt_self_iff Real.sinh_lt_self_iff

end Real

section

/-! ### Simp lemmas for derivatives of `λ x, real.cos (f x)` etc., `f : ℝ → ℝ` -/


variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

/-! #### `real.cos` -/


theorem HasStrictDerivAt.cos (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') x :=
  (Real.has_strict_deriv_at_cos (f x)).comp x hf
#align has_strict_deriv_at.cos HasStrictDerivAt.cos

theorem HasDerivAt.cos (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') x :=
  (Real.has_deriv_at_cos (f x)).comp x hf
#align has_deriv_at.cos HasDerivAt.cos

theorem HasDerivWithinAt.cos (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') s x :=
  (Real.has_deriv_at_cos (f x)).comp_has_deriv_within_at x hf
#align has_deriv_within_at.cos HasDerivWithinAt.cos

theorem deriv_within_cos (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.cos (f x)) s x = -Real.sin (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.cos.derivWithin hxs
#align deriv_within_cos deriv_within_cos

@[simp]
theorem deriv_cos (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.cos (f x)) x = -Real.sin (f x) * deriv f x :=
  hc.HasDerivAt.cos.deriv
#align deriv_cos deriv_cos

/-! #### `real.sin` -/


theorem HasStrictDerivAt.sin (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') x :=
  (Real.has_strict_deriv_at_sin (f x)).comp x hf
#align has_strict_deriv_at.sin HasStrictDerivAt.sin

theorem HasDerivAt.sin (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') x :=
  (Real.has_deriv_at_sin (f x)).comp x hf
#align has_deriv_at.sin HasDerivAt.sin

theorem HasDerivWithinAt.sin (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') s x :=
  (Real.has_deriv_at_sin (f x)).comp_has_deriv_within_at x hf
#align has_deriv_within_at.sin HasDerivWithinAt.sin

theorem deriv_within_sin (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.sin (f x)) s x = Real.cos (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.sin.derivWithin hxs
#align deriv_within_sin deriv_within_sin

@[simp]
theorem deriv_sin (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.sin (f x)) x = Real.cos (f x) * deriv f x :=
  hc.HasDerivAt.sin.deriv
#align deriv_sin deriv_sin

/-! #### `real.cosh` -/


theorem HasStrictDerivAt.cosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.has_strict_deriv_at_cosh (f x)).comp x hf
#align has_strict_deriv_at.cosh HasStrictDerivAt.cosh

theorem HasDerivAt.cosh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.has_deriv_at_cosh (f x)).comp x hf
#align has_deriv_at.cosh HasDerivAt.cosh

theorem HasDerivWithinAt.cosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') s x :=
  (Real.has_deriv_at_cosh (f x)).comp_has_deriv_within_at x hf
#align has_deriv_within_at.cosh HasDerivWithinAt.cosh

theorem deriv_within_cosh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.cosh (f x)) s x = Real.sinh (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.cosh.derivWithin hxs
#align deriv_within_cosh deriv_within_cosh

@[simp]
theorem deriv_cosh (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.cosh (f x)) x = Real.sinh (f x) * deriv f x :=
  hc.HasDerivAt.cosh.deriv
#align deriv_cosh deriv_cosh

/-! #### `real.sinh` -/


theorem HasStrictDerivAt.sinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.has_strict_deriv_at_sinh (f x)).comp x hf
#align has_strict_deriv_at.sinh HasStrictDerivAt.sinh

theorem HasDerivAt.sinh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.has_deriv_at_sinh (f x)).comp x hf
#align has_deriv_at.sinh HasDerivAt.sinh

theorem HasDerivWithinAt.sinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') s x :=
  (Real.has_deriv_at_sinh (f x)).comp_has_deriv_within_at x hf
#align has_deriv_within_at.sinh HasDerivWithinAt.sinh

theorem deriv_within_sinh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.sinh (f x)) s x = Real.cosh (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.sinh.derivWithin hxs
#align deriv_within_sinh deriv_within_sinh

@[simp]
theorem deriv_sinh (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.sinh (f x)) x = Real.cosh (f x) * deriv f x :=
  hc.HasDerivAt.sinh.deriv
#align deriv_sinh deriv_sinh

end

section

/-! ### Simp lemmas for derivatives of `λ x, real.cos (f x)` etc., `f : E → ℝ` -/


variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
  {s : Set E}

/-! #### `real.cos` -/


theorem HasStrictFderivAt.cos (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x :=
  (Real.has_strict_deriv_at_cos (f x)).compHasStrictFderivAt x hf
#align has_strict_fderiv_at.cos HasStrictFderivAt.cos

theorem HasFderivAt.cos (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x :=
  (Real.has_deriv_at_cos (f x)).compHasFderivAt x hf
#align has_fderiv_at.cos HasFderivAt.cos

theorem HasFderivWithinAt.cos (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') s x :=
  (Real.has_deriv_at_cos (f x)).compHasFderivWithinAt x hf
#align has_fderiv_within_at.cos HasFderivWithinAt.cos

theorem DifferentiableWithinAt.cos (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.cos (f x)) s x :=
  hf.HasFderivWithinAt.cos.DifferentiableWithinAt
#align differentiable_within_at.cos DifferentiableWithinAt.cos

@[simp]
theorem DifferentiableAt.cos (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.cos (f x)) x :=
  hc.HasFderivAt.cos.DifferentiableAt
#align differentiable_at.cos DifferentiableAt.cos

theorem DifferentiableOn.cos (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.cos (f x)) s := fun x h => (hc x h).cos
#align differentiable_on.cos DifferentiableOn.cos

@[simp]
theorem Differentiable.cos (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.cos (f x) :=
  fun x => (hc x).cos
#align differentiable.cos Differentiable.cos

theorem fderiv_within_cos (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.cos (f x)) s x = -Real.sin (f x) • fderivWithin ℝ f s x :=
  hf.HasFderivWithinAt.cos.fderivWithin hxs
#align fderiv_within_cos fderiv_within_cos

@[simp]
theorem fderiv_cos (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.cos (f x)) x = -Real.sin (f x) • fderiv ℝ f x :=
  hc.HasFderivAt.cos.fderiv
#align fderiv_cos fderiv_cos

theorem ContDiff.cos {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.cos (f x) :=
  Real.cont_diff_cos.comp h
#align cont_diff.cos ContDiff.cos

theorem ContDiffAt.cos {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.cos (f x)) x :=
  Real.cont_diff_cos.ContDiffAt.comp x hf
#align cont_diff_at.cos ContDiffAt.cos

theorem ContDiffOn.cos {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.cos (f x)) s :=
  Real.cont_diff_cos.comp_cont_diff_on hf
#align cont_diff_on.cos ContDiffOn.cos

theorem ContDiffWithinAt.cos {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.cos (f x)) s x :=
  Real.cont_diff_cos.ContDiffAt.comp_cont_diff_within_at x hf
#align cont_diff_within_at.cos ContDiffWithinAt.cos

/-! #### `real.sin` -/


theorem HasStrictFderivAt.sin (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') x :=
  (Real.has_strict_deriv_at_sin (f x)).compHasStrictFderivAt x hf
#align has_strict_fderiv_at.sin HasStrictFderivAt.sin

theorem HasFderivAt.sin (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') x :=
  (Real.has_deriv_at_sin (f x)).compHasFderivAt x hf
#align has_fderiv_at.sin HasFderivAt.sin

theorem HasFderivWithinAt.sin (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') s x :=
  (Real.has_deriv_at_sin (f x)).compHasFderivWithinAt x hf
#align has_fderiv_within_at.sin HasFderivWithinAt.sin

theorem DifferentiableWithinAt.sin (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.sin (f x)) s x :=
  hf.HasFderivWithinAt.sin.DifferentiableWithinAt
#align differentiable_within_at.sin DifferentiableWithinAt.sin

@[simp]
theorem DifferentiableAt.sin (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.sin (f x)) x :=
  hc.HasFderivAt.sin.DifferentiableAt
#align differentiable_at.sin DifferentiableAt.sin

theorem DifferentiableOn.sin (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.sin (f x)) s := fun x h => (hc x h).sin
#align differentiable_on.sin DifferentiableOn.sin

@[simp]
theorem Differentiable.sin (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.sin (f x) :=
  fun x => (hc x).sin
#align differentiable.sin Differentiable.sin

theorem fderiv_within_sin (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.sin (f x)) s x = Real.cos (f x) • fderivWithin ℝ f s x :=
  hf.HasFderivWithinAt.sin.fderivWithin hxs
#align fderiv_within_sin fderiv_within_sin

@[simp]
theorem fderiv_sin (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.sin (f x)) x = Real.cos (f x) • fderiv ℝ f x :=
  hc.HasFderivAt.sin.fderiv
#align fderiv_sin fderiv_sin

theorem ContDiff.sin {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.sin (f x) :=
  Real.cont_diff_sin.comp h
#align cont_diff.sin ContDiff.sin

theorem ContDiffAt.sin {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.sin (f x)) x :=
  Real.cont_diff_sin.ContDiffAt.comp x hf
#align cont_diff_at.sin ContDiffAt.sin

theorem ContDiffOn.sin {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.sin (f x)) s :=
  Real.cont_diff_sin.comp_cont_diff_on hf
#align cont_diff_on.sin ContDiffOn.sin

theorem ContDiffWithinAt.sin {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.sin (f x)) s x :=
  Real.cont_diff_sin.ContDiffAt.comp_cont_diff_within_at x hf
#align cont_diff_within_at.sin ContDiffWithinAt.sin

/-! #### `real.cosh` -/


theorem HasStrictFderivAt.cosh (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.has_strict_deriv_at_cosh (f x)).compHasStrictFderivAt x hf
#align has_strict_fderiv_at.cosh HasStrictFderivAt.cosh

theorem HasFderivAt.cosh (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.has_deriv_at_cosh (f x)).compHasFderivAt x hf
#align has_fderiv_at.cosh HasFderivAt.cosh

theorem HasFderivWithinAt.cosh (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') s x :=
  (Real.has_deriv_at_cosh (f x)).compHasFderivWithinAt x hf
#align has_fderiv_within_at.cosh HasFderivWithinAt.cosh

theorem DifferentiableWithinAt.cosh (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.cosh (f x)) s x :=
  hf.HasFderivWithinAt.cosh.DifferentiableWithinAt
#align differentiable_within_at.cosh DifferentiableWithinAt.cosh

@[simp]
theorem DifferentiableAt.cosh (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.cosh (f x)) x :=
  hc.HasFderivAt.cosh.DifferentiableAt
#align differentiable_at.cosh DifferentiableAt.cosh

theorem DifferentiableOn.cosh (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.cosh (f x)) s := fun x h => (hc x h).cosh
#align differentiable_on.cosh DifferentiableOn.cosh

@[simp]
theorem Differentiable.cosh (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.cosh (f x) :=
  fun x => (hc x).cosh
#align differentiable.cosh Differentiable.cosh

theorem fderiv_within_cosh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.cosh (f x)) s x = Real.sinh (f x) • fderivWithin ℝ f s x :=
  hf.HasFderivWithinAt.cosh.fderivWithin hxs
#align fderiv_within_cosh fderiv_within_cosh

@[simp]
theorem fderiv_cosh (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.cosh (f x)) x = Real.sinh (f x) • fderiv ℝ f x :=
  hc.HasFderivAt.cosh.fderiv
#align fderiv_cosh fderiv_cosh

theorem ContDiff.cosh {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.cosh (f x) :=
  Real.cont_diff_cosh.comp h
#align cont_diff.cosh ContDiff.cosh

theorem ContDiffAt.cosh {n} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun x => Real.cosh (f x)) x :=
  Real.cont_diff_cosh.ContDiffAt.comp x hf
#align cont_diff_at.cosh ContDiffAt.cosh

theorem ContDiffOn.cosh {n} (hf : ContDiffOn ℝ n f s) :
    ContDiffOn ℝ n (fun x => Real.cosh (f x)) s :=
  Real.cont_diff_cosh.comp_cont_diff_on hf
#align cont_diff_on.cosh ContDiffOn.cosh

theorem ContDiffWithinAt.cosh {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.cosh (f x)) s x :=
  Real.cont_diff_cosh.ContDiffAt.comp_cont_diff_within_at x hf
#align cont_diff_within_at.cosh ContDiffWithinAt.cosh

/-! #### `real.sinh` -/


theorem HasStrictFderivAt.sinh (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.has_strict_deriv_at_sinh (f x)).compHasStrictFderivAt x hf
#align has_strict_fderiv_at.sinh HasStrictFderivAt.sinh

theorem HasFderivAt.sinh (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.has_deriv_at_sinh (f x)).compHasFderivAt x hf
#align has_fderiv_at.sinh HasFderivAt.sinh

theorem HasFderivWithinAt.sinh (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') s x :=
  (Real.has_deriv_at_sinh (f x)).compHasFderivWithinAt x hf
#align has_fderiv_within_at.sinh HasFderivWithinAt.sinh

theorem DifferentiableWithinAt.sinh (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.sinh (f x)) s x :=
  hf.HasFderivWithinAt.sinh.DifferentiableWithinAt
#align differentiable_within_at.sinh DifferentiableWithinAt.sinh

@[simp]
theorem DifferentiableAt.sinh (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.sinh (f x)) x :=
  hc.HasFderivAt.sinh.DifferentiableAt
#align differentiable_at.sinh DifferentiableAt.sinh

theorem DifferentiableOn.sinh (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.sinh (f x)) s := fun x h => (hc x h).sinh
#align differentiable_on.sinh DifferentiableOn.sinh

@[simp]
theorem Differentiable.sinh (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.sinh (f x) :=
  fun x => (hc x).sinh
#align differentiable.sinh Differentiable.sinh

theorem fderiv_within_sinh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.sinh (f x)) s x = Real.cosh (f x) • fderivWithin ℝ f s x :=
  hf.HasFderivWithinAt.sinh.fderivWithin hxs
#align fderiv_within_sinh fderiv_within_sinh

@[simp]
theorem fderiv_sinh (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.sinh (f x)) x = Real.cosh (f x) • fderiv ℝ f x :=
  hc.HasFderivAt.sinh.fderiv
#align fderiv_sinh fderiv_sinh

theorem ContDiff.sinh {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.sinh (f x) :=
  Real.cont_diff_sinh.comp h
#align cont_diff.sinh ContDiff.sinh

theorem ContDiffAt.sinh {n} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun x => Real.sinh (f x)) x :=
  Real.cont_diff_sinh.ContDiffAt.comp x hf
#align cont_diff_at.sinh ContDiffAt.sinh

theorem ContDiffOn.sinh {n} (hf : ContDiffOn ℝ n f s) :
    ContDiffOn ℝ n (fun x => Real.sinh (f x)) s :=
  Real.cont_diff_sinh.comp_cont_diff_on hf
#align cont_diff_on.sinh ContDiffOn.sinh

theorem ContDiffWithinAt.sinh {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.sinh (f x)) s x :=
  Real.cont_diff_sinh.ContDiffAt.comp_cont_diff_within_at x hf
#align cont_diff_within_at.sinh ContDiffWithinAt.sinh

end

