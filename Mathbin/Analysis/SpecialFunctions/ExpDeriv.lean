/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import Mathbin.Analysis.Calculus.Inverse
import Mathbin.Analysis.Complex.RealDeriv
import Mathbin.Analysis.SpecialFunctions.Exp

/-!
# Complex and real exponential

In this file we prove that `complex.exp` and `real.exp` are infinitely smooth functions.

## Tags

exp, derivative
-/


noncomputable section

open Filter Asymptotics Set Function

open_locale Classical TopologicalSpace

namespace Complex

/-- The complex exponential is everywhere differentiable, with the derivative `exp x`. -/
theorem has_deriv_at_exp (x : ℂ) : HasDerivAt exp (exp x) x := by
  rw [has_deriv_at_iff_is_o_nhds_zero]
  have : (1 : ℕ) < 2 := by
    norm_num
  refine' (is_O.of_bound ∥exp x∥ _).trans_is_o (is_o_pow_id this)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one]
  simp only [Metric.mem_ball, dist_zero_right, norm_pow]
  exact fun z hz => exp_bound_sq x z hz.le

theorem differentiable_exp : Differentiable ℂ exp := fun x => (has_deriv_at_exp x).DifferentiableAt

theorem differentiable_at_exp {x : ℂ} : DifferentiableAt ℂ exp x :=
  differentiable_exp x

@[simp]
theorem deriv_exp : deriv exp = exp :=
  funext fun x => (has_deriv_at_exp x).deriv

@[simp]
theorem iter_deriv_exp : ∀ n : ℕ, (deriv^[n]) exp = exp
  | 0 => rfl
  | n + 1 => by
    rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

theorem cont_diff_exp : ∀ {n}, ContDiff ℂ n exp := by
  refine' cont_diff_all_iff_nat.2 fun n => _
  induction' n with n ihn
  · exact cont_diff_zero.2 continuous_exp
    
  · rw [cont_diff_succ_iff_deriv]
    use differentiable_exp
    rwa [deriv_exp]
    

theorem has_strict_deriv_at_exp (x : ℂ) : HasStrictDerivAt exp (exp x) x :=
  cont_diff_exp.ContDiffAt.has_strict_deriv_at' (has_deriv_at_exp x) le_rfl

theorem has_strict_fderiv_at_exp_real (x : ℂ) : HasStrictFderivAt exp (exp x • (1 : ℂ →L[ℝ] ℂ)) x :=
  (has_strict_deriv_at_exp x).complex_to_real_fderiv

theorem is_open_map_exp : IsOpenMap exp :=
  open_map_of_strict_deriv has_strict_deriv_at_exp exp_ne_zero

end Complex

section

variable {f : ℂ → ℂ} {f' x : ℂ} {s : Set ℂ}

theorem HasStrictDerivAt.cexp (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x :=
  (Complex.has_strict_deriv_at_exp (f x)).comp x hf

theorem HasDerivAt.cexp (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x :=
  (Complex.has_deriv_at_exp (f x)).comp x hf

theorem HasDerivWithinAt.cexp (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') s x :=
  (Complex.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_cexp (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.exp (f x)) s x = Complex.exp (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.cexp.derivWithin hxs

@[simp]
theorem deriv_cexp (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.exp (f x)) x = Complex.exp (f x) * deriv f x :=
  hc.HasDerivAt.cexp.deriv

end

section

variable {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} {s : Set ℝ}

open Complex

theorem HasStrictDerivAt.cexp_real (h : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => exp (f x)) (exp (f x) * f') x :=
  (has_strict_fderiv_at_exp_real (f x)).comp_has_strict_deriv_at x h

theorem HasDerivAt.cexp_real (h : HasDerivAt f f' x) : HasDerivAt (fun x => exp (f x)) (exp (f x) * f') x :=
  (has_strict_fderiv_at_exp_real (f x)).HasFderivAt.comp_has_deriv_at x h

theorem HasDerivWithinAt.cexp_real (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => exp (f x)) (exp (f x) * f') s x :=
  (has_strict_fderiv_at_exp_real (f x)).HasFderivAt.comp_has_deriv_within_at x h

end

section

variable {E : Type _} [NormedGroup E] [NormedSpace ℂ E] {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E} {s : Set E}

theorem HasStrictFderivAt.cexp (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') x :=
  (Complex.has_strict_deriv_at_exp (f x)).comp_has_strict_fderiv_at x hf

theorem HasFderivWithinAt.cexp (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') s x :=
  (Complex.has_deriv_at_exp (f x)).comp_has_fderiv_within_at x hf

theorem HasFderivAt.cexp (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') x :=
  has_fderiv_within_at_univ.1 <| hf.HasFderivWithinAt.cexp

theorem DifferentiableWithinAt.cexp (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.exp (f x)) s x :=
  hf.HasFderivWithinAt.cexp.DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.cexp (hc : DifferentiableAt ℂ f x) : DifferentiableAt ℂ (fun x => Complex.exp (f x)) x :=
  hc.HasFderivAt.cexp.DifferentiableAt

theorem DifferentiableOn.cexp (hc : DifferentiableOn ℂ f s) : DifferentiableOn ℂ (fun x => Complex.exp (f x)) s :=
  fun x h => (hc x h).cexp

@[simp]
theorem Differentiable.cexp (hc : Differentiable ℂ f) : Differentiable ℂ fun x => Complex.exp (f x) := fun x =>
  (hc x).cexp

theorem ContDiff.cexp {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.exp (f x) :=
  Complex.cont_diff_exp.comp h

theorem ContDiffAt.cexp {n} (hf : ContDiffAt ℂ n f x) : ContDiffAt ℂ n (fun x => Complex.exp (f x)) x :=
  Complex.cont_diff_exp.ContDiffAt.comp x hf

theorem ContDiffOn.cexp {n} (hf : ContDiffOn ℂ n f s) : ContDiffOn ℂ n (fun x => Complex.exp (f x)) s :=
  Complex.cont_diff_exp.comp_cont_diff_on hf

theorem ContDiffWithinAt.cexp {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.exp (f x)) s x :=
  Complex.cont_diff_exp.ContDiffAt.comp_cont_diff_within_at x hf

end

namespace Real

variable {x y z : ℝ}

theorem has_strict_deriv_at_exp (x : ℝ) : HasStrictDerivAt exp (exp x) x :=
  (Complex.has_strict_deriv_at_exp x).real_of_complex

theorem has_deriv_at_exp (x : ℝ) : HasDerivAt exp (exp x) x :=
  (Complex.has_deriv_at_exp x).real_of_complex

theorem cont_diff_exp {n} : ContDiff ℝ n exp :=
  Complex.cont_diff_exp.real_of_complex

theorem differentiable_exp : Differentiable ℝ exp := fun x => (has_deriv_at_exp x).DifferentiableAt

theorem differentiable_at_exp : DifferentiableAt ℝ exp x :=
  differentiable_exp x

@[simp]
theorem deriv_exp : deriv exp = exp :=
  funext fun x => (has_deriv_at_exp x).deriv

@[simp]
theorem iter_deriv_exp : ∀ n : ℕ, (deriv^[n]) exp = exp
  | 0 => rfl
  | n + 1 => by
    rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

end Real

section

/-! Register lemmas for the derivatives of the composition of `real.exp` with a differentiable
function, for standalone use and use with `simp`. -/


variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

theorem HasStrictDerivAt.exp (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x :=
  (Real.has_strict_deriv_at_exp (f x)).comp x hf

theorem HasDerivAt.exp (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x :=
  (Real.has_deriv_at_exp (f x)).comp x hf

theorem HasDerivWithinAt.exp (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') s x :=
  (Real.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_exp (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.exp (f x)) s x = Real.exp (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.exp.derivWithin hxs

@[simp]
theorem deriv_exp (hc : DifferentiableAt ℝ f x) : deriv (fun x => Real.exp (f x)) x = Real.exp (f x) * deriv f x :=
  hc.HasDerivAt.exp.deriv

end

section

/-! Register lemmas for the derivatives of the composition of `real.exp` with a differentiable
function, for standalone use and use with `simp`. -/


variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E} {s : Set E}

theorem ContDiff.exp {n} (hf : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.exp (f x) :=
  Real.cont_diff_exp.comp hf

theorem ContDiffAt.exp {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.exp (f x)) x :=
  Real.cont_diff_exp.ContDiffAt.comp x hf

theorem ContDiffOn.exp {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.exp (f x)) s :=
  Real.cont_diff_exp.comp_cont_diff_on hf

theorem ContDiffWithinAt.exp {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.exp (f x)) s x :=
  Real.cont_diff_exp.ContDiffAt.comp_cont_diff_within_at x hf

theorem HasFderivWithinAt.exp (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') s x :=
  (Real.has_deriv_at_exp (f x)).comp_has_fderiv_within_at x hf

theorem HasFderivAt.exp (hf : HasFderivAt f f' x) : HasFderivAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') x :=
  (Real.has_deriv_at_exp (f x)).comp_has_fderiv_at x hf

theorem HasStrictFderivAt.exp (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') x :=
  (Real.has_strict_deriv_at_exp (f x)).comp_has_strict_fderiv_at x hf

theorem DifferentiableWithinAt.exp (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.exp (f x)) s x :=
  hf.HasFderivWithinAt.exp.DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.exp (hc : DifferentiableAt ℝ f x) : DifferentiableAt ℝ (fun x => Real.exp (f x)) x :=
  hc.HasFderivAt.exp.DifferentiableAt

theorem DifferentiableOn.exp (hc : DifferentiableOn ℝ f s) : DifferentiableOn ℝ (fun x => Real.exp (f x)) s :=
  fun x h => (hc x h).exp

@[simp]
theorem Differentiable.exp (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.exp (f x) := fun x => (hc x).exp

theorem fderiv_within_exp (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.exp (f x)) s x = Real.exp (f x) • fderivWithin ℝ f s x :=
  hf.HasFderivWithinAt.exp.fderivWithin hxs

@[simp]
theorem fderiv_exp (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.exp (f x)) x = Real.exp (f x) • fderiv ℝ f x :=
  hc.HasFderivAt.exp.fderiv

end

