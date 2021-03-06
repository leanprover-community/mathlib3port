/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle SΓΆnne
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

open Classical TopologicalSpace

namespace Complex

variable {π : Type _} [NondiscreteNormedField π] [NormedAlgebra π β]

/-- The complex exponential is everywhere differentiable, with the derivative `exp x`. -/
theorem has_deriv_at_exp (x : β) : HasDerivAt exp (exp x) x := by
  rw [has_deriv_at_iff_is_o_nhds_zero]
  have : (1 : β) < 2 := by
    norm_num
  refine' (is_O.of_bound β₯exp xβ₯ _).trans_is_o (is_o_pow_id this)
  filter_upwards [Metric.ball_mem_nhds (0 : β) zero_lt_one]
  simp only [β Metric.mem_ball, β dist_zero_right, β norm_pow]
  exact fun z hz => exp_bound_sq x z hz.le

theorem differentiable_exp : Differentiable π exp := fun x => (has_deriv_at_exp x).DifferentiableAt.restrictScalars π

theorem differentiable_at_exp {x : β} : DifferentiableAt π exp x :=
  differentiable_exp x

@[simp]
theorem deriv_exp : deriv exp = exp :=
  funext fun x => (has_deriv_at_exp x).deriv

@[simp]
theorem iter_deriv_exp : β n : β, (deriv^[n]) exp = exp
  | 0 => rfl
  | n + 1 => by
    rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

theorem cont_diff_exp : β {n}, ContDiff π n exp := by
  refine' cont_diff_all_iff_nat.2 fun n => _
  have : ContDiff β (βn) exp := by
    induction' n with n ihn
    Β· exact cont_diff_zero.2 continuous_exp
      
    Β· rw [cont_diff_succ_iff_deriv]
      use differentiable_exp
      rwa [deriv_exp]
      
  exact this.restrict_scalars π

theorem has_strict_deriv_at_exp (x : β) : HasStrictDerivAt exp (exp x) x :=
  cont_diff_exp.ContDiffAt.has_strict_deriv_at' (has_deriv_at_exp x) le_rfl

theorem has_strict_fderiv_at_exp_real (x : β) : HasStrictFderivAt exp (exp x β’ (1 : β βL[β] β)) x :=
  (has_strict_deriv_at_exp x).complex_to_real_fderiv

theorem is_open_map_exp : IsOpenMap exp :=
  open_map_of_strict_deriv has_strict_deriv_at_exp exp_ne_zero

end Complex

section

variable {π : Type _} [NondiscreteNormedField π] [NormedAlgebra π β] {f : π β β} {f' : β} {x : π} {s : Set π}

theorem HasStrictDerivAt.cexp (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x :=
  (Complex.has_strict_deriv_at_exp (f x)).comp x hf

theorem HasDerivAt.cexp (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x :=
  (Complex.has_deriv_at_exp (f x)).comp x hf

theorem HasDerivWithinAt.cexp (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') s x :=
  (Complex.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_cexp (hf : DifferentiableWithinAt π f s x) (hxs : UniqueDiffWithinAt π s x) :
    derivWithin (fun x => Complex.exp (f x)) s x = Complex.exp (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.cexp.derivWithin hxs

@[simp]
theorem deriv_cexp (hc : DifferentiableAt π f x) :
    deriv (fun x => Complex.exp (f x)) x = Complex.exp (f x) * deriv f x :=
  hc.HasDerivAt.cexp.deriv

end

section

variable {π : Type _} [NondiscreteNormedField π] [NormedAlgebra π β] {E : Type _} [NormedGroup E] [NormedSpace π E]
  {f : E β β} {f' : E βL[π] β} {x : E} {s : Set E}

theorem HasStrictFderivAt.cexp (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) β’ f') x :=
  (Complex.has_strict_deriv_at_exp (f x)).comp_has_strict_fderiv_at x hf

theorem HasFderivWithinAt.cexp (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) β’ f') s x :=
  (Complex.has_deriv_at_exp (f x)).comp_has_fderiv_within_at x hf

theorem HasFderivAt.cexp (hf : HasFderivAt f f' x) :
    HasFderivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) β’ f') x :=
  has_fderiv_within_at_univ.1 <| hf.HasFderivWithinAt.cexp

theorem DifferentiableWithinAt.cexp (hf : DifferentiableWithinAt π f s x) :
    DifferentiableWithinAt π (fun x => Complex.exp (f x)) s x :=
  hf.HasFderivWithinAt.cexp.DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.cexp (hc : DifferentiableAt π f x) : DifferentiableAt π (fun x => Complex.exp (f x)) x :=
  hc.HasFderivAt.cexp.DifferentiableAt

theorem DifferentiableOn.cexp (hc : DifferentiableOn π f s) : DifferentiableOn π (fun x => Complex.exp (f x)) s :=
  fun x h => (hc x h).cexp

@[simp]
theorem Differentiable.cexp (hc : Differentiable π f) : Differentiable π fun x => Complex.exp (f x) := fun x =>
  (hc x).cexp

theorem ContDiff.cexp {n} (h : ContDiff π n f) : ContDiff π n fun x => Complex.exp (f x) :=
  Complex.cont_diff_exp.comp h

theorem ContDiffAt.cexp {n} (hf : ContDiffAt π n f x) : ContDiffAt π n (fun x => Complex.exp (f x)) x :=
  Complex.cont_diff_exp.ContDiffAt.comp x hf

theorem ContDiffOn.cexp {n} (hf : ContDiffOn π n f s) : ContDiffOn π n (fun x => Complex.exp (f x)) s :=
  Complex.cont_diff_exp.comp_cont_diff_on hf

theorem ContDiffWithinAt.cexp {n} (hf : ContDiffWithinAt π n f s x) :
    ContDiffWithinAt π n (fun x => Complex.exp (f x)) s x :=
  Complex.cont_diff_exp.ContDiffAt.comp_cont_diff_within_at x hf

end

namespace Real

variable {x y z : β}

theorem has_strict_deriv_at_exp (x : β) : HasStrictDerivAt exp (exp x) x :=
  (Complex.has_strict_deriv_at_exp x).real_of_complex

theorem has_deriv_at_exp (x : β) : HasDerivAt exp (exp x) x :=
  (Complex.has_deriv_at_exp x).real_of_complex

theorem cont_diff_exp {n} : ContDiff β n exp :=
  Complex.cont_diff_exp.real_of_complex

theorem differentiable_exp : Differentiable β exp := fun x => (has_deriv_at_exp x).DifferentiableAt

theorem differentiable_at_exp : DifferentiableAt β exp x :=
  differentiable_exp x

@[simp]
theorem deriv_exp : deriv exp = exp :=
  funext fun x => (has_deriv_at_exp x).deriv

@[simp]
theorem iter_deriv_exp : β n : β, (deriv^[n]) exp = exp
  | 0 => rfl
  | n + 1 => by
    rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

end Real

section

/-! Register lemmas for the derivatives of the composition of `real.exp` with a differentiable
function, for standalone use and use with `simp`. -/


variable {f : β β β} {f' x : β} {s : Set β}

theorem HasStrictDerivAt.exp (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x :=
  (Real.has_strict_deriv_at_exp (f x)).comp x hf

theorem HasDerivAt.exp (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x :=
  (Real.has_deriv_at_exp (f x)).comp x hf

theorem HasDerivWithinAt.exp (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') s x :=
  (Real.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

theorem deriv_within_exp (hf : DifferentiableWithinAt β f s x) (hxs : UniqueDiffWithinAt β s x) :
    derivWithin (fun x => Real.exp (f x)) s x = Real.exp (f x) * derivWithin f s x :=
  hf.HasDerivWithinAt.exp.derivWithin hxs

@[simp]
theorem deriv_exp (hc : DifferentiableAt β f x) : deriv (fun x => Real.exp (f x)) x = Real.exp (f x) * deriv f x :=
  hc.HasDerivAt.exp.deriv

end

section

/-! Register lemmas for the derivatives of the composition of `real.exp` with a differentiable
function, for standalone use and use with `simp`. -/


variable {E : Type _} [NormedGroup E] [NormedSpace β E] {f : E β β} {f' : E βL[β] β} {x : E} {s : Set E}

theorem ContDiff.exp {n} (hf : ContDiff β n f) : ContDiff β n fun x => Real.exp (f x) :=
  Real.cont_diff_exp.comp hf

theorem ContDiffAt.exp {n} (hf : ContDiffAt β n f x) : ContDiffAt β n (fun x => Real.exp (f x)) x :=
  Real.cont_diff_exp.ContDiffAt.comp x hf

theorem ContDiffOn.exp {n} (hf : ContDiffOn β n f s) : ContDiffOn β n (fun x => Real.exp (f x)) s :=
  Real.cont_diff_exp.comp_cont_diff_on hf

theorem ContDiffWithinAt.exp {n} (hf : ContDiffWithinAt β n f s x) :
    ContDiffWithinAt β n (fun x => Real.exp (f x)) s x :=
  Real.cont_diff_exp.ContDiffAt.comp_cont_diff_within_at x hf

theorem HasFderivWithinAt.exp (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) β’ f') s x :=
  (Real.has_deriv_at_exp (f x)).comp_has_fderiv_within_at x hf

theorem HasFderivAt.exp (hf : HasFderivAt f f' x) : HasFderivAt (fun x => Real.exp (f x)) (Real.exp (f x) β’ f') x :=
  (Real.has_deriv_at_exp (f x)).comp_has_fderiv_at x hf

theorem HasStrictFderivAt.exp (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => Real.exp (f x)) (Real.exp (f x) β’ f') x :=
  (Real.has_strict_deriv_at_exp (f x)).comp_has_strict_fderiv_at x hf

theorem DifferentiableWithinAt.exp (hf : DifferentiableWithinAt β f s x) :
    DifferentiableWithinAt β (fun x => Real.exp (f x)) s x :=
  hf.HasFderivWithinAt.exp.DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.exp (hc : DifferentiableAt β f x) : DifferentiableAt β (fun x => Real.exp (f x)) x :=
  hc.HasFderivAt.exp.DifferentiableAt

theorem DifferentiableOn.exp (hc : DifferentiableOn β f s) : DifferentiableOn β (fun x => Real.exp (f x)) s :=
  fun x h => (hc x h).exp

@[simp]
theorem Differentiable.exp (hc : Differentiable β f) : Differentiable β fun x => Real.exp (f x) := fun x => (hc x).exp

theorem fderiv_within_exp (hf : DifferentiableWithinAt β f s x) (hxs : UniqueDiffWithinAt β s x) :
    fderivWithin β (fun x => Real.exp (f x)) s x = Real.exp (f x) β’ fderivWithin β f s x :=
  hf.HasFderivWithinAt.exp.fderivWithin hxs

@[simp]
theorem fderiv_exp (hc : DifferentiableAt β f x) :
    fderiv β (fun x => Real.exp (f x)) x = Real.exp (f x) β’ fderiv β f x :=
  hc.HasFderivAt.exp.fderiv

end

