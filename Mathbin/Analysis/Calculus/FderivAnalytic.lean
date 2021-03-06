/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.Calculus.Deriv
import Mathbin.Analysis.Analytic.Basic
import Mathbin.Analysis.Calculus.ContDiff

/-!
# Frechet derivatives of analytic functions.

A function expressible as a power series at a point has a Frechet derivative there.
Also the special case in terms of `deriv` when the domain is 1-dimensional.
-/


open Filter Asymptotics

open Ennreal

variable {ð : Type _} [NondiscreteNormedField ð]

variable {E : Type _} [NormedGroup E] [NormedSpace ð E]

variable {F : Type _} [NormedGroup F] [NormedSpace ð F]

section fderiv

variable {p : FormalMultilinearSeries ð E F} {r : ââ¥0â}

variable {f : E â F} {x : E} {s : Set E}

theorem HasFpowerSeriesAt.has_strict_fderiv_at (h : HasFpowerSeriesAt f p x) :
    HasStrictFderivAt f (continuousMultilinearCurryFin1 ð E F (p 1)) x := by
  refine' h.is_O_image_sub_norm_mul_norm_sub.trans_is_o (is_o.of_norm_right _)
  refine' is_o_iff_exists_eq_mul.2 â¨fun y => â¥y - (x, x)â¥, _, eventually_eq.rflâ©
  refine' (continuous_id.sub continuous_const).norm.tendsto' _ _ _
  rw [_root_.id, sub_self, norm_zero]

theorem HasFpowerSeriesAt.has_fderiv_at (h : HasFpowerSeriesAt f p x) :
    HasFderivAt f (continuousMultilinearCurryFin1 ð E F (p 1)) x :=
  h.HasStrictFderivAt.HasFderivAt

theorem HasFpowerSeriesAt.differentiable_at (h : HasFpowerSeriesAt f p x) : DifferentiableAt ð f x :=
  h.HasFderivAt.DifferentiableAt

theorem AnalyticAt.differentiable_at : AnalyticAt ð f x â DifferentiableAt ð f x
  | â¨p, hpâ© => hp.DifferentiableAt

theorem AnalyticAt.differentiable_within_at (h : AnalyticAt ð f x) : DifferentiableWithinAt ð f s x :=
  h.DifferentiableAt.DifferentiableWithinAt

theorem HasFpowerSeriesAt.fderiv_eq (h : HasFpowerSeriesAt f p x) :
    fderiv ð f x = continuousMultilinearCurryFin1 ð E F (p 1) :=
  h.HasFderivAt.fderiv

theorem HasFpowerSeriesOnBall.differentiable_on [CompleteSpace F] (h : HasFpowerSeriesOnBall f p x r) :
    DifferentiableOn ð f (Emetric.Ball x r) := fun y hy => (h.analytic_at_of_mem hy).DifferentiableWithinAt

theorem AnalyticOn.differentiable_on (h : AnalyticOn ð f s) : DifferentiableOn ð f s := fun y hy =>
  (h y hy).DifferentiableWithinAt

theorem HasFpowerSeriesOnBall.has_fderiv_at [CompleteSpace F] (h : HasFpowerSeriesOnBall f p x r) {y : E}
    (hy : (â¥yâ¥â : ââ¥0â) < r) : HasFderivAt f (continuousMultilinearCurryFin1 ð E F (p.changeOrigin y 1)) (x + y) :=
  (h.changeOrigin hy).HasFpowerSeriesAt.HasFderivAt

theorem HasFpowerSeriesOnBall.fderiv_eq [CompleteSpace F] (h : HasFpowerSeriesOnBall f p x r) {y : E}
    (hy : (â¥yâ¥â : ââ¥0â) < r) : fderiv ð f (x + y) = continuousMultilinearCurryFin1 ð E F (p.changeOrigin y 1) :=
  (h.HasFderivAt hy).fderiv

/-- If a function has a power series on a ball, then so does its derivative. -/
theorem HasFpowerSeriesOnBall.fderiv [CompleteSpace F] (h : HasFpowerSeriesOnBall f p x r) :
    HasFpowerSeriesOnBall (fderiv ð f)
      ((continuousMultilinearCurryFin1 ð E F : (E[Ã1]âL[ð] F) âL[ð] E âL[ð] F).compFormalMultilinearSeries
        (p.changeOriginSeries 1))
      x r :=
  by
  suffices A :
    HasFpowerSeriesOnBall (fun z => continuousMultilinearCurryFin1 ð E F (p.change_origin (z - x) 1))
      ((continuousMultilinearCurryFin1 ð E F : (E[Ã1]âL[ð] F) âL[ð] E âL[ð] F).compFormalMultilinearSeries
        (p.change_origin_series 1))
      x r
  Â· apply A.congr
    intro z hz
    dsimp'
    rw [â h.fderiv_eq, add_sub_cancel'_right]
    simpa only [â edist_eq_coe_nnnorm_sub, â Emetric.mem_ball] using hz
    
  suffices B : HasFpowerSeriesOnBall (fun z => p.change_origin (z - x) 1) (p.change_origin_series 1) x r
  exact
    (continuousMultilinearCurryFin1 ð E F).toContinuousLinearEquiv.toContinuousLinearMap.comp_has_fpower_series_on_ball
      B
  simpa using ((p.has_fpower_series_on_ball_change_origin 1 (h.r_pos.trans_le h.r_le)).mono h.r_pos h.r_le).comp_sub x

/-- If a function is analytic on a set `s`, so is its FrÃ©chet derivative. -/
theorem AnalyticOn.fderiv [CompleteSpace F] (h : AnalyticOn ð f s) : AnalyticOn ð (fderiv ð f) s := by
  intro y hy
  rcases h y hy with â¨p, r, hpâ©
  exact hp.fderiv.analytic_at

/-- If a function is analytic on a set `s`, so are its successive FrÃ©chet derivative. -/
theorem AnalyticOn.iterated_fderiv [CompleteSpace F] (h : AnalyticOn ð f s) (n : â) :
    AnalyticOn ð (iteratedFderiv ð n f) s := by
  induction' n with n IH
  Â· rw [iterated_fderiv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 ð E F).symm : F âL[ð] E[Ã0]âL[ð] F).comp_analytic_on h
    
  Â· rw [iterated_fderiv_succ_eq_comp_left]
    apply
      (continuousMultilinearCurryLeftEquiv ð (fun i : Finâ (n + 1) => E)
              F).toContinuousLinearEquiv.toContinuousLinearMap.comp_analytic_on
    exact IH.fderiv
    

/-- An analytic function is infinitely differentiable. -/
theorem AnalyticOn.cont_diff_on [CompleteSpace F] (h : AnalyticOn ð f s) {n : WithTop â} : ContDiffOn ð n f s := by
  let t := { x | AnalyticAt ð f x }
  suffices : ContDiffOn ð n f t
  exact this.mono h
  have H : AnalyticOn ð f t := fun x hx => hx
  have t_open : IsOpen t := is_open_analytic_at ð f
  apply cont_diff_on_of_continuous_on_differentiable_on
  Â· intro m hm
    apply (H.iterated_fderiv m).ContinuousOn.congr
    intro x hx
    exact iterated_fderiv_within_of_is_open _ t_open hx
    
  Â· intro m hm
    apply (H.iterated_fderiv m).DifferentiableOn.congr
    intro x hx
    exact iterated_fderiv_within_of_is_open _ t_open hx
    

end fderiv

section deriv

variable {p : FormalMultilinearSeries ð ð F} {r : ââ¥0â}

variable {f : ð â F} {x : ð} {s : Set ð}

protected theorem HasFpowerSeriesAt.has_strict_deriv_at (h : HasFpowerSeriesAt f p x) :
    HasStrictDerivAt f (p 1 fun _ => 1) x :=
  h.HasStrictFderivAt.HasStrictDerivAt

protected theorem HasFpowerSeriesAt.has_deriv_at (h : HasFpowerSeriesAt f p x) : HasDerivAt f (p 1 fun _ => 1) x :=
  h.HasStrictDerivAt.HasDerivAt

protected theorem HasFpowerSeriesAt.deriv (h : HasFpowerSeriesAt f p x) : deriv f x = p 1 fun _ => 1 :=
  h.HasDerivAt.deriv

/-- If a function is analytic on a set `s`, so is its derivative. -/
theorem AnalyticOn.deriv [CompleteSpace F] (h : AnalyticOn ð f s) : AnalyticOn ð (deriv f) s :=
  (ContinuousLinearMap.apply ð F (1 : ð)).comp_analytic_on h.fderiv

/-- If a function is analytic on a set `s`, so are its successive derivatives. -/
theorem AnalyticOn.iterated_deriv [CompleteSpace F] (h : AnalyticOn ð f s) (n : â) : AnalyticOn ð ((deriv^[n]) f) s :=
  by
  induction' n with n IH
  Â· exact h
    
  Â· simpa only [â Function.iterate_succ', â Function.comp_app] using IH.deriv
    

end deriv

