/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.Calculus.ParametricIntegral
import Mathbin.MeasureTheory.Integral.IntervalIntegral

/-!
# Derivatives of interval integrals depending on parameters

In this file we restate theorems about derivatives of integrals depending on parameters for interval
integrals.  -/


open TopologicalSpace MeasureTheory Filter Metric

open TopologicalSpace Filter Interval

variable {π : Type _} [IsROrC π] {ΞΌ : Measureβ β} {E : Type _} [NormedGroup E] [NormedSpace β E] [NormedSpace π E]
  [CompleteSpace E] {H : Type _} [NormedGroup H] [NormedSpace π H] {a b Ξ΅ : β} {bound : β β β}

namespace intervalIntegral

/-- Differentiation under integral of `x β¦ β« t in a..b, F x t` at a given point `xβ`, assuming
`F xβ` is integrable, `x β¦ F x a` is locally Lipschitz on a ball around `xβ` for ae `a`
(with a ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is ae-measurable
for `x` in a possibly smaller neighborhood of `xβ`. -/
theorem has_fderiv_at_integral_of_dominated_loc_of_lip {F : H β β β E} {F' : β β H βL[π] E} {xβ : H} (Ξ΅_pos : 0 < Ξ΅)
    (hF_meas : βαΆ  x in π xβ, AeStronglyMeasurable (F x) (ΞΌ.restrict (Ξ a b))) (hF_int : IntervalIntegrable (F xβ) ΞΌ a b)
    (hF'_meas : AeStronglyMeasurable F' (ΞΌ.restrict (Ξ a b)))
    (h_lip : βα΅ t βΞΌ, t β Ξ a b β LipschitzOnWith (Real.nnabs <| bound t) (fun x => F x t) (Ball xβ Ξ΅))
    (bound_integrable : IntervalIntegrable bound ΞΌ a b)
    (h_diff : βα΅ t βΞΌ, t β Ξ a b β HasFderivAt (fun x => F x t) (F' t) xβ) :
    IntervalIntegrable F' ΞΌ a b β§ HasFderivAt (fun x => β« t in a..b, F x t βΞΌ) (β« t in a..b, F' t βΞΌ) xβ := by
  simp only [β interval_integrable_iff, β interval_integral_eq_integral_interval_oc,
    ae_restrict_iff' measurable_set_interval_oc] at *
  have := has_fderiv_at_integral_of_dominated_loc_of_lip Ξ΅_pos hF_meas hF_int hF'_meas h_lip bound_integrable h_diff
  exact β¨this.1, this.2.const_smul _β©

/-- Differentiation under integral of `x β¦ β« F x a` at a given point `xβ`, assuming
`F xβ` is integrable, `x β¦ F x a` is differentiable on a ball around `xβ` for ae `a` with
derivative norm uniformly bounded by an integrable function (the ball radius is independent of `a`),
and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `xβ`. -/
theorem has_fderiv_at_integral_of_dominated_of_fderiv_le {F : H β β β E} {F' : H β β β H βL[π] E} {xβ : H}
    (Ξ΅_pos : 0 < Ξ΅) (hF_meas : βαΆ  x in π xβ, AeStronglyMeasurable (F x) (ΞΌ.restrict (Ξ a b)))
    (hF_int : IntervalIntegrable (F xβ) ΞΌ a b) (hF'_meas : AeStronglyMeasurable (F' xβ) (ΞΌ.restrict (Ξ a b)))
    (h_bound : βα΅ t βΞΌ, t β Ξ a b β β, β x β Ball xβ Ξ΅, β, β₯F' x tβ₯ β€ bound t)
    (bound_integrable : IntervalIntegrable bound ΞΌ a b)
    (h_diff : βα΅ t βΞΌ, t β Ξ a b β β, β x β Ball xβ Ξ΅, β, HasFderivAt (fun x => F x t) (F' x t) x) :
    HasFderivAt (fun x => β« t in a..b, F x t βΞΌ) (β« t in a..b, F' xβ t βΞΌ) xβ := by
  simp only [β interval_integrable_iff, β interval_integral_eq_integral_interval_oc,
    ae_restrict_iff' measurable_set_interval_oc] at *
  exact
    (has_fderiv_at_integral_of_dominated_of_fderiv_le Ξ΅_pos hF_meas hF_int hF'_meas h_bound bound_integrable
          h_diff).const_smul
      _

/-- Derivative under integral of `x β¦ β« F x a` at a given point `xβ : π`, `π = β` or `π = β`,
assuming `F xβ` is integrable, `x β¦ F x a` is locally Lipschitz on a ball around `xβ` for ae `a`
(with ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is
ae-measurable for `x` in a possibly smaller neighborhood of `xβ`. -/
theorem has_deriv_at_integral_of_dominated_loc_of_lip {F : π β β β E} {F' : β β E} {xβ : π} (Ξ΅_pos : 0 < Ξ΅)
    (hF_meas : βαΆ  x in π xβ, AeStronglyMeasurable (F x) (ΞΌ.restrict (Ξ a b))) (hF_int : IntervalIntegrable (F xβ) ΞΌ a b)
    (hF'_meas : AeStronglyMeasurable F' (ΞΌ.restrict (Ξ a b)))
    (h_lipsch : βα΅ t βΞΌ, t β Ξ a b β LipschitzOnWith (Real.nnabs <| bound t) (fun x => F x t) (Ball xβ Ξ΅))
    (bound_integrable : IntervalIntegrable (bound : β β β) ΞΌ a b)
    (h_diff : βα΅ t βΞΌ, t β Ξ a b β HasDerivAt (fun x => F x t) (F' t) xβ) :
    IntervalIntegrable F' ΞΌ a b β§ HasDerivAt (fun x => β« t in a..b, F x t βΞΌ) (β« t in a..b, F' t βΞΌ) xβ := by
  simp only [β interval_integrable_iff, β interval_integral_eq_integral_interval_oc,
    ae_restrict_iff' measurable_set_interval_oc] at *
  have := has_deriv_at_integral_of_dominated_loc_of_lip Ξ΅_pos hF_meas hF_int hF'_meas h_lipsch bound_integrable h_diff
  exact β¨this.1, this.2.const_smul _β©

/-- Derivative under integral of `x β¦ β« F x a` at a given point `xβ : π`, `π = β` or `π = β`,
assuming `F xβ` is integrable, `x β¦ F x a` is differentiable on an interval around `xβ` for ae `a`
(with interval radius independent of `a`) with derivative uniformly bounded by an integrable
function, and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `xβ`. -/
theorem has_deriv_at_integral_of_dominated_loc_of_deriv_le {F : π β β β E} {F' : π β β β E} {xβ : π} (Ξ΅_pos : 0 < Ξ΅)
    (hF_meas : βαΆ  x in π xβ, AeStronglyMeasurable (F x) (ΞΌ.restrict (Ξ a b))) (hF_int : IntervalIntegrable (F xβ) ΞΌ a b)
    (hF'_meas : AeStronglyMeasurable (F' xβ) (ΞΌ.restrict (Ξ a b)))
    (h_bound : βα΅ t βΞΌ, t β Ξ a b β β, β x β Ball xβ Ξ΅, β, β₯F' x tβ₯ β€ bound t)
    (bound_integrable : IntervalIntegrable bound ΞΌ a b)
    (h_diff : βα΅ t βΞΌ, t β Ξ a b β β, β x β Ball xβ Ξ΅, β, HasDerivAt (fun x => F x t) (F' x t) x) :
    IntervalIntegrable (F' xβ) ΞΌ a b β§ HasDerivAt (fun x => β« t in a..b, F x t βΞΌ) (β« t in a..b, F' xβ t βΞΌ) xβ := by
  simp only [β interval_integrable_iff, β interval_integral_eq_integral_interval_oc,
    ae_restrict_iff' measurable_set_interval_oc] at *
  have :=
    has_deriv_at_integral_of_dominated_loc_of_deriv_le Ξ΅_pos hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
  exact β¨this.1, this.2.const_smul _β©

end intervalIntegral

