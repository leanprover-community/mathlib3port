/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module analysis.special_functions.gamma
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Integral.ExpDecay
import Mathbin.Analysis.Calculus.ParametricIntegral
import Mathbin.Analysis.SpecialFunctions.Integrals

/-!
# The Gamma function

This file defines the `Γ` function (of a real or complex variable `s`). We define this by Euler's
integral `Γ(s) = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` in the range where this integral converges
(i.e., for `0 < s` in the real case, and `0 < re s` in the complex case).

We show that this integral satisfies `Γ(1) = 1` and `Γ(s + 1) = s * Γ(s)`; hence we can define
`Γ(s)` for all `s` as the unique function satisfying this recurrence and agreeing with Euler's
integral in the convergence range. In the complex case we also prove that the resulting function is
holomorphic on `ℂ` away from the points `{-n : n ∈ ℕ}`.

## Main statements (real case)

* `real.Gamma` : the `Γ` function (of a real variable).
* `real.Gamma_eq_integral` : for `0 < s`, `Γ(s)` agrees with Euler's integral
  `∫ (x:ℝ) in Ioi 0, exp (-x) * x ^ (s - 1)`
* `real.Gamma_add_one` : for all `s : ℝ` with `s ≠ 0`, we have `Γ(s + 1) = s Γ(s)`.
* `real.Gamma_nat_eq_factorial` : for all `n : ℕ` we have `Γ (n + 1) = n!`.
* `real.differentiable_at_Gamma` : `Γ` is real-differentiable at all `s : ℝ` with
  `s ∉ {-n : n ∈ ℕ}`.
* `real.Gamma_ne_zero`: for all `s : ℝ` with `s ∉ {-n : n ∈ ℕ}` we have `Γ s ≠ 0`.
* `real.tendsto_log_Gamma`: for all `0 < s`, the limit as `n → ∞` of the sequence
  `n ↦ s log n + log n! - (log s + ... + log (s + n))` is `log Γ(s)`.
* `real.convex_on_log_Gamma` : `log ∘ Γ` is convex on `Ioi 0`.
* `real.eq_Gamma_of_log_convex` : the Bohr-Mollerup theorem, which states that the `Γ` function is
  the unique log-convex, positive-valued function on `Ioi 0` satisfying the functional equation
  and having `Γ 1 = 1`.

## Main statements (complex case)

* `complex.Gamma` : the `Γ` function (of a complex variable).
* `complex.Gamma_eq_integral` : for `0 < re s`, `Γ(s)` agrees with Euler's integral.
* `complex.Gamma_add_one` : for all `s : ℂ` with `s ≠ 0`, we have `Γ(s + 1) = s Γ(s)`.
* `complex.Gamma_nat_eq_factorial` : for all `n : ℕ` we have `Γ (n + 1) = n!`.
* `complex.differentiable_at_Gamma` : `Γ` is complex-differentiable at all `s : ℂ` with
  `s ∉ {-n : n ∈ ℕ}`.

## Tags

Gamma
-/


noncomputable section

open Filter intervalIntegral Set Real MeasureTheory Asymptotics

open Nat TopologicalSpace Ennreal BigOperators

theorem integral_exp_neg_ioi : (∫ x : ℝ in Ioi 0, exp (-x)) = 1 :=
  by
  refine' tendsto_nhds_unique (interval_integral_tendsto_integral_Ioi _ _ tendsto_id) _
  · simpa only [neg_mul, one_mul] using expNegIntegrableOnIoi 0 zero_lt_one
  · simpa using tendsto_exp_neg_at_top_nhds_0.const_sub 1
#align integral_exp_neg_Ioi integral_exp_neg_ioi

namespace Real

/-- Asymptotic bound for the `Γ` function integrand. -/
theorem Gamma_integrand_isO (s : ℝ) :
    (fun x : ℝ => exp (-x) * x ^ s) =o[at_top] fun x : ℝ => exp (-(1 / 2) * x) :=
  by
  refine' is_o_of_tendsto (fun x hx => _) _
  · exfalso
    exact (exp_pos (-(1 / 2) * x)).ne' hx
  have :
    (fun x : ℝ => exp (-x) * x ^ s / exp (-(1 / 2) * x)) =
      (fun x : ℝ => exp (1 / 2 * x) / x ^ s)⁻¹ :=
    by
    ext1 x
    field_simp [exp_ne_zero, exp_neg, ← Real.exp_add]
    left
    ring
  rw [this]
  exact (tendsto_exp_mul_div_rpow_atTop s (1 / 2) one_half_pos).inv_tendsto_at_top
#align real.Gamma_integrand_is_o Real.Gamma_integrand_isO

/-- The Euler integral for the `Γ` function converges for positive real `s`. -/
theorem gammaIntegralConvergent {s : ℝ} (h : 0 < s) :
    IntegrableOn (fun x : ℝ => exp (-x) * x ^ (s - 1)) (Ioi 0) :=
  by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrable_on_union]
  constructor
  · rw [← integrableOn_icc_iff_integrableOn_ioc]
    refine' integrable_on.continuous_on_mul continuous_on_id.neg.exp _ is_compact_Icc
    refine' (intervalIntegrable_iff_integrable_icc_of_le zero_le_one).mp _
    exact interval_integrable_rpow' (by linarith)
  · refine' integrableOfIsOExpNeg one_half_pos _ (Gamma_integrand_is_o _).IsO
    refine' continuous_on_id.neg.exp.mul (continuous_on_id.rpow_const _)
    intro x hx
    exact Or.inl ((zero_lt_one : (0 : ℝ) < 1).trans_le hx).ne'
#align real.Gamma_integral_convergent Real.gammaIntegralConvergent

end Real

namespace Complex

/- Technical note: In defining the Gamma integrand exp (-x) * x ^ (s - 1) for s complex, we have to
make a choice between ↑(real.exp (-x)), complex.exp (↑(-x)), and complex.exp (-↑x), all of which are
equal but not definitionally so. We use the first of these throughout. -/
/-- The integral defining the `Γ` function converges for complex `s` with `0 < re s`.

This is proved by reduction to the real case. -/
theorem gammaIntegralConvergent {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) :=
  by
  constructor
  · refine' ContinuousOn.aeStronglyMeasurable _ measurableSet_ioi
    apply (continuous_of_real.comp continuous_neg.exp).ContinuousOn.mul
    apply ContinuousAt.continuousOn
    intro x hx
    have : ContinuousAt (fun x : ℂ => x ^ (s - 1)) ↑x :=
      by
      apply continuousAt_cpow_const
      rw [of_real_re]
      exact Or.inl hx
    exact ContinuousAt.comp this continuous_of_real.continuous_at
  · rw [← has_finite_integral_norm_iff]
    refine' has_finite_integral.congr (Real.gammaIntegralConvergent hs).2 _
    refine' (ae_restrict_iff' measurableSet_ioi).mpr (ae_of_all _ fun x hx => _)
    dsimp only
    rw [norm_eq_abs, map_mul, abs_of_nonneg <| le_of_lt <| exp_pos <| -x,
      abs_cpow_eq_rpow_re_of_pos hx _]
    simp
#align complex.Gamma_integral_convergent Complex.gammaIntegralConvergent

/-- Euler's integral for the `Γ` function (of a complex variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `complex.Gamma_integral_convergent` for a proof of the convergence of the integral for
`0 < re s`. -/
def gammaIntegral (s : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), ↑(-x).exp * ↑x ^ (s - 1)
#align complex.Gamma_integral Complex.gammaIntegral

theorem gammaIntegral_of_real (s : ℝ) :
    gammaIntegral ↑s = ↑(∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ (s - 1)) :=
  by
  rw [Gamma_integral, ← _root_.integral_of_real]
  refine' set_integral_congr measurableSet_ioi _
  intro x hx; dsimp only
  rw [of_real_mul, of_real_cpow (mem_Ioi.mp hx).le]
  simp
#align complex.Gamma_integral_of_real Complex.gammaIntegral_of_real

theorem gammaIntegral_one : gammaIntegral 1 = 1 := by
  simpa only [← of_real_one, Gamma_integral_of_real, of_real_inj, sub_self, rpow_zero,
    mul_one] using integral_exp_neg_ioi
#align complex.Gamma_integral_one Complex.gammaIntegral_one

end Complex

/-! Now we establish the recurrence relation `Γ(s + 1) = s * Γ(s)` using integration by parts. -/


namespace Complex

section GammaRecurrence

/-- The indefinite version of the `Γ` function, `Γ(s, X) = ∫ x ∈ 0..X, exp(-x) x ^ (s - 1)`. -/
def partialGamma (s : ℂ) (X : ℝ) : ℂ :=
  ∫ x in 0 ..X, (-x).exp * x ^ (s - 1)
#align complex.partial_Gamma Complex.partialGamma

theorem tendsto_partialGamma {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun X : ℝ => partialGamma s X) atTop (𝓝 <| gammaIntegral s) :=
  intervalIntegral_tendsto_integral_ioi 0 (gammaIntegralConvergent hs) tendsto_id
#align complex.tendsto_partial_Gamma Complex.tendsto_partialGamma

private theorem Gamma_integrand_interval_integrable (s : ℂ) {X : ℝ} (hs : 0 < s.re) (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) volume 0 X :=
  by
  rw [intervalIntegrable_iff_integrable_ioc_of_le hX]
  exact integrable_on.mono_set (Gamma_integral_convergent hs) Ioc_subset_Ioi_self
#align complex.Gamma_integrand_interval_integrable complex.Gamma_integrand_interval_integrable

private theorem Gamma_integrand_deriv_integrable_A {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => -((-x).exp * x ^ s) : ℝ → ℂ) volume 0 X :=
  by
  convert (Gamma_integrand_interval_integrable (s + 1) _ hX).neg
  · ext1
    simp only [add_sub_cancel, Pi.neg_apply]
  · simp only [add_re, one_re]
    linarith
#align complex.Gamma_integrand_deriv_integrable_A complex.Gamma_integrand_deriv_integrable_A

private theorem Gamma_integrand_deriv_integrable_B {s : ℂ} (hs : 0 < s.re) {Y : ℝ} (hY : 0 ≤ Y) :
    IntervalIntegrable (fun x : ℝ => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) volume 0 Y :=
  by
  have :
    (fun x => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) =
      (fun x => s * ((-x).exp * x ^ (s - 1)) : ℝ → ℂ) :=
    by
    ext1
    ring
  rw [this, intervalIntegrable_iff_integrable_ioc_of_le hY]
  constructor
  · refine' (continuous_on_const.mul _).AeStronglyMeasurable measurableSet_ioc
    apply (continuous_of_real.comp continuous_neg.exp).ContinuousOn.mul
    apply ContinuousAt.continuousOn
    intro x hx
    refine' (_ : ContinuousAt (fun x : ℂ => x ^ (s - 1)) _).comp continuous_of_real.continuous_at
    apply continuousAt_cpow_const
    rw [of_real_re]
    exact Or.inl hx.1
  rw [← has_finite_integral_norm_iff]
  simp_rw [norm_eq_abs, map_mul]
  refine'
    (((Real.gammaIntegralConvergent hs).monoSet Ioc_subset_Ioi_self).HasFiniteIntegral.congr
          _).const_mul
      _
  rw [eventually_eq, ae_restrict_iff']
  · apply ae_of_all
    intro x hx
    rw [abs_of_nonneg (exp_pos _).le, abs_cpow_eq_rpow_re_of_pos hx.1]
    simp
  · exact measurableSet_ioc
#align complex.Gamma_integrand_deriv_integrable_B complex.Gamma_integrand_deriv_integrable_B

/-- The recurrence relation for the indefinite version of the `Γ` function. -/
theorem partialGamma_add_one {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 0 ≤ X) :
    partialGamma (s + 1) X = s * partialGamma s X - (-X).exp * X ^ s :=
  by
  rw [partial_Gamma, partial_Gamma, add_sub_cancel]
  have F_der_I :
    ∀ x : ℝ,
      x ∈ Ioo 0 X →
        HasDerivAt (fun x => (-x).exp * x ^ s : ℝ → ℂ)
          (-((-x).exp * x ^ s) + (-x).exp * (s * x ^ (s - 1))) x :=
    by
    intro x hx
    have d1 : HasDerivAt (fun y : ℝ => (-y).exp) (-(-x).exp) x := by
      simpa using (hasDerivAt_neg x).exp
    have d2 : HasDerivAt (fun y : ℝ => ↑y ^ s) (s * x ^ (s - 1)) x :=
      by
      have t := @HasDerivAt.cpow_const _ _ _ s (hasDerivAt_id ↑x) _
      simpa only [mul_one] using t.comp_of_real
      simpa only [id.def, of_real_re, of_real_im, Ne.def, eq_self_iff_true, not_true, or_false_iff,
        mul_one] using hx.1
    simpa only [of_real_neg, neg_mul] using d1.of_real_comp.mul d2
  have cont := (continuous_of_real.comp continuous_neg.exp).mul (continuous_of_real_cpow_const hs)
  have der_ible :=
    (Gamma_integrand_deriv_integrable_A hs hX).add (Gamma_integrand_deriv_integrable_B hs hX)
  have int_eval := integral_eq_sub_of_has_deriv_at_of_le hX cont.continuous_on F_der_I der_ible
  -- We are basically done here but manipulating the output into the right form is fiddly.
  apply_fun fun x : ℂ => -x  at int_eval
  rw [intervalIntegral.integral_add (Gamma_integrand_deriv_integrable_A hs hX)
      (Gamma_integrand_deriv_integrable_B hs hX),
    intervalIntegral.integral_neg, neg_add, neg_neg] at int_eval
  rw [eq_sub_of_add_eq int_eval, sub_neg_eq_add, neg_sub, add_comm, add_sub]
  simp only [sub_left_inj, add_left_inj]
  have :
    (fun x => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) =
      (fun x => s * (-x).exp * x ^ (s - 1) : ℝ → ℂ) :=
    by
    ext1
    ring
  rw [this]
  have t := @integral_const_mul 0 X volume _ _ s fun x : ℝ => (-x).exp * x ^ (s - 1)
  dsimp at t
  rw [← t, of_real_zero, zero_cpow]
  · rw [mul_zero, add_zero]
    congr
    ext1
    ring
  · contrapose! hs
    rw [hs, zero_re]
#align complex.partial_Gamma_add_one Complex.partialGamma_add_one

/-- The recurrence relation for the `Γ` integral. -/
theorem gammaIntegral_add_one {s : ℂ} (hs : 0 < s.re) :
    gammaIntegral (s + 1) = s * gammaIntegral s :=
  by
  suffices tendsto (s + 1).partialGamma at_top (𝓝 <| s * Gamma_integral s)
    by
    refine' tendsto_nhds_unique _ this
    apply tendsto_partial_Gamma
    rw [add_re, one_re]
    linarith
  have : (fun X : ℝ => s * partial_Gamma s X - X ^ s * (-X).exp) =ᶠ[at_top] (s + 1).partialGamma :=
    by
    apply eventually_eq_of_mem (Ici_mem_at_top (0 : ℝ))
    intro X hX
    rw [partial_Gamma_add_one hs (mem_Ici.mp hX)]
    ring_nf
  refine' tendsto.congr' this _
  suffices tendsto (fun X => -X ^ s * (-X).exp : ℝ → ℂ) at_top (𝓝 0) by
    simpa using tendsto.add (tendsto.const_mul s (tendsto_partial_Gamma hs)) this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have : (fun e : ℝ => ‖-(e : ℂ) ^ s * (-e).exp‖) =ᶠ[at_top] fun e : ℝ => e ^ s.re * (-1 * e).exp :=
    by
    refine' eventually_eq_of_mem (Ioi_mem_at_top 0) _
    intro x hx
    dsimp only
    rw [norm_eq_abs, map_mul, abs.map_neg, abs_cpow_eq_rpow_re_of_pos hx,
      abs_of_nonneg (exp_pos (-x)).le, neg_mul, one_mul]
  exact (tendsto_congr' this).mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_0 _ _ zero_lt_one)
#align complex.Gamma_integral_add_one Complex.gammaIntegral_add_one

end GammaRecurrence

/-! Now we define `Γ(s)` on the whole complex plane, by recursion. -/


section GammaDef

/-- The `n`th function in this family is `Γ(s)` if `-n < s.re`, and junk otherwise. -/
noncomputable def gammaAux : ℕ → ℂ → ℂ
  | 0 => gammaIntegral
  | n + 1 => fun s : ℂ => Gamma_aux n (s + 1) / s
#align complex.Gamma_aux Complex.gammaAux

theorem gammaAux_recurrence1 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
    gammaAux n s = gammaAux n (s + 1) / s :=
  by
  induction' n with n hn generalizing s
  · simp only [Nat.cast_zero, neg_lt_zero] at h1
    dsimp only [Gamma_aux]
    rw [Gamma_integral_add_one h1]
    rw [mul_comm, mul_div_cancel]
    contrapose! h1
    rw [h1]
    simp
  · dsimp only [Gamma_aux]
    have hh1 : -(s + 1).re < n :=
      by
      rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at h1
      rw [add_re, one_re]
      linarith
    rw [← hn (s + 1) hh1]
#align complex.Gamma_aux_recurrence1 Complex.gammaAux_recurrence1

theorem gammaAux_recurrence2 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
    gammaAux n s = gammaAux (n + 1) s := by
  cases n
  · simp only [Nat.cast_zero, neg_lt_zero] at h1
    dsimp only [Gamma_aux]
    rw [Gamma_integral_add_one h1, mul_div_cancel_left]
    rintro rfl
    rw [zero_re] at h1
    exact h1.false
  · dsimp only [Gamma_aux]
    have : Gamma_aux n (s + 1 + 1) / (s + 1) = Gamma_aux n (s + 1) :=
      by
      have hh1 : -(s + 1).re < n :=
        by
        rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at h1
        rw [add_re, one_re]
        linarith
      rw [Gamma_aux_recurrence1 (s + 1) n hh1]
    rw [this]
#align complex.Gamma_aux_recurrence2 Complex.gammaAux_recurrence2

/-- The `Γ` function (of a complex variable `s`). -/
@[pp_nodot]
def gamma (s : ℂ) : ℂ :=
  gammaAux ⌊1 - s.re⌋₊ s
#align complex.Gamma Complex.gamma

theorem gamma_eq_gammaAux (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) : gamma s = gammaAux n s :=
  by
  have u : ∀ k : ℕ, Gamma_aux (⌊1 - s.re⌋₊ + k) s = Gamma s :=
    by
    intro k
    induction' k with k hk
    · simp [Gamma]
    · rw [← hk, Nat.succ_eq_add_one, ← add_assoc]
      refine' (Gamma_aux_recurrence2 s (⌊1 - s.re⌋₊ + k) _).symm
      rw [Nat.cast_add]
      have i0 := Nat.sub_one_lt_floor (1 - s.re)
      simp only [sub_sub_cancel_left] at i0
      refine' lt_add_of_lt_of_nonneg i0 _
      rw [← Nat.cast_zero, Nat.cast_le]
      exact Nat.zero_le k
  convert (u <| n - ⌊1 - s.re⌋₊).symm
  rw [Nat.add_sub_of_le]
  by_cases 0 ≤ 1 - s.re
  · apply Nat.le_of_lt_succ
    exact_mod_cast lt_of_le_of_lt (Nat.floor_le h) (by linarith : 1 - s.re < n + 1)
  · rw [Nat.floor_of_nonpos]
    linarith
    linarith
#align complex.Gamma_eq_Gamma_aux Complex.gamma_eq_gammaAux

/-- The recurrence relation for the `Γ` function. -/
theorem gamma_add_one (s : ℂ) (h2 : s ≠ 0) : gamma (s + 1) = s * gamma s :=
  by
  let n := ⌊1 - s.re⌋₊
  have t1 : -s.re < n := by simpa only [sub_sub_cancel_left] using Nat.sub_one_lt_floor (1 - s.re)
  have t2 : -(s + 1).re < n := by
    rw [add_re, one_re]
    linarith
  rw [Gamma_eq_Gamma_aux s n t1, Gamma_eq_Gamma_aux (s + 1) n t2, Gamma_aux_recurrence1 s n t1]
  field_simp
  ring
#align complex.Gamma_add_one Complex.gamma_add_one

theorem gamma_eq_integral {s : ℂ} (hs : 0 < s.re) : gamma s = gammaIntegral s :=
  gamma_eq_gammaAux s 0
    (by
      norm_cast
      linarith)
#align complex.Gamma_eq_integral Complex.gamma_eq_integral

theorem gamma_one : gamma 1 = 1 := by
  rw [Gamma_eq_integral]
  simpa using Gamma_integral_one
  simp
#align complex.Gamma_one Complex.gamma_one

theorem gamma_nat_eq_factorial (n : ℕ) : gamma (n + 1) = n ! :=
  by
  induction' n with n hn
  · simpa using Gamma_one
  · rw [Gamma_add_one n.succ <| nat.cast_ne_zero.mpr <| Nat.succ_ne_zero n]
    simp only [Nat.cast_succ, Nat.factorial_succ, Nat.cast_mul]
    congr
    exact hn
#align complex.Gamma_nat_eq_factorial Complex.gamma_nat_eq_factorial

end GammaDef

end Complex

/-! Now check that the `Γ` function is differentiable, wherever this makes sense. -/


section GammaHasDeriv

/-- Integrand for the derivative of the `Γ` function -/
def dGammaIntegrand (s : ℂ) (x : ℝ) : ℂ :=
  exp (-x) * log x * x ^ (s - 1)
#align dGamma_integrand dGammaIntegrand

/-- Integrand for the absolute value of the derivative of the `Γ` function -/
def dGammaIntegrandReal (s x : ℝ) : ℝ :=
  |exp (-x) * log x * x ^ (s - 1)|
#align dGamma_integrand_real dGammaIntegrandReal

theorem dGamma_integrand_isO_atTop (s : ℝ) :
    (fun x : ℝ => exp (-x) * log x * x ^ (s - 1)) =o[at_top] fun x => exp (-(1 / 2) * x) :=
  by
  refine' is_o_of_tendsto (fun x hx => _) _
  · exfalso
    exact (-(1 / 2) * x).exp_pos.ne' hx
  have :
    eventually_eq at_top (fun x : ℝ => exp (-x) * log x * x ^ (s - 1) / exp (-(1 / 2) * x))
      (fun x : ℝ => (fun z : ℝ => exp (1 / 2 * z) / z ^ s) x * (fun z : ℝ => z / log z) x)⁻¹ :=
    by
    refine' eventually_of_mem (Ioi_mem_at_top 1) _
    intro x hx
    dsimp
    replace hx := lt_trans zero_lt_one (mem_Ioi.mp hx)
    rw [Real.exp_neg, neg_mul, Real.exp_neg, rpow_sub hx]
    have : exp x = exp (x / 2) * exp (x / 2) := by rw [← Real.exp_add, add_halves]
    rw [this]
    field_simp [hx.ne', exp_ne_zero (x / 2)]
    ring
  refine' tendsto.congr' this.symm (tendsto.inv_tendsto_at_top _)
  apply tendsto.at_top_mul_at_top (tendsto_exp_mul_div_rpow_atTop s (1 / 2) one_half_pos)
  refine' tendsto.congr' _ ((tendsto_exp_div_pow_at_top 1).comp tendsto_log_at_top)
  apply eventually_eq_of_mem (Ioi_mem_at_top (0 : ℝ))
  intro x hx
  simp [exp_log hx]
#align dGamma_integrand_is_o_at_top dGamma_integrand_isO_atTop

/-- Absolute convergence of the integral which will give the derivative of the `Γ` function on
`1 < re s`. -/
theorem dGammaIntegralAbsConvergent (s : ℝ) (hs : 1 < s) :
    IntegrableOn (fun x : ℝ => ‖exp (-x) * log x * x ^ (s - 1)‖) (Ioi 0) :=
  by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrable_on_union]
  refine' ⟨⟨_, _⟩, _⟩
  · refine' ContinuousOn.aeStronglyMeasurable (ContinuousOn.mul _ _).norm measurableSet_ioc
    · refine' (continuous_exp.comp continuous_neg).ContinuousOn.mul (continuous_on_log.mono _)
      simp
    · apply continuous_on_id.rpow_const
      intro x hx
      right
      linarith
  · apply has_finite_integral_of_bounded
    swap
    · exact 1 / (s - 1)
    refine' (ae_restrict_iff' measurableSet_ioc).mpr (ae_of_all _ fun x hx => _)
    rw [norm_norm, norm_eq_abs, mul_assoc, abs_mul, ← one_mul (1 / (s - 1))]
    refine' mul_le_mul _ _ (abs_nonneg _) zero_le_one
    · rw [abs_of_pos (exp_pos (-x)), exp_le_one_iff, neg_le, neg_zero]
      exact hx.1.le
    · exact (abs_log_mul_self_rpow_lt x (s - 1) hx.1 hx.2 (sub_pos.mpr hs)).le
  · have := (dGamma_integrand_isO_atTop s).IsO.norm_left
    refine' integrableOfIsOExpNeg one_half_pos (ContinuousOn.mul _ _).norm this
    · refine' (continuous_exp.comp continuous_neg).ContinuousOn.mul (continuous_on_log.mono _)
      simp
    · apply ContinuousAt.continuousOn fun x hx => _
      apply continuous_at_id.rpow continuousAt_const
      dsimp
      right
      linarith
#align dGamma_integral_abs_convergent dGammaIntegralAbsConvergent

/-- A uniform bound for the `s`-derivative of the `Γ` integrand for `s` in vertical strips. -/
theorem loc_unif_bound_dGammaIntegrand {t : ℂ} {s1 s2 x : ℝ} (ht1 : s1 ≤ t.re) (ht2 : t.re ≤ s2)
    (hx : 0 < x) : ‖dGammaIntegrand t x‖ ≤ dGammaIntegrandReal s1 x + dGammaIntegrandReal s2 x :=
  by
  rcases le_or_lt 1 x with (h | h)
  · -- case 1 ≤ x
    refine' le_add_of_nonneg_of_le (abs_nonneg _) _
    rw [dGammaIntegrand, dGammaIntegrandReal, Complex.norm_eq_abs, map_mul, abs_mul, ←
      Complex.of_real_mul, Complex.abs_of_real]
    refine' mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [Complex.abs_cpow_eq_rpow_re_of_pos hx]
    refine' le_trans _ (le_abs_self _)
    apply rpow_le_rpow_of_exponent_le h
    rw [Complex.sub_re, Complex.one_re]
    linarith
  · refine' le_add_of_le_of_nonneg _ (abs_nonneg _)
    rw [dGammaIntegrand, dGammaIntegrandReal, Complex.norm_eq_abs, map_mul, abs_mul, ←
      Complex.of_real_mul, Complex.abs_of_real]
    refine' mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [Complex.abs_cpow_eq_rpow_re_of_pos hx]
    refine' le_trans _ (le_abs_self _)
    apply rpow_le_rpow_of_exponent_ge hx h.le
    rw [Complex.sub_re, Complex.one_re]
    linarith
#align loc_unif_bound_dGamma_integrand loc_unif_bound_dGammaIntegrand

namespace Complex

/-- The derivative of the `Γ` integral, at any `s ∈ ℂ` with `1 < re s`, is given by the integral
of `exp (-x) * log x * x ^ (s - 1)` over `[0, ∞)`. -/
theorem hasDerivAt_gammaIntegral {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x => Real.exp (-x) * Real.log x * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) volume ∧
      HasDerivAt gammaIntegral (∫ x : ℝ in Ioi 0, Real.exp (-x) * Real.log x * x ^ (s - 1)) s :=
  by
  let ε := (s.re - 1) / 2
  let μ := volume.restrict (Ioi (0 : ℝ))
  let bound := fun x : ℝ => dGammaIntegrandReal (s.re - ε) x + dGammaIntegrandReal (s.re + ε) x
  have cont : ∀ t : ℂ, ContinuousOn (fun x => Real.exp (-x) * x ^ (t - 1) : ℝ → ℂ) (Ioi 0) :=
    by
    intro t
    apply (continuous_of_real.comp continuous_neg.exp).ContinuousOn.mul
    apply ContinuousAt.continuousOn
    intro x hx
    refine' (continuousAt_cpow_const _).comp continuous_of_real.continuous_at
    exact Or.inl hx
  have eps_pos : 0 < ε := div_pos (sub_pos.mpr hs) zero_lt_two
  have hF_meas :
    ∀ᶠ t : ℂ in 𝓝 s, ae_strongly_measurable (fun x => Real.exp (-x) * x ^ (t - 1) : ℝ → ℂ) μ :=
    by
    apply eventually_of_forall
    intro t
    exact (cont t).AeStronglyMeasurable measurableSet_ioi
  have hF'_meas : ae_strongly_measurable (dGammaIntegrand s) μ :=
    by
    refine' ContinuousOn.aeStronglyMeasurable _ measurableSet_ioi
    have : dGammaIntegrand s = (fun x => Real.exp (-x) * x ^ (s - 1) * Real.log x : ℝ → ℂ) :=
      by
      ext1
      simp only [dGammaIntegrand]
      ring
    rw [this]
    refine' ContinuousOn.mul (cont s) (ContinuousAt.continuousOn _)
    exact fun x hx => continuous_of_real.continuous_at.comp (continuous_at_log (mem_Ioi.mp hx).ne')
  have h_bound : ∀ᵐ x : ℝ ∂μ, ∀ t : ℂ, t ∈ Metric.ball s ε → ‖dGammaIntegrand t x‖ ≤ bound x :=
    by
    refine' (ae_restrict_iff' measurableSet_ioi).mpr (ae_of_all _ fun x hx => _)
    intro t ht
    rw [Metric.mem_ball, Complex.dist_eq] at ht
    replace ht := lt_of_le_of_lt (Complex.abs_re_le_abs <| t - s) ht
    rw [Complex.sub_re, @abs_sub_lt_iff ℝ _ t.re s.re ((s.re - 1) / 2)] at ht
    refine' loc_unif_bound_dGammaIntegrand _ _ hx
    all_goals simp only [ε]; linarith
  have bound_integrable : integrable bound μ :=
    by
    apply integrable.add
    · refine' dGammaIntegralAbsConvergent (s.re - ε) _
      field_simp
      rw [one_lt_div]
      · linarith
      · exact zero_lt_two
    · refine' dGammaIntegralAbsConvergent (s.re + ε) _
      linarith
  have h_diff :
    ∀ᵐ x : ℝ ∂μ,
      ∀ t : ℂ,
        t ∈ Metric.ball s ε →
          HasDerivAt (fun u => Real.exp (-x) * x ^ (u - 1) : ℂ → ℂ) (dGammaIntegrand t x) t :=
    by
    refine' (ae_restrict_iff' measurableSet_ioi).mpr (ae_of_all _ fun x hx => _)
    intro t ht
    rw [mem_Ioi] at hx
    simp only [dGammaIntegrand]
    rw [mul_assoc]
    apply HasDerivAt.const_mul
    rw [of_real_log hx.le, mul_comm]
    have := ((hasDerivAt_id t).sub_const 1).const_cpow (Or.inl (of_real_ne_zero.mpr hx.ne'))
    rwa [mul_one] at this
  exact
    hasDerivAt_integral_of_dominated_loc_of_deriv_le eps_pos hF_meas
      (Gamma_integral_convergent (zero_lt_one.trans hs)) hF'_meas h_bound bound_integrable h_diff
#align complex.has_deriv_at_Gamma_integral Complex.hasDerivAt_gammaIntegral

theorem differentiableAt_gammaAux (s : ℂ) (n : ℕ) (h1 : 1 - s.re < n) (h2 : ∀ m : ℕ, s + m ≠ 0) :
    DifferentiableAt ℂ (gammaAux n) s :=
  by
  induction' n with n hn generalizing s
  · refine' (has_deriv_at_Gamma_integral _).2.DifferentiableAt
    rw [Nat.cast_zero] at h1
    linarith
  · dsimp only [Gamma_aux]
    specialize hn (s + 1)
    have a : 1 - (s + 1).re < ↑n := by
      rw [Nat.cast_succ] at h1
      rw [Complex.add_re, Complex.one_re]
      linarith
    have b : ∀ m : ℕ, s + 1 + m ≠ 0 := by
      intro m
      have := h2 (1 + m)
      rwa [Nat.cast_add, Nat.cast_one, ← add_assoc] at this
    refine' DifferentiableAt.div (DifferentiableAt.comp _ (hn a b) _) _ _
    simp
    simp
    simpa using h2 0
#align complex.differentiable_at_Gamma_aux Complex.differentiableAt_gammaAux

theorem differentiableAt_gamma (s : ℂ) (hs : ∀ m : ℕ, s + m ≠ 0) : DifferentiableAt ℂ gamma s :=
  by
  let n := ⌊1 - s.re⌋₊ + 1
  have hn : 1 - s.re < n := by exact_mod_cast Nat.lt_floor_add_one (1 - s.re)
  apply (differentiable_at_Gamma_aux s n hn hs).congr_of_eventually_eq
  let S := { t : ℂ | 1 - t.re < n }
  have : S ∈ 𝓝 s := by
    rw [mem_nhds_iff]
    use S
    refine' ⟨subset.rfl, _, hn⟩
    have : S = re ⁻¹' Ioi (1 - n : ℝ) := by
      ext
      rw [preimage, Ioi, mem_set_of_eq, mem_set_of_eq, mem_set_of_eq]
      exact sub_lt_comm
    rw [this]
    refine' Continuous.isOpen_preimage continuous_re _ isOpen_ioi
  apply eventually_eq_of_mem this
  intro t ht
  rw [mem_set_of_eq] at ht
  apply Gamma_eq_Gamma_aux
  linarith
#align complex.differentiable_at_Gamma Complex.differentiableAt_gamma

end Complex

end GammaHasDeriv

namespace Real

/-- The `Γ` function (of a real variable `s`). -/
@[pp_nodot]
def gamma (s : ℝ) : ℝ :=
  (Complex.gamma s).re
#align real.Gamma Real.gamma

theorem gamma_eq_integral {s : ℝ} (hs : 0 < s) : gamma s = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1) :=
  by
  rw [Gamma, Complex.gamma_eq_integral (by rwa [Complex.of_real_re] : 0 < Complex.re s)]
  dsimp only [Complex.gammaIntegral]
  simp_rw [← Complex.of_real_one, ← Complex.of_real_sub]
  suffices
    (∫ x : ℝ in Ioi 0, ↑(exp (-x)) * (x : ℂ) ^ ((s - 1 : ℝ) : ℂ)) =
      ∫ x : ℝ in Ioi 0, ((exp (-x) * x ^ (s - 1) : ℝ) : ℂ)
    by rw [this, _root_.integral_of_real, Complex.of_real_re]
  refine' set_integral_congr measurableSet_ioi fun x hx => _
  push_cast
  rw [Complex.of_real_cpow (le_of_lt hx)]
  push_cast
#align real.Gamma_eq_integral Real.gamma_eq_integral

theorem gamma_add_one {s : ℝ} (hs : s ≠ 0) : gamma (s + 1) = s * gamma s :=
  by
  simp_rw [Gamma]
  rw [Complex.of_real_add, Complex.of_real_one, Complex.gamma_add_one, Complex.of_real_mul_re]
  rwa [Complex.of_real_ne_zero]
#align real.Gamma_add_one Real.gamma_add_one

theorem gamma_one : gamma 1 = 1 := by
  rw [Gamma, Complex.of_real_one, Complex.gamma_one, Complex.one_re]
#align real.Gamma_one Real.gamma_one

theorem gamma_nat_eq_factorial (n : ℕ) : gamma (n + 1) = n ! := by
  rw [Gamma, Complex.of_real_add, Complex.of_real_nat_cast, Complex.of_real_one,
    Complex.gamma_nat_eq_factorial, ← Complex.of_real_nat_cast, Complex.of_real_re]
#align real.Gamma_nat_eq_factorial Real.gamma_nat_eq_factorial

theorem gamma_pos_of_pos {s : ℝ} (hs : 0 < s) : 0 < gamma s :=
  by
  rw [Gamma_eq_integral hs]
  have : (Function.support fun x : ℝ => exp (-x) * x ^ (s - 1)) ∩ Ioi 0 = Ioi 0 :=
    by
    rw [inter_eq_right_iff_subset]
    intro x hx
    rw [Function.mem_support]
    exact mul_ne_zero (exp_pos _).ne' (rpow_pos_of_pos hx _).ne'
  rw [set_integral_pos_iff_support_of_nonneg_ae]
  · rw [this, volume_Ioi, ← Ennreal.ofReal_zero]
    exact Ennreal.ofReal_lt_top
  · refine' eventually_of_mem (self_mem_ae_restrict measurableSet_ioi) _
    exact fun x hx => (mul_pos (exp_pos _) (rpow_pos_of_pos hx _)).le
  · exact Gamma_integral_convergent hs
#align real.Gamma_pos_of_pos Real.gamma_pos_of_pos

theorem gamma_ne_zero {s : ℝ} (hs : ∀ m : ℕ, s + m ≠ 0) : gamma s ≠ 0 :=
  by
  suffices ∀ {n : ℕ}, -(n : ℝ) < s → Gamma s ≠ 0
    by
    apply this
    swap
    use ⌊-s⌋₊ + 1
    rw [neg_lt, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  intro n
  induction n generalizing s
  · intro hs
    refine' (Gamma_pos_of_pos _).ne'
    rwa [Nat.cast_zero, neg_zero] at hs
  · intro hs'
    have : Gamma (s + 1) ≠ 0 := by
      apply n_ih
      · intro m
        convert hs (1 + m) using 1
        push_cast
        ring
      · rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, neg_add] at hs'
        linarith
    rw [Gamma_add_one, mul_ne_zero_iff] at this
    · exact this.2
    · simpa using hs 0
#align real.Gamma_ne_zero Real.gamma_ne_zero

theorem differentiableAt_gamma {s : ℝ} (hs : ∀ m : ℕ, s + m ≠ 0) : DifferentiableAt ℝ gamma s :=
  by
  apply HasDerivAt.differentiableAt
  apply HasDerivAt.real_of_complex
  apply DifferentiableAt.hasDerivAt
  apply Complex.differentiableAt_gamma
  simp_rw [← Complex.of_real_nat_cast, ← Complex.of_real_add, Complex.of_real_ne_zero]
  exact hs
#align real.differentiable_at_Gamma Real.differentiableAt_gamma

/-- Log-convexity of the Gamma function on the positive reals (stated in multiplicative form),
proved using the Hölder inequality applied to Euler's integral. -/
theorem gamma_mul_add_mul_le_rpow_gamma_mul_rpow_gamma {s t a b : ℝ} (hs : 0 < s) (ht : 0 < t)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    gamma (a * s + b * t) ≤ gamma s ^ a * gamma t ^ b :=
  by
  -- We will apply Hölder's inequality, for the conjugate exponents `p = 1 / a`
  -- and `q = 1 / b`, to the functions `f a s` and `f b t`, where `f` is as follows:
  let f : ℝ → ℝ → ℝ → ℝ := fun c u x => exp (-c * x) * x ^ (c * (u - 1))
  have e : is_conjugate_exponent (1 / a) (1 / b) := Real.isConjugateExponent_one_div ha hb hab
  have hab' : b = 1 - a := by linarith
  have hst : 0 < a * s + b * t := add_pos (mul_pos ha hs) (mul_pos hb ht)
  -- some properties of f:
  have posf : ∀ c u x : ℝ, x ∈ Ioi (0 : ℝ) → 0 ≤ f c u x := fun c u x hx =>
    mul_nonneg (exp_pos _).le (rpow_pos_of_pos hx _).le
  have posf' : ∀ c u : ℝ, ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0), 0 ≤ f c u x := fun c u =>
    (ae_restrict_iff' measurableSet_ioi).mpr (ae_of_all _ (posf c u))
  have fpow :
    ∀ {c x : ℝ} (hc : 0 < c) (u : ℝ) (hx : 0 < x), exp (-x) * x ^ (u - 1) = f c u x ^ (1 / c) :=
    by
    intro c x hc u hx
    dsimp only [f]
    rw [mul_rpow (exp_pos _).le ((rpow_nonneg_of_nonneg hx.le) _), ← exp_mul, ← rpow_mul hx.le]
    congr 2 <;>
      · field_simp [hc.ne']
        ring
  -- show `f c u` is in `ℒp` for `p = 1/c`:
  have f_mem_Lp :
    ∀ {c u : ℝ} (hc : 0 < c) (hu : 0 < u),
      mem_ℒp (f c u) (Ennreal.ofReal (1 / c)) (volume.restrict (Ioi 0)) :=
    by
    intro c u hc hu
    have A : Ennreal.ofReal (1 / c) ≠ 0 := by
      rwa [Ne.def, Ennreal.ofReal_eq_zero, not_le, one_div_pos]
    have B : Ennreal.ofReal (1 / c) ≠ ∞ := Ennreal.ofReal_ne_top
    rw [← mem_ℒp_norm_rpow_iff _ A B, Ennreal.toReal_ofReal (one_div_nonneg.mpr hc.le),
      Ennreal.div_self A B, mem_ℒp_one_iff_integrable]
    · apply integrable.congr (Gamma_integral_convergent hu)
      refine' eventually_eq_of_mem (self_mem_ae_restrict measurableSet_ioi) fun x hx => _
      dsimp only
      rw [fpow hc u hx]
      congr 1
      exact (norm_of_nonneg (posf _ _ x hx)).symm
    · refine' ContinuousOn.aeStronglyMeasurable _ measurableSet_ioi
      refine' (Continuous.continuousOn _).mul (ContinuousAt.continuousOn fun x hx => _)
      · exact continuous_exp.comp (continuous_const.mul continuous_id')
      · exact continuous_at_rpow_const _ _ (Or.inl (ne_of_lt hx).symm)
  -- now apply Hölder:
  rw [Gamma_eq_integral hs, Gamma_eq_integral ht, Gamma_eq_integral hst]
  convert
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg e (posf' a s) (posf' b t) (f_mem_Lp ha hs)
      (f_mem_Lp hb ht) using
    1
  · refine' set_integral_congr measurableSet_ioi fun x hx => _
    dsimp only [f]
    have A : exp (-x) = exp (-a * x) * exp (-b * x) := by
      rw [← exp_add, ← add_mul, ← neg_add, hab, neg_one_mul]
    have B : x ^ (a * s + b * t - 1) = x ^ (a * (s - 1)) * x ^ (b * (t - 1)) :=
      by
      rw [← rpow_add hx, hab']
      congr 1
      ring
    rw [A, B]
    ring
  · rw [one_div_one_div, one_div_one_div]
    congr 2 <;> exact set_integral_congr measurableSet_ioi fun x hx => fpow (by assumption) _ hx
#align real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma Real.gamma_mul_add_mul_le_rpow_gamma_mul_rpow_gamma

theorem convexOn_log_gamma : ConvexOn ℝ (Ioi 0) (log ∘ Gamma) :=
  by
  refine' convex_on_iff_forall_pos.mpr ⟨convex_ioi _, fun x hx y hy a b ha hb hab => _⟩
  have : b = 1 - a := by linarith; subst this
  simp_rw [Function.comp_apply, smul_eq_mul]
  rw [← log_rpow (Gamma_pos_of_pos hy), ← log_rpow (Gamma_pos_of_pos hx), ←
    log_mul (rpow_pos_of_pos (Gamma_pos_of_pos hx) _).ne'
      (rpow_pos_of_pos (Gamma_pos_of_pos hy) _).ne',
    log_le_log (Gamma_pos_of_pos (add_pos (mul_pos ha hx) (mul_pos hb hy)))
      (mul_pos (rpow_pos_of_pos (Gamma_pos_of_pos hx) _) (rpow_pos_of_pos (Gamma_pos_of_pos hy) _))]
  exact Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx hy ha hb hab
#align real.convex_on_log_Gamma Real.convexOn_log_gamma

section BohrMollerup

/-! ## The Euler limit formula and the Bohr-Mollerup theorem

In this section we prove two interrelated statements about the `Γ` function on the positive reals:

* the Euler limit formula `real.tendsto_log_gamma_seq`, stating that the sequence
  `x * log n + log n! - ∑ (m : ℕ) in finset.range (n + 1), log (x + m)`
  tends to `log Γ(x)` as `n → ∞`.
* the Bohr-Mollerup theorem (`real.eq_Gamma_of_log_convex`) which states that `Γ` is the unique
  *log-convex*, positive-real-valued function on the positive reals satisfying
  `f (x + 1) = x f x` and `f 1 = 1`.

To do this, we prove that any function satisfying the hypotheses of the Bohr--Mollerup theorem must
agree with the limit in the Gauss formula, so there is at most one such function. Then we show that
`Γ` satisfies these conditions.
-/


/-- The function `n ↦ x log n + log n! - (log x + ... + log (x + n))`, which we will show tends to
`log (Gamma x)` as `n → ∞`. -/
def logGammaSeq (x : ℝ) (n : ℕ) : ℝ :=
  x * log n + log n ! - ∑ m : ℕ in Finset.range (n + 1), log (x + m)
#align real.log_gamma_seq Real.logGammaSeq

/-! The following are auxiliary lemmas for the Bohr-Mollerup theorem, which are
placed in a separate namespace `bohr_mollerup` to avoid clutter. -/


namespace BohrMollerup

variable {f : ℝ → ℝ} {x : ℝ} {n : ℕ}

theorem f_nat_eq (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hn : n ≠ 0) :
    f n = f 1 + log (n - 1)! :=
  by
  refine' Nat.le_induction (by simp) (fun m hm IH => _) n (Nat.one_le_iff_ne_zero.2 hn)
  have A : 0 < (m : ℝ) := Nat.cast_pos.2 hm
  simp only [hf_feq A, Nat.cast_add, algebraMap.coe_one, Nat.add_succ_sub_one, add_zero]
  rw [IH, add_assoc, ← log_mul (nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) A.ne', ←
    Nat.cast_mul]
  conv_rhs => rw [← Nat.succ_pred_eq_of_pos hm, Nat.factorial_succ, mul_comm]
  congr
  exact (Nat.succ_pred_eq_of_pos hm).symm
#align real.bohr_mollerup.f_nat_eq Real.BohrMollerup.f_nat_eq

theorem f_add_nat_eq (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hx : 0 < x) (n : ℕ) :
    f (x + n) = f x + ∑ m : ℕ in Finset.range n, log (x + m) :=
  by
  induction' n with n hn
  · simp
  · have : x + n.succ = x + n + 1 := by
      push_cast
      ring
    rw [this, hf_feq, hn]
    rw [Finset.range_succ, Finset.sum_insert Finset.not_mem_range_self]
    abel
    linarith [(Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
#align real.bohr_mollerup.f_add_nat_eq Real.BohrMollerup.f_add_nat_eq

/-- Linear upper bound for `f (x + n)` on unit interval -/
theorem f_add_nat_le (hf_conv : ConvexOn ℝ (Ioi 0) f)
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hn : n ≠ 0) (hx : 0 < x) (hx' : x ≤ 1) :
    f (n + x) ≤ f n + x * log n :=
  by
  have hn' : 0 < (n : ℝ) := nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have : f n + x * log n = (1 - x) * f n + x * f (n + 1) :=
    by
    rw [hf_feq hn']
    ring
  rw [this, (by ring : (n : ℝ) + x = (1 - x) * n + x * (n + 1))]
  simpa only [smul_eq_mul] using
    hf_conv.2 hn' (by linarith : 0 < (n + 1 : ℝ)) (by linarith : 0 ≤ 1 - x) hx.le (by linarith)
#align real.bohr_mollerup.f_add_nat_le Real.BohrMollerup.f_add_nat_le

/-- Linear lower bound for `f (x + n)` on unit interval -/
theorem f_add_nat_ge (hf_conv : ConvexOn ℝ (Ioi 0) f)
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hn : 2 ≤ n) (hx : 0 < x) :
    f n + x * log (n - 1) ≤ f (n + x) :=
  by
  have npos : 0 < (n : ℝ) - 1 :=
    by
    rw [← Nat.cast_one, sub_pos, Nat.cast_lt]
    linarith
  have c :=
    (convex_on_iff_slope_mono_adjacent.mp <| hf_conv).2 npos (by linarith : 0 < (n : ℝ) + x)
      (by linarith : (n : ℝ) - 1 < (n : ℝ)) (by linarith)
  rw [add_sub_cancel', sub_sub_cancel, div_one] at c
  have : f (↑n - 1) = f n - log (↑n - 1) :=
    by
    nth_rw_rhs 1 [(by ring : (n : ℝ) = ↑n - 1 + 1)]
    rw [hf_feq npos, add_sub_cancel]
  rwa [this, le_div_iff hx, sub_sub_cancel, le_sub_iff_add_le, mul_comm _ x, add_comm] at c
#align real.bohr_mollerup.f_add_nat_ge Real.BohrMollerup.f_add_nat_ge

theorem logGammaSeq_add_one (x : ℝ) (n : ℕ) :
    logGammaSeq (x + 1) n = logGammaSeq x (n + 1) + log x - (x + 1) * (log (n + 1) - log n) :=
  by
  dsimp only [Nat.factorial_succ, log_gamma_seq]
  conv_rhs => rw [Finset.sum_range_succ', Nat.cast_zero, add_zero]
  rw [Nat.cast_mul, log_mul]
  rotate_left
  · rw [Nat.cast_ne_zero]
    exact Nat.succ_ne_zero n
  · rw [Nat.cast_ne_zero]
    exact Nat.factorial_ne_zero n
  have :
    (∑ m : ℕ in Finset.range (n + 1), log (x + 1 + ↑m)) =
      ∑ k : ℕ in Finset.range (n + 1), log (x + ↑(k + 1)) :=
    by
    refine' Finset.sum_congr (by rfl) fun m hm => _
    congr 1
    push_cast
    abel
  rw [← this, Nat.cast_add_one n]
  ring
#align real.bohr_mollerup.log_gamma_seq_add_one Real.BohrMollerup.logGammaSeq_add_one

theorem le_logGammaSeq (hf_conv : ConvexOn ℝ (Ioi 0) f)
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hx : 0 < x) (hx' : x ≤ 1) (n : ℕ) :
    f x ≤ f 1 + x * log (n + 1) - x * log n + logGammaSeq x n :=
  by
  rw [log_gamma_seq, ← add_sub_assoc, le_sub_iff_add_le, ← f_add_nat_eq (@hf_feq) hx, add_comm x]
  refine' (f_add_nat_le hf_conv (@hf_feq) (Nat.add_one_ne_zero n) hx hx').trans (le_of_eq _)
  rw [f_nat_eq @hf_feq (by linarith : n + 1 ≠ 0), Nat.add_sub_cancel, Nat.cast_add_one]
  ring
#align real.bohr_mollerup.le_log_gamma_seq Real.BohrMollerup.le_logGammaSeq

theorem ge_logGammaSeq (hf_conv : ConvexOn ℝ (Ioi 0) f)
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hx : 0 < x) (hn : n ≠ 0) :
    f 1 + logGammaSeq x n ≤ f x := by
  dsimp [log_gamma_seq]
  rw [← add_sub_assoc, sub_le_iff_le_add, ← f_add_nat_eq (@hf_feq) hx, add_comm x _]
  refine' le_trans (le_of_eq _) (f_add_nat_ge hf_conv @hf_feq _ hx)
  · rw [f_nat_eq @hf_feq, Nat.add_sub_cancel, Nat.cast_add_one, add_sub_cancel]
    · ring
    · exact Nat.succ_ne_zero _
  · apply Nat.succ_le_succ
    linarith [Nat.pos_of_ne_zero hn]
#align real.bohr_mollerup.ge_log_gamma_seq Real.BohrMollerup.ge_logGammaSeq

theorem tendsto_logGammaSeq_of_le_one (hf_conv : ConvexOn ℝ (Ioi 0) f)
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hx : 0 < x) (hx' : x ≤ 1) :
    Tendsto (logGammaSeq x) atTop (𝓝 <| f x - f 1) :=
  by
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' _ tendsto_const_nhds _ _
  show ∀ᶠ n : ℕ in at_top, log_gamma_seq x n ≤ f x - f 1
  · refine' eventually.mp (eventually_ne_at_top 0) (eventually_of_forall fun n hn => _)
    exact le_sub_iff_add_le'.mpr (ge_log_gamma_seq hf_conv (@hf_feq) hx hn)
  show ∀ᶠ n : ℕ in at_top, f x - f 1 - x * (log (n + 1) - log n) ≤ log_gamma_seq x n
  · refine' eventually_of_forall fun n => _
    rw [sub_le_iff_le_add', sub_le_iff_le_add']
    convert le_log_gamma_seq hf_conv (@hf_feq) hx hx' n using 1
    ring
  · have : f x - f 1 = f x - f 1 - x * 0 := by ring
    nth_rw 1 [this]
    exact tendsto.sub tendsto_const_nhds (tendsto_log_nat_add_one_sub_log.const_mul _)
#align real.bohr_mollerup.tendsto_log_gamma_seq_of_le_one Real.BohrMollerup.tendsto_logGammaSeq_of_le_one

theorem tendsto_logGammaSeq (hf_conv : ConvexOn ℝ (Ioi 0) f)
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y) (hx : 0 < x) :
    Tendsto (logGammaSeq x) atTop (𝓝 <| f x - f 1) :=
  by
  suffices ∀ m : ℕ, ↑m < x → x ≤ m + 1 → tendsto (log_gamma_seq x) at_top (𝓝 <| f x - f 1)
    by
    refine' this ⌈x - 1⌉₊ _ _
    · rcases lt_or_le x 1 with ⟨⟩
      · rwa [nat.ceil_eq_zero.mpr (by linarith : x - 1 ≤ 0), Nat.cast_zero]
      · convert Nat.ceil_lt_add_one (by linarith : 0 ≤ x - 1)
        abel
    · rw [← sub_le_iff_le_add]
      exact Nat.le_ceil _
  intro m
  induction' m with m hm generalizing x
  · rw [Nat.cast_zero, zero_add]
    exact fun _ hx' => tendsto_log_gamma_seq_of_le_one hf_conv (@hf_feq) hx hx'
  · intro hy hy'
    rw [Nat.cast_succ, ← sub_le_iff_le_add] at hy'
    rw [Nat.cast_succ, ← lt_sub_iff_add_lt] at hy
    specialize hm ((Nat.cast_nonneg _).trans_lt hy) hy hy'
    -- now massage gauss_product n (x - 1) into gauss_product (n - 1) x
    have :
      ∀ᶠ n : ℕ in at_top,
        log_gamma_seq (x - 1) n =
          log_gamma_seq x (n - 1) + x * (log (↑(n - 1) + 1) - log ↑(n - 1)) - log (x - 1) :=
      by
      refine' eventually.mp (eventually_ge_at_top 1) (eventually_of_forall fun n hn => _)
      have := log_gamma_seq_add_one (x - 1) (n - 1)
      rw [sub_add_cancel, Nat.sub_add_cancel hn] at this
      rw [this]
      ring
    replace hm :=
      ((tendsto.congr' this hm).add (tendsto_const_nhds : tendsto (fun _ => log (x - 1)) _ _)).comp
        (tendsto_add_at_top_nat 1)
    have :
      ((fun x_1 : ℕ =>
            (fun n : ℕ =>
                  log_gamma_seq x (n - 1) + x * (log (↑(n - 1) + 1) - log ↑(n - 1)) - log (x - 1))
                x_1 +
              (fun b : ℕ => log (x - 1)) x_1) ∘
          fun a : ℕ => a + 1) =
        fun n => log_gamma_seq x n + x * (log (↑n + 1) - log ↑n) :=
      by
      ext1 n
      dsimp only [Function.comp_apply]
      rw [sub_add_cancel, Nat.add_sub_cancel]
    rw [this] at hm
    convert hm.sub (tendsto_log_nat_add_one_sub_log.const_mul x) using 2
    · ext1 n
      ring
    · have := hf_feq ((Nat.cast_nonneg m).trans_lt hy)
      rw [sub_add_cancel] at this
      rw [this]
      ring
#align real.bohr_mollerup.tendsto_log_gamma_seq Real.BohrMollerup.tendsto_logGammaSeq

end BohrMollerup

theorem tendsto_log_gamma {x : ℝ} (hx : 0 < x) :
    Tendsto (logGammaSeq x) atTop (𝓝 <| log (gamma x)) :=
  by
  have : log (Gamma x) = (log ∘ Gamma) x - (log ∘ Gamma) 1 := by
    simp_rw [Function.comp_apply, Gamma_one, log_one, sub_zero]
  rw [this]
  refine' bohr_mollerup.tendsto_log_gamma_seq convex_on_log_Gamma (fun y hy => _) hx
  rw [Function.comp_apply, Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne', add_comm]
#align real.tendsto_log_Gamma Real.tendsto_log_gamma

/-- The **Bohr-Mollerup theorem**: the Gamma function is the *unique* log-convex, positive-valued
function on the positive reals which satisfies `f 1 = 1` and `f (x + 1) = x * f x` for all `x`. -/
theorem eq_gamma_of_log_convex {f : ℝ → ℝ} (hf_conv : ConvexOn ℝ (Ioi 0) (log ∘ f))
    (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = y * f y) (hf_pos : ∀ {y : ℝ}, 0 < y → 0 < f y)
    (hf_one : f 1 = 1) : EqOn f gamma (Ioi (0 : ℝ)) :=
  by
  suffices : eq_on (log ∘ f) (log ∘ Gamma) (Ioi (0 : ℝ))
  exact fun x hx => log_inj_on_pos (hf_pos hx) (Gamma_pos_of_pos hx) (this hx)
  intro x hx
  have e1 := bohr_mollerup.tendsto_log_gamma_seq hf_conv _ hx
  · rw [Function.comp_apply log f 1, hf_one, log_one, sub_zero] at e1
    exact tendsto_nhds_unique e1 (tendsto_log_Gamma hx)
  · intro y hy
    rw [Function.comp_apply, hf_feq hy, log_mul hy.ne' (hf_pos hy).ne']
    ring
#align real.eq_Gamma_of_log_convex Real.eq_gamma_of_log_convex

end BohrMollerup

end Real

