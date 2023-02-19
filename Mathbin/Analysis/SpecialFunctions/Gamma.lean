/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module analysis.special_functions.gamma
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Integral.ExpDecay
import Mathbin.Analysis.Calculus.ParametricIntegral
import Mathbin.Analysis.SpecialFunctions.Integrals
import Mathbin.Analysis.Convolution
import Mathbin.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

/-!
# The Gamma and Beta functions

This file defines the `Γ` function (of a real or complex variable `s`). We define this by Euler's
integral `Γ(s) = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` in the range where this integral converges
(i.e., for `0 < s` in the real case, and `0 < re s` in the complex case).

We show that this integral satisfies `Γ(1) = 1` and `Γ(s + 1) = s * Γ(s)`; hence we can define
`Γ(s)` for all `s` as the unique function satisfying this recurrence and agreeing with Euler's
integral in the convergence range. (If `s = -n` for `n ∈ ℕ`, then the function is undefined, and we
set it to be `0` by convention.)

## Gamma function: main statements (complex case)

* `complex.Gamma`: the `Γ` function (of a complex variable).
* `complex.Gamma_eq_integral`: for `0 < re s`, `Γ(s)` agrees with Euler's integral.
* `complex.Gamma_add_one`: for all `s : ℂ` with `s ≠ 0`, we have `Γ (s + 1) = s Γ(s)`.
* `complex.Gamma_nat_eq_factorial`: for all `n : ℕ` we have `Γ (n + 1) = n!`.
* `complex.differentiable_at_Gamma`: `Γ` is complex-differentiable at all `s : ℂ` with
  `s ∉ {-n : n ∈ ℕ}`.
* `complex.Gamma_ne_zero`: for all `s : ℂ` with `s ∉ {-n : n ∈ ℕ}` we have `Γ s ≠ 0`.
* `complex.Gamma_seq_tendsto_Gamma`: for all `s`, the limit as `n → ∞` of the sequence
  `n ↦ n ^ s * n! / (s * (s + 1) * ... * (s + n))` is `Γ(s)`.
* `complex.Gamma_mul_Gamma_one_sub`: Euler's reflection formula
  `Gamma s * Gamma (1 - s) = π / sin π s`.

## Gamma function: main statements (real case)

* `real.Gamma`: the `Γ` function (of a real variable).
* Real counterparts of all the properties of the complex Gamma function listed above:
  `real.Gamma_eq_integral`, `real.Gamma_add_one`, `real.Gamma_nat_eq_factorial`,
  `real.differentiable_at_Gamma`, `real.Gamma_ne_zero`, `real.Gamma_seq_tendsto_Gamma`,
  `real.Gamma_mul_Gamma_one_sub`.
* `real.convex_on_log_Gamma` : `log ∘ Γ` is convex on `Ioi 0`.
* `real.eq_Gamma_of_log_convex` : the Bohr-Mollerup theorem, which states that the `Γ` function is
  the unique log-convex, positive-valued function on `Ioi 0` satisfying the functional equation
  and having `Γ 1 = 1`.

## Beta function

* `complex.beta_integral`: the Beta function `Β(u, v)`, where `u`, `v` are complex with positive
  real part.
* `complex.Gamma_mul_Gamma_eq_beta_integral`: the formula
  `Gamma u * Gamma v = Gamma (u + v) * beta_integral u v`.

## Tags

Gamma
-/


noncomputable section

open Filter intervalIntegral Set Real MeasureTheory Asymptotics

open Nat Topology Ennreal BigOperators ComplexConjugate

theorem integral_exp_neg_Ioi : (∫ x : ℝ in Ioi 0, exp (-x)) = 1 :=
  by
  refine' tendsto_nhds_unique (interval_integral_tendsto_integral_Ioi _ _ tendsto_id) _
  · simpa only [neg_mul, one_mul] using expNegIntegrableOnIoi 0 zero_lt_one
  · simpa using tendsto_exp_neg_at_top_nhds_0.const_sub 1
#align integral_exp_neg_Ioi integral_exp_neg_Ioi

namespace Real

/-- Asymptotic bound for the `Γ` function integrand. -/
theorem Gamma_integrand_isOCat (s : ℝ) :
    (fun x : ℝ => exp (-x) * x ^ s) =o[atTop] fun x : ℝ => exp (-(1 / 2) * x) :=
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
  exact (tendsto_exp_mul_div_rpow_atTop s (1 / 2) one_half_pos).inv_tendsto_atTop
#align real.Gamma_integrand_is_o Real.Gamma_integrand_isOCat

/-- The Euler integral for the `Γ` function converges for positive real `s`. -/
theorem gammaIntegralConvergent {s : ℝ} (h : 0 < s) :
    IntegrableOn (fun x : ℝ => exp (-x) * x ^ (s - 1)) (Ioi 0) :=
  by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrable_on_union]
  constructor
  · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    refine' integrable_on.continuous_on_mul continuous_on_id.neg.exp _ is_compact_Icc
    refine' (intervalIntegrable_iff_integrable_Icc_of_le zero_le_one).mp _
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
  · refine' ContinuousOn.aeStronglyMeasurable _ measurableSet_Ioi
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
    refine' (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => _)
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

theorem gammaIntegral_conj (s : ℂ) : gammaIntegral (conj s) = conj (gammaIntegral s) :=
  by
  rw [Gamma_integral, Gamma_integral, ← integral_conj]
  refine' set_integral_congr measurableSet_Ioi fun x hx => _
  dsimp only
  rw [RingHom.map_mul, conj_of_real, cpow_def_of_ne_zero (of_real_ne_zero.mpr (ne_of_gt hx)),
    cpow_def_of_ne_zero (of_real_ne_zero.mpr (ne_of_gt hx)), ← exp_conj, RingHom.map_mul, ←
    of_real_log (le_of_lt hx), conj_of_real, RingHom.map_sub, RingHom.map_one]
#align complex.Gamma_integral_conj Complex.gammaIntegral_conj

theorem gammaIntegral_of_real (s : ℝ) :
    gammaIntegral ↑s = ↑(∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ (s - 1)) :=
  by
  rw [Gamma_integral, ← _root_.integral_of_real]
  refine' set_integral_congr measurableSet_Ioi _
  intro x hx; dsimp only
  rw [of_real_mul, of_real_cpow (mem_Ioi.mp hx).le]
  simp
#align complex.Gamma_integral_of_real Complex.gammaIntegral_of_real

theorem gammaIntegral_one : gammaIntegral 1 = 1 := by
  simpa only [← of_real_one, Gamma_integral_of_real, of_real_inj, sub_self, rpow_zero,
    mul_one] using integral_exp_neg_Ioi
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
  intervalIntegral_tendsto_integral_Ioi 0 (gammaIntegralConvergent hs) tendsto_id
#align complex.tendsto_partial_Gamma Complex.tendsto_partialGamma

private theorem Gamma_integrand_interval_integrable (s : ℂ) {X : ℝ} (hs : 0 < s.re) (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) volume 0 X :=
  by
  rw [intervalIntegrable_iff_integrable_Ioc_of_le hX]
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
  rw [this, intervalIntegrable_iff_integrable_Ioc_of_le hY]
  constructor
  · refine' (continuous_on_const.mul _).AeStronglyMeasurable measurableSet_Ioc
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
  · exact measurableSet_Ioc
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

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
theorem gamma_zero : gamma 0 = 0 := by
  simp_rw [Gamma, zero_re, sub_zero, Nat.floor_one, Gamma_aux, div_zero]
#align complex.Gamma_zero Complex.gamma_zero

/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value 0. -/
theorem gamma_neg_nat_eq_zero (n : ℕ) : gamma (-n) = 0 :=
  by
  induction' n with n IH
  · rw [Nat.cast_zero, neg_zero, Gamma_zero]
  · have A : -(n.succ : ℂ) ≠ 0 := by
      rw [neg_ne_zero, Nat.cast_ne_zero]
      apply Nat.succ_ne_zero
    have : -(n : ℂ) = -↑n.succ + 1 := by simp
    rw [this, Gamma_add_one _ A] at IH
    contrapose! IH
    exact mul_ne_zero A IH
#align complex.Gamma_neg_nat_eq_zero Complex.gamma_neg_nat_eq_zero

theorem gamma_conj (s : ℂ) : gamma (conj s) = conj (gamma s) :=
  by
  suffices : ∀ (n : ℕ) (s : ℂ), Gamma_aux n (conj s) = conj (Gamma_aux n s); exact this _ _
  intro n
  induction' n with n IH
  · rw [Gamma_aux]
    exact Gamma_integral_conj
  · intro s
    rw [Gamma_aux]
    dsimp only
    rw [div_eq_mul_inv _ s, RingHom.map_mul, conj_inv, ← div_eq_mul_inv]
    suffices conj s + 1 = conj (s + 1) by rw [this, IH]
    rw [RingHom.map_add, RingHom.map_one]
#align complex.Gamma_conj Complex.gamma_conj

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

theorem dGamma_integrand_isOCat_atTop (s : ℝ) :
    (fun x : ℝ => exp (-x) * log x * x ^ (s - 1)) =o[atTop] fun x => exp (-(1 / 2) * x) :=
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
#align dGamma_integrand_is_o_at_top dGamma_integrand_isOCat_atTop

/-- Absolute convergence of the integral which will give the derivative of the `Γ` function on
`1 < re s`. -/
theorem dGammaIntegralAbsConvergent (s : ℝ) (hs : 1 < s) :
    IntegrableOn (fun x : ℝ => ‖exp (-x) * log x * x ^ (s - 1)‖) (Ioi 0) :=
  by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrable_on_union]
  refine' ⟨⟨_, _⟩, _⟩
  · refine' ContinuousOn.aeStronglyMeasurable (ContinuousOn.mul _ _).norm measurableSet_Ioc
    · refine' (continuous_exp.comp continuous_neg).ContinuousOn.mul (continuous_on_log.mono _)
      simp
    · apply continuous_on_id.rpow_const
      intro x hx
      right
      linarith
  · apply has_finite_integral_of_bounded
    swap
    · exact 1 / (s - 1)
    refine' (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => _)
    rw [norm_norm, norm_eq_abs, mul_assoc, abs_mul, ← one_mul (1 / (s - 1))]
    refine' mul_le_mul _ _ (abs_nonneg _) zero_le_one
    · rw [abs_of_pos (exp_pos (-x)), exp_le_one_iff, neg_le, neg_zero]
      exact hx.1.le
    · exact (abs_log_mul_self_rpow_lt x (s - 1) hx.1 hx.2 (sub_pos.mpr hs)).le
  · have := (dGamma_integrand_isOCat_atTop s).IsO.norm_left
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
    exact (cont t).AeStronglyMeasurable measurableSet_Ioi
  have hF'_meas : ae_strongly_measurable (dGammaIntegrand s) μ :=
    by
    refine' ContinuousOn.aeStronglyMeasurable _ measurableSet_Ioi
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
    refine' (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => _)
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
    refine' (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => _)
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

theorem differentiableAt_gammaAux (s : ℂ) (n : ℕ) (h1 : 1 - s.re < n) (h2 : ∀ m : ℕ, s ≠ -m) :
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
    have b : ∀ m : ℕ, s + 1 ≠ -m := by
      intro m
      have := h2 (1 + m)
      contrapose! this
      rw [← eq_sub_iff_add_eq] at this
      simpa using this
    refine' DifferentiableAt.div (DifferentiableAt.comp _ (hn a b) _) _ _
    simp
    simp
    simpa using h2 0
#align complex.differentiable_at_Gamma_aux Complex.differentiableAt_gammaAux

theorem differentiableAt_gamma (s : ℂ) (hs : ∀ m : ℕ, s ≠ -m) : DifferentiableAt ℂ gamma s :=
  by
  let n := ⌊1 - s.re⌋₊ + 1
  have hn : 1 - s.re < n := by exact_mod_cast Nat.lt_floor_add_one (1 - s.re)
  apply (differentiable_at_Gamma_aux s n hn hs).congr_of_eventuallyEq
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
    refine' Continuous.isOpen_preimage continuous_re _ isOpen_Ioi
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
  refine' set_integral_congr measurableSet_Ioi fun x hx => _
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

theorem Complex.gamma_of_real (s : ℝ) : Complex.gamma (s : ℂ) = gamma s := by
  rw [Gamma, eq_comm, ← Complex.eq_conj_iff_re, ← Complex.gamma_conj, Complex.conj_of_real]
#align complex.Gamma_of_real Complex.gamma_of_real

theorem gamma_nat_eq_factorial (n : ℕ) : gamma (n + 1) = n ! := by
  rw [Gamma, Complex.of_real_add, Complex.of_real_nat_cast, Complex.of_real_one,
    Complex.gamma_nat_eq_factorial, ← Complex.of_real_nat_cast, Complex.of_real_re]
#align real.Gamma_nat_eq_factorial Real.gamma_nat_eq_factorial

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
theorem gamma_zero : gamma 0 = 0 := by
  simpa only [← Complex.of_real_zero, Complex.gamma_of_real, Complex.of_real_inj] using
    Complex.gamma_zero
#align real.Gamma_zero Real.gamma_zero

/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value `0`.
-/
theorem gamma_neg_nat_eq_zero (n : ℕ) : gamma (-n) = 0 := by
  simpa only [← Complex.of_real_nat_cast, ← Complex.of_real_neg, Complex.gamma_of_real,
    Complex.of_real_eq_zero] using Complex.gamma_neg_nat_eq_zero n
#align real.Gamma_neg_nat_eq_zero Real.gamma_neg_nat_eq_zero

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
  · refine' eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) _
    exact fun x hx => (mul_pos (exp_pos _) (rpow_pos_of_pos hx _)).le
  · exact Gamma_integral_convergent hs
#align real.Gamma_pos_of_pos Real.gamma_pos_of_pos

/-- The Gamma function does not vanish on `ℝ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
theorem gamma_ne_zero {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : gamma s ≠ 0 :=
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
        specialize hs (1 + m)
        contrapose! hs
        rw [← eq_sub_iff_add_eq] at hs
        rw [hs]
        push_cast
        ring
      · rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, neg_add] at hs'
        linarith
    rw [Gamma_add_one, mul_ne_zero_iff] at this
    · exact this.2
    · simpa using hs 0
#align real.Gamma_ne_zero Real.gamma_ne_zero

theorem gamma_eq_zero_iff (s : ℝ) : gamma s = 0 ↔ ∃ m : ℕ, s = -m :=
  ⟨by
    contrapose!
    exact Gamma_ne_zero, by
    rintro ⟨m, rfl⟩
    exact Gamma_neg_nat_eq_zero m⟩
#align real.Gamma_eq_zero_iff Real.gamma_eq_zero_iff

theorem differentiableAt_gamma {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : DifferentiableAt ℝ gamma s :=
  by
  refine' (Complex.differentiableAt_gamma _ _).HasDerivAt.real_of_complex.DifferentiableAt
  simp_rw [← Complex.of_real_nat_cast, ← Complex.of_real_neg, Ne.def, Complex.of_real_inj]
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
    (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (posf c u))
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
      refine' eventually_eq_of_mem (self_mem_ae_restrict measurableSet_Ioi) fun x hx => _
      dsimp only
      rw [fpow hc u hx]
      congr 1
      exact (norm_of_nonneg (posf _ _ x hx)).symm
    · refine' ContinuousOn.aeStronglyMeasurable _ measurableSet_Ioi
      refine' (Continuous.continuousOn _).mul (ContinuousAt.continuousOn fun x hx => _)
      · exact continuous_exp.comp (continuous_const.mul continuous_id')
      · exact continuous_at_rpow_const _ _ (Or.inl (ne_of_lt hx).symm)
  -- now apply Hölder:
  rw [Gamma_eq_integral hs, Gamma_eq_integral ht, Gamma_eq_integral hst]
  convert
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg e (posf' a s) (posf' b t) (f_mem_Lp ha hs)
      (f_mem_Lp hb ht) using
    1
  · refine' set_integral_congr measurableSet_Ioi fun x hx => _
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
    congr 2 <;> exact set_integral_congr measurableSet_Ioi fun x hx => fpow (by assumption) _ hx
#align real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma Real.gamma_mul_add_mul_le_rpow_gamma_mul_rpow_gamma

theorem convexOn_log_gamma : ConvexOn ℝ (Ioi 0) (log ∘ gamma) :=
  by
  refine' convex_on_iff_forall_pos.mpr ⟨convex_Ioi _, fun x hx y hy a b ha hb hab => _⟩
  have : b = 1 - a := by linarith; subst this
  simp_rw [Function.comp_apply, smul_eq_mul]
  rw [← log_rpow (Gamma_pos_of_pos hy), ← log_rpow (Gamma_pos_of_pos hx), ←
    log_mul (rpow_pos_of_pos (Gamma_pos_of_pos hx) _).ne'
      (rpow_pos_of_pos (Gamma_pos_of_pos hy) _).ne',
    log_le_log (Gamma_pos_of_pos (add_pos (mul_pos ha hx) (mul_pos hb hy)))
      (mul_pos (rpow_pos_of_pos (Gamma_pos_of_pos hx) _) (rpow_pos_of_pos (Gamma_pos_of_pos hy) _))]
  exact Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx hy ha hb hab
#align real.convex_on_log_Gamma Real.convexOn_log_gamma

theorem convexOn_gamma : ConvexOn ℝ (Ioi 0) gamma :=
  by
  refine' ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => _⟩
  have :=
    ConvexOn.comp (convex_on_exp.subset (subset_univ _) _) convex_on_log_Gamma fun u hu v hv huv =>
      exp_le_exp.mpr huv
  convert this.2 hx hy ha hb hab
  · rw [Function.comp_apply, exp_log (Gamma_pos_of_pos <| this.1 hx hy ha hb hab)]
  · rw [Function.comp_apply, exp_log (Gamma_pos_of_pos hx)]
  · rw [Function.comp_apply, exp_log (Gamma_pos_of_pos hy)]
  · rw [convex_iff_is_preconnected]
    refine' is_preconnected_Ioi.image _ fun x hx => ContinuousAt.continuousWithinAt _
    refine' (differentiable_at_Gamma fun m => _).ContinuousAt.log (Gamma_pos_of_pos hx).ne'
    exact (neg_lt_iff_pos_add.mpr (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg m))).ne'
#align real.convex_on_Gamma Real.convexOn_gamma

section BohrMollerup

/-! ## The Bohr-Mollerup theorem

In this section we prove two interrelated statements about the `Γ` function on the positive reals:

* the Euler limit formula `real.bohr_mollerup.tendsto_log_gamma_seq`, stating that for positive
  real `x` the sequence `x * log n + log n! - ∑ (m : ℕ) in finset.range (n + 1), log (x + m)`
  tends to `log Γ(x)` as `n → ∞`.
* the Bohr-Mollerup theorem (`real.eq_Gamma_of_log_convex`) which states that `Γ` is the unique
  *log-convex*, positive-real-valued function on the positive reals satisfying
  `f (x + 1) = x f x` and `f 1 = 1`.

To do this, we prove that any function satisfying the hypotheses of the Bohr--Mollerup theorem must
agree with the limit in the Euler limit formula, so there is at most one such function. Then we
show that `Γ` satisfies these conditions.

Since most of the auxiliary lemmas for the Bohr-Mollerup theorem are of no relevance outside the
context of this proof, we place them in a separate namespace `real.bohr_mollerup` to avoid clutter.
(This includes the logarithmic form of the Euler limit formula, since later we will prove a more
general form of the Euler limit formula valid for any real or complex `x`; see
`real.Gamma_seq_tendsto_Gamma` and `complex.Gamma_seq_tendsto_Gamma`.)
-/


namespace BohrMollerup

/-- The function `n ↦ x log n + log n! - (log x + ... + log (x + n))`, which we will show tends to
`log (Gamma x)` as `n → ∞`. -/
def logGammaSeq (x : ℝ) (n : ℕ) : ℝ :=
  x * log n + log n ! - ∑ m : ℕ in Finset.range (n + 1), log (x + m)
#align real.bohr_mollerup.log_gamma_seq Real.BohrMollerup.logGammaSeq

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

theorem tendsto_log_gamma {x : ℝ} (hx : 0 < x) :
    Tendsto (logGammaSeq x) atTop (𝓝 <| log (gamma x)) :=
  by
  have : log (Gamma x) = (log ∘ Gamma) x - (log ∘ Gamma) 1 := by
    simp_rw [Function.comp_apply, Gamma_one, log_one, sub_zero]
  rw [this]
  refine' bohr_mollerup.tendsto_log_gamma_seq convex_on_log_Gamma (fun y hy => _) hx
  rw [Function.comp_apply, Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne', add_comm]
#align real.bohr_mollerup.tendsto_log_Gamma Real.BohrMollerup.tendsto_log_gamma

end BohrMollerup

-- (namespace)
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
    exact tendsto_nhds_unique e1 (bohr_mollerup.tendsto_log_Gamma hx)
  · intro y hy
    rw [Function.comp_apply, hf_feq hy, log_mul hy.ne' (hf_pos hy).ne']
    ring
#align real.eq_Gamma_of_log_convex Real.eq_gamma_of_log_convex

end BohrMollerup

-- (section)
section StrictMono

theorem gamma_two : gamma 2 = 1 := by simpa using Gamma_nat_eq_factorial 1
#align real.Gamma_two Real.gamma_two

theorem gamma_three_div_two_lt_one : gamma (3 / 2) < 1 :=
  by
  -- This can also be proved using the closed-form evaluation of `Gamma (1 / 2)` in
  -- `analysis.special_functions.gaussian`, but we give a self-contained proof using log-convexity
  -- to avoid unnecessary imports.
  have A : (0 : ℝ) < 3 / 2 := by norm_num
  have :=
    bohr_mollerup.f_add_nat_le convex_on_log_Gamma (fun y hy => _) two_ne_zero one_half_pos
      (by norm_num : 1 / 2 ≤ (1 : ℝ))
  swap
  ·
    rw [Function.comp_apply, Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne',
      add_comm]
  rw [Function.comp_apply, Function.comp_apply, Nat.cast_two, Gamma_two, log_one, zero_add,
    (by norm_num : (2 : ℝ) + 1 / 2 = 3 / 2 + 1), Gamma_add_one A.ne',
    log_mul A.ne' (Gamma_pos_of_pos A).ne', ← le_sub_iff_add_le',
    log_le_iff_le_exp (Gamma_pos_of_pos A)] at this
  refine' this.trans_lt (exp_lt_one_iff.mpr _)
  rw [mul_comm, ← mul_div_assoc, div_sub' _ _ (2 : ℝ) two_ne_zero]
  refine' div_neg_of_neg_of_pos _ two_pos
  rw [sub_neg, mul_one, ← Nat.cast_two, ← log_pow, ← exp_lt_exp, Nat.cast_two, exp_log two_pos,
      exp_log] <;>
    norm_num
#align real.Gamma_three_div_two_lt_one Real.gamma_three_div_two_lt_one

theorem gamma_strictMonoOn_Ici : StrictMonoOn gamma (Ici 2) :=
  by
  convert
    convex_on_Gamma.strict_mono_of_lt (by norm_num : (0 : ℝ) < 3 / 2)
      (by norm_num : (3 / 2 : ℝ) < 2) (Gamma_two.symm ▸ Gamma_three_div_two_lt_one)
  symm
  rw [inter_eq_right_iff_subset]
  exact fun x hx => two_pos.trans_le hx
#align real.Gamma_strict_mono_on_Ici Real.gamma_strictMonoOn_Ici

end StrictMono

end Real

section BetaIntegral

/-! ## The Beta function -/


namespace Complex

-- mathport name: exprcexp
notation "cexp" => Complex.exp

/-- The Beta function `Β (u, v)`, defined as `∫ x:ℝ in 0..1, x ^ (u - 1) * (1 - x) ^ (v - 1)`. -/
noncomputable def betaIntegral (u v : ℂ) : ℂ :=
  ∫ x : ℝ in 0 ..1, x ^ (u - 1) * (1 - x) ^ (v - 1)
#align complex.beta_integral Complex.betaIntegral

/-- Auxiliary lemma for `beta_integral_convergent`, showing convergence at the left endpoint. -/
theorem betaIntegralConvergentLeft {u : ℂ} (hu : 0 < re u) (v : ℂ) :
    IntervalIntegrable (fun x => x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ → ℂ) volume 0 (1 / 2) :=
  by
  apply IntervalIntegrable.mulContinuousOn
  · refine' intervalIntegral.intervalIntegrableCpow' _
    rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
  · apply ContinuousAt.continuousOn
    intro x hx
    rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 1 / 2)] at hx
    apply ContinuousAt.cpow
    · exact (continuous_const.sub continuous_of_real).ContinuousAt
    · exact continuousAt_const
    · rw [sub_re, one_re, of_real_re, sub_pos]
      exact Or.inl (hx.2.trans_lt (by norm_num : (1 / 2 : ℝ) < 1))
#align complex.beta_integral_convergent_left Complex.betaIntegralConvergentLeft

/-- The Beta integral is convergent for all `u, v` of positive real part. -/
theorem betaIntegralConvergent {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
    IntervalIntegrable (fun x => x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ → ℂ) volume 0 1 :=
  by
  refine' (beta_integral_convergent_left hu v).trans _
  rw [IntervalIntegrable.iff_comp_neg]
  convert ((beta_integral_convergent_left hv u).comp_add_right 1).symm
  · ext1 x
    conv_lhs => rw [mul_comm]
    congr 2 <;>
      · push_cast
        ring
  · norm_num
  · norm_num
#align complex.beta_integral_convergent Complex.betaIntegralConvergent

theorem betaIntegral_symm (u v : ℂ) : betaIntegral v u = betaIntegral u v :=
  by
  rw [beta_integral, beta_integral]
  have :=
    intervalIntegral.integral_comp_mul_add (fun x : ℝ => (x : ℂ) ^ (u - 1) * (1 - ↑x) ^ (v - 1))
      neg_one_lt_zero.ne 1
  rw [inv_neg, inv_one, neg_one_smul, ← intervalIntegral.integral_symm] at this
  convert this
  · ext1 x
    rw [mul_comm]
    congr <;>
      · push_cast
        ring
  · ring; · ring
#align complex.beta_integral_symm Complex.betaIntegral_symm

theorem betaIntegral_eval_one_right {u : ℂ} (hu : 0 < re u) : betaIntegral u 1 = 1 / u :=
  by
  simp_rw [beta_integral, sub_self, cpow_zero, mul_one]
  rw [integral_cpow (Or.inl _)]
  · rw [of_real_zero, of_real_one, one_cpow, zero_cpow, sub_zero, sub_add_cancel]
    rw [sub_add_cancel]
    contrapose! hu
    rw [hu, zero_re]
  · rwa [sub_re, one_re, ← sub_pos, sub_neg_eq_add, sub_add_cancel]
#align complex.beta_integral_eval_one_right Complex.betaIntegral_eval_one_right

theorem betaIntegral_scaled (s t : ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ x in 0 ..a, (x : ℂ) ^ (s - 1) * (a - x) ^ (t - 1)) = a ^ (s + t - 1) * betaIntegral s t :=
  by
  have ha' : (a : ℂ) ≠ 0 := of_real_ne_zero.mpr ha.ne'
  rw [beta_integral]
  have A : (a : ℂ) ^ (s + t - 1) = a * (a ^ (s - 1) * a ^ (t - 1)) := by
    rw [(by abel : s + t - 1 = 1 + (s - 1) + (t - 1)), cpow_add _ _ ha', cpow_add 1 _ ha', cpow_one,
      mul_assoc]
  rw [A, mul_assoc, ← intervalIntegral.integral_const_mul (↑a ^ _ * _), ← real_smul, ← zero_div a, ←
    div_self ha.ne', ← intervalIntegral.integral_comp_div _ ha.ne', zero_div]
  simp_rw [intervalIntegral.integral_of_le ha.le]
  refine' set_integral_congr measurableSet_Ioc fun x hx => _
  dsimp only
  rw [mul_mul_mul_comm]
  congr 1
  · rw [← mul_cpow_of_real_nonneg ha.le (div_pos hx.1 ha).le, of_real_div, mul_div_cancel' _ ha']
  · rw [(by push_cast : (1 : ℂ) - ↑(x / a) = ↑(1 - x / a)), ←
      mul_cpow_of_real_nonneg ha.le (sub_nonneg.mpr <| (div_le_one ha).mpr hx.2)]
    push_cast
    rw [mul_sub, mul_one, mul_div_cancel' _ ha']
#align complex.beta_integral_scaled Complex.betaIntegral_scaled

/-- Relation between Beta integral and Gamma function.  -/
theorem gamma_mul_gamma_eq_betaIntegral {s t : ℂ} (hs : 0 < re s) (ht : 0 < re t) :
    gamma s * gamma t = gamma (s + t) * betaIntegral s t :=
  by
  -- Note that we haven't proved (yet) that the Gamma function has no zeroes, so we can't formulate
  -- this as a formula for the Beta function.
  have conv_int :=
    integral_pos_convolution (Gamma_integral_convergent hs) (Gamma_integral_convergent ht)
      (ContinuousLinearMap.mul ℝ ℂ)
  simp_rw [ContinuousLinearMap.mul_apply'] at conv_int
  have hst : 0 < re (s + t) := by
    rw [add_re]
    exact add_pos hs ht
  rw [Gamma_eq_integral hs, Gamma_eq_integral ht, Gamma_eq_integral hst, Gamma_integral,
    Gamma_integral, Gamma_integral, ← conv_int, ← integral_mul_right (beta_integral _ _)]
  refine' set_integral_congr measurableSet_Ioi fun x hx => _
  dsimp only
  rw [mul_assoc, ← beta_integral_scaled s t hx, ← intervalIntegral.integral_const_mul]
  congr 1 with y : 1
  push_cast
  suffices cexp (-x) = cexp (-y) * cexp (-(x - y))
    by
    rw [this]
    ring
  · rw [← Complex.exp_add]
    congr 1
    abel
#align complex.Gamma_mul_Gamma_eq_beta_integral Complex.gamma_mul_gamma_eq_betaIntegral

/-- Recurrence formula for the Beta function. -/
theorem betaIntegral_recurrence {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
    u * betaIntegral u (v + 1) = v * betaIntegral (u + 1) v :=
  by
  -- NB: If we knew `Gamma (u + v + 1) ≠ 0` this would be an easy consequence of
  -- `Gamma_mul_Gamma_eq_beta_integral`; but we don't know that yet. We will prove it later, but
  -- this lemma is needed in the proof. So we give a (somewhat laborious) direct argument.
  let F : ℝ → ℂ := fun x => x ^ u * (1 - x) ^ v
  have hu' : 0 < re (u + 1) := by
    rw [add_re, one_re]
    positivity
  have hv' : 0 < re (v + 1) := by
    rw [add_re, one_re]
    positivity
  have hc : ContinuousOn F (Icc 0 1) :=
    by
    refine' (ContinuousAt.continuousOn fun x hx => _).mul (ContinuousAt.continuousOn fun x hx => _)
    · refine'
        (continuous_at_cpow_const_of_re_pos (Or.inl _) hu).comp continuous_of_real.continuous_at
      rw [of_real_re]
      exact hx.1
    · refine'
        (continuous_at_cpow_const_of_re_pos (Or.inl _) hv).comp
          (continuous_const.sub continuous_of_real).ContinuousAt
      rw [sub_re, one_re, of_real_re, sub_nonneg]
      exact hx.2
  have hder :
    ∀ x : ℝ,
      x ∈ Ioo (0 : ℝ) 1 →
        HasDerivAt F (u * (↑x ^ (u - 1) * (1 - ↑x) ^ v) - v * (↑x ^ u * (1 - ↑x) ^ (v - 1))) x :=
    by
    intro x hx
    have U : HasDerivAt (fun y : ℂ => y ^ u) (u * ↑x ^ (u - 1)) ↑x :=
      by
      have := HasDerivAt.cpow_const (hasDerivAt_id ↑x) (Or.inl _)
      · rw [mul_one] at this
        exact this
      · rw [id.def, of_real_re]
        exact hx.1
    have V : HasDerivAt (fun y : ℂ => (1 - y) ^ v) (-v * (1 - ↑x) ^ (v - 1)) ↑x :=
      by
      have A := HasDerivAt.cpow_const (hasDerivAt_id (1 - ↑x)) (Or.inl _)
      rotate_left
      · exact v
      · rw [id.def, sub_re, one_re, of_real_re, sub_pos]
        exact hx.2
      simp_rw [id.def] at A
      have B : HasDerivAt (fun y : ℂ => 1 - y) (-1) ↑x :=
        by
        apply HasDerivAt.const_sub
        apply hasDerivAt_id
      convert HasDerivAt.comp (↑x) A B using 1
      ring
    convert (U.mul V).comp_of_real
    ring
  have h_int :=
    ((beta_integral_convergent hu hv').const_mul u).sub
      ((beta_integral_convergent hu' hv).const_mul v)
  dsimp only at h_int
  rw [add_sub_cancel, add_sub_cancel] at h_int
  have int_ev := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hder h_int
  have hF0 : F 0 = 0 :=
    by
    simp only [mul_eq_zero, of_real_zero, cpow_eq_zero_iff, eq_self_iff_true, Ne.def, true_and_iff,
      sub_zero, one_cpow, one_ne_zero, or_false_iff]
    contrapose! hu
    rw [hu, zero_re]
  have hF1 : F 1 = 0 :=
    by
    simp only [mul_eq_zero, of_real_one, one_cpow, one_ne_zero, sub_self, cpow_eq_zero_iff,
      eq_self_iff_true, Ne.def, true_and_iff, false_or_iff]
    contrapose! hv
    rw [hv, zero_re]
  rw [hF0, hF1, sub_zero, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at int_ev
  · rw [beta_integral, beta_integral, ← sub_eq_zero]
    convert int_ev <;>
      · ext1 x
        congr
        abel
  · apply IntervalIntegrable.constMul
    convert beta_integral_convergent hu hv'
    ext1 x
    rw [add_sub_cancel]
  · apply IntervalIntegrable.constMul
    convert beta_integral_convergent hu' hv
    ext1 x
    rw [add_sub_cancel]
#align complex.beta_integral_recurrence Complex.betaIntegral_recurrence

/-- Explicit formula for the Beta function when second argument is a positive integer. -/
theorem betaIntegral_eval_nat_add_one_right {u : ℂ} (hu : 0 < re u) (n : ℕ) :
    betaIntegral u (n + 1) = n ! / ∏ j : ℕ in Finset.range (n + 1), u + j :=
  by
  induction' n with n IH generalizing u
  ·
    rw [Nat.cast_zero, zero_add, beta_integral_eval_one_right hu, Nat.factorial_zero, Nat.cast_one,
      zero_add, Finset.prod_range_one, Nat.cast_zero, add_zero]
  · have := beta_integral_recurrence hu (_ : 0 < re n.succ)
    swap
    · rw [← of_real_nat_cast, of_real_re]
      positivity
    rw [mul_comm u _, ← eq_div_iff] at this
    swap
    · contrapose! hu
      rw [hu, zero_re]
    rw [this, Finset.prod_range_succ', Nat.cast_succ, IH]
    swap
    · rw [add_re, one_re]
      positivity
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ←
      mul_div_assoc, ← div_div]
    congr 3 with j : 1
    push_cast
    abel
#align complex.beta_integral_eval_nat_add_one_right Complex.betaIntegral_eval_nat_add_one_right

end Complex

end BetaIntegral

section LimitFormula

/-! ## The Euler limit formula -/


namespace Complex

/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for complex `s`.
We will show that this tends to `Γ(s)` as `n → ∞`. -/
noncomputable def gammaSeq (s : ℂ) (n : ℕ) :=
  (n : ℂ) ^ s * n ! / ∏ j : ℕ in Finset.range (n + 1), s + j
#align complex.Gamma_seq Complex.gammaSeq

theorem gammaSeq_eq_betaIntegral_of_re_pos {s : ℂ} (hs : 0 < re s) (n : ℕ) :
    gammaSeq s n = n ^ s * betaIntegral s (n + 1) := by
  rw [Gamma_seq, beta_integral_eval_nat_add_one_right hs n, ← mul_div_assoc]
#align complex.Gamma_seq_eq_beta_integral_of_re_pos Complex.gammaSeq_eq_betaIntegral_of_re_pos

theorem gammaSeq_add_one_left (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    gammaSeq (s + 1) n / s = n / (n + 1 + s) * gammaSeq s n :=
  by
  conv_lhs => rw [Gamma_seq, Finset.prod_range_succ, div_div]
  conv_rhs =>
    rw [Gamma_seq, Finset.prod_range_succ', Nat.cast_zero, add_zero, div_mul_div_comm, ← mul_assoc,
      ← mul_assoc, mul_comm _ (Finset.prod _ _)]
  congr 3
  · rw [cpow_add _ _ (nat.cast_ne_zero.mpr hn), cpow_one, mul_comm]
  · refine' Finset.prod_congr (by rfl) fun x hx => _
    push_cast
    ring
  · abel
#align complex.Gamma_seq_add_one_left Complex.gammaSeq_add_one_left

theorem gammaSeq_eq_approx_Gamma_integral {s : ℂ} (hs : 0 < re s) {n : ℕ} (hn : n ≠ 0) :
    gammaSeq s n = ∫ x : ℝ in 0 ..n, ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1) :=
  by
  have : ∀ x : ℝ, x = x / n * n := by
    intro x
    rw [div_mul_cancel]
    exact nat.cast_ne_zero.mpr hn
  conv in ↑_ ^ _ =>
    congr
    rw [this x]
  rw [Gamma_seq_eq_beta_integral_of_re_pos hs]
  rw [beta_integral,
    @intervalIntegral.integral_comp_div _ _ _ _ 0 n _
      (fun x => ↑((1 - x) ^ n) * ↑(x * ↑n) ^ (s - 1) : ℝ → ℂ) (nat.cast_ne_zero.mpr hn),
    real_smul, zero_div, div_self, add_sub_cancel, ← intervalIntegral.integral_const_mul, ←
    intervalIntegral.integral_const_mul]
  swap
  · exact nat.cast_ne_zero.mpr hn
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  refine' set_integral_congr measurableSet_Ioc fun x hx => _
  push_cast
  have hn' : (n : ℂ) ≠ 0 := nat.cast_ne_zero.mpr hn
  have A : (n : ℂ) ^ s = (n : ℂ) ^ (s - 1) * n :=
    by
    conv_lhs => rw [(by ring : s = s - 1 + 1), cpow_add _ _ hn']
    simp
  have B : ((x : ℂ) * ↑n) ^ (s - 1) = (x : ℂ) ^ (s - 1) * ↑n ^ (s - 1) := by
    rw [← of_real_nat_cast,
      mul_cpow_of_real_nonneg hx.1.le (nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)).le]
  rw [A, B, cpow_nat_cast]
  ring
#align complex.Gamma_seq_eq_approx_Gamma_integral Complex.gammaSeq_eq_approx_Gamma_integral

/-- The main techical lemma for `Gamma_seq_tendsto_Gamma`, expressing the integral defining the
Gamma function for `0 < re s` as the limit of a sequence of integrals over finite intervals. -/
theorem approx_gamma_integral_tendsto_gamma_integral {s : ℂ} (hs : 0 < re s) :
    Tendsto (fun n : ℕ => ∫ x : ℝ in 0 ..n, ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1)) atTop
      (𝓝 <| gamma s) :=
  by
  rw [Gamma_eq_integral hs]
  -- We apply dominated convergence to the following function, which we will show is uniformly
  -- bounded above by the Gamma integrand `exp (-x) * x ^ (re s - 1)`.
  let f : ℕ → ℝ → ℂ := fun n =>
    indicator (Ioc 0 (n : ℝ)) fun x : ℝ => ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1)
  -- integrability of f
  have f_ible : ∀ n : ℕ, integrable (f n) (volume.restrict (Ioi 0)) :=
    by
    intro n
    rw [integrable_indicator_iff (measurableSet_Ioc : MeasurableSet (Ioc (_ : ℝ) _)), integrable_on,
      measure.restrict_restrict_of_subset Ioc_subset_Ioi_self, ← integrable_on, ←
      intervalIntegrable_iff_integrable_Ioc_of_le (by positivity : (0 : ℝ) ≤ n)]
    apply IntervalIntegrable.continuousOnMul
    · refine' intervalIntegral.intervalIntegrableCpow' _
      rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
    · apply Continuous.continuousOn
      continuity
  -- pointwise limit of f
  have f_tends :
    ∀ x : ℝ,
      x ∈ Ioi (0 : ℝ) →
        tendsto (fun n : ℕ => f n x) at_top (𝓝 <| ↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1)) :=
    by
    intro x hx
    apply tendsto.congr'
    show ∀ᶠ n : ℕ in at_top, ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1) = f n x
    · refine' eventually.mp (eventually_ge_at_top ⌈x⌉₊) (eventually_of_forall fun n hn => _)
      rw [Nat.ceil_le] at hn
      dsimp only [f]
      rw [indicator_of_mem]
      exact ⟨hx, hn⟩
    · simp_rw [mul_comm _ (↑x ^ _)]
      refine' (tendsto.comp (continuous_of_real.tendsto _) _).const_mul _
      convert tendsto_one_plus_div_pow_exp (-x)
      ext1 n
      rw [neg_div, ← sub_eq_add_neg]
  -- let `convert` identify the remaining goals
  convert
    tendsto_integral_of_dominated_convergence _ (fun n => (f_ible n).1)
      (Real.gammaIntegralConvergent hs) _
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ f_tends))
  -- limit of f is the integrand we want
  · ext1 n
    rw [integral_indicator (measurableSet_Ioc : MeasurableSet (Ioc (_ : ℝ) _)),
      intervalIntegral.integral_of_le (by positivity : 0 ≤ (n : ℝ)),
      measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
  -- f is uniformly bounded by the Gamma integrand
  · intro n
    refine' (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => _)
    dsimp only [f]
    rcases lt_or_le (n : ℝ) x with (hxn | hxn)
    · rw [indicator_of_not_mem (not_mem_Ioc_of_gt hxn), norm_zero,
        mul_nonneg_iff_right_nonneg_of_pos (exp_pos _)]
      exact rpow_nonneg_of_nonneg (le_of_lt hx) _
    · rw [indicator_of_mem (mem_Ioc.mpr ⟨hx, hxn⟩), norm_mul, Complex.norm_eq_abs,
        Complex.abs_of_nonneg
          (pow_nonneg (sub_nonneg.mpr <| div_le_one_of_le hxn <| by positivity) _),
        Complex.norm_eq_abs, abs_cpow_eq_rpow_re_of_pos hx, sub_re, one_re,
        mul_le_mul_right (rpow_pos_of_pos hx _)]
      exact one_sub_div_pow_le_exp_neg hxn
#align complex.approx_Gamma_integral_tendsto_Gamma_integral Complex.approx_gamma_integral_tendsto_gamma_integral

/-- Euler's limit formula for the complex Gamma function. -/
theorem gammaSeq_tendsto_gamma (s : ℂ) : Tendsto (gammaSeq s) atTop (𝓝 <| gamma s) :=
  by
  suffices ∀ m : ℕ, -↑m < re s → tendsto (Gamma_seq s) at_top (𝓝 <| Gamma_aux m s)
    by
    rw [Gamma]
    apply this
    rw [neg_lt]
    rcases lt_or_le 0 (re s) with (hs | hs)
    · exact (neg_neg_of_pos hs).trans_le (Nat.cast_nonneg _)
    · refine' (Nat.lt_floor_add_one _).trans_le _
      rw [sub_eq_neg_add, Nat.floor_add_one (neg_nonneg.mpr hs), Nat.cast_add_one]
  intro m
  induction' m with m IH generalizing s
  · -- Base case: `0 < re s`, so Gamma is given by the integral formula
    intro hs
    rw [Nat.cast_zero, neg_zero] at hs
    rw [← Gamma_eq_Gamma_aux]
    · refine' tendsto.congr' _ (approx_Gamma_integral_tendsto_Gamma_integral hs)
      refine' (eventually_ne_at_top 0).mp (eventually_of_forall fun n hn => _)
      exact (Gamma_seq_eq_approx_Gamma_integral hs hn).symm
    · rwa [Nat.cast_zero, neg_lt_zero]
  · -- Induction step: use recurrence formulae in `s` for Gamma and Gamma_seq
    intro hs
    rw [Nat.cast_succ, neg_add, ← sub_eq_add_neg, sub_lt_iff_lt_add, ← one_re, ← add_re] at hs
    rw [Gamma_aux]
    have :=
      tendsto.congr' ((eventually_ne_at_top 0).mp (eventually_of_forall fun n hn => _))
        ((IH _ hs).div_const s)
    pick_goal 3
    · exact Gamma_seq_add_one_left s hn
    -- doesn't work if inlined?
    conv at this in _ / _ * _ => rw [mul_comm]
    rwa [← mul_one (Gamma_aux m (s + 1) / s), tendsto_mul_iff_of_ne_zero _ (one_ne_zero' ℂ)] at this
    simp_rw [add_assoc]
    exact tendsto_coe_nat_div_add_atTop (1 + s)
#align complex.Gamma_seq_tendsto_Gamma Complex.gammaSeq_tendsto_gamma

end Complex

end LimitFormula

section GammaReflection

/-! ## The reflection formula -/


open Real

namespace Complex

theorem gammaSeq_mul (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
    gammaSeq z n * gammaSeq (1 - z) n =
      n / (n + 1 - z) * (1 / (z * ∏ j in Finset.range n, 1 - z ^ 2 / (j + 1) ^ 2)) :=
  by
  -- also true for n = 0 but we don't need it
  have aux : ∀ a b c d : ℂ, a * b * (c * d) = a * c * (b * d) :=
    by
    intros
    ring
  rw [Gamma_seq, Gamma_seq, div_mul_div_comm, aux, ← pow_two]
  have : (n : ℂ) ^ z * n ^ (1 - z) = n := by
    rw [← cpow_add _ _ (nat.cast_ne_zero.mpr hn), add_sub_cancel'_right, cpow_one]
  rw [this, Finset.prod_range_succ', Finset.prod_range_succ, aux, ← Finset.prod_mul_distrib,
    Nat.cast_zero, add_zero, add_comm (1 - z) n, ← add_sub_assoc]
  have : ∀ j : ℕ, (z + ↑(j + 1)) * (1 - z + ↑j) = ↑((j + 1) ^ 2) * (1 - z ^ 2 / (↑j + 1) ^ 2) :=
    by
    intro j
    push_cast
    have : (j : ℂ) + 1 ≠ 0 := by
      rw [← Nat.cast_succ, Nat.cast_ne_zero]
      exact Nat.succ_ne_zero j
    field_simp
    ring
  simp_rw [this]
  rw [Finset.prod_mul_distrib, ← Nat.cast_prod, Finset.prod_pow,
    Finset.prod_range_add_one_eq_factorial, Nat.cast_pow,
    (by
      intros
      ring : ∀ a b c d : ℂ, a * b * (c * d) = a * (d * (b * c))),
    ← div_div, mul_div_cancel, ← div_div, mul_comm z _, mul_one_div]
  exact pow_ne_zero 2 (nat.cast_ne_zero.mpr <| Nat.factorial_ne_zero n)
#align complex.Gamma_seq_mul Complex.gammaSeq_mul

/-- Euler's reflection formula for the complex Gamma function. -/
theorem gamma_mul_gamma_one_sub (z : ℂ) : gamma z * gamma (1 - z) = π / sin (π * z) :=
  by
  have pi_ne : (π : ℂ) ≠ 0 := complex.of_real_ne_zero.mpr pi_ne_zero
  by_cases hs : sin (↑π * z) = 0
  · -- first deal with silly case z = integer
    rw [hs, div_zero]
    rw [← neg_eq_zero, ← Complex.sin_neg, ← mul_neg, Complex.sin_eq_zero_iff, mul_comm] at hs
    obtain ⟨k, hk⟩ := hs
    rw [mul_eq_mul_right_iff, eq_false (of_real_ne_zero.mpr pi_pos.ne'), or_false_iff,
      neg_eq_iff_neg_eq] at hk
    rw [← hk]
    cases k
    · rw [Int.cast_ofNat, Complex.gamma_neg_nat_eq_zero, zero_mul]
    ·
      rw [Int.cast_negSucc, neg_neg, Nat.cast_add, Nat.cast_one, add_comm, sub_add_cancel',
        Complex.gamma_neg_nat_eq_zero, mul_zero]
  refine' tendsto_nhds_unique ((Gamma_seq_tendsto_Gamma z).mul (Gamma_seq_tendsto_Gamma <| 1 - z)) _
  have : ↑π / sin (↑π * z) = 1 * (π / sin (π * z)) := by rw [one_mul]
  rw [this]
  refine'
    tendsto.congr'
      ((eventually_ne_at_top 0).mp (eventually_of_forall fun n hn => (Gamma_seq_mul z hn).symm))
      (tendsto.mul _ _)
  · convert tendsto_coe_nat_div_add_atTop (1 - z)
    ext1 n
    rw [add_sub_assoc]
  · have : ↑π / sin (↑π * z) = 1 / (sin (π * z) / π) := by field_simp
    rw [this]
    refine' tendsto_const_nhds.div _ (div_ne_zero hs pi_ne)
    rw [← tendsto_mul_iff_of_ne_zero tendsto_const_nhds pi_ne, div_mul_cancel _ pi_ne]
    convert tendsto_euler_sin_prod z
    ext1 n
    rw [mul_comm, ← mul_assoc]
#align complex.Gamma_mul_Gamma_one_sub Complex.gamma_mul_gamma_one_sub

/-- The Gamma function does not vanish on `ℂ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
theorem gamma_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) : gamma s ≠ 0 :=
  by
  by_cases h_im : s.im = 0
  · have : s = ↑s.re := by
      conv_lhs => rw [← Complex.re_add_im s]
      rw [h_im, of_real_zero, zero_mul, add_zero]
    rw [this, Gamma_of_real, of_real_ne_zero]
    refine' Real.gamma_ne_zero fun n => _
    specialize hs n
    contrapose! hs
    rwa [this, ← of_real_nat_cast, ← of_real_neg, of_real_inj]
  · have : sin (↑π * s) ≠ 0 := by
      rw [Complex.sin_ne_zero_iff]
      intro k
      apply_fun im
      rw [of_real_mul_im, ← of_real_int_cast, ← of_real_mul, of_real_im]
      exact mul_ne_zero real.pi_pos.ne' h_im
    have A := div_ne_zero (of_real_ne_zero.mpr real.pi_pos.ne') this
    rw [← Complex.gamma_mul_gamma_one_sub s, mul_ne_zero_iff] at A
    exact A.1
#align complex.Gamma_ne_zero Complex.gamma_ne_zero

theorem gamma_eq_zero_iff (s : ℂ) : gamma s = 0 ↔ ∃ m : ℕ, s = -m :=
  by
  constructor
  · contrapose!
    exact Gamma_ne_zero
  · rintro ⟨m, rfl⟩
    exact Gamma_neg_nat_eq_zero m
#align complex.Gamma_eq_zero_iff Complex.gamma_eq_zero_iff

end Complex

namespace Real

/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for real `s`. We
will show that this tends to `Γ(s)` as `n → ∞`. -/
noncomputable def gammaSeq (s : ℝ) (n : ℕ) :=
  (n : ℝ) ^ s * n ! / ∏ j : ℕ in Finset.range (n + 1), s + j
#align real.Gamma_seq Real.gammaSeq

/-- Euler's limit formula for the real Gamma function. -/
theorem gammaSeq_tendsto_gamma (s : ℝ) : Tendsto (gammaSeq s) atTop (𝓝 <| gamma s) :=
  by
  suffices : tendsto (coe ∘ Gamma_seq s : ℕ → ℂ) at_top (𝓝 <| Complex.gamma s)
  exact (complex.continuous_re.tendsto (Complex.gamma ↑s)).comp this
  convert Complex.gammaSeq_tendsto_gamma s
  ext1 n
  dsimp only [Gamma_seq, Function.comp_apply, Complex.gammaSeq]
  push_cast
  rw [Complex.of_real_cpow n.cast_nonneg, Complex.of_real_nat_cast]
#align real.Gamma_seq_tendsto_Gamma Real.gammaSeq_tendsto_gamma

/-- Euler's reflection formula for the real Gamma function. -/
theorem gamma_mul_gamma_one_sub (s : ℝ) : gamma s * gamma (1 - s) = π / sin (π * s) :=
  by
  simp_rw [← Complex.of_real_inj, Complex.of_real_div, Complex.of_real_sin, Complex.of_real_mul, ←
    Complex.gamma_of_real, Complex.of_real_sub, Complex.of_real_one]
  exact Complex.gamma_mul_gamma_one_sub s
#align real.Gamma_mul_Gamma_one_sub Real.gamma_mul_gamma_one_sub

end Real

end GammaReflection

