/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module analysis.special_functions.gamma.basic
! leanprover-community/mathlib commit 7982767093ae38cba236487f9c9dd9cd99f63c16
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Integral.ExpDecay
import Mathbin.Analysis.SpecialFunctions.ImproperIntegrals
import Mathbin.Analysis.Calculus.ParametricIntegral

/-!
# The Gamma function

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

## Gamma function: main statements (real case)

* `real.Gamma`: the `Γ` function (of a real variable).
* Real counterparts of all the properties of the complex Gamma function listed above:
  `real.Gamma_eq_integral`, `real.Gamma_add_one`, `real.Gamma_nat_eq_factorial`,
  `real.differentiable_at_Gamma`.

## Tags

Gamma
-/


noncomputable section

open Filter intervalIntegral Set Real MeasureTheory Asymptotics

open Nat Topology ComplexConjugate

namespace Real

/-- Asymptotic bound for the `Γ` function integrand. -/
theorem Gamma_integrand_isLittleO (s : ℝ) :
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
#align real.Gamma_integrand_is_o Real.Gamma_integrand_isLittleO

/-- The Euler integral for the `Γ` function converges for positive real `s`. -/
theorem Gamma_integral_convergent {s : ℝ} (h : 0 < s) :
    IntegrableOn (fun x : ℝ => exp (-x) * x ^ (s - 1)) (Ioi 0) :=
  by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrable_on_union]
  constructor
  · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    refine' integrable_on.continuous_on_mul continuous_on_id.neg.exp _ is_compact_Icc
    refine' (intervalIntegrable_iff_integrable_Icc_of_le zero_le_one).mp _
    exact interval_integrable_rpow' (by linarith)
  · refine' integrable_of_isBigO_exp_neg one_half_pos _ (Gamma_integrand_is_o _).IsBigO
    refine' continuous_on_id.neg.exp.mul (continuous_on_id.rpow_const _)
    intro x hx
    exact Or.inl ((zero_lt_one : (0 : ℝ) < 1).trans_le hx).ne'
#align real.Gamma_integral_convergent Real.Gamma_integral_convergent

end Real

namespace Complex

/- Technical note: In defining the Gamma integrand exp (-x) * x ^ (s - 1) for s complex, we have to
make a choice between ↑(real.exp (-x)), complex.exp (↑(-x)), and complex.exp (-↑x), all of which are
equal but not definitionally so. We use the first of these throughout. -/
/-- The integral defining the `Γ` function converges for complex `s` with `0 < re s`.

This is proved by reduction to the real case. -/
theorem Gamma_integral_convergent {s : ℂ} (hs : 0 < s.re) :
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
    refine' has_finite_integral.congr (Real.Gamma_integral_convergent hs).2 _
    refine' (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => _)
    dsimp only
    rw [norm_eq_abs, map_mul, abs_of_nonneg <| le_of_lt <| exp_pos <| -x,
      abs_cpow_eq_rpow_re_of_pos hx _]
    simp
#align complex.Gamma_integral_convergent Complex.Gamma_integral_convergent

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
    mul_one] using integral_exp_neg_Ioi_zero
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
  intervalIntegral_tendsto_integral_Ioi 0 (Gamma_integral_convergent hs) tendsto_id
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
  convert(Gamma_integrand_interval_integrable (s + 1) _ hX).neg
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
    (((Real.Gamma_integral_convergent hs).mono_set Ioc_subset_Ioi_self).HasFiniteIntegral.congr
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
  · rw [MulZeroClass.mul_zero, add_zero]
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
  convert(u <| n - ⌊1 - s.re⌋₊).symm
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

theorem dGamma_integrand_isLittleO_atTop (s : ℝ) :
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
#align dGamma_integrand_is_o_at_top dGamma_integrand_isLittleO_atTop

/-- Absolute convergence of the integral which will give the derivative of the `Γ` function on
`1 < re s`. -/
theorem dGamma_integral_abs_convergent (s : ℝ) (hs : 1 < s) :
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
  · have := (dGamma_integrand_isLittleO_atTop s).IsBigO.norm_left
    refine' integrable_of_isBigO_exp_neg one_half_pos (ContinuousOn.mul _ _).norm this
    · refine' (continuous_exp.comp continuous_neg).ContinuousOn.mul (continuous_on_log.mono _)
      simp
    · apply ContinuousAt.continuousOn fun x hx => _
      apply continuous_at_id.rpow continuousAt_const
      dsimp
      right
      linarith
#align dGamma_integral_abs_convergent dGamma_integral_abs_convergent

/-- A uniform bound for the `s`-derivative of the `Γ` integrand for `s` in vertical strips. -/
theorem loc_unif_bound_dGammaIntegrand {t : ℂ} {s1 s2 x : ℝ} (ht1 : s1 ≤ t.re) (ht2 : t.re ≤ s2)
    (hx : 0 < x) : ‖dGammaIntegrand t x‖ ≤ dGammaIntegrandReal s1 x + dGammaIntegrandReal s2 x :=
  by
  rcases le_or_lt 1 x with (h | h)
  · -- case 1 ≤ x
    refine' le_add_of_nonneg_of_le (abs_nonneg _) _
    rw [dGammaIntegrand, dGammaIntegrandReal, Complex.norm_eq_abs, map_mul, abs_mul, ←
      Complex.ofReal_mul, Complex.abs_ofReal]
    refine' mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [Complex.abs_cpow_eq_rpow_re_of_pos hx]
    refine' le_trans _ (le_abs_self _)
    apply rpow_le_rpow_of_exponent_le h
    rw [Complex.sub_re, Complex.one_re]
    linarith
  · refine' le_add_of_le_of_nonneg _ (abs_nonneg _)
    rw [dGammaIntegrand, dGammaIntegrandReal, Complex.norm_eq_abs, map_mul, abs_mul, ←
      Complex.ofReal_mul, Complex.abs_ofReal]
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
    · refine' dGamma_integral_abs_convergent (s.re - ε) _
      field_simp
      rw [one_lt_div]
      · linarith
      · exact zero_lt_two
    · refine' dGamma_integral_abs_convergent (s.re + ε) _
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
  rw [Gamma, Complex.gamma_eq_integral (by rwa [Complex.ofReal_re] : 0 < Complex.re s)]
  dsimp only [Complex.gammaIntegral]
  simp_rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
  suffices
    (∫ x : ℝ in Ioi 0, ↑(exp (-x)) * (x : ℂ) ^ ((s - 1 : ℝ) : ℂ)) =
      ∫ x : ℝ in Ioi 0, ((exp (-x) * x ^ (s - 1) : ℝ) : ℂ)
    by rw [this, _root_.integral_of_real, Complex.ofReal_re]
  refine' set_integral_congr measurableSet_Ioi fun x hx => _
  push_cast
  rw [Complex.of_real_cpow (le_of_lt hx)]
  push_cast
#align real.Gamma_eq_integral Real.gamma_eq_integral

theorem gamma_add_one {s : ℝ} (hs : s ≠ 0) : gamma (s + 1) = s * gamma s :=
  by
  simp_rw [Gamma]
  rw [Complex.ofReal_add, Complex.ofReal_one, Complex.gamma_add_one, Complex.ofReal_mul_re]
  rwa [Complex.ofReal_ne_zero]
#align real.Gamma_add_one Real.gamma_add_one

theorem gamma_one : gamma 1 = 1 := by
  rw [Gamma, Complex.ofReal_one, Complex.gamma_one, Complex.one_re]
#align real.Gamma_one Real.gamma_one

theorem Complex.gamma_of_real (s : ℝ) : Complex.gamma (s : ℂ) = gamma s := by
  rw [Gamma, eq_comm, ← Complex.conj_eq_iff_re, ← Complex.gamma_conj, Complex.conj_ofReal]
#align complex.Gamma_of_real Complex.gamma_of_real

theorem gamma_nat_eq_factorial (n : ℕ) : gamma (n + 1) = n ! := by
  rw [Gamma, Complex.ofReal_add, Complex.ofReal_nat_cast, Complex.ofReal_one,
    Complex.gamma_nat_eq_factorial, ← Complex.ofReal_nat_cast, Complex.ofReal_re]
#align real.Gamma_nat_eq_factorial Real.gamma_nat_eq_factorial

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
theorem gamma_zero : gamma 0 = 0 := by
  simpa only [← Complex.ofReal_zero, Complex.gamma_of_real, Complex.ofReal_inj] using
    Complex.gamma_zero
#align real.Gamma_zero Real.gamma_zero

/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value `0`.
-/
theorem gamma_neg_nat_eq_zero (n : ℕ) : gamma (-n) = 0 := by
  simpa only [← Complex.ofReal_nat_cast, ← Complex.ofReal_neg, Complex.gamma_of_real,
    Complex.ofReal_eq_zero] using Complex.gamma_neg_nat_eq_zero n
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
  · rw [this, volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
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
  simp_rw [← Complex.ofReal_nat_cast, ← Complex.ofReal_neg, Ne.def, Complex.ofReal_inj]
  exact hs
#align real.differentiable_at_Gamma Real.differentiableAt_gamma

end Real

