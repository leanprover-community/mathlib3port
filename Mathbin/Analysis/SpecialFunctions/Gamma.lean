/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathbin.MeasureTheory.Integral.ExpDecay

/-!
# The Gamma function

This file defines the `Γ` function (of a real or complex variable `s`). We define this by Euler's
integral `Γ(s) = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` in a range where we can prove this is
convergent: presently `1 ≤ s` in the real case, and `1 ≤ re s` in the complex case (which is
non-optimal, but the optimal bound of `0 < s`, resp `0 < re s`, is harder to prove using the
methods in the library).

We show that this integral satisfies `Γ(1) = 1` and `Γ(s + 1) = s * Γ(s)`; hence we can define
`Γ(s)` for all `s` as the unique function satisfying this recurrence and agreeing with Euler's
integral in the convergence range.

TODO: Holomorpy in `s` (away from the poles at `-n : n ∈ ℕ`) will be added in a future PR.

## Tags

Gamma
-/


noncomputable section

open Filter intervalIntegral Set Real MeasureTheory

open TopologicalSpace

theorem integral_exp_neg_Ioi : (∫ x : ℝ in Ioi 0, exp (-x)) = 1 := by
  refine' tendsto_nhds_unique (interval_integral_tendsto_integral_Ioi _ _ tendsto_id) _
  · simpa only [neg_mul, one_mulₓ] using exp_neg_integrable_on_Ioi 0 zero_lt_one
    
  · simpa using tendsto_exp_neg_at_top_nhds_0.const_sub 1
    

namespace Real

/-- Asymptotic bound for the Γ function integrand. -/
theorem Gamma_integrand_is_O (s : ℝ) :
    Asymptotics.IsO (fun x : ℝ => exp (-x) * x ^ s) (fun x : ℝ => exp (-(1 / 2) * x)) atTop := by
  refine' Asymptotics.IsOₓ.is_O (Asymptotics.is_o_of_tendsto _ _)
  · intro x hx
    exfalso
    exact (exp_pos (-(1 / 2) * x)).ne' hx
    
  have : (fun x : ℝ => exp (-x) * x ^ s / exp (-(1 / 2) * x)) = (fun x : ℝ => exp (1 / 2 * x) / x ^ s)⁻¹ := by
    ext1 x
    field_simp [exp_ne_zero, exp_neg, ← Real.exp_add]
    left
    ring
  rw [this]
  exact (tendsto_exp_mul_div_rpow_at_top s (1 / 2) one_half_pos).inv_tendsto_at_top

/-- Euler's integral for the `Γ` function (of a real variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `Gamma_integral_convergent` for a proof of the convergence of the integral for `1 ≤ s`. -/
def gammaIntegral (s : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), exp (-x) * x ^ (s - 1)

/-- The integral defining the Γ function converges for real `s` with `1 ≤ s`.

This is not optimal, but the optimal bound (convergence for `0 < s`) is hard to establish with the
results currently in the library. -/
theorem Gamma_integral_convergent {s : ℝ} (h : 1 ≤ s) : IntegrableOn (fun x : ℝ => exp (-x) * x ^ (s - 1)) (Ioi 0) := by
  refine' integrable_of_is_O_exp_neg one_half_pos _ (Gamma_integrand_is_O _)
  refine' continuous_on_id.neg.exp.mul (continuous_on_id.rpow_const _)
  intro x hx
  right
  simpa only [sub_nonneg] using h

theorem Gamma_integral_one : gammaIntegral 1 = 1 := by
  simpa only [Gamma_integral, sub_self, rpow_zero, mul_oneₓ] using integral_exp_neg_Ioi

end Real

namespace Complex

/-- The integral defining the Γ function converges for complex `s` with `1 ≤ re s`.

This is proved by reduction to the real case. The bound is not optimal, but the optimal bound
(convergence for `0 < re s`) is hard to establish with the results currently in the library. -/
/- Technical note: In defining the Gamma integrand exp (-x) * x ^ (s - 1) for s complex, we have to
make a choice between ↑(real.exp (-x)), complex.exp (↑(-x)), and complex.exp (-↑x), all of which are
equal but not definitionally so. We use the first of these throughout. -/
theorem Gamma_integral_convergent {s : ℂ} (hs : 1 ≤ s.re) :
    IntegrableOn (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) := by
  -- This is slightly subtle if `s` is non-real but `s.re = 1`, as the integrand is not continuous
  -- at the lower endpoint. However, it is continuous on the interior, and its norm is continuous
  -- at the endpoint, which is good enough.
  constructor
  · refine' ContinuousOn.ae_strongly_measurable _ measurable_set_Ioi
    apply (continuous_of_real.comp continuous_neg.exp).ContinuousOn.mul
    apply ContinuousAt.continuous_on
    intro x hx
    have : ContinuousAt (fun x : ℂ => x ^ (s - 1)) ↑x := by
      apply continuous_at_cpow_const
      rw [of_real_re]
      exact Or.inl hx
    exact ContinuousAt.comp this continuous_of_real.continuous_at
    
  · rw [← has_finite_integral_norm_iff]
    refine' has_finite_integral.congr (Real.Gamma_integral_convergent hs).2 _
    refine' (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ fun x hx => _)
    dsimp only
    rw [norm_eq_abs, abs_mul, abs_of_nonneg <| le_of_ltₓ <| exp_pos <| -x, abs_cpow_eq_rpow_re_of_pos hx _]
    simp
    

/-- Euler's integral for the `Γ` function (of a complex variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `complex.Gamma_integral_convergent` for a proof of the convergence of the integral for
`1 ≤ re s`. -/
def gammaIntegral (s : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), ↑(-x).exp * ↑x ^ (s - 1)

theorem Gamma_integral_of_real (s : ℝ) : gammaIntegral ↑s = ↑s.gammaIntegral := by
  rw [Real.gammaIntegral, ← integral_of_real]
  refine' set_integral_congr measurable_set_Ioi _
  intro x hx
  dsimp only
  rw [of_real_mul, of_real_cpow (mem_Ioi.mp hx).le]
  simp

theorem Gamma_integral_one : gammaIntegral 1 = 1 := by
  rw [← of_real_one, Gamma_integral_of_real, of_real_inj]
  exact Real.Gamma_integral_one

end Complex

/-! Now we establish the recurrence relation `Γ(s + 1) = s * Γ(s)` using integration by parts. -/


namespace Complex

section GammaRecurrence

/-- The indefinite version of the Γ function, Γ(s, X) = ∫ x ∈ 0..X, exp(-x) x ^ (s - 1). -/
def partialGamma (s : ℂ) (X : ℝ) : ℂ :=
  ∫ x in 0 ..X, (-x).exp * x ^ (s - 1)

theorem tendsto_partial_Gamma {s : ℂ} (hs : 1 ≤ s.re) :
    Tendsto (fun X : ℝ => partialGamma s X) atTop (𝓝 <| gammaIntegral s) :=
  interval_integral_tendsto_integral_Ioi 0 (Gamma_integral_convergent hs) tendsto_id

private theorem Gamma_integrand_interval_integrable (s : ℂ) {X : ℝ} (hs : 1 ≤ s.re) (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) volume 0 X := by
  rw [interval_integrable_iff_integrable_Ioc_of_le hX]
  exact integrable_on.mono_set (Gamma_integral_convergent hs) Ioc_subset_Ioi_self

private theorem Gamma_integrand_deriv_integrable_A {s : ℂ} (hs : 1 ≤ s.re) {X : ℝ} (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => -((-x).exp * x ^ s) : ℝ → ℂ) volume 0 X := by
  have t := (Gamma_integrand_interval_integrable (s + 1) _ hX).neg
  · simpa using t
    
  · simp only [add_re, one_re]
    linarith
    

private theorem Gamma_integrand_deriv_integrable_B {s : ℂ} (hs : 1 ≤ s.re) {Y : ℝ} (hY : 0 ≤ Y) :
    IntervalIntegrable (fun x : ℝ => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) volume 0 Y := by
  have : (fun x => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) = (fun x => s * ((-x).exp * x ^ (s - 1)) : ℝ → ℂ) := by
    ext1
    ring
  rw [this, interval_integrable_iff_integrable_Ioc_of_le hY]
  constructor
  · refine' (continuous_on_const.mul _).AeStronglyMeasurable measurable_set_Ioc
    apply (continuous_of_real.comp continuous_neg.exp).ContinuousOn.mul
    apply ContinuousAt.continuous_on
    intro x hx
    refine' (_ : ContinuousAt (fun x : ℂ => x ^ (s - 1)) _).comp continuous_of_real.continuous_at
    apply continuous_at_cpow_const
    rw [of_real_re]
    exact Or.inl hx.1
    
  apply has_finite_integral_of_bounded
  swap
  exact s.abs * Y ^ (s.re - 1)
  refine' (ae_restrict_iff' measurable_set_Ioc).mpr (ae_of_all _ fun x hx => _)
  rw [norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (exp_pos (-x)).le]
  refine' mul_le_mul_of_nonneg_left _ (abs_nonneg s)
  have i1 : (-x).exp ≤ 1 := by
    simpa using hx.1.le
  have i2 : abs (↑x ^ (s - 1)) ≤ Y ^ (s.re - 1) := by
    rw [abs_cpow_eq_rpow_re_of_pos hx.1 _, sub_re, one_re]
    apply rpow_le_rpow hx.1.le hx.2
    linarith
  simpa using mul_le_mul i1 i2 (abs_nonneg (↑x ^ (s - 1))) zero_le_one

/-- The recurrence relation for the indefinite version of the Γ function. -/
theorem partial_Gamma_add_one {s : ℂ} (hs : 1 ≤ s.re) {X : ℝ} (hX : 0 ≤ X) :
    partialGamma (s + 1) X = s * partialGamma s X - (-X).exp * X ^ s := by
  rw [partial_Gamma, partial_Gamma, add_sub_cancel]
  have F_der_I :
    ∀ x : ℝ,
      x ∈ Ioo 0 X →
        HasDerivAt (fun x => (-x).exp * x ^ s : ℝ → ℂ) (-((-x).exp * x ^ s) + (-x).exp * (s * x ^ (s - 1))) x :=
    by
    intro x hx
    have d1 : HasDerivAt (fun y : ℝ => (-y).exp) (-(-x).exp) x := by
      simpa using (has_deriv_at_neg x).exp
    have d1b : HasDerivAt (fun y => ↑(-y).exp : ℝ → ℂ) (↑(-(-x).exp)) x := by
      convert HasDerivAt.scomp x of_real_clm.has_deriv_at d1
      simp
    have d2 : HasDerivAt (fun y : ℝ => ↑y ^ s) (s * x ^ (s - 1)) x := by
      have t := @HasDerivAt.cpow_const _ _ _ s (has_deriv_at_id ↑x)
      simp only [id.def, of_real_re, of_real_im, Ne.def, eq_self_iff_true, not_true, or_falseₓ, mul_oneₓ] at t
      simpa using HasDerivAt.comp x (t hx.left) of_real_clm.has_deriv_at
    simpa only [of_real_neg, neg_mul] using d1b.mul d2
  have cont :=
    (continuous_of_real.comp continuous_neg.exp).mul (continuous_of_real_cpow_const <| lt_of_lt_of_leₓ zero_lt_one hs)
  have der_ible := (Gamma_integrand_deriv_integrable_A hs hX).add (Gamma_integrand_deriv_integrable_B hs hX)
  have int_eval := integral_eq_sub_of_has_deriv_at_of_le hX cont.continuous_on F_der_I der_ible
  -- We are basically done here but manipulating the output into the right form is fiddly.
  apply_fun fun x : ℂ => -x  at int_eval
  rw
    [intervalIntegral.integral_add (Gamma_integrand_deriv_integrable_A hs hX)
      (Gamma_integrand_deriv_integrable_B hs hX),
    intervalIntegral.integral_neg, neg_add, neg_negₓ] at int_eval
  replace int_eval := eq_sub_of_add_eq int_eval
  rw [int_eval, sub_neg_eq_add, neg_sub, add_commₓ, add_sub]
  simp only [sub_left_inj, add_left_injₓ]
  have : (fun x => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) = (fun x => s * (-x).exp * x ^ (s - 1) : ℝ → ℂ) := by
    ext1
    ring
  rw [this]
  have t := @integral_const_mul (0 : ℝ) X volume _ _ s fun x : ℝ => (-x).exp * x ^ (s - 1)
  dsimp  at t
  rw [← t, of_real_zero, zero_cpow]
  · rw [mul_zero, add_zeroₓ]
    congr
    ext1
    ring
    
  · contrapose! hs
    rw [hs, zero_re]
    exact zero_lt_one
    

/-- The recurrence relation for the Γ integral. -/
theorem Gamma_integral_add_one {s : ℂ} (hs : 1 ≤ s.re) : gammaIntegral (s + 1) = s * gammaIntegral s := by
  suffices tendsto (s + 1).partialGamma at_top (𝓝 <| s * Gamma_integral s) by
    refine' tendsto_nhds_unique _ this
    apply tendsto_partial_Gamma
    rw [add_re, one_re]
    linarith
  have : (fun X : ℝ => s * partial_Gamma s X - X ^ s * (-X).exp) =ᶠ[at_top] (s + 1).partialGamma := by
    apply eventually_eq_of_mem (Ici_mem_at_top (0 : ℝ))
    intro X hX
    rw [partial_Gamma_add_one hs (mem_Ici.mp hX)]
    ring_nf
  refine' tendsto.congr' this _
  suffices tendsto (fun X => -(X ^ s) * (-X).exp : ℝ → ℂ) at_top (𝓝 0) by
    simpa using tendsto.add (tendsto.const_mul s (tendsto_partial_Gamma hs)) this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have : (fun e : ℝ => ∥-((e : ℂ) ^ s) * (-e).exp∥) =ᶠ[at_top] fun e : ℝ => e ^ s.re * (-1 * e).exp := by
    refine' eventually_eq_of_mem (Ioi_mem_at_top 0) _
    intro x hx
    dsimp only
    rw [norm_eq_abs, abs_mul, abs_neg, abs_cpow_eq_rpow_re_of_pos hx, abs_of_nonneg (exp_pos (-x)).le, neg_mul,
      one_mulₓ]
  exact (tendsto_congr' this).mpr (tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0 _ _ zero_lt_one)

end GammaRecurrence

/-! Now we define `Γ(s)` on the whole complex plane, by recursion. -/


section GammaDef

/-- Th `n`th function in this family is `Γ(s)` if `1-n ≤ s.re`, and junk otherwise. -/
noncomputable def gammaAux : ℕ → ℂ → ℂ
  | 0 => gammaIntegral
  | n + 1 => fun s : ℂ => Gamma_aux n (s + 1) / s

theorem Gamma_aux_recurrence1 (s : ℂ) (n : ℕ) (h1 : 1 - s.re ≤ ↑n) : gammaAux n s = gammaAux n (s + 1) / s := by
  induction' n with n hn generalizing s
  · simp only [Nat.cast_zeroₓ, sub_nonpos] at h1
    dsimp only [Gamma_aux]
    rw [Gamma_integral_add_one h1]
    rw [mul_comm, mul_div_cancel]
    contrapose! h1
    rw [h1]
    simp
    
  · dsimp only [Gamma_aux]
    have hh1 : 1 - (s + 1).re ≤ n := by
      rw [Nat.succ_eq_add_one, Nat.cast_addₓ, Nat.cast_oneₓ] at h1
      rw [add_re, one_re]
      linarith
    rw [← hn (s + 1) hh1]
    

theorem Gamma_aux_recurrence2 (s : ℂ) (n : ℕ) (h1 : 1 - s.re ≤ ↑n) : gammaAux n s = gammaAux (n + 1) s := by
  cases n
  · simp only [Nat.cast_zeroₓ, sub_nonpos] at h1
    dsimp only [Gamma_aux]
    rw [Gamma_integral_add_one h1]
    have : s ≠ 0 := by
      contrapose! h1
      rw [h1]
      simp
    field_simp
    ring
    
  · dsimp only [Gamma_aux]
    have : Gamma_aux n (s + 1 + 1) / (s + 1) = Gamma_aux n (s + 1) := by
      have hh1 : 1 - (s + 1).re ≤ n := by
        rw [Nat.succ_eq_add_one, Nat.cast_addₓ, Nat.cast_oneₓ] at h1
        rw [add_re, one_re]
        linarith
      rw [Gamma_aux_recurrence1 (s + 1) n hh1]
    rw [this]
    

/-- The `Γ` function (of a complex variable `s`). -/
def gamma (s : ℂ) : ℂ :=
  gammaAux ⌈1 - s.re⌉₊ s

theorem Gamma_eq_Gamma_aux (s : ℂ) (n : ℕ) (h1 : 1 - s.re ≤ ↑n) : gamma s = gammaAux n s := by
  have u : ∀ k : ℕ, Gamma_aux (⌈1 - s.re⌉₊ + k) s = Gamma s := by
    intro k
    induction' k with k hk
    · simp [Gamma]
      
    · rw [← hk, Nat.succ_eq_add_one, ← add_assocₓ]
      refine' (Gamma_aux_recurrence2 s (⌈1 - s.re⌉₊ + k) _).symm
      rw [Nat.cast_addₓ]
      have i1 := Nat.le_ceil (1 - s.re)
      refine' le_add_of_le_of_nonneg i1 _
      rw [← Nat.cast_zeroₓ, Nat.cast_le]
      exact Nat.zero_leₓ k
      
  rw [← Nat.add_sub_of_leₓ (nat.ceil_le.mpr h1), u (n - ⌈1 - s.re⌉₊)]

/-- The recurrence relation for the Γ function. -/
theorem Gamma_add_one (s : ℂ) (h2 : s ≠ 0) : gamma (s + 1) = s * gamma s := by
  let n := ⌈1 - s.re⌉₊
  have t1 : 1 - s.re ≤ n := Nat.le_ceil (1 - s.re)
  have t2 : 1 - (s + 1).re ≤ n := by
    rw [add_re, one_re]
    linarith
  rw [Gamma_eq_Gamma_aux s n t1, Gamma_eq_Gamma_aux (s + 1) n t2, Gamma_aux_recurrence1 s n t1]
  field_simp
  ring

theorem Gamma_eq_integral (s : ℂ) (hs : 1 ≤ s.re) : gamma s = gammaIntegral s := by
  refine' Gamma_eq_Gamma_aux s 0 (_ : _ ≤ 0)
  linarith

theorem Gamma_nat_eq_factorial (n : ℕ) : gamma (n + 1) = Nat.factorial n := by
  induction' n with n hn
  · rw [Nat.cast_zeroₓ, zero_addₓ]
    rw [Gamma_eq_integral]
    simpa using Gamma_integral_one
    simp
    
  rw [Gamma_add_one n.succ <| nat.cast_ne_zero.mpr <| Nat.succ_ne_zero n]
  · simp only [Nat.cast_succₓ, Nat.factorial_succ, Nat.cast_mulₓ]
    congr
    exact hn
    

end GammaDef

end Complex

