/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import MeasureTheory.Integral.ExpDecay
import Analysis.SpecialFunctions.ImproperIntegrals
import Analysis.MellinTransform

#align_import analysis.special_functions.gamma.basic from "leanprover-community/mathlib"@"8af7091a43227e179939ba132e54e54e9f3b089a"

/-!
# The Gamma function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

open scoped Nat Topology ComplexConjugate

namespace Real

#print Real.Gamma_integrand_isLittleO /-
/-- Asymptotic bound for the `Γ` function integrand. -/
theorem Gamma_integrand_isLittleO (s : ℝ) :
    (fun x : ℝ => exp (-x) * x ^ s) =o[atTop] fun x : ℝ => exp (-(1 / 2) * x) :=
  by
  refine' is_o_of_tendsto (fun x hx => _) _
  · exfalso; exact (exp_pos (-(1 / 2) * x)).ne' hx
  have :
    (fun x : ℝ => NormedSpace.exp (-x) * x ^ s / NormedSpace.exp (-(1 / 2) * x)) =
      (fun x : ℝ => NormedSpace.exp (1 / 2 * x) / x ^ s)⁻¹ :=
    by
    ext1 x
    field_simp [exp_ne_zero, NormedSpace.exp_neg, ← Real.exp_add]
    left
    ring
  rw [this]
  exact (tendsto_exp_mul_div_rpow_atTop s (1 / 2) one_half_pos).inv_tendsto_atTop
#align real.Gamma_integrand_is_o Real.Gamma_integrand_isLittleO
-/

#print Real.GammaIntegral_convergent /-
/-- The Euler integral for the `Γ` function converges for positive real `s`. -/
theorem GammaIntegral_convergent {s : ℝ} (h : 0 < s) :
    IntegrableOn (fun x : ℝ => exp (-x) * x ^ (s - 1)) (Ioi 0) :=
  by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrable_on_union]
  constructor
  · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    refine' integrable_on.continuous_on_mul continuous_on_id.neg.exp _ is_compact_Icc
    refine' (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp _
    exact interval_integrable_rpow' (by linarith)
  · refine' integrable_of_isBigO_exp_neg one_half_pos _ (Gamma_integrand_is_o _).IsBigO
    refine' continuous_on_id.neg.exp.mul (continuous_on_id.rpow_const _)
    intro x hx
    exact Or.inl ((zero_lt_one : (0 : ℝ) < 1).trans_le hx).ne'
#align real.Gamma_integral_convergent Real.GammaIntegral_convergent
-/

end Real

namespace Complex

#print Complex.GammaIntegral_convergent /-
/- Technical note: In defining the Gamma integrand exp (-x) * x ^ (s - 1) for s complex, we have to
make a choice between ↑(real.exp (-x)), complex.exp (↑(-x)), and complex.exp (-↑x), all of which are
equal but not definitionally so. We use the first of these throughout. -/
/-- The integral defining the `Γ` function converges for complex `s` with `0 < re s`.

This is proved by reduction to the real case. -/
theorem GammaIntegral_convergent {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) :=
  by
  constructor
  · refine' ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply (continuous_of_real.comp continuous_neg.exp).ContinuousOn.mul
    apply ContinuousAt.continuousOn
    intro x hx
    have : ContinuousAt (fun x : ℂ => x ^ (s - 1)) ↑x := by apply continuousAt_cpow_const;
      rw [of_real_re]; exact Or.inl hx
    exact ContinuousAt.comp this continuous_of_real.continuous_at
  · rw [← has_finite_integral_norm_iff]
    refine' has_finite_integral.congr (Real.GammaIntegral_convergent hs).2 _
    refine' (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => _)
    dsimp only
    rw [norm_eq_abs, map_mul, abs_of_nonneg <| le_of_lt <| exp_pos <| -x,
      abs_cpow_eq_rpow_re_of_pos hx _]
    simp
#align complex.Gamma_integral_convergent Complex.GammaIntegral_convergent
-/

#print Complex.GammaIntegral /-
/-- Euler's integral for the `Γ` function (of a complex variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `complex.Gamma_integral_convergent` for a proof of the convergence of the integral for
`0 < re s`. -/
def GammaIntegral (s : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), ↑(-x).exp * ↑x ^ (s - 1)
#align complex.Gamma_integral Complex.GammaIntegral
-/

#print Complex.GammaIntegral_conj /-
theorem GammaIntegral_conj (s : ℂ) : GammaIntegral (conj s) = conj (GammaIntegral s) :=
  by
  rw [Gamma_integral, Gamma_integral, ← integral_conj]
  refine' set_integral_congr measurableSet_Ioi fun x hx => _
  dsimp only
  rw [RingHom.map_mul, conj_of_real, cpow_def_of_ne_zero (of_real_ne_zero.mpr (ne_of_gt hx)),
    cpow_def_of_ne_zero (of_real_ne_zero.mpr (ne_of_gt hx)), ← NormedSpace.exp_conj,
    RingHom.map_mul, ← of_real_log (le_of_lt hx), conj_of_real, RingHom.map_sub, RingHom.map_one]
#align complex.Gamma_integral_conj Complex.GammaIntegral_conj
-/

#print Complex.GammaIntegral_ofReal /-
theorem GammaIntegral_ofReal (s : ℝ) :
    GammaIntegral ↑s = ↑(∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ (s - 1)) :=
  by
  rw [Gamma_integral, ← _root_.integral_of_real]
  refine' set_integral_congr measurableSet_Ioi _
  intro x hx; dsimp only
  rw [of_real_mul, of_real_cpow (mem_Ioi.mp hx).le]
  simp
#align complex.Gamma_integral_of_real Complex.GammaIntegral_ofReal
-/

#print Complex.GammaIntegral_one /-
theorem GammaIntegral_one : GammaIntegral 1 = 1 := by
  simpa only [← of_real_one, Gamma_integral_of_real, of_real_inj, sub_self, rpow_zero,
    mul_one] using integral_exp_neg_Ioi_zero
#align complex.Gamma_integral_one Complex.GammaIntegral_one
-/

end Complex

/-! Now we establish the recurrence relation `Γ(s + 1) = s * Γ(s)` using integration by parts. -/


namespace Complex

section GammaRecurrence

#print Complex.partialGamma /-
/-- The indefinite version of the `Γ` function, `Γ(s, X) = ∫ x ∈ 0..X, exp(-x) x ^ (s - 1)`. -/
def partialGamma (s : ℂ) (X : ℝ) : ℂ :=
  ∫ x in 0 ..X, (-x).exp * x ^ (s - 1)
#align complex.partial_Gamma Complex.partialGamma
-/

#print Complex.tendsto_partialGamma /-
theorem tendsto_partialGamma {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun X : ℝ => partialGamma s X) atTop (𝓝 <| GammaIntegral s) :=
  intervalIntegral_tendsto_integral_Ioi 0 (GammaIntegral_convergent hs) tendsto_id
#align complex.tendsto_partial_Gamma Complex.tendsto_partialGamma
-/

private theorem Gamma_integrand_interval_integrable (s : ℂ) {X : ℝ} (hs : 0 < s.re) (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) volume 0 X :=
  by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX]
  exact integrable_on.mono_set (Gamma_integral_convergent hs) Ioc_subset_Ioi_self

private theorem Gamma_integrand_deriv_integrable_A {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => -((-x).exp * x ^ s) : ℝ → ℂ) volume 0 X :=
  by
  convert (Gamma_integrand_interval_integrable (s + 1) _ hX).neg
  · ext1; simp only [add_sub_cancel_right, Pi.neg_apply]
  · simp only [add_re, one_re]; linarith

private theorem Gamma_integrand_deriv_integrable_B {s : ℂ} (hs : 0 < s.re) {Y : ℝ} (hY : 0 ≤ Y) :
    IntervalIntegrable (fun x : ℝ => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) volume 0 Y :=
  by
  have :
    (fun x => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) =
      (fun x => s * ((-x).exp * x ^ (s - 1)) : ℝ → ℂ) :=
    by ext1; ring
  rw [this, intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
  constructor
  · refine' (continuous_on_const.mul _).AEStronglyMeasurable measurableSet_Ioc
    apply (continuous_of_real.comp continuous_neg.exp).ContinuousOn.mul
    apply ContinuousAt.continuousOn
    intro x hx
    refine' (_ : ContinuousAt (fun x : ℂ => x ^ (s - 1)) _).comp continuous_of_real.continuous_at
    apply continuousAt_cpow_const; rw [of_real_re]; exact Or.inl hx.1
  rw [← has_finite_integral_norm_iff]
  simp_rw [norm_eq_abs, map_mul]
  refine'
    (((Real.GammaIntegral_convergent hs).mono_set Ioc_subset_Ioi_self).HasFiniteIntegral.congr
          _).const_mul
      _
  rw [eventually_eq, ae_restrict_iff']
  · apply ae_of_all; intro x hx
    rw [abs_of_nonneg (exp_pos _).le, abs_cpow_eq_rpow_re_of_pos hx.1]
    simp
  · exact measurableSet_Ioc

#print Complex.partialGamma_add_one /-
/-- The recurrence relation for the indefinite version of the `Γ` function. -/
theorem partialGamma_add_one {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 0 ≤ X) :
    partialGamma (s + 1) X = s * partialGamma s X - (-X).exp * X ^ s :=
  by
  rw [partial_Gamma, partial_Gamma, add_sub_cancel_right]
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
  apply_fun fun x : ℂ => -x at int_eval
  rw [intervalIntegral.integral_add (Gamma_integrand_deriv_integrable_A hs hX)
      (Gamma_integrand_deriv_integrable_B hs hX),
    intervalIntegral.integral_neg, neg_add, neg_neg] at int_eval
  rw [eq_sub_of_add_eq int_eval, sub_neg_eq_add, neg_sub, add_comm, add_sub]
  simp only [sub_left_inj, add_left_inj]
  have :
    (fun x => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) =
      (fun x => s * (-x).exp * x ^ (s - 1) : ℝ → ℂ) :=
    by ext1; ring
  rw [this]
  have t := @integral_const_mul 0 X volume _ _ s fun x : ℝ => (-x).exp * x ^ (s - 1)
  dsimp at t; rw [← t, of_real_zero, zero_cpow]
  · rw [MulZeroClass.mul_zero, add_zero]; congr; ext1; ring
  · contrapose! hs; rw [hs, zero_re]
#align complex.partial_Gamma_add_one Complex.partialGamma_add_one
-/

#print Complex.GammaIntegral_add_one /-
/-- The recurrence relation for the `Γ` integral. -/
theorem GammaIntegral_add_one {s : ℂ} (hs : 0 < s.re) :
    GammaIntegral (s + 1) = s * GammaIntegral s :=
  by
  suffices tendsto (s + 1).partialGamma at_top (𝓝 <| s * Gamma_integral s)
    by
    refine' tendsto_nhds_unique _ this
    apply tendsto_partial_Gamma; rw [add_re, one_re]; linarith
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
    intro x hx; dsimp only
    rw [norm_eq_abs, map_mul, abs.map_neg, abs_cpow_eq_rpow_re_of_pos hx,
      abs_of_nonneg (exp_pos (-x)).le, neg_mul, one_mul]
  exact (tendsto_congr' this).mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ zero_lt_one)
#align complex.Gamma_integral_add_one Complex.GammaIntegral_add_one
-/

end GammaRecurrence

/-! Now we define `Γ(s)` on the whole complex plane, by recursion. -/


section GammaDef

#print Complex.GammaAux /-
/-- The `n`th function in this family is `Γ(s)` if `-n < s.re`, and junk otherwise. -/
noncomputable def GammaAux : ℕ → ℂ → ℂ
  | 0 => GammaIntegral
  | n + 1 => fun s : ℂ => Gamma_aux n (s + 1) / s
#align complex.Gamma_aux Complex.GammaAux
-/

#print Complex.GammaAux_recurrence1 /-
theorem GammaAux_recurrence1 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
    GammaAux n s = GammaAux n (s + 1) / s :=
  by
  induction' n with n hn generalizing s
  · simp only [Nat.cast_zero, neg_lt_zero] at h1
    dsimp only [Gamma_aux]; rw [Gamma_integral_add_one h1]
    rw [mul_comm, mul_div_cancel_right₀]; contrapose! h1; rw [h1]
    simp
  · dsimp only [Gamma_aux]
    have hh1 : -(s + 1).re < n :=
      by
      rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at h1
      rw [add_re, one_re]; linarith
    rw [← hn (s + 1) hh1]
#align complex.Gamma_aux_recurrence1 Complex.GammaAux_recurrence1
-/

#print Complex.GammaAux_recurrence2 /-
theorem GammaAux_recurrence2 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
    GammaAux n s = GammaAux (n + 1) s := by
  cases n
  · simp only [Nat.cast_zero, neg_lt_zero] at h1
    dsimp only [Gamma_aux]
    rw [Gamma_integral_add_one h1, mul_div_cancel_left₀]
    rintro rfl
    rw [zero_re] at h1
    exact h1.false
  · dsimp only [Gamma_aux]
    have : Gamma_aux n (s + 1 + 1) / (s + 1) = Gamma_aux n (s + 1) :=
      by
      have hh1 : -(s + 1).re < n :=
        by
        rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at h1
        rw [add_re, one_re]; linarith
      rw [Gamma_aux_recurrence1 (s + 1) n hh1]
    rw [this]
#align complex.Gamma_aux_recurrence2 Complex.GammaAux_recurrence2
-/

#print Complex.Gamma /-
/-- The `Γ` function (of a complex variable `s`). -/
@[pp_nodot]
def Gamma (s : ℂ) : ℂ :=
  GammaAux ⌊1 - s.re⌋₊ s
#align complex.Gamma Complex.Gamma
-/

#print Complex.Gamma_eq_GammaAux /-
theorem Gamma_eq_GammaAux (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) : Gamma s = GammaAux n s :=
  by
  have u : ∀ k : ℕ, Gamma_aux (⌊1 - s.re⌋₊ + k) s = CongruenceSubgroup.Gamma s :=
    by
    intro k; induction' k with k hk
    · simp [CongruenceSubgroup.Gamma]
    · rw [← hk, Nat.succ_eq_add_one, ← add_assoc]
      refine' (Gamma_aux_recurrence2 s (⌊1 - s.re⌋₊ + k) _).symm
      rw [Nat.cast_add]
      have i0 := Nat.sub_one_lt_floor (1 - s.re)
      simp only [sub_sub_cancel_left] at i0
      refine' lt_add_of_lt_of_nonneg i0 _
      rw [← Nat.cast_zero, Nat.cast_le]; exact Nat.zero_le k
  convert (u <| n - ⌊1 - s.re⌋₊).symm; rw [Nat.add_sub_of_le]
  by_cases 0 ≤ 1 - s.re
  · apply Nat.le_of_lt_succ
    exact_mod_cast lt_of_le_of_lt (Nat.floor_le h) (by linarith : 1 - s.re < n + 1)
  · rw [Nat.floor_of_nonpos]; linarith; linarith
#align complex.Gamma_eq_Gamma_aux Complex.Gamma_eq_GammaAux
-/

#print Complex.Gamma_add_one /-
/-- The recurrence relation for the `Γ` function. -/
theorem Gamma_add_one (s : ℂ) (h2 : s ≠ 0) : Gamma (s + 1) = s * Gamma s :=
  by
  let n := ⌊1 - s.re⌋₊
  have t1 : -s.re < n := by simpa only [sub_sub_cancel_left] using Nat.sub_one_lt_floor (1 - s.re)
  have t2 : -(s + 1).re < n := by rw [add_re, one_re]; linarith
  rw [Gamma_eq_Gamma_aux s n t1, Gamma_eq_Gamma_aux (s + 1) n t2, Gamma_aux_recurrence1 s n t1]
  field_simp; ring
#align complex.Gamma_add_one Complex.Gamma_add_one
-/

#print Complex.Gamma_eq_integral /-
theorem Gamma_eq_integral {s : ℂ} (hs : 0 < s.re) : Gamma s = GammaIntegral s :=
  Gamma_eq_GammaAux s 0 (by norm_cast; linarith)
#align complex.Gamma_eq_integral Complex.Gamma_eq_integral
-/

#print Complex.Gamma_one /-
theorem Gamma_one : Gamma 1 = 1 := by rw [Gamma_eq_integral]; simpa using Gamma_integral_one; simp
#align complex.Gamma_one Complex.Gamma_one
-/

#print Complex.Gamma_nat_eq_factorial /-
theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n + 1) = n ! :=
  by
  induction' n with n hn
  · simpa using Gamma_one
  · rw [Gamma_add_one n.succ <| nat.cast_ne_zero.mpr <| Nat.succ_ne_zero n]
    simp only [Nat.cast_succ, Nat.factorial_succ, Nat.cast_mul]; congr; exact hn
#align complex.Gamma_nat_eq_factorial Complex.Gamma_nat_eq_factorial
-/

#print Complex.Gamma_zero /-
/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
theorem Gamma_zero : Gamma 0 = 0 := by
  simp_rw [CongruenceSubgroup.Gamma, zero_re, sub_zero, Nat.floor_one, Gamma_aux, div_zero]
#align complex.Gamma_zero Complex.Gamma_zero
-/

#print Complex.Gamma_neg_nat_eq_zero /-
/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value 0. -/
theorem Gamma_neg_nat_eq_zero (n : ℕ) : Gamma (-n) = 0 :=
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
#align complex.Gamma_neg_nat_eq_zero Complex.Gamma_neg_nat_eq_zero
-/

#print Complex.Gamma_conj /-
theorem Gamma_conj (s : ℂ) : Gamma (conj s) = conj (Gamma s) :=
  by
  suffices : ∀ (n : ℕ) (s : ℂ), Gamma_aux n (conj s) = conj (Gamma_aux n s); exact this _ _
  intro n
  induction' n with n IH
  · rw [Gamma_aux]; exact Gamma_integral_conj
  · intro s
    rw [Gamma_aux]
    dsimp only
    rw [div_eq_mul_inv _ s, RingHom.map_mul, conj_inv, ← div_eq_mul_inv]
    suffices conj s + 1 = conj (s + 1) by rw [this, IH]
    rw [RingHom.map_add, RingHom.map_one]
#align complex.Gamma_conj Complex.Gamma_conj
-/

end GammaDef

/-! Now check that the `Γ` function is differentiable, wherever this makes sense. -/


section GammaHasDeriv

#print Complex.GammaIntegral_eq_mellin /-
/-- Rewrite the Gamma integral as an example of a Mellin transform. -/
theorem GammaIntegral_eq_mellin : GammaIntegral = mellin fun x => Real.exp (-x) :=
  funext fun s => by simp only [mellin, Gamma_integral, smul_eq_mul, mul_comm]
#align complex.Gamma_integral_eq_mellin Complex.GammaIntegral_eq_mellin
-/

#print Complex.hasDerivAt_GammaIntegral /-
/-- The derivative of the `Γ` integral, at any `s ∈ ℂ` with `1 < re s`, is given by the Melllin
transform of `log t * exp (-t)`. -/
theorem hasDerivAt_GammaIntegral {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt GammaIntegral (∫ t : ℝ in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t))) s :=
  by
  rw [Gamma_integral_eq_mellin]
  convert (mellin_hasDerivAt_of_isBigO_rpow _ _ (lt_add_one _) _ hs).2
  · refine' (Continuous.continuousOn _).LocallyIntegrableOn measurableSet_Ioi
    exact continuous_of_real.comp (real.continuous_exp.comp continuous_neg)
  · rw [← is_O_norm_left]
    simp_rw [Complex.norm_eq_abs, abs_of_real, ← Real.norm_eq_abs, is_O_norm_left]
    simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).IsBigO
  · simp_rw [neg_zero, rpow_zero]
    refine' is_O_const_of_tendsto (_ : tendsto _ _ (𝓝 1)) one_ne_zero
    rw [(by simp : (1 : ℂ) = Real.exp (-0))]
    exact (continuous_of_real.comp (real.continuous_exp.comp continuous_neg)).ContinuousWithinAt
#align complex.has_deriv_at_Gamma_integral Complex.hasDerivAt_GammaIntegral
-/

#print Complex.differentiableAt_GammaAux /-
theorem differentiableAt_GammaAux (s : ℂ) (n : ℕ) (h1 : 1 - s.re < n) (h2 : ∀ m : ℕ, s ≠ -m) :
    DifferentiableAt ℂ (GammaAux n) s :=
  by
  induction' n with n hn generalizing s
  · refine' (has_deriv_at_Gamma_integral _).DifferentiableAt
    rw [Nat.cast_zero] at h1; linarith
  · dsimp only [Gamma_aux]
    specialize hn (s + 1)
    have a : 1 - (s + 1).re < ↑n := by rw [Nat.cast_succ] at h1;
      rw [Complex.add_re, Complex.one_re]; linarith
    have b : ∀ m : ℕ, s + 1 ≠ -m := by
      intro m; have := h2 (1 + m)
      contrapose! this
      rw [← eq_sub_iff_add_eq] at this
      simpa using this
    refine' DifferentiableAt.div (DifferentiableAt.comp _ (hn a b) _) _ _
    simp; simp; simpa using h2 0
#align complex.differentiable_at_Gamma_aux Complex.differentiableAt_GammaAux
-/

#print Complex.differentiableAt_Gamma /-
theorem differentiableAt_Gamma (s : ℂ) (hs : ∀ m : ℕ, s ≠ -m) : DifferentiableAt ℂ Gamma s :=
  by
  let n := ⌊1 - s.re⌋₊ + 1
  have hn : 1 - s.re < n := by exact_mod_cast Nat.lt_floor_add_one (1 - s.re)
  apply (differentiable_at_Gamma_aux s n hn hs).congr_of_eventuallyEq
  let S := {t : ℂ | 1 - t.re < n}
  have : S ∈ 𝓝 s := by
    rw [mem_nhds_iff]; use S
    refine' ⟨subset.rfl, _, hn⟩
    have : S = re ⁻¹' Ioi (1 - n : ℝ) := by ext;
      rw [preimage, Ioi, mem_set_of_eq, mem_set_of_eq, mem_set_of_eq]; exact sub_lt_comm
    rw [this]
    refine' Continuous.isOpen_preimage continuous_re _ isOpen_Ioi
  apply eventually_eq_of_mem this
  intro t ht; rw [mem_set_of_eq] at ht
  apply Gamma_eq_Gamma_aux; linarith
#align complex.differentiable_at_Gamma Complex.differentiableAt_Gamma
-/

end GammaHasDeriv

#print Complex.tendsto_self_mul_Gamma_nhds_zero /-
/-- At `s = 0`, the Gamma function has a simple pole with residue 1. -/
theorem tendsto_self_mul_Gamma_nhds_zero : Tendsto (fun z : ℂ => z * Gamma z) (𝓝[≠] 0) (𝓝 1) :=
  by
  rw [show 𝓝 (1 : ℂ) = 𝓝 (CongruenceSubgroup.Gamma (0 + 1)) by
      simp only [zero_add, Complex.Gamma_one]]
  convert
    (tendsto.mono_left _ nhdsWithin_le_nhds).congr'
      (eventually_eq_of_mem self_mem_nhdsWithin Complex.Gamma_add_one)
  refine' ContinuousAt.comp _ (continuous_id.add continuous_const).ContinuousAt
  refine' (Complex.differentiableAt_Gamma _ fun m => _).ContinuousAt
  rw [zero_add, ← of_real_nat_cast, ← of_real_neg, ← of_real_one, Ne.def, of_real_inj]
  refine' (lt_of_le_of_lt _ zero_lt_one).ne'
  exact neg_nonpos.mpr (Nat.cast_nonneg _)
#align complex.tendsto_self_mul_Gamma_nhds_zero Complex.tendsto_self_mul_Gamma_nhds_zero
-/

end Complex

namespace Real

#print Real.Gamma /-
/-- The `Γ` function (of a real variable `s`). -/
@[pp_nodot]
def Gamma (s : ℝ) : ℝ :=
  (Complex.Gamma s).re
#align real.Gamma Real.Gamma
-/

#print Real.Gamma_eq_integral /-
theorem Gamma_eq_integral {s : ℝ} (hs : 0 < s) : Gamma s = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1) :=
  by
  rw [CongruenceSubgroup.Gamma,
    Complex.Gamma_eq_integral (by rwa [Complex.ofReal_re] : 0 < Complex.re s)]
  dsimp only [Complex.GammaIntegral]
  simp_rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
  suffices
    ∫ x : ℝ in Ioi 0, ↑(NormedSpace.exp (-x)) * (x : ℂ) ^ ((s - 1 : ℝ) : ℂ) =
      ∫ x : ℝ in Ioi 0, ((NormedSpace.exp (-x) * x ^ (s - 1) : ℝ) : ℂ)
    by rw [this, _root_.integral_of_real, Complex.ofReal_re]
  refine' set_integral_congr measurableSet_Ioi fun x hx => _
  push_cast
  rw [Complex.ofReal_cpow (le_of_lt hx)]
  push_cast
#align real.Gamma_eq_integral Real.Gamma_eq_integral
-/

#print Real.Gamma_add_one /-
theorem Gamma_add_one {s : ℝ} (hs : s ≠ 0) : Gamma (s + 1) = s * Gamma s :=
  by
  simp_rw [CongruenceSubgroup.Gamma]
  rw [Complex.ofReal_add, Complex.ofReal_one, Complex.Gamma_add_one, Complex.re_ofReal_mul]
  rwa [Complex.ofReal_ne_zero]
#align real.Gamma_add_one Real.Gamma_add_one
-/

#print Real.Gamma_one /-
theorem Gamma_one : Gamma 1 = 1 := by
  rw [CongruenceSubgroup.Gamma, Complex.ofReal_one, Complex.Gamma_one, Complex.one_re]
#align real.Gamma_one Real.Gamma_one
-/

#print Complex.Gamma_ofReal /-
theorem Complex.Gamma_ofReal (s : ℝ) : Complex.Gamma (s : ℂ) = Gamma s := by
  rw [CongruenceSubgroup.Gamma, eq_comm, ← Complex.conj_eq_iff_re, ← Complex.Gamma_conj,
    Complex.conj_ofReal]
#align complex.Gamma_of_real Complex.Gamma_ofReal
-/

#print Real.Gamma_nat_eq_factorial /-
theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n + 1) = n ! := by
  rw [CongruenceSubgroup.Gamma, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.Gamma_nat_eq_factorial, ← Complex.ofReal_natCast, Complex.ofReal_re]
#align real.Gamma_nat_eq_factorial Real.Gamma_nat_eq_factorial
-/

#print Real.Gamma_zero /-
/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
theorem Gamma_zero : Gamma 0 = 0 := by
  simpa only [← Complex.ofReal_zero, Complex.Gamma_ofReal, Complex.ofReal_inj] using
    Complex.Gamma_zero
#align real.Gamma_zero Real.Gamma_zero
-/

#print Real.Gamma_neg_nat_eq_zero /-
/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value `0`.
-/
theorem Gamma_neg_nat_eq_zero (n : ℕ) : Gamma (-n) = 0 := by
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.Gamma_ofReal,
    Complex.ofReal_eq_zero] using Complex.Gamma_neg_nat_eq_zero n
#align real.Gamma_neg_nat_eq_zero Real.Gamma_neg_nat_eq_zero
-/

#print Real.Gamma_pos_of_pos /-
theorem Gamma_pos_of_pos {s : ℝ} (hs : 0 < s) : 0 < Gamma s :=
  by
  rw [Gamma_eq_integral hs]
  have : (Function.support fun x : ℝ => NormedSpace.exp (-x) * x ^ (s - 1)) ∩ Ioi 0 = Ioi 0 :=
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
#align real.Gamma_pos_of_pos Real.Gamma_pos_of_pos
-/

#print Real.Gamma_ne_zero /-
/-- The Gamma function does not vanish on `ℝ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
theorem Gamma_ne_zero {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : Gamma s ≠ 0 :=
  by
  suffices ∀ {n : ℕ}, -(n : ℝ) < s → CongruenceSubgroup.Gamma s ≠ 0
    by
    apply this
    swap; use⌊-s⌋₊ + 1
    rw [neg_lt, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  intro n
  induction n generalizing s
  · intro hs
    refine' (Gamma_pos_of_pos _).ne'
    rwa [Nat.cast_zero, neg_zero] at hs
  · intro hs'
    have : CongruenceSubgroup.Gamma (s + 1) ≠ 0 :=
      by
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
#align real.Gamma_ne_zero Real.Gamma_ne_zero
-/

#print Real.Gamma_eq_zero_iff /-
theorem Gamma_eq_zero_iff (s : ℝ) : Gamma s = 0 ↔ ∃ m : ℕ, s = -m :=
  ⟨by contrapose!; exact Gamma_ne_zero, by rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m⟩
#align real.Gamma_eq_zero_iff Real.Gamma_eq_zero_iff
-/

#print Real.differentiableAt_Gamma /-
theorem differentiableAt_Gamma {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : DifferentiableAt ℝ Gamma s :=
  by
  refine' (Complex.differentiableAt_Gamma _ _).HasDerivAt.real_of_complex.DifferentiableAt
  simp_rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Ne.def, Complex.ofReal_inj]
  exact hs
#align real.differentiable_at_Gamma Real.differentiableAt_Gamma
-/

end Real

