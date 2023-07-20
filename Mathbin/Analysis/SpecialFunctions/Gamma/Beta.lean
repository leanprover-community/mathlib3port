/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathbin.Analysis.Convolution
import Mathbin.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathbin.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathbin.Analysis.Analytic.IsolatedZeros

#align_import analysis.special_functions.gamma.beta from "leanprover-community/mathlib"@"9240e8be927a0955b9a82c6c85ef499ee3a626b8"

/-!
# The Beta function, and further properties of the Gamma function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the Beta integral, relate Beta and Gamma functions, and prove some
refined properties of the Gamma function using these relations.

## Results on the Beta function

* `complex.beta_integral`: the Beta function `Β(u, v)`, where `u`, `v` are complex with positive
  real part.
* `complex.Gamma_mul_Gamma_eq_beta_integral`: the formula
  `Gamma u * Gamma v = Gamma (u + v) * beta_integral u v`.

## Results on the Gamma function

* `complex.Gamma_ne_zero`: for all `s : ℂ` with `s ∉ {-n : n ∈ ℕ}` we have `Γ s ≠ 0`.
* `complex.Gamma_seq_tendsto_Gamma`: for all `s`, the limit as `n → ∞` of the sequence
  `n ↦ n ^ s * n! / (s * (s + 1) * ... * (s + n))` is `Γ(s)`.
* `complex.Gamma_mul_Gamma_one_sub`: Euler's reflection formula
  `Gamma s * Gamma (1 - s) = π / sin π s`.
* `complex.differentiable_one_div_Gamma`: the function `1 / Γ(s)` is differentiable everywhere.
* `complex.Gamma_mul_Gamma_add_half`: Legendre's duplication formula
  `Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * 2 ^ (1 - 2 * s) * sqrt π`.
* `real.Gamma_ne_zero`, `real.Gamma_seq_tendsto_Gamma`,
  `real.Gamma_mul_Gamma_one_sub`, `real.Gamma_mul_Gamma_add_half`: real versions of the above.
-/


noncomputable section

open Filter intervalIntegral Set Real MeasureTheory

open scoped Nat Topology BigOperators Real

section BetaIntegral

/-! ## The Beta function -/


namespace Complex

notation "cexp" => Complex.exp

#print Complex.betaIntegral /-
/-- The Beta function `Β (u, v)`, defined as `∫ x:ℝ in 0..1, x ^ (u - 1) * (1 - x) ^ (v - 1)`. -/
noncomputable def betaIntegral (u v : ℂ) : ℂ :=
  ∫ x : ℝ in 0 ..1, x ^ (u - 1) * (1 - x) ^ (v - 1)
#align complex.beta_integral Complex.betaIntegral
-/

#print Complex.betaIntegral_convergent_left /-
/-- Auxiliary lemma for `beta_integral_convergent`, showing convergence at the left endpoint. -/
theorem betaIntegral_convergent_left {u : ℂ} (hu : 0 < re u) (v : ℂ) :
    IntervalIntegrable (fun x => x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ → ℂ) volume 0 (1 / 2) :=
  by
  apply IntervalIntegrable.mul_continuousOn
  · refine' intervalIntegral.intervalIntegrable_cpow' _
    rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
  · apply ContinuousAt.continuousOn
    intro x hx
    rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 1 / 2)] at hx 
    apply ContinuousAt.cpow
    · exact (continuous_const.sub continuous_of_real).ContinuousAt
    · exact continuousAt_const
    · rw [sub_re, one_re, of_real_re, sub_pos]
      exact Or.inl (hx.2.trans_lt (by norm_num : (1 / 2 : ℝ) < 1))
#align complex.beta_integral_convergent_left Complex.betaIntegral_convergent_left
-/

#print Complex.betaIntegral_convergent /-
/-- The Beta integral is convergent for all `u, v` of positive real part. -/
theorem betaIntegral_convergent {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
    IntervalIntegrable (fun x => x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ → ℂ) volume 0 1 :=
  by
  refine' (beta_integral_convergent_left hu v).trans _
  rw [IntervalIntegrable.iff_comp_neg]
  convert ((beta_integral_convergent_left hv u).comp_add_right 1).symm
  · ext1 x
    conv_lhs => rw [mul_comm]
    congr 2 <;> · push_cast ; ring
  · norm_num
  · norm_num
#align complex.beta_integral_convergent Complex.betaIntegral_convergent
-/

#print Complex.betaIntegral_symm /-
theorem betaIntegral_symm (u v : ℂ) : betaIntegral v u = betaIntegral u v :=
  by
  rw [beta_integral, beta_integral]
  have :=
    intervalIntegral.integral_comp_mul_add (fun x : ℝ => (x : ℂ) ^ (u - 1) * (1 - ↑x) ^ (v - 1))
      neg_one_lt_zero.ne 1
  rw [inv_neg, inv_one, neg_one_smul, ← intervalIntegral.integral_symm] at this 
  convert this
  · ext1 x; rw [mul_comm]; congr <;> · push_cast ; ring
  · ring; · ring
#align complex.beta_integral_symm Complex.betaIntegral_symm
-/

#print Complex.betaIntegral_eval_one_right /-
theorem betaIntegral_eval_one_right {u : ℂ} (hu : 0 < re u) : betaIntegral u 1 = 1 / u :=
  by
  simp_rw [beta_integral, sub_self, cpow_zero, mul_one]
  rw [integral_cpow (Or.inl _)]
  · rw [of_real_zero, of_real_one, one_cpow, zero_cpow, sub_zero, sub_add_cancel]
    rw [sub_add_cancel]
    contrapose! hu; rw [hu, zero_re]
  · rwa [sub_re, one_re, ← sub_pos, sub_neg_eq_add, sub_add_cancel]
#align complex.beta_integral_eval_one_right Complex.betaIntegral_eval_one_right
-/

#print Complex.betaIntegral_scaled /-
theorem betaIntegral_scaled (s t : ℂ) {a : ℝ} (ha : 0 < a) :
    ∫ x in 0 ..a, (x : ℂ) ^ (s - 1) * (a - x) ^ (t - 1) = a ^ (s + t - 1) * betaIntegral s t :=
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
-/

#print Complex.Gamma_mul_Gamma_eq_betaIntegral /-
/-- Relation between Beta integral and Gamma function.  -/
theorem Gamma_mul_Gamma_eq_betaIntegral {s t : ℂ} (hs : 0 < re s) (ht : 0 < re t) :
    Gamma s * Gamma t = Gamma (s + t) * betaIntegral s t :=
  by
  -- Note that we haven't proved (yet) that the Gamma function has no zeroes, so we can't formulate
  -- this as a formula for the Beta function.
  have conv_int :=
    integral_posConvolution (Gamma_integral_convergent hs) (Gamma_integral_convergent ht)
      (ContinuousLinearMap.mul ℝ ℂ)
  simp_rw [ContinuousLinearMap.mul_apply'] at conv_int 
  have hst : 0 < re (s + t) := by rw [add_re]; exact add_pos hs ht
  rw [Gamma_eq_integral hs, Gamma_eq_integral ht, Gamma_eq_integral hst, Gamma_integral,
    Gamma_integral, Gamma_integral, ← conv_int, ← integral_mul_right (beta_integral _ _)]
  refine' set_integral_congr measurableSet_Ioi fun x hx => _
  dsimp only
  rw [mul_assoc, ← beta_integral_scaled s t hx, ← intervalIntegral.integral_const_mul]
  congr 1 with y : 1
  push_cast
  suffices cexp (-x) = cexp (-y) * cexp (-(x - y)) by rw [this]; ring
  · rw [← Complex.exp_add]; congr 1; abel
#align complex.Gamma_mul_Gamma_eq_beta_integral Complex.Gamma_mul_Gamma_eq_betaIntegral
-/

#print Complex.betaIntegral_recurrence /-
/-- Recurrence formula for the Beta function. -/
theorem betaIntegral_recurrence {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
    u * betaIntegral u (v + 1) = v * betaIntegral (u + 1) v :=
  by
  -- NB: If we knew `Gamma (u + v + 1) ≠ 0` this would be an easy consequence of
  -- `Gamma_mul_Gamma_eq_beta_integral`; but we don't know that yet. We will prove it later, but
  -- this lemma is needed in the proof. So we give a (somewhat laborious) direct argument.
  let F : ℝ → ℂ := fun x => x ^ u * (1 - x) ^ v
  have hu' : 0 < re (u + 1) := by rw [add_re, one_re]; positivity
  have hv' : 0 < re (v + 1) := by rw [add_re, one_re]; positivity
  have hc : ContinuousOn F (Icc 0 1) :=
    by
    refine' (ContinuousAt.continuousOn fun x hx => _).mul (ContinuousAt.continuousOn fun x hx => _)
    · refine'
        (continuous_at_cpow_const_of_re_pos (Or.inl _) hu).comp continuous_of_real.continuous_at
      rw [of_real_re]; exact hx.1
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
      · rw [mul_one] at this ; exact this
      · rw [id.def, of_real_re]; exact hx.1
    have V : HasDerivAt (fun y : ℂ => (1 - y) ^ v) (-v * (1 - ↑x) ^ (v - 1)) ↑x :=
      by
      have A := HasDerivAt.cpow_const (hasDerivAt_id (1 - ↑x)) (Or.inl _)
      rotate_left; · exact v
      · rw [id.def, sub_re, one_re, of_real_re, sub_pos]; exact hx.2
      simp_rw [id.def] at A 
      have B : HasDerivAt (fun y : ℂ => 1 - y) (-1) ↑x := by apply HasDerivAt.const_sub;
        apply hasDerivAt_id
      convert HasDerivAt.comp (↑x) A B using 1
      ring
    convert (U.mul V).comp_ofReal
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
    contrapose! hu; rw [hu, zero_re]
  have hF1 : F 1 = 0 :=
    by
    simp only [mul_eq_zero, of_real_one, one_cpow, one_ne_zero, sub_self, cpow_eq_zero_iff,
      eq_self_iff_true, Ne.def, true_and_iff, false_or_iff]
    contrapose! hv; rw [hv, zero_re]
  rw [hF0, hF1, sub_zero, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at int_ev 
  · rw [beta_integral, beta_integral, ← sub_eq_zero]
    convert int_ev <;> · ext1 x; congr; abel
  · apply IntervalIntegrable.const_mul
    convert beta_integral_convergent hu hv'
    ext1 x; rw [add_sub_cancel]
  · apply IntervalIntegrable.const_mul
    convert beta_integral_convergent hu' hv
    ext1 x; rw [add_sub_cancel]
#align complex.beta_integral_recurrence Complex.betaIntegral_recurrence
-/

#print Complex.betaIntegral_eval_nat_add_one_right /-
/-- Explicit formula for the Beta function when second argument is a positive integer. -/
theorem betaIntegral_eval_nat_add_one_right {u : ℂ} (hu : 0 < re u) (n : ℕ) :
    betaIntegral u (n + 1) = n ! / ∏ j : ℕ in Finset.range (n + 1), (u + j) :=
  by
  induction' n with n IH generalizing u
  ·
    rw [Nat.cast_zero, zero_add, beta_integral_eval_one_right hu, Nat.factorial_zero, Nat.cast_one,
      zero_add, Finset.prod_range_one, Nat.cast_zero, add_zero]
  · have := beta_integral_recurrence hu (_ : 0 < re n.succ)
    swap; · rw [← of_real_nat_cast, of_real_re]; positivity
    rw [mul_comm u _, ← eq_div_iff] at this 
    swap; · contrapose! hu; rw [hu, zero_re]
    rw [this, Finset.prod_range_succ', Nat.cast_succ, IH]
    swap; · rw [add_re, one_re]; positivity
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ←
      mul_div_assoc, ← div_div]
    congr 3 with j : 1
    push_cast ; abel
#align complex.beta_integral_eval_nat_add_one_right Complex.betaIntegral_eval_nat_add_one_right
-/

end Complex

end BetaIntegral

section LimitFormula

/-! ## The Euler limit formula -/


namespace Complex

#print Complex.GammaSeq /-
/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for complex `s`.
We will show that this tends to `Γ(s)` as `n → ∞`. -/
noncomputable def GammaSeq (s : ℂ) (n : ℕ) :=
  (n : ℂ) ^ s * n ! / ∏ j : ℕ in Finset.range (n + 1), (s + j)
#align complex.Gamma_seq Complex.GammaSeq
-/

#print Complex.GammaSeq_eq_betaIntegral_of_re_pos /-
theorem GammaSeq_eq_betaIntegral_of_re_pos {s : ℂ} (hs : 0 < re s) (n : ℕ) :
    GammaSeq s n = n ^ s * betaIntegral s (n + 1) := by
  rw [Gamma_seq, beta_integral_eval_nat_add_one_right hs n, ← mul_div_assoc]
#align complex.Gamma_seq_eq_beta_integral_of_re_pos Complex.GammaSeq_eq_betaIntegral_of_re_pos
-/

#print Complex.GammaSeq_add_one_left /-
theorem GammaSeq_add_one_left (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq (s + 1) n / s = n / (n + 1 + s) * GammaSeq s n :=
  by
  conv_lhs => rw [Gamma_seq, Finset.prod_range_succ, div_div]
  conv_rhs =>
    rw [Gamma_seq, Finset.prod_range_succ', Nat.cast_zero, add_zero, div_mul_div_comm, ← mul_assoc,
      ← mul_assoc, mul_comm _ (Finset.prod _ _)]
  congr 3
  · rw [cpow_add _ _ (nat.cast_ne_zero.mpr hn), cpow_one, mul_comm]
  · refine' Finset.prod_congr (by rfl) fun x hx => _
    push_cast ; ring
  · abel
#align complex.Gamma_seq_add_one_left Complex.GammaSeq_add_one_left
-/

#print Complex.GammaSeq_eq_approx_Gamma_integral /-
theorem GammaSeq_eq_approx_Gamma_integral {s : ℂ} (hs : 0 < re s) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq s n = ∫ x : ℝ in 0 ..n, ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1) :=
  by
  have : ∀ x : ℝ, x = x / n * n := by intro x; rw [div_mul_cancel]; exact nat.cast_ne_zero.mpr hn
  conv in ↑_ ^ _ =>
    congr
    rw [this x]
  rw [Gamma_seq_eq_beta_integral_of_re_pos hs]
  rw [beta_integral,
    @intervalIntegral.integral_comp_div _ _ _ _ 0 n _
      (fun x => ↑((1 - x) ^ n) * ↑(x * ↑n) ^ (s - 1) : ℝ → ℂ) (nat.cast_ne_zero.mpr hn),
    real_smul, zero_div, div_self, add_sub_cancel, ← intervalIntegral.integral_const_mul, ←
    intervalIntegral.integral_const_mul]
  swap; · exact nat.cast_ne_zero.mpr hn
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
  rw [A, B, cpow_nat_cast]; ring
#align complex.Gamma_seq_eq_approx_Gamma_integral Complex.GammaSeq_eq_approx_Gamma_integral
-/

#print Complex.approx_Gamma_integral_tendsto_Gamma_integral /-
/-- The main techical lemma for `Gamma_seq_tendsto_Gamma`, expressing the integral defining the
Gamma function for `0 < re s` as the limit of a sequence of integrals over finite intervals. -/
theorem approx_Gamma_integral_tendsto_Gamma_integral {s : ℂ} (hs : 0 < re s) :
    Tendsto (fun n : ℕ => ∫ x : ℝ in 0 ..n, ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1)) atTop
      (𝓝 <| Gamma s) :=
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
    apply IntervalIntegrable.continuousOn_mul
    · refine' intervalIntegral.intervalIntegrable_cpow' _
      rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
    · apply Continuous.continuousOn; continuity
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
      (Real.GammaIntegral_convergent hs) _
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
#align complex.approx_Gamma_integral_tendsto_Gamma_integral Complex.approx_Gamma_integral_tendsto_Gamma_integral
-/

#print Complex.GammaSeq_tendsto_Gamma /-
/-- Euler's limit formula for the complex Gamma function. -/
theorem GammaSeq_tendsto_Gamma (s : ℂ) : Tendsto (GammaSeq s) atTop (𝓝 <| Gamma s) :=
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
    pick_goal 3; · exact Gamma_seq_add_one_left s hn
    -- doesn't work if inlined?
    conv at this in _ / _ * _ => rw [mul_comm]
    rwa [← mul_one (Gamma_aux m (s + 1) / s), tendsto_mul_iff_of_ne_zero _ (one_ne_zero' ℂ)] at this 
    simp_rw [add_assoc]
    exact tendsto_coe_nat_div_add_atTop (1 + s)
#align complex.Gamma_seq_tendsto_Gamma Complex.GammaSeq_tendsto_Gamma
-/

end Complex

end LimitFormula

section GammaReflection

/-! ## The reflection formula -/


namespace Complex

#print Complex.GammaSeq_mul /-
theorem GammaSeq_mul (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq z n * GammaSeq (1 - z) n =
      n / (n + 1 - z) * (1 / (z * ∏ j in Finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))) :=
  by
  -- also true for n = 0 but we don't need it
  have aux : ∀ a b c d : ℂ, a * b * (c * d) = a * c * (b * d) := by intros; ring
  rw [Gamma_seq, Gamma_seq, div_mul_div_comm, aux, ← pow_two]
  have : (n : ℂ) ^ z * n ^ (1 - z) = n := by
    rw [← cpow_add _ _ (nat.cast_ne_zero.mpr hn), add_sub_cancel'_right, cpow_one]
  rw [this, Finset.prod_range_succ', Finset.prod_range_succ, aux, ← Finset.prod_mul_distrib,
    Nat.cast_zero, add_zero, add_comm (1 - z) n, ← add_sub_assoc]
  have : ∀ j : ℕ, (z + ↑(j + 1)) * (1 - z + ↑j) = ↑((j + 1) ^ 2) * (1 - z ^ 2 / (↑j + 1) ^ 2) :=
    by
    intro j
    push_cast
    have : (j : ℂ) + 1 ≠ 0 := by rw [← Nat.cast_succ, Nat.cast_ne_zero]; exact Nat.succ_ne_zero j
    field_simp; ring
  simp_rw [this]
  rw [Finset.prod_mul_distrib, ← Nat.cast_prod, Finset.prod_pow,
    Finset.prod_range_add_one_eq_factorial, Nat.cast_pow,
    (by intros; ring : ∀ a b c d : ℂ, a * b * (c * d) = a * (d * (b * c))), ← div_div,
    mul_div_cancel, ← div_div, mul_comm z _, mul_one_div]
  exact pow_ne_zero 2 (nat.cast_ne_zero.mpr <| Nat.factorial_ne_zero n)
#align complex.Gamma_seq_mul Complex.GammaSeq_mul
-/

#print Complex.Gamma_mul_Gamma_one_sub /-
/-- Euler's reflection formula for the complex Gamma function. -/
theorem Gamma_mul_Gamma_one_sub (z : ℂ) : Gamma z * Gamma (1 - z) = π / sin (π * z) :=
  by
  have pi_ne : (π : ℂ) ≠ 0 := complex.of_real_ne_zero.mpr pi_ne_zero
  by_cases hs : sin (↑π * z) = 0
  · -- first deal with silly case z = integer
    rw [hs, div_zero]
    rw [← neg_eq_zero, ← Complex.sin_neg, ← mul_neg, Complex.sin_eq_zero_iff, mul_comm] at hs 
    obtain ⟨k, hk⟩ := hs
    rw [mul_eq_mul_right_iff, eq_false (of_real_ne_zero.mpr pi_pos.ne'), or_false_iff,
      neg_eq_iff_eq_neg] at hk 
    rw [hk]
    cases k
    · rw [Int.cast_ofNat, Complex.Gamma_neg_nat_eq_zero, MulZeroClass.zero_mul]
    ·
      rw [Int.cast_negSucc, neg_neg, Nat.cast_add, Nat.cast_one, add_comm, sub_add_cancel',
        Complex.Gamma_neg_nat_eq_zero, MulZeroClass.mul_zero]
  refine' tendsto_nhds_unique ((Gamma_seq_tendsto_Gamma z).mul (Gamma_seq_tendsto_Gamma <| 1 - z)) _
  have : ↑π / sin (↑π * z) = 1 * (π / sin (π * z)) := by rw [one_mul]; rw [this]
  refine'
    tendsto.congr'
      ((eventually_ne_at_top 0).mp (eventually_of_forall fun n hn => (Gamma_seq_mul z hn).symm))
      (tendsto.mul _ _)
  · convert tendsto_coe_nat_div_add_atTop (1 - z); ext1 n; rw [add_sub_assoc]
  · have : ↑π / sin (↑π * z) = 1 / (sin (π * z) / π) := by field_simp; rw [this]
    refine' tendsto_const_nhds.div _ (div_ne_zero hs pi_ne)
    rw [← tendsto_mul_iff_of_ne_zero tendsto_const_nhds pi_ne, div_mul_cancel _ pi_ne]
    convert tendsto_euler_sin_prod z
    ext1 n; rw [mul_comm, ← mul_assoc]
#align complex.Gamma_mul_Gamma_one_sub Complex.Gamma_mul_Gamma_one_sub
-/

#print Complex.Gamma_ne_zero /-
/-- The Gamma function does not vanish on `ℂ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
theorem Gamma_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) : Gamma s ≠ 0 :=
  by
  by_cases h_im : s.im = 0
  · have : s = ↑s.re := by conv_lhs => rw [← Complex.re_add_im s];
      rw [h_im, of_real_zero, MulZeroClass.zero_mul, add_zero]
    rw [this, Gamma_of_real, of_real_ne_zero]
    refine' Real.Gamma_ne_zero fun n => _
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
    rw [← Complex.Gamma_mul_Gamma_one_sub s, mul_ne_zero_iff] at A 
    exact A.1
#align complex.Gamma_ne_zero Complex.Gamma_ne_zero
-/

#print Complex.Gamma_eq_zero_iff /-
theorem Gamma_eq_zero_iff (s : ℂ) : Gamma s = 0 ↔ ∃ m : ℕ, s = -m :=
  by
  constructor
  · contrapose!; exact Gamma_ne_zero
  · rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m
#align complex.Gamma_eq_zero_iff Complex.Gamma_eq_zero_iff
-/

#print Complex.Gamma_ne_zero_of_re_pos /-
/-- A weaker, but easier-to-apply, version of `complex.Gamma_ne_zero`. -/
theorem Gamma_ne_zero_of_re_pos {s : ℂ} (hs : 0 < re s) : Gamma s ≠ 0 :=
  by
  refine' Gamma_ne_zero fun m => _
  contrapose! hs
  simpa only [hs, neg_re, ← of_real_nat_cast, of_real_re, neg_nonpos] using Nat.cast_nonneg _
#align complex.Gamma_ne_zero_of_re_pos Complex.Gamma_ne_zero_of_re_pos
-/

end Complex

namespace Real

#print Real.GammaSeq /-
/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for real `s`. We
will show that this tends to `Γ(s)` as `n → ∞`. -/
noncomputable def GammaSeq (s : ℝ) (n : ℕ) :=
  (n : ℝ) ^ s * n ! / ∏ j : ℕ in Finset.range (n + 1), (s + j)
#align real.Gamma_seq Real.GammaSeq
-/

#print Real.GammaSeq_tendsto_Gamma /-
/-- Euler's limit formula for the real Gamma function. -/
theorem GammaSeq_tendsto_Gamma (s : ℝ) : Tendsto (GammaSeq s) atTop (𝓝 <| Gamma s) :=
  by
  suffices : tendsto (coe ∘ Gamma_seq s : ℕ → ℂ) at_top (𝓝 <| Complex.Gamma s)
  exact (complex.continuous_re.tendsto (Complex.Gamma ↑s)).comp this
  convert Complex.GammaSeq_tendsto_Gamma s
  ext1 n
  dsimp only [Gamma_seq, Function.comp_apply, Complex.GammaSeq]
  push_cast
  rw [Complex.ofReal_cpow n.cast_nonneg, Complex.ofReal_nat_cast]
#align real.Gamma_seq_tendsto_Gamma Real.GammaSeq_tendsto_Gamma
-/

#print Real.Gamma_mul_Gamma_one_sub /-
/-- Euler's reflection formula for the real Gamma function. -/
theorem Gamma_mul_Gamma_one_sub (s : ℝ) : Gamma s * Gamma (1 - s) = π / sin (π * s) :=
  by
  simp_rw [← Complex.ofReal_inj, Complex.ofReal_div, Complex.ofReal_sin, Complex.ofReal_mul, ←
    Complex.Gamma_ofReal, Complex.ofReal_sub, Complex.ofReal_one]
  exact Complex.Gamma_mul_Gamma_one_sub s
#align real.Gamma_mul_Gamma_one_sub Real.Gamma_mul_Gamma_one_sub
-/

end Real

end GammaReflection

section InvGamma

open scoped Real

namespace Complex

/-! ## The reciprocal Gamma function

We show that the reciprocal Gamma function `1 / Γ(s)` is entire. These lemmas show that (in this
case at least) mathlib's conventions for division by zero do actually give a mathematically useful
answer! (These results are useful in the theory of zeta and L-functions.) -/


#print Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one /-
/-- A reformulation of the Gamma recurrence relation which is true for `s = 0` as well. -/
theorem one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s : ℂ) :
    (Gamma s)⁻¹ = s * (Gamma (s + 1))⁻¹ :=
  by
  rcases ne_or_eq s 0 with (h | rfl)
  · rw [Gamma_add_one s h, mul_inv, mul_inv_cancel_left₀ h]
  · rw [zero_add, Gamma_zero, inv_zero, MulZeroClass.zero_mul]
#align complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
-/

#print Complex.differentiable_one_div_Gamma /-
/-- The reciprocal of the Gamma function is differentiable everywhere (including the points where
Gamma itself is not). -/
theorem differentiable_one_div_Gamma : Differentiable ℂ fun s : ℂ => (Gamma s)⁻¹ :=
  by
  suffices : ∀ n : ℕ, ∀ (s : ℂ) (hs : -s.re < n), DifferentiableAt ℂ (fun u : ℂ => (Gamma u)⁻¹) s
  exact fun s =>
    let ⟨n, h⟩ := exists_nat_gt (-s.re)
    this n s h
  intro n
  induction' n with m hm
  · intro s hs
    rw [Nat.cast_zero, neg_lt_zero] at hs 
    suffices : ∀ m : ℕ, s ≠ -↑m; exact (differentiable_at_Gamma _ this).inv (Gamma_ne_zero this)
    contrapose! hs
    rcases hs with ⟨m, rfl⟩
    simpa only [neg_re, ← of_real_nat_cast, of_real_re, neg_nonpos] using Nat.cast_nonneg m
  · intro s hs
    rw [funext one_div_Gamma_eq_self_mul_one_div_Gamma_add_one]
    specialize hm (s + 1) (by rwa [add_re, one_re, neg_add', sub_lt_iff_lt_add, ← Nat.cast_succ])
    refine' differentiable_at_id.mul (hm.comp s _)
    exact differentiable_at_id.add (differentiableAt_const _)
#align complex.differentiable_one_div_Gamma Complex.differentiable_one_div_Gamma
-/

end Complex

end InvGamma

section Doubling

/-!
## The doubling formula for Gamma

We prove the doubling formula for arbitrary real or complex arguments, by analytic continuation from
the positive real case. (Knowing that `Γ⁻¹` is analytic everywhere makes this much simpler, since we
do not have to do any special-case handling for the poles of `Γ`.)
-/


namespace Complex

#print Complex.Gamma_mul_Gamma_add_half /-
theorem Gamma_mul_Gamma_add_half (s : ℂ) :
    Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * 2 ^ (1 - 2 * s) * ↑(Real.sqrt π) :=
  by
  suffices
    (fun z => (Gamma z)⁻¹ * (Gamma (z + 1 / 2))⁻¹) = fun z =>
      (Gamma (2 * z))⁻¹ * 2 ^ (2 * z - 1) / ↑(Real.sqrt π)
    by
    convert congr_arg Inv.inv (congr_fun this s) using 1
    · rw [mul_inv, inv_inv, inv_inv]
    · rw [div_eq_mul_inv, mul_inv, mul_inv, inv_inv, inv_inv, ← cpow_neg, neg_sub]
  have h1 : AnalyticOn ℂ (fun z : ℂ => (Gamma z)⁻¹ * (Gamma (z + 1 / 2))⁻¹) univ :=
    by
    refine' DifferentiableOn.analyticOn _ isOpen_univ
    refine' (differentiable_one_div_Gamma.mul _).DifferentiableOn
    exact differentiable_one_div_Gamma.comp (differentiable_id.add (differentiable_const _))
  have h2 : AnalyticOn ℂ (fun z => (Gamma (2 * z))⁻¹ * 2 ^ (2 * z - 1) / ↑(Real.sqrt π)) univ :=
    by
    refine' DifferentiableOn.analyticOn _ isOpen_univ
    refine' (Differentiable.mul _ (differentiable_const _)).DifferentiableOn
    apply Differentiable.mul
    · exact differentiable_one_div_Gamma.comp (differentiable_id'.const_mul _)
    · refine' fun t => DifferentiableAt.const_cpow _ (Or.inl two_ne_zero)
      refine' DifferentiableAt.sub_const (differentiable_at_id.const_mul _) _
  have h3 : tendsto (coe : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1) :=
    by
    rw [tendsto_nhdsWithin_iff]; constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuous_of_real.continuous_at
    · exact eventually_nhds_within_iff.mpr (eventually_of_forall fun t ht => of_real_ne_one.mpr ht)
  refine' AnalyticOn.eq_of_frequently_eq h1 h2 (h3.frequently _)
  refine' ((eventually.filter_mono nhdsWithin_le_nhds) _).Frequently
  refine' (eventually_gt_nhds zero_lt_one).mp (eventually_of_forall fun t ht => _)
  rw [← mul_inv, Gamma_of_real, (by push_cast : (t : ℂ) + 1 / 2 = ↑(t + 1 / 2)), Gamma_of_real, ←
    of_real_mul, Gamma_mul_Gamma_add_half_of_pos ht, of_real_mul, of_real_mul, ← Gamma_of_real,
    mul_inv, mul_inv, (by push_cast : 2 * (t : ℂ) = ↑(2 * t)), Gamma_of_real,
    of_real_cpow zero_le_two, of_real_bit0, of_real_one, ← cpow_neg, of_real_sub, of_real_one,
    neg_sub, ← div_eq_mul_inv]
#align complex.Gamma_mul_Gamma_add_half Complex.Gamma_mul_Gamma_add_half
-/

end Complex

namespace Real

open Complex

#print Real.Gamma_mul_Gamma_add_half /-
theorem Gamma_mul_Gamma_add_half (s : ℝ) :
    Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * 2 ^ (1 - 2 * s) * sqrt π :=
  by
  rw [← of_real_inj]
  simpa only [← Gamma_of_real, of_real_cpow zero_le_two, of_real_mul, of_real_add, of_real_div,
    of_real_bit0, of_real_one, of_real_sub] using Complex.Gamma_mul_Gamma_add_half ↑s
#align real.Gamma_mul_Gamma_add_half Real.Gamma_mul_Gamma_add_half
-/

end Real

end Doubling

