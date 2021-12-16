import Mathbin.Analysis.SpecialFunctions.Log 
import Mathbin.Analysis.SpecialFunctions.ExpDeriv

/-!
# Derivative and series expansion of real logarithm

In this file we prove that `real.log` is infinitely smooth at all nonzero `x : ℝ`. We also prove
that the series `∑' n : ℕ, x ^ (n + 1) / (n + 1)` converges to `(-real.log (1 - x))` for all
`x : ℝ`, `|x| < 1`.

## Tags

logarighm, derivative
-/


open Filter Finset Set

open_locale TopologicalSpace BigOperators

namespace Real

variable {x : ℝ}

theorem has_strict_deriv_at_log_of_pos (hx : 0 < x) : HasStrictDerivAt log (x⁻¹) x :=
  have  : HasStrictDerivAt log ((exp$ log x)⁻¹) x :=
    (has_strict_deriv_at_exp$ log x).of_local_left_inverse (continuous_at_log hx.ne') (ne_of_gtₓ$ exp_pos _)$
      eventually.mono (lt_mem_nhds hx) @exp_log 
  by 
    rwa [exp_log hx] at this

theorem has_strict_deriv_at_log (hx : x ≠ 0) : HasStrictDerivAt log (x⁻¹) x :=
  by 
    cases' hx.lt_or_lt with hx hx
    ·
      convert (has_strict_deriv_at_log_of_pos (neg_pos.mpr hx)).comp x (has_strict_deriv_at_neg x)
      ·
        ext y 
        exact (log_neg_eq_log y).symm
      ·
        fieldSimp [hx.ne]
    ·
      exact has_strict_deriv_at_log_of_pos hx

theorem has_deriv_at_log (hx : x ≠ 0) : HasDerivAt log (x⁻¹) x :=
  (has_strict_deriv_at_log hx).HasDerivAt

theorem differentiable_at_log (hx : x ≠ 0) : DifferentiableAt ℝ log x :=
  (has_deriv_at_log hx).DifferentiableAt

theorem differentiable_on_log : DifferentiableOn ℝ log ({0}ᶜ) :=
  fun x hx => (differentiable_at_log hx).DifferentiableWithinAt

@[simp]
theorem differentiable_at_log_iff : DifferentiableAt ℝ log x ↔ x ≠ 0 :=
  ⟨fun h => continuous_at_log_iff.1 h.continuous_at, differentiable_at_log⟩

theorem deriv_log (x : ℝ) : deriv log x = x⁻¹ :=
  if hx : x = 0 then
    by 
      rw [deriv_zero_of_not_differentiable_at (mt differentiable_at_log_iff.1 (not_not.2 hx)), hx, inv_zero]
  else (has_deriv_at_log hx).deriv

@[simp]
theorem deriv_log' : deriv log = HasInv.inv :=
  funext deriv_log

theorem times_cont_diff_on_log {n : WithTop ℕ} : TimesContDiffOn ℝ n log ({0}ᶜ) :=
  by 
    suffices  : TimesContDiffOn ℝ ⊤ log ({0}ᶜ)
    exact this.of_le le_top 
    refine' (times_cont_diff_on_top_iff_deriv_of_open is_open_compl_singleton).2 _ 
    simp [differentiable_on_log, times_cont_diff_on_inv]

theorem times_cont_diff_at_log {n : WithTop ℕ} : TimesContDiffAt ℝ n log x ↔ x ≠ 0 :=
  ⟨fun h => continuous_at_log_iff.1 h.continuous_at,
    fun hx => (times_cont_diff_on_log x hx).TimesContDiffAt$ IsOpen.mem_nhds is_open_compl_singleton hx⟩

end Real

section LogDifferentiable

open Real

section deriv

variable {f : ℝ → ℝ} {x f' : ℝ} {s : Set ℝ}

theorem HasDerivWithinAt.log (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
  HasDerivWithinAt (fun y => log (f y)) (f' / f x) s x :=
  by 
    rw [div_eq_inv_mul]
    exact (has_deriv_at_log hx).comp_has_deriv_within_at x hf

theorem HasDerivAt.log (hf : HasDerivAt f f' x) (hx : f x ≠ 0) : HasDerivAt (fun y => log (f y)) (f' / f x) x :=
  by 
    rw [←has_deriv_within_at_univ] at *
    exact hf.log hx

theorem HasStrictDerivAt.log (hf : HasStrictDerivAt f f' x) (hx : f x ≠ 0) :
  HasStrictDerivAt (fun y => log (f y)) (f' / f x) x :=
  by 
    rw [div_eq_inv_mul]
    exact (has_strict_deriv_at_log hx).comp x hf

theorem derivWithin.log (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) (hxs : UniqueDiffWithinAt ℝ s x) :
  derivWithin (fun x => log (f x)) s x = derivWithin f s x / f x :=
  (hf.has_deriv_within_at.log hx).derivWithin hxs

@[simp]
theorem deriv.log (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) : deriv (fun x => log (f x)) x = deriv f x / f x :=
  (hf.has_deriv_at.log hx).deriv

end deriv

section fderiv

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E} {f' : E →L[ℝ] ℝ} {s : Set E}

theorem HasFderivWithinAt.log (hf : HasFderivWithinAt f f' s x) (hx : f x ≠ 0) :
  HasFderivWithinAt (fun x => log (f x)) (f x⁻¹ • f') s x :=
  (has_deriv_at_log hx).comp_has_fderiv_within_at x hf

theorem HasFderivAt.log (hf : HasFderivAt f f' x) (hx : f x ≠ 0) : HasFderivAt (fun x => log (f x)) (f x⁻¹ • f') x :=
  (has_deriv_at_log hx).comp_has_fderiv_at x hf

theorem HasStrictFderivAt.log (hf : HasStrictFderivAt f f' x) (hx : f x ≠ 0) :
  HasStrictFderivAt (fun x => log (f x)) (f x⁻¹ • f') x :=
  (has_strict_deriv_at_log hx).comp_has_strict_fderiv_at x hf

theorem DifferentiableWithinAt.log (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) :
  DifferentiableWithinAt ℝ (fun x => log (f x)) s x :=
  (hf.has_fderiv_within_at.log hx).DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.log (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) : DifferentiableAt ℝ (fun x => log (f x)) x :=
  (hf.has_fderiv_at.log hx).DifferentiableAt

theorem TimesContDiffAt.log {n} (hf : TimesContDiffAt ℝ n f x) (hx : f x ≠ 0) :
  TimesContDiffAt ℝ n (fun x => log (f x)) x :=
  (times_cont_diff_at_log.2 hx).comp x hf

theorem TimesContDiffWithinAt.log {n} (hf : TimesContDiffWithinAt ℝ n f s x) (hx : f x ≠ 0) :
  TimesContDiffWithinAt ℝ n (fun x => log (f x)) s x :=
  (times_cont_diff_at_log.2 hx).comp_times_cont_diff_within_at x hf

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
theorem TimesContDiffOn.log {n} (hf : TimesContDiffOn ℝ n f s) (hs : ∀ x _ : x ∈ s, f x ≠ 0) :
  TimesContDiffOn ℝ n (fun x => log (f x)) s :=
  fun x hx => (hf x hx).log (hs x hx)

theorem TimesContDiff.log {n} (hf : TimesContDiff ℝ n f) (h : ∀ x, f x ≠ 0) : TimesContDiff ℝ n fun x => log (f x) :=
  times_cont_diff_iff_times_cont_diff_at.2$ fun x => hf.times_cont_diff_at.log (h x)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
theorem DifferentiableOn.log (hf : DifferentiableOn ℝ f s) (hx : ∀ x _ : x ∈ s, f x ≠ 0) :
  DifferentiableOn ℝ (fun x => log (f x)) s :=
  fun x h => (hf x h).log (hx x h)

@[simp]
theorem Differentiable.log (hf : Differentiable ℝ f) (hx : ∀ x, f x ≠ 0) : Differentiable ℝ fun x => log (f x) :=
  fun x => (hf x).log (hx x)

theorem fderivWithin.log (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) (hxs : UniqueDiffWithinAt ℝ s x) :
  fderivWithin ℝ (fun x => log (f x)) s x = f x⁻¹ • fderivWithin ℝ f s x :=
  (hf.has_fderiv_within_at.log hx).fderivWithin hxs

@[simp]
theorem fderiv.log (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
  fderiv ℝ (fun x => log (f x)) x = f x⁻¹ • fderiv ℝ f x :=
  (hf.has_fderiv_at.log hx).fderiv

end fderiv

end LogDifferentiable

namespace Real

/-- The function `x * log (1 + t / x)` tends to `t` at `+∞`. -/
theorem tendsto_mul_log_one_plus_div_at_top (t : ℝ) : tendsto (fun x => x*log (1+t / x)) at_top (𝓝 t) :=
  by 
    have h₁ : tendsto (fun h => h⁻¹*log (1+t*h)) (𝓝[{0}ᶜ] 0) (𝓝 t)
    ·
      simpa [has_deriv_at_iff_tendsto_slope] using
        ((has_deriv_at_const _ 1).add ((has_deriv_at_id (0 : ℝ)).const_mul t)).log
          (by 
            simp )
    have h₂ : tendsto (fun x : ℝ => x⁻¹) at_top (𝓝[{0}ᶜ] 0) :=
      tendsto_inv_at_top_zero'.mono_right (nhds_within_mono _ fun x hx => (set.mem_Ioi.mp hx).ne')
    convert h₁.comp h₂ 
    ext 
    fieldSimp [mul_commₓ]

open_locale BigOperators

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » Ioo («expr- »(1) : exprℝ()) 1)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » Icc «expr- »(«expr| |»(x)) «expr| |»(x))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » Icc «expr- »(«expr| |»(x)) «expr| |»(x))
/-- A crude lemma estimating the difference between `log (1-x)` and its Taylor series at `0`,
where the main point of the bound is that it tends to `0`. The goal is to deduce the series
expansion of the logarithm, in `has_sum_pow_div_log_of_abs_lt_1`.
-/
theorem abs_log_sub_add_sum_range_le {x : ℝ} (h : |x| < 1) (n : ℕ) :
  |(∑ i in range n, (x^i+1) / i+1)+log (1 - x)| ≤ (|x|^n+1) / (1 - |x|) :=
  by 
    let F : ℝ → ℝ := fun x => (∑ i in range n, (x^i+1) / i+1)+log (1 - x)
    have A : ∀ y _ : y ∈ Ioo (-1 : ℝ) 1, deriv F y = -(y^n) / (1 - y)
    ·
      intro y hy 
      have  : (∑ i in range n, (((↑i)+1)*y^i) / (↑i)+1) = ∑ i in range n, y^i
      ·
        congr with i 
        have  : ((i : ℝ)+1) ≠ 0 := ne_of_gtₓ (Nat.cast_add_one_pos i)
        fieldSimp [this, mul_commₓ]
      fieldSimp [F, this, ←geom_sum_def, geom_sum_eq (ne_of_ltₓ hy.2), sub_ne_zero_of_ne (ne_of_gtₓ hy.2),
        sub_ne_zero_of_ne (ne_of_ltₓ hy.2)]
      ring 
    have B : ∀ y _ : y ∈ Icc (-|x|) |x|, |deriv F y| ≤ (|x|^n) / (1 - |x|)
    ·
      intro y hy 
      have  : y ∈ Ioo (-(1 : ℝ)) 1 := ⟨lt_of_lt_of_leₓ (neg_lt_neg h) hy.1, lt_of_le_of_ltₓ hy.2 h⟩
      calc |deriv F y| = |-(y^n) / (1 - y)| :=
        by 
          rw [A y this]_ ≤ (|x|^n) / (1 - |x|) :=
        by 
          have  : |y| ≤ |x| := abs_le.2 hy 
          have  : 0 < 1 - |x|
          ·
            linarith 
          have  : 1 - |x| ≤ |1 - y| :=
            le_transₓ
              (by 
                linarith [hy.2])
              (le_abs_self _)
          simp only [←pow_abs, abs_div, abs_neg]
          applyRules [div_le_div, pow_nonneg, abs_nonneg, pow_le_pow_of_le_left]
    have C : ∥F x - F 0∥ ≤ ((|x|^n) / (1 - |x|))*∥x - 0∥
    ·
      have  : ∀ y _ : y ∈ Icc (-|x|) |x|, DifferentiableAt ℝ F y
      ·
        intro y hy 
        have  : 1 - y ≠ 0 := sub_ne_zero_of_ne (ne_of_gtₓ (lt_of_le_of_ltₓ hy.2 h))
        simp [F, this]
      apply Convex.norm_image_sub_le_of_norm_deriv_le this B (convex_Icc _ _) _ _
      ·
        simpa using abs_nonneg x
      ·
        simp [le_abs_self x, neg_le.mp (neg_le_abs_self x)]
    simpa [F, norm_eq_abs, div_mul_eq_mul_div, pow_succ'ₓ] using C

/-- Power series expansion of the logarithm around `1`. -/
theorem has_sum_pow_div_log_of_abs_lt_1 {x : ℝ} (h : |x| < 1) : HasSum (fun n : ℕ => (x^n+1) / n+1) (-log (1 - x)) :=
  by 
    rw [Summable.has_sum_iff_tendsto_nat]
    show tendsto (fun n : ℕ => ∑ i : ℕ in range n, (x^i+1) / i+1) at_top (𝓝 (-log (1 - x)))
    ·
      rw [tendsto_iff_norm_tendsto_zero]
      simp only [norm_eq_abs, sub_neg_eq_add]
      refine' squeeze_zero (fun n => abs_nonneg _) (abs_log_sub_add_sum_range_le h) _ 
      suffices  : tendsto (fun t : ℕ => (|x|^t+1) / (1 - |x|)) at_top (𝓝 ((|x|*0) / (1 - |x|)))
      ·
        simpa 
      simp only [pow_succₓ]
      refine' (tendsto_const_nhds.mul _).div_const 
      exact tendsto_pow_at_top_nhds_0_of_lt_1 (abs_nonneg _) h 
    show Summable fun n : ℕ => (x^n+1) / n+1
    ·
      refine' summable_of_norm_bounded _ (summable_geometric_of_lt_1 (abs_nonneg _) h) fun i => _ 
      calc ∥(x^i+1) / i+1∥ = (|x|^i+1) / i+1 :=
        by 
          have  : (0 : ℝ) ≤ i+1 := le_of_ltₓ (Nat.cast_add_one_pos i)
          rw [norm_eq_abs, abs_div, ←pow_abs, abs_of_nonneg this]_ ≤ (|x|^i+1) / 0+1 :=
        by 
          applyRules [div_le_div_of_le_left, pow_nonneg, abs_nonneg, add_le_add_right, i.cast_nonneg]
          normNum _ ≤ (|x|^i) :=
        by 
          simpa [pow_succ'ₓ] using mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) i) (le_of_ltₓ h)

end Real

