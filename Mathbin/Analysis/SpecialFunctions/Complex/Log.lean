/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathbin.Analysis.SpecialFunctions.Complex.Arg
import Mathbin.Analysis.SpecialFunctions.Log.Basic

/-!
# The complex `log` function

Basic properties, relationship with `exp`.
-/


noncomputable section

namespace Complex

open Set Filter

open Real TopologicalSpace

/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0`-/
@[pp_nodot]
noncomputable def log (x : ℂ) : ℂ :=
  x.abs.log + arg x * I

theorem log_re (x : ℂ) : x.log.re = x.abs.log := by
  simp [log]

theorem log_im (x : ℂ) : x.log.im = x.arg := by
  simp [log]

theorem neg_pi_lt_log_im (x : ℂ) : -π < (log x).im := by
  simp only [log_im, neg_pi_lt_arg]

theorem log_im_le_pi (x : ℂ) : (log x).im ≤ π := by
  simp only [log_im, arg_le_pi]

theorem exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x := by
  rw [log, exp_add_mul_I, ← of_real_sin, sin_arg, ← of_real_cos, cos_arg hx, ← of_real_exp, Real.exp_log (abs_pos.2 hx),
    mul_addₓ, of_real_div, of_real_div, mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), ← mul_assoc,
    mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), re_add_im]

@[simp]
theorem range_exp : Range exp = {0}ᶜ :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨x, rfl⟩
      exact exp_ne_zero x, fun hx => ⟨log x, exp_log hx⟩⟩

theorem log_exp {x : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π) : log (exp x) = x := by
  rw [log, abs_exp, Real.log_exp, exp_eq_exp_re_mul_sin_add_cos, ← of_real_exp,
    arg_mul_cos_add_sin_mul_I (Real.exp_pos _) ⟨hx₁, hx₂⟩, re_add_im]

theorem exp_inj_of_neg_pi_lt_of_le_pi {x y : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π) (hy₁ : -π < y.im) (hy₂ : y.im ≤ π)
    (hxy : exp x = exp y) : x = y := by
  rw [← log_exp hx₁ hx₂, ← log_exp hy₁ hy₂, hxy]

theorem of_real_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x :=
  Complex.ext
    (by
      rw [log_re, of_real_re, abs_of_nonneg hx])
    (by
      rw [of_real_im, log_im, arg_of_real_of_nonneg hx])

theorem log_of_real_re (x : ℝ) : (log (x : ℂ)).re = Real.log x := by
  simp [log_re]

@[simp]
theorem log_zero : log 0 = 0 := by
  simp [log]

@[simp]
theorem log_one : log 1 = 0 := by
  simp [log]

theorem log_neg_one : log (-1) = π * I := by
  simp [log]

theorem log_I : log i = π / 2 * I := by
  simp [log]

theorem log_neg_I : log (-I) = -(π / 2) * I := by
  simp [log]

theorem two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 := by
  norm_num [Real.pi_ne_zero, I_ne_zero]

theorem exp_eq_one_iff {x : ℂ} : exp x = 1 ↔ ∃ n : ℤ, x = n * (2 * π * I) := by
  constructor
  · intro h
    rcases exists_unique_add_zsmul_mem_Ioc Real.two_pi_pos x.im (-π) with ⟨n, hn, -⟩
    use -n
    rw [Int.cast_neg, neg_mul, eq_neg_iff_add_eq_zero]
    have : (x + n * (2 * π * I)).im ∈ Ioc (-π) π := by
      simpa [two_mul, mul_addₓ] using hn
    rw [← log_exp this.1 this.2, exp_periodic.int_mul n, h, log_one]
    
  · rintro ⟨n, rfl⟩
    exact (exp_periodic.int_mul n).Eq.trans exp_zero
    

theorem exp_eq_exp_iff_exp_sub_eq_one {x y : ℂ} : exp x = exp y ↔ exp (x - y) = 1 := by
  rw [exp_sub, div_eq_one_iff_eq (exp_ne_zero _)]

theorem exp_eq_exp_iff_exists_int {x y : ℂ} : exp x = exp y ↔ ∃ n : ℤ, x = y + n * (2 * π * I) := by
  simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']

@[simp]
theorem countable_preimage_exp {s : Set ℂ} : Countable (exp ⁻¹' s) ↔ Countable s := by
  refine' ⟨fun hs => _, fun hs => _⟩
  · refine' ((hs.image exp).insert 0).mono _
    rw [image_preimage_eq_inter_range, range_exp, ← diff_eq, ← union_singleton, diff_union_self]
    exact subset_union_left _ _
    
  · rw [← bUnion_preimage_singleton]
    refine' hs.bUnion fun z hz => _
    rcases em (∃ w, exp w = z) with (⟨w, rfl⟩ | hne)
    · simp only [preimage, mem_singleton_iff, exp_eq_exp_iff_exists_int, set_of_exists]
      exact countable_Union fun m => countable_singleton _
      
    · push_neg  at hne
      simp [preimage, hne]
      
    

alias countable_preimage_exp ↔ _ Set.Countable.preimage_cexp

theorem tendsto_log_nhds_within_im_neg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    Tendsto log (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 <| Real.log (abs z) - π * I) := by
  have :=
    (continuous_of_real.continuous_at.comp_continuous_within_at (continuous_abs.continuous_within_at.log _)).Tendsto.add
      (((continuous_of_real.tendsto _).comp <| tendsto_arg_nhds_within_im_neg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds)
  convert this
  · simp [sub_eq_add_neg]
    
  · lift z to ℝ using him
    simpa using hre.ne
    

theorem continuous_within_at_log_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    ContinuousWithinAt log { z : ℂ | 0 ≤ z.im } z := by
  have :=
    (continuous_of_real.continuous_at.comp_continuous_within_at (continuous_abs.continuous_within_at.log _)).Tendsto.add
      ((continuous_of_real.continuous_at.comp_continuous_within_at <|
            continuous_within_at_arg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds)
  convert this
  · lift z to ℝ using him
    simpa using hre.ne
    

theorem tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    Tendsto log (𝓝[{ z : ℂ | 0 ≤ z.im }] z) (𝓝 <| Real.log (abs z) + π * I) := by
  simpa only [log, arg_eq_pi_iff.2 ⟨hre, him⟩] using (continuous_within_at_log_of_re_neg_of_im_zero hre him).Tendsto

end Complex

section LogDeriv

open Complex Filter

open TopologicalSpace

variable {α : Type _}

theorem continuous_at_clog {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) : ContinuousAt log x := by
  refine' ContinuousAt.add _ _
  · refine' continuous_of_real.continuous_at.comp _
    refine' (Real.continuous_at_log _).comp complex.continuous_abs.continuous_at
    rw [abs_ne_zero]
    rintro rfl
    simpa using h
    
  · have h_cont_mul : Continuous fun x : ℂ => x * I := continuous_id'.mul continuous_const
    refine' h_cont_mul.continuous_at.comp (continuous_of_real.continuous_at.comp _)
    exact continuous_at_arg h
    

theorem Filter.Tendsto.clog {l : Filter α} {f : α → ℂ} {x : ℂ} (h : Tendsto f l (𝓝 x)) (hx : 0 < x.re ∨ x.im ≠ 0) :
    Tendsto (fun t => log (f t)) l (𝓝 <| log x) :=
  (continuous_at_clog hx).Tendsto.comp h

variable [TopologicalSpace α]

theorem ContinuousAt.clog {f : α → ℂ} {x : α} (h₁ : ContinuousAt f x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
    ContinuousAt (fun t => log (f t)) x :=
  h₁.clog h₂

theorem ContinuousWithinAt.clog {f : α → ℂ} {s : Set α} {x : α} (h₁ : ContinuousWithinAt f s x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : ContinuousWithinAt (fun t => log (f t)) s x :=
  h₁.clog h₂

theorem ContinuousOn.clog {f : α → ℂ} {s : Set α} (h₁ : ContinuousOn f s)
    (h₂ : ∀, ∀ x ∈ s, ∀, 0 < (f x).re ∨ (f x).im ≠ 0) : ContinuousOn (fun t => log (f t)) s := fun x hx =>
  (h₁ x hx).clog (h₂ x hx)

theorem Continuous.clog {f : α → ℂ} (h₁ : Continuous f) (h₂ : ∀ x, 0 < (f x).re ∨ (f x).im ≠ 0) :
    Continuous fun t => log (f t) :=
  continuous_iff_continuous_at.2 fun x => h₁.ContinuousAt.clog (h₂ x)

end LogDeriv

