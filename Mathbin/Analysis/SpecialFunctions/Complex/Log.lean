import Mathbin.Analysis.SpecialFunctions.Complex.Arg 
import Mathbin.Analysis.SpecialFunctions.Log

/-!
# The complex `log` function

Basic properties, relationship with `exp`.
-/


noncomputable theory

namespace Complex

open Set Filter

open_locale Real TopologicalSpace

/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0`-/
@[pp_nodot]
noncomputable def log (x : ℂ) : ℂ :=
  x.abs.log+arg x*I

theorem log_re (x : ℂ) : x.log.re = x.abs.log :=
  by 
    simp [log]

theorem log_im (x : ℂ) : x.log.im = x.arg :=
  by 
    simp [log]

theorem neg_pi_lt_log_im (x : ℂ) : -π < (log x).im :=
  by 
    simp only [log_im, neg_pi_lt_arg]

theorem log_im_le_pi (x : ℂ) : (log x).im ≤ π :=
  by 
    simp only [log_im, arg_le_pi]

theorem exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x :=
  by 
    rw [log, exp_add_mul_I, ←of_real_sin, sin_arg, ←of_real_cos, cos_arg hx, ←of_real_exp, Real.exp_log (abs_pos.2 hx),
      mul_addₓ, of_real_div, of_real_div, mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), ←mul_assocₓ,
      mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), re_add_im]

@[simp]
theorem range_exp : range exp = «expr ᶜ» {0} :=
  Set.ext$
    fun x =>
      ⟨by 
          rintro ⟨x, rfl⟩
          exact exp_ne_zero x,
        fun hx => ⟨log x, exp_log hx⟩⟩

theorem log_exp {x : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π) : log (exp x) = x :=
  by 
    rw [log, abs_exp, Real.log_exp, exp_eq_exp_re_mul_sin_add_cos, ←of_real_exp,
      arg_mul_cos_add_sin_mul_I (Real.exp_pos _) ⟨hx₁, hx₂⟩, re_add_im]

theorem exp_inj_of_neg_pi_lt_of_le_pi {x y : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π) (hy₁ : -π < y.im) (hy₂ : y.im ≤ π)
  (hxy : exp x = exp y) : x = y :=
  by 
    rw [←log_exp hx₁ hx₂, ←log_exp hy₁ hy₂, hxy]

theorem of_real_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x :=
  Complex.ext
    (by 
      rw [log_re, of_real_re, abs_of_nonneg hx])
    (by 
      rw [of_real_im, log_im, arg_of_real_of_nonneg hx])

theorem log_of_real_re (x : ℝ) : (log (x : ℂ)).re = Real.log x :=
  by 
    simp [log_re]

@[simp]
theorem log_zero : log 0 = 0 :=
  by 
    simp [log]

@[simp]
theorem log_one : log 1 = 0 :=
  by 
    simp [log]

theorem log_neg_one : log (-1) = π*I :=
  by 
    simp [log]

theorem log_I : log I = (π / 2)*I :=
  by 
    simp [log]

theorem log_neg_I : log (-I) = (-(π / 2))*I :=
  by 
    simp [log]

theorem two_pi_I_ne_zero : ((2*π)*I : ℂ) ≠ 0 :=
  by 
    normNum [Real.pi_ne_zero, I_ne_zero]

-- error in Analysis.SpecialFunctions.Complex.Log: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exp_eq_one_iff
{x : exprℂ()} : «expr ↔ »(«expr = »(exp x, 1), «expr∃ , »((n : exprℤ()), «expr = »(x, «expr * »(n, «expr * »(«expr * »(2, exprπ()), I))))) :=
begin
  split,
  { intro [ident h],
    rcases [expr exists_unique_add_zsmul_mem_Ioc real.two_pi_pos x.im «expr- »(exprπ()), "with", "⟨", ident n, ",", ident hn, ",", "-", "⟩"],
    use [expr «expr- »(n)],
    rw ["[", expr int.cast_neg, ",", "<-", expr neg_mul_eq_neg_mul, ",", expr eq_neg_iff_add_eq_zero, "]"] [],
    have [] [":", expr «expr ∈ »(«expr + »(x, «expr * »(n, «expr * »(«expr * »(2, exprπ()), I))).im, Ioc «expr- »(exprπ()) exprπ())] [],
    by simpa [] [] [] ["[", expr two_mul, ",", expr mul_add, "]"] [] ["using", expr hn],
    rw ["[", "<-", expr log_exp this.1 this.2, ",", expr exp_periodic.int_mul n, ",", expr h, ",", expr log_one, "]"] [] },
  { rintro ["⟨", ident n, ",", ident rfl, "⟩"],
    exact [expr (exp_periodic.int_mul n).eq.trans exp_zero] }
end

theorem exp_eq_exp_iff_exp_sub_eq_one {x y : ℂ} : exp x = exp y ↔ exp (x - y) = 1 :=
  by 
    rw [exp_sub, div_eq_one_iff_eq (exp_ne_zero _)]

theorem exp_eq_exp_iff_exists_int {x y : ℂ} : exp x = exp y ↔ ∃ n : ℤ, x = y+n*(2*π)*I :=
  by 
    simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']

@[simp]
theorem countable_preimage_exp {s : Set ℂ} : countable (exp ⁻¹' s) ↔ countable s :=
  by 
    refine' ⟨fun hs => _, fun hs => _⟩
    ·
      refine' ((hs.image exp).insert 0).mono _ 
      rw [image_preimage_eq_inter_range, range_exp, ←diff_eq, ←union_singleton, diff_union_self]
      exact subset_union_left _ _
    ·
      rw [←bUnion_preimage_singleton]
      refine' hs.bUnion fun z hz => _ 
      rcases em (∃ w, exp w = z) with (⟨w, rfl⟩ | hne)
      ·
        simp only [preimage, mem_singleton_iff, exp_eq_exp_iff_exists_int, set_of_exists]
        exact countable_Union fun m => countable_singleton _
      ·
        pushNeg  at hne 
        simp [preimage, hne]

alias countable_preimage_exp ↔ _ Set.Countable.preimage_cexp

-- error in Analysis.SpecialFunctions.Complex.Log: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_log_nhds_within_im_neg_of_re_neg_of_im_zero
{z : exprℂ()}
(hre : «expr < »(z.re, 0))
(him : «expr = »(z.im, 0)) : tendsto log «expr𝓝[ ] »({z : exprℂ() | «expr < »(z.im, 0)}, z) «expr $ »(expr𝓝(), «expr - »(real.log (abs z), «expr * »(exprπ(), I))) :=
begin
  have [] [] [":=", expr (continuous_of_real.continuous_at.comp_continuous_within_at (continuous_abs.continuous_within_at.log _)).tendsto.add («expr $ »((continuous_of_real.tendsto _).comp, tendsto_arg_nhds_within_im_neg_of_re_neg_of_im_zero hre him).mul tendsto_const_nhds)],
  convert [] [expr this] [],
  { simp [] [] [] ["[", expr sub_eq_add_neg, "]"] [] [] },
  { lift [expr z] ["to", expr exprℝ()] ["using", expr him] [],
    simpa [] [] [] [] [] ["using", expr hre.ne] }
end

-- error in Analysis.SpecialFunctions.Complex.Log: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_within_at_log_of_re_neg_of_im_zero
{z : exprℂ()}
(hre : «expr < »(z.re, 0))
(him : «expr = »(z.im, 0)) : continuous_within_at log {z : exprℂ() | «expr ≤ »(0, z.im)} z :=
begin
  have [] [] [":=", expr (continuous_of_real.continuous_at.comp_continuous_within_at (continuous_abs.continuous_within_at.log _)).tendsto.add («expr $ »(continuous_of_real.continuous_at.comp_continuous_within_at, continuous_within_at_arg_of_re_neg_of_im_zero hre him).mul tendsto_const_nhds)],
  convert [] [expr this] [],
  { lift [expr z] ["to", expr exprℝ()] ["using", expr him] [],
    simpa [] [] [] [] [] ["using", expr hre.ne] }
end

theorem tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
  tendsto log (𝓝[{ z:ℂ | 0 ≤ z.im }] z) (𝓝$ Real.log (abs z)+π*I) :=
  by 
    simpa only [log, arg_eq_pi_iff.2 ⟨hre, him⟩] using (continuous_within_at_log_of_re_neg_of_im_zero hre him).Tendsto

end Complex

section LogDeriv

open Complex Filter

open_locale TopologicalSpace

variable{α : Type _}

-- error in Analysis.SpecialFunctions.Complex.Log: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_at_clog
{x : exprℂ()}
(h : «expr ∨ »(«expr < »(0, x.re), «expr ≠ »(x.im, 0))) : continuous_at log x :=
begin
  refine [expr continuous_at.add _ _],
  { refine [expr continuous_of_real.continuous_at.comp _],
    refine [expr (real.continuous_at_log _).comp complex.continuous_abs.continuous_at],
    rw [expr abs_ne_zero] [],
    rintro [ident rfl],
    simpa [] [] [] [] [] ["using", expr h] },
  { have [ident h_cont_mul] [":", expr continuous (λ x : exprℂ(), «expr * »(x, I))] [],
    from [expr continuous_id'.mul continuous_const],
    refine [expr h_cont_mul.continuous_at.comp (continuous_of_real.continuous_at.comp _)],
    exact [expr continuous_at_arg h] }
end

theorem Filter.Tendsto.clog {l : Filter α} {f : α → ℂ} {x : ℂ} (h : tendsto f l (𝓝 x)) (hx : 0 < x.re ∨ x.im ≠ 0) :
  tendsto (fun t => log (f t)) l (𝓝$ log x) :=
  (continuous_at_clog hx).Tendsto.comp h

variable[TopologicalSpace α]

theorem ContinuousAt.clog {f : α → ℂ} {x : α} (h₁ : ContinuousAt f x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  ContinuousAt (fun t => log (f t)) x :=
  h₁.clog h₂

theorem ContinuousWithinAt.clog {f : α → ℂ} {s : Set α} {x : α} (h₁ : ContinuousWithinAt f s x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : ContinuousWithinAt (fun t => log (f t)) s x :=
  h₁.clog h₂

theorem ContinuousOn.clog {f : α → ℂ} {s : Set α} (h₁ : ContinuousOn f s)
  (h₂ : ∀ x _ : x ∈ s, 0 < (f x).re ∨ (f x).im ≠ 0) : ContinuousOn (fun t => log (f t)) s :=
  fun x hx => (h₁ x hx).clog (h₂ x hx)

theorem Continuous.clog {f : α → ℂ} (h₁ : Continuous f) (h₂ : ∀ x, 0 < (f x).re ∨ (f x).im ≠ 0) :
  Continuous fun t => log (f t) :=
  continuous_iff_continuous_at.2$ fun x => h₁.continuous_at.clog (h₂ x)

end LogDeriv

