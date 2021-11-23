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

variable{x : ℝ}

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

theorem differentiable_on_log : DifferentiableOn ℝ log («expr ᶜ» {0}) :=
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

theorem times_cont_diff_on_log {n : WithTop ℕ} : TimesContDiffOn ℝ n log («expr ᶜ» {0}) :=
  by 
    suffices  : TimesContDiffOn ℝ ⊤ log («expr ᶜ» {0})
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

variable{f : ℝ → ℝ}{x f' : ℝ}{s : Set ℝ}

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

variable{E : Type _}[NormedGroup E][NormedSpace ℝ E]{f : E → ℝ}{x : E}{f' : E →L[ℝ] ℝ}{s : Set E}

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

theorem TimesContDiffOn.log {n} (hf : TimesContDiffOn ℝ n f s) (hs : ∀ x _ : x ∈ s, f x ≠ 0) :
  TimesContDiffOn ℝ n (fun x => log (f x)) s :=
  fun x hx => (hf x hx).log (hs x hx)

theorem TimesContDiff.log {n} (hf : TimesContDiff ℝ n f) (h : ∀ x, f x ≠ 0) : TimesContDiff ℝ n fun x => log (f x) :=
  times_cont_diff_iff_times_cont_diff_at.2$ fun x => hf.times_cont_diff_at.log (h x)

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

-- error in Analysis.SpecialFunctions.LogDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The function `x * log (1 + t / x)` tends to `t` at `+∞`. -/
theorem tendsto_mul_log_one_plus_div_at_top
(t : exprℝ()) : tendsto (λ x, «expr * »(x, log «expr + »(1, «expr / »(t, x)))) at_top (expr𝓝() t) :=
begin
  have [ident h₁] [":", expr tendsto (λ
    h, «expr * »(«expr ⁻¹»(h), log «expr + »(1, «expr * »(t, h)))) «expr𝓝[ ] »(«expr ᶜ»({0}), 0) (expr𝓝() t)] [],
  { simpa [] [] [] ["[", expr has_deriv_at_iff_tendsto_slope, "]"] [] ["using", expr ((has_deriv_at_const _ 1).add ((has_deriv_at_id (0 : exprℝ())).const_mul t)).log (by simp [] [] [] [] [] [])] },
  have [ident h₂] [":", expr tendsto (λ
    x : exprℝ(), «expr ⁻¹»(x)) at_top «expr𝓝[ ] »(«expr ᶜ»({0}), 0)] [":=", expr tendsto_inv_at_top_zero'.mono_right (nhds_within_mono _ (λ
     x hx, (set.mem_Ioi.mp hx).ne'))],
  convert [] [expr h₁.comp h₂] [],
  ext [] [] [],
  field_simp [] ["[", expr mul_comm, "]"] [] []
end

open_locale BigOperators

-- error in Analysis.SpecialFunctions.LogDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A crude lemma estimating the difference between `log (1-x)` and its Taylor series at `0`,
where the main point of the bound is that it tends to `0`. The goal is to deduce the series
expansion of the logarithm, in `has_sum_pow_div_log_of_abs_lt_1`.
-/
theorem abs_log_sub_add_sum_range_le
{x : exprℝ()}
(h : «expr < »(«expr| |»(x), 1))
(n : exprℕ()) : «expr ≤ »(«expr| |»(«expr + »(«expr∑ in , »((i), range n, «expr / »(«expr ^ »(x, «expr + »(i, 1)), «expr + »(i, 1))), log «expr - »(1, x))), «expr / »(«expr ^ »(«expr| |»(x), «expr + »(n, 1)), «expr - »(1, «expr| |»(x)))) :=
begin
  let [ident F] [":", expr exprℝ() → exprℝ()] [":=", expr λ
   x, «expr + »(«expr∑ in , »((i), range n, «expr / »(«expr ^ »(x, «expr + »(i, 1)), «expr + »(i, 1))), log «expr - »(1, x))],
  have [ident A] [":", expr ∀
   y «expr ∈ » Ioo («expr- »(1) : exprℝ()) 1, «expr = »(deriv F y, «expr / »(«expr- »(«expr ^ »(y, n)), «expr - »(1, y)))] [],
  { assume [binders (y hy)],
    have [] [":", expr «expr = »(«expr∑ in , »((i), range n, «expr / »(«expr * »(«expr + »(«expr↑ »(i), 1), «expr ^ »(y, i)), «expr + »(«expr↑ »(i), 1))), «expr∑ in , »((i), range n, «expr ^ »(y, i)))] [],
    { congr' [] ["with", ident i],
      have [] [":", expr «expr ≠ »(«expr + »((i : exprℝ()), 1), 0)] [":=", expr ne_of_gt (nat.cast_add_one_pos i)],
      field_simp [] ["[", expr this, ",", expr mul_comm, "]"] [] [] },
    field_simp [] ["[", expr F, ",", expr this, ",", "<-", expr geom_sum_def, ",", expr geom_sum_eq (ne_of_lt hy.2), ",", expr sub_ne_zero_of_ne (ne_of_gt hy.2), ",", expr sub_ne_zero_of_ne (ne_of_lt hy.2), "]"] [] [],
    ring [] },
  have [ident B] [":", expr ∀
   y «expr ∈ » Icc «expr- »(«expr| |»(x)) «expr| |»(x), «expr ≤ »(«expr| |»(deriv F y), «expr / »(«expr ^ »(«expr| |»(x), n), «expr - »(1, «expr| |»(x))))] [],
  { assume [binders (y hy)],
    have [] [":", expr «expr ∈ »(y, Ioo «expr- »((1 : exprℝ())) 1)] [":=", expr ⟨lt_of_lt_of_le (neg_lt_neg h) hy.1, lt_of_le_of_lt hy.2 h⟩],
    calc
      «expr = »(«expr| |»(deriv F y), «expr| |»(«expr / »(«expr- »(«expr ^ »(y, n)), «expr - »(1, y)))) : by rw ["[", expr A y this, "]"] []
      «expr ≤ »(..., «expr / »(«expr ^ »(«expr| |»(x), n), «expr - »(1, «expr| |»(x)))) : begin
        have [] [":", expr «expr ≤ »(«expr| |»(y), «expr| |»(x))] [":=", expr abs_le.2 hy],
        have [] [":", expr «expr < »(0, «expr - »(1, «expr| |»(x)))] [],
        by linarith [] [] [],
        have [] [":", expr «expr ≤ »(«expr - »(1, «expr| |»(x)), «expr| |»(«expr - »(1, y)))] [":=", expr le_trans (by linarith [] [] ["[", expr hy.2, "]"]) (le_abs_self _)],
        simp [] [] ["only"] ["[", "<-", expr pow_abs, ",", expr abs_div, ",", expr abs_neg, "]"] [] [],
        apply_rules ["[", expr div_le_div, ",", expr pow_nonneg, ",", expr abs_nonneg, ",", expr pow_le_pow_of_le_left, "]"]
      end },
  have [ident C] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(F x, F 0)), «expr * »(«expr / »(«expr ^ »(«expr| |»(x), n), «expr - »(1, «expr| |»(x))), «expr∥ ∥»(«expr - »(x, 0))))] [],
  { have [] [":", expr ∀ y «expr ∈ » Icc «expr- »(«expr| |»(x)) «expr| |»(x), differentiable_at exprℝ() F y] [],
    { assume [binders (y hy)],
      have [] [":", expr «expr ≠ »(«expr - »(1, y), 0)] [":=", expr sub_ne_zero_of_ne (ne_of_gt (lt_of_le_of_lt hy.2 h))],
      simp [] [] [] ["[", expr F, ",", expr this, "]"] [] [] },
    apply [expr convex.norm_image_sub_le_of_norm_deriv_le this B (convex_Icc _ _) _ _],
    { simpa [] [] [] [] [] ["using", expr abs_nonneg x] },
    { simp [] [] [] ["[", expr le_abs_self x, ",", expr neg_le.mp (neg_le_abs_self x), "]"] [] [] } },
  simpa [] [] [] ["[", expr F, ",", expr norm_eq_abs, ",", expr div_mul_eq_mul_div, ",", expr pow_succ', "]"] [] ["using", expr C]
end

-- error in Analysis.SpecialFunctions.LogDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Power series expansion of the logarithm around `1`. -/
theorem has_sum_pow_div_log_of_abs_lt_1
{x : exprℝ()}
(h : «expr < »(«expr| |»(x), 1)) : has_sum (λ
 n : exprℕ(), «expr / »(«expr ^ »(x, «expr + »(n, 1)), «expr + »(n, 1))) «expr- »(log «expr - »(1, x)) :=
begin
  rw [expr summable.has_sum_iff_tendsto_nat] [],
  show [expr tendsto (λ
    n : exprℕ(), «expr∑ in , »((i : exprℕ()), range n, «expr / »(«expr ^ »(x, «expr + »(i, 1)), «expr + »(i, 1)))) at_top (expr𝓝() «expr- »(log «expr - »(1, x)))],
  { rw ["[", expr tendsto_iff_norm_tendsto_zero, "]"] [],
    simp [] [] ["only"] ["[", expr norm_eq_abs, ",", expr sub_neg_eq_add, "]"] [] [],
    refine [expr squeeze_zero (λ n, abs_nonneg _) (abs_log_sub_add_sum_range_le h) _],
    suffices [] [":", expr tendsto (λ
      t : exprℕ(), «expr / »(«expr ^ »(«expr| |»(x), «expr + »(t, 1)), «expr - »(1, «expr| |»(x)))) at_top (expr𝓝() «expr / »(«expr * »(«expr| |»(x), 0), «expr - »(1, «expr| |»(x))))],
    by simpa [] [] [] [] [] [],
    simp [] [] ["only"] ["[", expr pow_succ, "]"] [] [],
    refine [expr (tendsto_const_nhds.mul _).div_const],
    exact [expr tendsto_pow_at_top_nhds_0_of_lt_1 (abs_nonneg _) h] },
  show [expr summable (λ n : exprℕ(), «expr / »(«expr ^ »(x, «expr + »(n, 1)), «expr + »(n, 1)))],
  { refine [expr summable_of_norm_bounded _ (summable_geometric_of_lt_1 (abs_nonneg _) h) (λ i, _)],
    calc
      «expr = »(«expr∥ ∥»(«expr / »(«expr ^ »(x, «expr + »(i, 1)), «expr + »(i, 1))), «expr / »(«expr ^ »(«expr| |»(x), «expr + »(i, 1)), «expr + »(i, 1))) : begin
        have [] [":", expr «expr ≤ »((0 : exprℝ()), «expr + »(i, 1))] [":=", expr le_of_lt (nat.cast_add_one_pos i)],
        rw ["[", expr norm_eq_abs, ",", expr abs_div, ",", "<-", expr pow_abs, ",", expr abs_of_nonneg this, "]"] []
      end
      «expr ≤ »(..., «expr / »(«expr ^ »(«expr| |»(x), «expr + »(i, 1)), «expr + »(0, 1))) : begin
        apply_rules ["[", expr div_le_div_of_le_left, ",", expr pow_nonneg, ",", expr abs_nonneg, ",", expr add_le_add_right, ",", expr i.cast_nonneg, "]"],
        norm_num [] []
      end
      «expr ≤ »(..., «expr ^ »(«expr| |»(x), i)) : by simpa [] [] [] ["[", expr pow_succ', "]"] [] ["using", expr mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) i) (le_of_lt h)] }
end

end Real

