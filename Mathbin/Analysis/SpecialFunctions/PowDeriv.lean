import Mathbin.Analysis.SpecialFunctions.Pow 
import Mathbin.Analysis.SpecialFunctions.Complex.LogDeriv 
import Mathbin.Analysis.Calculus.ExtendDeriv 
import Mathbin.Analysis.SpecialFunctions.LogDeriv 
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Derivatives of power function on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`

We also prove differentiability and provide derivatives for the power functions `x ^ y`.
-/


noncomputable theory

open_locale Classical Real TopologicalSpace Nnreal Ennreal Filter

open Filter

namespace Complex

-- error in Analysis.SpecialFunctions.PowDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_strict_fderiv_at_cpow
{p : «expr × »(exprℂ(), exprℂ())}
(hp : «expr ∨ »(«expr < »(0, p.1.re), «expr ≠ »(p.1.im, 0))) : has_strict_fderiv_at (λ
 x : «expr × »(exprℂ(), exprℂ()), «expr ^ »(x.1, x.2)) «expr + »(«expr • »(«expr * »(p.2, «expr ^ »(p.1, «expr - »(p.2, 1))), continuous_linear_map.fst exprℂ() exprℂ() exprℂ()), «expr • »(«expr * »(«expr ^ »(p.1, p.2), log p.1), continuous_linear_map.snd exprℂ() exprℂ() exprℂ())) p :=
begin
  have [ident A] [":", expr «expr ≠ »(p.1, 0)] [],
  by { intro [ident h],
    simpa [] [] [] ["[", expr h, ",", expr lt_irrefl, "]"] [] ["using", expr hp] },
  have [] [":", expr «expr =ᶠ[ ] »(λ
    x : «expr × »(exprℂ(), exprℂ()), «expr ^ »(x.1, x.2), expr𝓝() p, λ x, exp «expr * »(log x.1, x.2))] [],
  from [expr ((is_open_ne.preimage continuous_fst).eventually_mem A).mono (λ p hp, cpow_def_of_ne_zero hp _)],
  rw ["[", expr cpow_sub _ _ A, ",", expr cpow_one, ",", expr mul_div_comm, ",", expr mul_smul, ",", expr mul_smul, ",", "<-", expr smul_add, "]"] [],
  refine [expr has_strict_fderiv_at.congr_of_eventually_eq _ this.symm],
  simpa [] [] ["only"] ["[", expr cpow_def_of_ne_zero A, ",", expr div_eq_mul_inv, ",", expr mul_smul, ",", expr add_comm, "]"] [] ["using", expr ((has_strict_fderiv_at_fst.clog hp).mul has_strict_fderiv_at_snd).cexp]
end

theorem has_strict_fderiv_at_cpow' {x y : ℂ} (hp : 0 < x.re ∨ x.im ≠ 0) :
  HasStrictFderivAt (fun x : ℂ × ℂ => x.1^x.2)
    (((y*x^y - 1) • ContinuousLinearMap.fst ℂ ℂ ℂ)+((x^y)*log x) • ContinuousLinearMap.snd ℂ ℂ ℂ) (x, y) :=
  @has_strict_fderiv_at_cpow (x, y) hp

theorem has_strict_deriv_at_const_cpow {x y : ℂ} (h : x ≠ 0 ∨ y ≠ 0) :
  HasStrictDerivAt (fun y => x^y) ((x^y)*log x) y :=
  by 
    rcases em (x = 0) with (rfl | hx)
    ·
      replace h := h.neg_resolve_left rfl 
      rw [log_zero, mul_zero]
      refine' (has_strict_deriv_at_const _ 0).congr_of_eventually_eq _ 
      exact (is_open_ne.eventually_mem h).mono fun y hy => (zero_cpow hy).symm
    ·
      simpa only [cpow_def_of_ne_zero hx, mul_oneₓ] using ((has_strict_deriv_at_id y).const_mul (log x)).cexp

theorem has_fderiv_at_cpow {p : ℂ × ℂ} (hp : 0 < p.1.re ∨ p.1.im ≠ 0) :
  HasFderivAt (fun x : ℂ × ℂ => x.1^x.2)
    (((p.2*p.1^p.2 - 1) • ContinuousLinearMap.fst ℂ ℂ ℂ)+((p.1^p.2)*log p.1) • ContinuousLinearMap.snd ℂ ℂ ℂ) p :=
  (has_strict_fderiv_at_cpow hp).HasFderivAt

end Complex

section fderiv

open Complex

variable{E : Type _}[NormedGroup E][NormedSpace ℂ E]{f g : E → ℂ}{f' g' : E →L[ℂ] ℂ}{x : E}{s : Set E}{c : ℂ}

theorem HasStrictFderivAt.cpow (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x)
  (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  HasStrictFderivAt (fun x => f x^g x) (((g x*f x^g x - 1) • f')+((f x^g x)*log (f x)) • g') x :=
  by 
    convert (@has_strict_fderiv_at_cpow ((fun x => (f x, g x)) x) h0).comp x (hf.prod hg)

theorem HasStrictFderivAt.const_cpow (hf : HasStrictFderivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
  HasStrictFderivAt (fun x => c^f x) (((c^f x)*log c) • f') x :=
  (has_strict_deriv_at_const_cpow h0).comp_has_strict_fderiv_at x hf

theorem HasFderivAt.cpow (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  HasFderivAt (fun x => f x^g x) (((g x*f x^g x - 1) • f')+((f x^g x)*log (f x)) • g') x :=
  by 
    convert (@Complex.has_fderiv_at_cpow ((fun x => (f x, g x)) x) h0).comp x (hf.prod hg)

theorem HasFderivAt.const_cpow (hf : HasFderivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
  HasFderivAt (fun x => c^f x) (((c^f x)*log c) • f') x :=
  (has_strict_deriv_at_const_cpow h0).HasDerivAt.comp_has_fderiv_at x hf

theorem HasFderivWithinAt.cpow (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt g g' s x)
  (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  HasFderivWithinAt (fun x => f x^g x) (((g x*f x^g x - 1) • f')+((f x^g x)*log (f x)) • g') s x :=
  by 
    convert (@Complex.has_fderiv_at_cpow ((fun x => (f x, g x)) x) h0).comp_has_fderiv_within_at x (hf.prod hg)

theorem HasFderivWithinAt.const_cpow (hf : HasFderivWithinAt f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
  HasFderivWithinAt (fun x => c^f x) (((c^f x)*log c) • f') s x :=
  (has_strict_deriv_at_const_cpow h0).HasDerivAt.comp_has_fderiv_within_at x hf

theorem DifferentiableAt.cpow (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x)
  (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) : DifferentiableAt ℂ (fun x => f x^g x) x :=
  (hf.has_fderiv_at.cpow hg.has_fderiv_at h0).DifferentiableAt

theorem DifferentiableAt.const_cpow (hf : DifferentiableAt ℂ f x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
  DifferentiableAt ℂ (fun x => c^f x) x :=
  (hf.has_fderiv_at.const_cpow h0).DifferentiableAt

theorem DifferentiableWithinAt.cpow (hf : DifferentiableWithinAt ℂ f s x) (hg : DifferentiableWithinAt ℂ g s x)
  (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) : DifferentiableWithinAt ℂ (fun x => f x^g x) s x :=
  (hf.has_fderiv_within_at.cpow hg.has_fderiv_within_at h0).DifferentiableWithinAt

theorem DifferentiableWithinAt.const_cpow (hf : DifferentiableWithinAt ℂ f s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
  DifferentiableWithinAt ℂ (fun x => c^f x) s x :=
  (hf.has_fderiv_within_at.const_cpow h0).DifferentiableWithinAt

end fderiv

section deriv

open Complex

variable{f g : ℂ → ℂ}{s : Set ℂ}{f' g' x c : ℂ}

/-- A private lemma that rewrites the output of lemmas like `has_fderiv_at.cpow` to the form
expected by lemmas like `has_deriv_at.cpow`. -/
private theorem aux :
  (((g x*f x^g x - 1) • (1 : ℂ →L[ℂ] ℂ).smulRight f')+((f x^g x)*log (f x)) • (1 : ℂ →L[ℂ] ℂ).smulRight g') 1 =
    ((g x*f x^g x - 1)*f')+((f x^g x)*log (f x))*g' :=
  by 
    simp only [Algebra.id.smul_eq_mul, one_mulₓ, ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_right_apply,
      ContinuousLinearMap.add_apply, Pi.smul_apply, ContinuousLinearMap.coe_smul']

theorem HasStrictDerivAt.cpow (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x)
  (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  HasStrictDerivAt (fun x => f x^g x) (((g x*f x^g x - 1)*f')+((f x^g x)*log (f x))*g') x :=
  by 
    simpa only [aux] using (hf.cpow hg h0).HasStrictDerivAt

theorem HasStrictDerivAt.const_cpow (hf : HasStrictDerivAt f f' x) (h : c ≠ 0 ∨ f x ≠ 0) :
  HasStrictDerivAt (fun x => c^f x) (((c^f x)*log c)*f') x :=
  (has_strict_deriv_at_const_cpow h).comp x hf

theorem Complex.has_strict_deriv_at_cpow_const (h : 0 < x.re ∨ x.im ≠ 0) :
  HasStrictDerivAt (fun z : ℂ => z^c) (c*x^c - 1) x :=
  by 
    simpa only [mul_zero, add_zeroₓ, mul_oneₓ] using (has_strict_deriv_at_id x).cpow (has_strict_deriv_at_const x c) h

theorem HasStrictDerivAt.cpow_const (hf : HasStrictDerivAt f f' x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  HasStrictDerivAt (fun x => f x^c) ((c*f x^c - 1)*f') x :=
  (Complex.has_strict_deriv_at_cpow_const h0).comp x hf

theorem HasDerivAt.cpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  HasDerivAt (fun x => f x^g x) (((g x*f x^g x - 1)*f')+((f x^g x)*log (f x))*g') x :=
  by 
    simpa only [aux] using (hf.has_fderiv_at.cpow hg h0).HasDerivAt

theorem HasDerivAt.const_cpow (hf : HasDerivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
  HasDerivAt (fun x => c^f x) (((c^f x)*log c)*f') x :=
  (has_strict_deriv_at_const_cpow h0).HasDerivAt.comp x hf

theorem HasDerivAt.cpow_const (hf : HasDerivAt f f' x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  HasDerivAt (fun x => f x^c) ((c*f x^c - 1)*f') x :=
  (Complex.has_strict_deriv_at_cpow_const h0).HasDerivAt.comp x hf

theorem HasDerivWithinAt.cpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
  (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  HasDerivWithinAt (fun x => f x^g x) (((g x*f x^g x - 1)*f')+((f x^g x)*log (f x))*g') s x :=
  by 
    simpa only [aux] using (hf.has_fderiv_within_at.cpow hg h0).HasDerivWithinAt

theorem HasDerivWithinAt.const_cpow (hf : HasDerivWithinAt f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
  HasDerivWithinAt (fun x => c^f x) (((c^f x)*log c)*f') s x :=
  (has_strict_deriv_at_const_cpow h0).HasDerivAt.comp_has_deriv_within_at x hf

theorem HasDerivWithinAt.cpow_const (hf : HasDerivWithinAt f f' s x) (h0 : 0 < (f x).re ∨ (f x).im ≠ 0) :
  HasDerivWithinAt (fun x => f x^c) ((c*f x^c - 1)*f') s x :=
  (Complex.has_strict_deriv_at_cpow_const h0).HasDerivAt.comp_has_deriv_within_at x hf

end deriv

namespace Real

variable{x y z : ℝ}

-- error in Analysis.SpecialFunctions.PowDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `0 < p.fst`. -/
theorem has_strict_fderiv_at_rpow_of_pos
(p : «expr × »(exprℝ(), exprℝ()))
(hp : «expr < »(0, p.1)) : has_strict_fderiv_at (λ
 x : «expr × »(exprℝ(), exprℝ()), «expr ^ »(x.1, x.2)) «expr + »(«expr • »(«expr * »(p.2, «expr ^ »(p.1, «expr - »(p.2, 1))), continuous_linear_map.fst exprℝ() exprℝ() exprℝ()), «expr • »(«expr * »(«expr ^ »(p.1, p.2), log p.1), continuous_linear_map.snd exprℝ() exprℝ() exprℝ())) p :=
begin
  have [] [":", expr «expr =ᶠ[ ] »(λ
    x : «expr × »(exprℝ(), exprℝ()), «expr ^ »(x.1, x.2), expr𝓝() p, λ x, exp «expr * »(log x.1, x.2))] [],
  from [expr (continuous_at_fst.eventually (lt_mem_nhds hp)).mono (λ p hp, rpow_def_of_pos hp _)],
  refine [expr has_strict_fderiv_at.congr_of_eventually_eq _ this.symm],
  convert [] [expr ((has_strict_fderiv_at_fst.log hp.ne').mul has_strict_fderiv_at_snd).exp] [],
  rw ["[", expr rpow_sub_one hp.ne', ",", "<-", expr rpow_def_of_pos hp, ",", expr smul_add, ",", expr smul_smul, ",", expr mul_div_comm, ",", expr div_eq_mul_inv, ",", expr smul_smul, ",", expr smul_smul, ",", expr mul_assoc, ",", expr add_comm, "]"] []
end

-- error in Analysis.SpecialFunctions.PowDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `p.fst < 0`. -/
theorem has_strict_fderiv_at_rpow_of_neg
(p : «expr × »(exprℝ(), exprℝ()))
(hp : «expr < »(p.1, 0)) : has_strict_fderiv_at (λ
 x : «expr × »(exprℝ(), exprℝ()), «expr ^ »(x.1, x.2)) «expr + »(«expr • »(«expr * »(p.2, «expr ^ »(p.1, «expr - »(p.2, 1))), continuous_linear_map.fst exprℝ() exprℝ() exprℝ()), «expr • »(«expr - »(«expr * »(«expr ^ »(p.1, p.2), log p.1), «expr * »(«expr * »(exp «expr * »(log p.1, p.2), sin «expr * »(p.2, exprπ())), exprπ())), continuous_linear_map.snd exprℝ() exprℝ() exprℝ())) p :=
begin
  have [] [":", expr «expr =ᶠ[ ] »(λ
    x : «expr × »(exprℝ(), exprℝ()), «expr ^ »(x.1, x.2), expr𝓝() p, λ
    x, «expr * »(exp «expr * »(log x.1, x.2), cos «expr * »(x.2, exprπ())))] [],
  from [expr (continuous_at_fst.eventually (gt_mem_nhds hp)).mono (λ p hp, rpow_def_of_neg hp _)],
  refine [expr has_strict_fderiv_at.congr_of_eventually_eq _ this.symm],
  convert [] [expr ((has_strict_fderiv_at_fst.log hp.ne).mul has_strict_fderiv_at_snd).exp.mul (has_strict_fderiv_at_snd.mul_const _).cos] ["using", 1],
  simp_rw ["[", expr rpow_sub_one hp.ne, ",", expr smul_add, ",", "<-", expr add_assoc, ",", expr smul_smul, ",", "<-", expr add_smul, ",", "<-", expr mul_assoc, ",", expr mul_comm (cos _), ",", "<-", expr rpow_def_of_neg hp, "]"] [],
  rw ["[", expr div_eq_mul_inv, ",", expr add_comm, "]"] [],
  congr' [2] []; ring []
end

/-- The function `λ (x, y), x ^ y` is infinitely smooth at `(x, y)` unless `x = 0`. -/
theorem times_cont_diff_at_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) {n : WithTop ℕ} :
  TimesContDiffAt ℝ n (fun p : ℝ × ℝ => p.1^p.2) p :=
  by 
    cases' hp.lt_or_lt with hneg hpos 
    exacts[(((times_cont_diff_at_fst.log hneg.ne).mul times_cont_diff_at_snd).exp.mul
            (times_cont_diff_at_snd.mul times_cont_diff_at_const).cos).congr_of_eventually_eq
        ((continuous_at_fst.eventually (gt_mem_nhds hneg)).mono fun p hp => rpow_def_of_neg hp _),
      ((times_cont_diff_at_fst.log hpos.ne').mul times_cont_diff_at_snd).exp.congr_of_eventually_eq
        ((continuous_at_fst.eventually (lt_mem_nhds hpos)).mono fun p hp => rpow_def_of_pos hp _)]

theorem differentiable_at_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1^p.2) p :=
  (times_cont_diff_at_rpow_of_ne p hp).DifferentiableAt le_rfl

theorem _root_.has_strict_deriv_at.rpow {f g : ℝ → ℝ} {f' g' : ℝ} (hf : HasStrictDerivAt f f' x)
  (hg : HasStrictDerivAt g g' x) (h : 0 < f x) :
  HasStrictDerivAt (fun x => f x^g x) (((f'*g x)*f x^g x - 1)+(g'*f x^g x)*log (f x)) x :=
  by 
    convert (has_strict_fderiv_at_rpow_of_pos ((fun x => (f x, g x)) x) h).comp_has_strict_deriv_at _ (hf.prod hg) using
      1
    simp [mul_assocₓ, mul_commₓ, mul_left_commₓ]

-- error in Analysis.SpecialFunctions.PowDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_strict_deriv_at_rpow_const_of_ne
{x : exprℝ()}
(hx : «expr ≠ »(x, 0))
(p : exprℝ()) : has_strict_deriv_at (λ x, «expr ^ »(x, p)) «expr * »(p, «expr ^ »(x, «expr - »(p, 1))) x :=
begin
  cases [expr hx.lt_or_lt] ["with", ident hx, ident hx],
  { have [] [] [":=", expr (has_strict_fderiv_at_rpow_of_neg (x, p) hx).comp_has_strict_deriv_at x ((has_strict_deriv_at_id x).prod (has_strict_deriv_at_const _ _))],
    convert [] [expr this] [],
    simp [] [] [] [] [] [] },
  { simpa [] [] [] [] [] ["using", expr (has_strict_deriv_at_id x).rpow (has_strict_deriv_at_const x p) hx] }
end

theorem has_strict_deriv_at_const_rpow {a : ℝ} (ha : 0 < a) (x : ℝ) : HasStrictDerivAt (fun x => a^x) ((a^x)*log a) x :=
  by 
    simpa using (has_strict_deriv_at_const _ _).rpow (has_strict_deriv_at_id x) ha

/-- This lemma says that `λ x, a ^ x` is strictly differentiable for `a < 0`. Note that these
values of `a` are outside of the "official" domain of `a ^ x`, and we may redefine `a ^ x`
for negative `a` if some other definition will be more convenient. -/
theorem has_strict_deriv_at_const_rpow_of_neg {a x : ℝ} (ha : a < 0) :
  HasStrictDerivAt (fun x => a^x) (((a^x)*log a) - (exp (log a*x)*sin (x*π))*π) x :=
  by 
    simpa using
      (has_strict_fderiv_at_rpow_of_neg (a, x) ha).comp_has_strict_deriv_at x
        ((has_strict_deriv_at_const _ _).Prod (has_strict_deriv_at_id _))

end Real

namespace Real

variable{z x y : ℝ}

theorem has_deriv_at_rpow_const {x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p) : HasDerivAt (fun x => x^p) (p*x^p - 1) x :=
  by 
    rcases ne_or_eq x 0 with (hx | rfl)
    ·
      exact (has_strict_deriv_at_rpow_const_of_ne hx _).HasDerivAt 
    replace h : 1 ≤ p := h.neg_resolve_left rfl 
    apply has_deriv_at_of_has_deriv_at_of_ne fun x hx => (has_strict_deriv_at_rpow_const_of_ne hx p).HasDerivAt 
    exacts[continuous_at_id.rpow_const (Or.inr (zero_le_one.trans h)),
      continuous_at_const.mul (continuous_at_id.rpow_const (Or.inr (sub_nonneg.2 h)))]

theorem differentiable_rpow_const {p : ℝ} (hp : 1 ≤ p) : Differentiable ℝ fun x : ℝ => x^p :=
  fun x => (has_deriv_at_rpow_const (Or.inr hp)).DifferentiableAt

theorem deriv_rpow_const {x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p) : deriv (fun x : ℝ => x^p) x = p*x^p - 1 :=
  (has_deriv_at_rpow_const h).deriv

theorem deriv_rpow_const' {p : ℝ} (h : 1 ≤ p) : (deriv fun x : ℝ => x^p) = fun x => p*x^p - 1 :=
  funext$ fun x => deriv_rpow_const (Or.inr h)

theorem times_cont_diff_at_rpow_const_of_ne {x p : ℝ} {n : WithTop ℕ} (h : x ≠ 0) :
  TimesContDiffAt ℝ n (fun x => x^p) x :=
  (times_cont_diff_at_rpow_of_ne (x, p) h).comp x (times_cont_diff_at_id.Prod times_cont_diff_at_const)

-- error in Analysis.SpecialFunctions.PowDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem times_cont_diff_rpow_const_of_le
{p : exprℝ()}
{n : exprℕ()}
(h : «expr ≤ »(«expr↑ »(n), p)) : times_cont_diff exprℝ() n (λ x : exprℝ(), «expr ^ »(x, p)) :=
begin
  induction [expr n] [] ["with", ident n, ident ihn] ["generalizing", ident p],
  { exact [expr times_cont_diff_zero.2 (continuous_id.rpow_const (λ x, or.inr h))] },
  { have [ident h1] [":", expr «expr ≤ »(1, p)] [],
    from [expr le_trans (by simp [] [] [] [] [] []) h],
    rw ["[", expr nat.cast_succ, ",", "<-", expr le_sub_iff_add_le, "]"] ["at", ident h],
    simpa [] [] [] ["[", expr times_cont_diff_succ_iff_deriv, ",", expr differentiable_rpow_const, ",", expr h1, ",", expr deriv_rpow_const', "]"] [] ["using", expr times_cont_diff_const.mul (ihn h)] }
end

theorem times_cont_diff_at_rpow_const_of_le {x p : ℝ} {n : ℕ} (h : «expr↑ » n ≤ p) :
  TimesContDiffAt ℝ n (fun x : ℝ => x^p) x :=
  (times_cont_diff_rpow_const_of_le h).TimesContDiffAt

theorem times_cont_diff_at_rpow_const {x p : ℝ} {n : ℕ} (h : x ≠ 0 ∨ «expr↑ » n ≤ p) :
  TimesContDiffAt ℝ n (fun x : ℝ => x^p) x :=
  h.elim times_cont_diff_at_rpow_const_of_ne times_cont_diff_at_rpow_const_of_le

theorem has_strict_deriv_at_rpow_const {x p : ℝ} (hx : x ≠ 0 ∨ 1 ≤ p) : HasStrictDerivAt (fun x => x^p) (p*x^p - 1) x :=
  TimesContDiffAt.has_strict_deriv_at'
    (times_cont_diff_at_rpow_const
      (by 
        rwa [Nat.cast_one]))
    (has_deriv_at_rpow_const hx) le_rfl

end Real

section Differentiability

open Real

section fderiv

variable{E :
    Type _}[NormedGroup E][NormedSpace ℝ E]{f g : E → ℝ}{f' g' : E →L[ℝ] ℝ}{x : E}{s : Set E}{c p : ℝ}{n : WithTop ℕ}

theorem HasFderivWithinAt.rpow (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt g g' s x) (h : 0 < f x) :
  HasFderivWithinAt (fun x => f x^g x) (((g x*f x^g x - 1) • f')+((f x^g x)*log (f x)) • g') s x :=
  (has_strict_fderiv_at_rpow_of_pos (f x, g x) h).HasFderivAt.comp_has_fderiv_within_at x (hf.prod hg)

theorem HasFderivAt.rpow (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x) (h : 0 < f x) :
  HasFderivAt (fun x => f x^g x) (((g x*f x^g x - 1) • f')+((f x^g x)*log (f x)) • g') x :=
  (has_strict_fderiv_at_rpow_of_pos (f x, g x) h).HasFderivAt.comp x (hf.prod hg)

theorem HasStrictFderivAt.rpow (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x) (h : 0 < f x) :
  HasStrictFderivAt (fun x => f x^g x) (((g x*f x^g x - 1) • f')+((f x^g x)*log (f x)) • g') x :=
  (has_strict_fderiv_at_rpow_of_pos (f x, g x) h).comp x (hf.prod hg)

theorem DifferentiableWithinAt.rpow (hf : DifferentiableWithinAt ℝ f s x) (hg : DifferentiableWithinAt ℝ g s x)
  (h : f x ≠ 0) : DifferentiableWithinAt ℝ (fun x => f x^g x) s x :=
  (differentiable_at_rpow_of_ne (f x, g x) h).comp_differentiable_within_at x (hf.prod hg)

theorem DifferentiableAt.rpow (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (h : f x ≠ 0) :
  DifferentiableAt ℝ (fun x => f x^g x) x :=
  (differentiable_at_rpow_of_ne (f x, g x) h).comp x (hf.prod hg)

theorem DifferentiableOn.rpow (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s) (h : ∀ x _ : x ∈ s, f x ≠ 0) :
  DifferentiableOn ℝ (fun x => f x^g x) s :=
  fun x hx => (hf x hx).rpow (hg x hx) (h x hx)

theorem Differentiable.rpow (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (h : ∀ x, f x ≠ 0) :
  Differentiable ℝ fun x => f x^g x :=
  fun x => (hf x).rpow (hg x) (h x)

theorem HasFderivWithinAt.rpow_const (hf : HasFderivWithinAt f f' s x) (h : f x ≠ 0 ∨ 1 ≤ p) :
  HasFderivWithinAt (fun x => f x^p) ((p*f x^p - 1) • f') s x :=
  (has_deriv_at_rpow_const h).comp_has_fderiv_within_at x hf

theorem HasFderivAt.rpow_const (hf : HasFderivAt f f' x) (h : f x ≠ 0 ∨ 1 ≤ p) :
  HasFderivAt (fun x => f x^p) ((p*f x^p - 1) • f') x :=
  (has_deriv_at_rpow_const h).comp_has_fderiv_at x hf

theorem HasStrictFderivAt.rpow_const (hf : HasStrictFderivAt f f' x) (h : f x ≠ 0 ∨ 1 ≤ p) :
  HasStrictFderivAt (fun x => f x^p) ((p*f x^p - 1) • f') x :=
  (has_strict_deriv_at_rpow_const h).comp_has_strict_fderiv_at x hf

theorem DifferentiableWithinAt.rpow_const (hf : DifferentiableWithinAt ℝ f s x) (h : f x ≠ 0 ∨ 1 ≤ p) :
  DifferentiableWithinAt ℝ (fun x => f x^p) s x :=
  (hf.has_fderiv_within_at.rpow_const h).DifferentiableWithinAt

@[simp]
theorem DifferentiableAt.rpow_const (hf : DifferentiableAt ℝ f x) (h : f x ≠ 0 ∨ 1 ≤ p) :
  DifferentiableAt ℝ (fun x => f x^p) x :=
  (hf.has_fderiv_at.rpow_const h).DifferentiableAt

theorem DifferentiableOn.rpow_const (hf : DifferentiableOn ℝ f s) (h : ∀ x _ : x ∈ s, f x ≠ 0 ∨ 1 ≤ p) :
  DifferentiableOn ℝ (fun x => f x^p) s :=
  fun x hx => (hf x hx).rpow_const (h x hx)

theorem Differentiable.rpow_const (hf : Differentiable ℝ f) (h : ∀ x, f x ≠ 0 ∨ 1 ≤ p) :
  Differentiable ℝ fun x => f x^p :=
  fun x => (hf x).rpow_const (h x)

theorem HasFderivWithinAt.const_rpow (hf : HasFderivWithinAt f f' s x) (hc : 0 < c) :
  HasFderivWithinAt (fun x => c^f x) (((c^f x)*log c) • f') s x :=
  (has_strict_deriv_at_const_rpow hc (f x)).HasDerivAt.comp_has_fderiv_within_at x hf

theorem HasFderivAt.const_rpow (hf : HasFderivAt f f' x) (hc : 0 < c) :
  HasFderivAt (fun x => c^f x) (((c^f x)*log c) • f') x :=
  (has_strict_deriv_at_const_rpow hc (f x)).HasDerivAt.comp_has_fderiv_at x hf

theorem HasStrictFderivAt.const_rpow (hf : HasStrictFderivAt f f' x) (hc : 0 < c) :
  HasStrictFderivAt (fun x => c^f x) (((c^f x)*log c) • f') x :=
  (has_strict_deriv_at_const_rpow hc (f x)).comp_has_strict_fderiv_at x hf

theorem TimesContDiffWithinAt.rpow (hf : TimesContDiffWithinAt ℝ n f s x) (hg : TimesContDiffWithinAt ℝ n g s x)
  (h : f x ≠ 0) : TimesContDiffWithinAt ℝ n (fun x => f x^g x) s x :=
  (times_cont_diff_at_rpow_of_ne (f x, g x) h).comp_times_cont_diff_within_at x (hf.prod hg)

theorem TimesContDiffAt.rpow (hf : TimesContDiffAt ℝ n f x) (hg : TimesContDiffAt ℝ n g x) (h : f x ≠ 0) :
  TimesContDiffAt ℝ n (fun x => f x^g x) x :=
  (times_cont_diff_at_rpow_of_ne (f x, g x) h).comp x (hf.prod hg)

theorem TimesContDiffOn.rpow (hf : TimesContDiffOn ℝ n f s) (hg : TimesContDiffOn ℝ n g s)
  (h : ∀ x _ : x ∈ s, f x ≠ 0) : TimesContDiffOn ℝ n (fun x => f x^g x) s :=
  fun x hx => (hf x hx).rpow (hg x hx) (h x hx)

theorem TimesContDiff.rpow (hf : TimesContDiff ℝ n f) (hg : TimesContDiff ℝ n g) (h : ∀ x, f x ≠ 0) :
  TimesContDiff ℝ n fun x => f x^g x :=
  times_cont_diff_iff_times_cont_diff_at.mpr$ fun x => hf.times_cont_diff_at.rpow hg.times_cont_diff_at (h x)

theorem TimesContDiffWithinAt.rpow_const_of_ne (hf : TimesContDiffWithinAt ℝ n f s x) (h : f x ≠ 0) :
  TimesContDiffWithinAt ℝ n (fun x => f x^p) s x :=
  hf.rpow times_cont_diff_within_at_const h

theorem TimesContDiffAt.rpow_const_of_ne (hf : TimesContDiffAt ℝ n f x) (h : f x ≠ 0) :
  TimesContDiffAt ℝ n (fun x => f x^p) x :=
  hf.rpow times_cont_diff_at_const h

theorem TimesContDiffOn.rpow_const_of_ne (hf : TimesContDiffOn ℝ n f s) (h : ∀ x _ : x ∈ s, f x ≠ 0) :
  TimesContDiffOn ℝ n (fun x => f x^p) s :=
  fun x hx => (hf x hx).rpow_const_of_ne (h x hx)

theorem TimesContDiff.rpow_const_of_ne (hf : TimesContDiff ℝ n f) (h : ∀ x, f x ≠ 0) :
  TimesContDiff ℝ n fun x => f x^p :=
  hf.rpow times_cont_diff_const h

variable{m : ℕ}

theorem TimesContDiffWithinAt.rpow_const_of_le (hf : TimesContDiffWithinAt ℝ m f s x) (h : «expr↑ » m ≤ p) :
  TimesContDiffWithinAt ℝ m (fun x => f x^p) s x :=
  (times_cont_diff_at_rpow_const_of_le h).comp_times_cont_diff_within_at x hf

theorem TimesContDiffAt.rpow_const_of_le (hf : TimesContDiffAt ℝ m f x) (h : «expr↑ » m ≤ p) :
  TimesContDiffAt ℝ m (fun x => f x^p) x :=
  by 
    rw [←times_cont_diff_within_at_univ] at *
    exact hf.rpow_const_of_le h

theorem TimesContDiffOn.rpow_const_of_le (hf : TimesContDiffOn ℝ m f s) (h : «expr↑ » m ≤ p) :
  TimesContDiffOn ℝ m (fun x => f x^p) s :=
  fun x hx => (hf x hx).rpow_const_of_le h

theorem TimesContDiff.rpow_const_of_le (hf : TimesContDiff ℝ m f) (h : «expr↑ » m ≤ p) :
  TimesContDiff ℝ m fun x => f x^p :=
  times_cont_diff_iff_times_cont_diff_at.mpr$ fun x => hf.times_cont_diff_at.rpow_const_of_le h

end fderiv

section deriv

variable{f g : ℝ → ℝ}{f' g' x y p : ℝ}{s : Set ℝ}

theorem HasDerivWithinAt.rpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x) (h : 0 < f x) :
  HasDerivWithinAt (fun x => f x^g x) (((f'*g x)*f x^g x - 1)+(g'*f x^g x)*log (f x)) s x :=
  by 
    convert (hf.has_fderiv_within_at.rpow hg.has_fderiv_within_at h).HasDerivWithinAt using 1
    dsimp 
    ring

theorem HasDerivAt.rpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (h : 0 < f x) :
  HasDerivAt (fun x => f x^g x) (((f'*g x)*f x^g x - 1)+(g'*f x^g x)*log (f x)) x :=
  by 
    rw [←has_deriv_within_at_univ] at *
    exact hf.rpow hg h

theorem HasDerivWithinAt.rpow_const (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
  HasDerivWithinAt (fun y => f y^p) ((f'*p)*f x^p - 1) s x :=
  by 
    convert (has_deriv_at_rpow_const hx).comp_has_deriv_within_at x hf using 1
    ring

theorem HasDerivAt.rpow_const (hf : HasDerivAt f f' x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
  HasDerivAt (fun y => f y^p) ((f'*p)*f x^p - 1) x :=
  by 
    rw [←has_deriv_within_at_univ] at *
    exact hf.rpow_const hx

theorem deriv_within_rpow_const (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0 ∨ 1 ≤ p)
  (hxs : UniqueDiffWithinAt ℝ s x) : derivWithin (fun x => f x^p) s x = (derivWithin f s x*p)*f x^p - 1 :=
  (hf.has_deriv_within_at.rpow_const hx).derivWithin hxs

@[simp]
theorem deriv_rpow_const (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
  deriv (fun x => f x^p) x = (deriv f x*p)*f x^p - 1 :=
  (hf.has_deriv_at.rpow_const hx).deriv

end deriv

end Differentiability

section Limits

open Real Filter

-- error in Analysis.SpecialFunctions.PowDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The function `(1 + t/x) ^ x` tends to `exp t` at `+∞`. -/
theorem tendsto_one_plus_div_rpow_exp
(t : exprℝ()) : tendsto (λ x : exprℝ(), «expr ^ »(«expr + »(1, «expr / »(t, x)), x)) at_top (expr𝓝() (exp t)) :=
begin
  apply [expr ((real.continuous_exp.tendsto _).comp (tendsto_mul_log_one_plus_div_at_top t)).congr' _],
  have [ident h₁] [":", expr «expr < »(«expr / »((1 : exprℝ()), 2), 1)] [":=", expr by linarith [] [] []],
  have [ident h₂] [":", expr tendsto (λ
    x : exprℝ(), «expr + »(1, «expr / »(t, x))) at_top (expr𝓝() 1)] [":=", expr by simpa [] [] [] [] [] ["using", expr (tendsto_inv_at_top_zero.const_mul t).const_add 1]],
  refine [expr (eventually_ge_of_tendsto_gt h₁ h₂).mono (λ x hx, _)],
  have [ident hx'] [":", expr «expr < »(0, «expr + »(1, «expr / »(t, x)))] [":=", expr by linarith [] [] []],
  simp [] [] [] ["[", expr mul_comm x, ",", expr exp_mul, ",", expr exp_log hx', "]"] [] []
end

/-- The function `(1 + t/x) ^ x` tends to `exp t` at `+∞` for naturals `x`. -/
theorem tendsto_one_plus_div_pow_exp (t : ℝ) : tendsto (fun x : ℕ => (1+t / (x : ℝ))^x) at_top (𝓝 (Real.exp t)) :=
  ((tendsto_one_plus_div_rpow_exp t).comp tendsto_coe_nat_at_top_at_top).congr
    (by 
      simp )

end Limits

