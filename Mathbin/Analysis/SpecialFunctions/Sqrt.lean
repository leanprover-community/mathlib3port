import Mathbin.Analysis.Calculus.TimesContDiff

/-!
# Smoothness of `real.sqrt`

In this file we prove that `real.sqrt` is infinitely smooth at all points `x ≠ 0` and provide some
dot-notation lemmas.

## Tags

sqrt, differentiable
-/


open Set

open_locale TopologicalSpace

namespace Real

/-- Local homeomorph between `(0, +∞)` and `(0, +∞)` with `to_fun = λ x, x ^ 2` and
`inv_fun = sqrt`. -/
noncomputable def sq_local_homeomorph : LocalHomeomorph ℝ ℝ :=
  { toFun := fun x => x^2, invFun := sqrt, Source := Ioi 0, Target := Ioi 0,
    map_source' := fun x hx => mem_Ioi.2 (pow_pos hx _), map_target' := fun x hx => mem_Ioi.2 (sqrt_pos.2 hx),
    left_inv' := fun x hx => sqrt_sq (le_of_ltₓ hx), right_inv' := fun x hx => sq_sqrt (le_of_ltₓ hx),
    open_source := is_open_Ioi, open_target := is_open_Ioi, continuous_to_fun := (continuous_pow 2).ContinuousOn,
    continuous_inv_fun := continuous_on_id.sqrt }

-- error in Analysis.SpecialFunctions.Sqrt: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem deriv_sqrt_aux
{x : exprℝ()}
(hx : «expr ≠ »(x, 0)) : «expr ∧ »(has_strict_deriv_at sqrt «expr / »(1, «expr * »(2, sqrt x)) x, ∀
 n, times_cont_diff_at exprℝ() n sqrt x) :=
begin
  cases [expr hx.lt_or_lt] ["with", ident hx, ident hx],
  { rw ["[", expr sqrt_eq_zero_of_nonpos hx.le, ",", expr mul_zero, ",", expr div_zero, "]"] [],
    have [] [":", expr «expr =ᶠ[ ] »(sqrt, expr𝓝() x, λ
      _, 0)] [":=", expr (gt_mem_nhds hx).mono (λ x hx, sqrt_eq_zero_of_nonpos hx.le)],
    exact [expr ⟨(has_strict_deriv_at_const x (0 : exprℝ())).congr_of_eventually_eq this.symm, λ
      n, times_cont_diff_at_const.congr_of_eventually_eq this⟩] },
  { have [] [":", expr «expr ≠ »(«expr * »(«expr↑ »(2), «expr ^ »(sqrt x, «expr - »(2, 1))), 0)] [],
    by simp [] [] [] ["[", expr (sqrt_pos.2 hx).ne', ",", expr @two_ne_zero exprℝ(), "]"] [] [],
    split,
    { simpa [] [] [] [] [] ["using", expr sq_local_homeomorph.has_strict_deriv_at_symm hx this (has_strict_deriv_at_pow 2 _)] },
    { exact [expr λ
       n, sq_local_homeomorph.times_cont_diff_at_symm_deriv this hx (has_deriv_at_pow 2 (sqrt x)) (times_cont_diff_at_id.pow 2)] } }
end

theorem has_strict_deriv_at_sqrt {x : ℝ} (hx : x ≠ 0) : HasStrictDerivAt sqrt (1 / 2*sqrt x) x :=
  (deriv_sqrt_aux hx).1

theorem times_cont_diff_at_sqrt {x : ℝ} {n : WithTop ℕ} (hx : x ≠ 0) : TimesContDiffAt ℝ n sqrt x :=
  (deriv_sqrt_aux hx).2 n

theorem has_deriv_at_sqrt {x : ℝ} (hx : x ≠ 0) : HasDerivAt sqrt (1 / 2*sqrt x) x :=
  (has_strict_deriv_at_sqrt hx).HasDerivAt

end Real

open Real

section deriv

variable{f : ℝ → ℝ}{s : Set ℝ}{f' x : ℝ}

theorem HasDerivWithinAt.sqrt (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
  HasDerivWithinAt (fun y => sqrt (f y)) (f' / 2*sqrt (f x)) s x :=
  by 
    simpa only [· ∘ ·, div_eq_inv_mul, mul_oneₓ] using (has_deriv_at_sqrt hx).comp_has_deriv_within_at x hf

theorem HasDerivAt.sqrt (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
  HasDerivAt (fun y => sqrt (f y)) (f' / 2*sqrt (f x)) x :=
  by 
    simpa only [· ∘ ·, div_eq_inv_mul, mul_oneₓ] using (has_deriv_at_sqrt hx).comp x hf

theorem HasStrictDerivAt.sqrt (hf : HasStrictDerivAt f f' x) (hx : f x ≠ 0) :
  HasStrictDerivAt (fun t => sqrt (f t)) (f' / 2*sqrt (f x)) x :=
  by 
    simpa only [· ∘ ·, div_eq_inv_mul, mul_oneₓ] using (has_strict_deriv_at_sqrt hx).comp x hf

theorem deriv_within_sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) (hxs : UniqueDiffWithinAt ℝ s x) :
  derivWithin (fun x => sqrt (f x)) s x = derivWithin f s x / 2*sqrt (f x) :=
  (hf.has_deriv_within_at.sqrt hx).derivWithin hxs

@[simp]
theorem deriv_sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
  deriv (fun x => sqrt (f x)) x = deriv f x / 2*sqrt (f x) :=
  (hf.has_deriv_at.sqrt hx).deriv

end deriv

section fderiv

variable{E : Type _}[NormedGroup E][NormedSpace ℝ E]{f : E → ℝ}{n : WithTop ℕ}{s : Set E}{x : E}{f' : E →L[ℝ] ℝ}

theorem HasFderivAt.sqrt (hf : HasFderivAt f f' x) (hx : f x ≠ 0) :
  HasFderivAt (fun y => sqrt (f y)) ((1 / 2*sqrt (f x)) • f') x :=
  (has_deriv_at_sqrt hx).comp_has_fderiv_at x hf

theorem HasStrictFderivAt.sqrt (hf : HasStrictFderivAt f f' x) (hx : f x ≠ 0) :
  HasStrictFderivAt (fun y => sqrt (f y)) ((1 / 2*sqrt (f x)) • f') x :=
  (has_strict_deriv_at_sqrt hx).comp_has_strict_fderiv_at x hf

theorem HasFderivWithinAt.sqrt (hf : HasFderivWithinAt f f' s x) (hx : f x ≠ 0) :
  HasFderivWithinAt (fun y => sqrt (f y)) ((1 / 2*sqrt (f x)) • f') s x :=
  (has_deriv_at_sqrt hx).comp_has_fderiv_within_at x hf

theorem DifferentiableWithinAt.sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) :
  DifferentiableWithinAt ℝ (fun y => sqrt (f y)) s x :=
  (hf.has_fderiv_within_at.sqrt hx).DifferentiableWithinAt

theorem DifferentiableAt.sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
  DifferentiableAt ℝ (fun y => sqrt (f y)) x :=
  (hf.has_fderiv_at.sqrt hx).DifferentiableAt

theorem DifferentiableOn.sqrt (hf : DifferentiableOn ℝ f s) (hs : ∀ x _ : x ∈ s, f x ≠ 0) :
  DifferentiableOn ℝ (fun y => sqrt (f y)) s :=
  fun x hx => (hf x hx).sqrt (hs x hx)

theorem Differentiable.sqrt (hf : Differentiable ℝ f) (hs : ∀ x, f x ≠ 0) : Differentiable ℝ fun y => sqrt (f y) :=
  fun x => (hf x).sqrt (hs x)

theorem fderiv_within_sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) (hxs : UniqueDiffWithinAt ℝ s x) :
  fderivWithin ℝ (fun x => sqrt (f x)) s x = (1 / 2*sqrt (f x)) • fderivWithin ℝ f s x :=
  (hf.has_fderiv_within_at.sqrt hx).fderivWithin hxs

@[simp]
theorem fderiv_sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
  fderiv ℝ (fun x => sqrt (f x)) x = (1 / 2*sqrt (f x)) • fderiv ℝ f x :=
  (hf.has_fderiv_at.sqrt hx).fderiv

theorem TimesContDiffAt.sqrt (hf : TimesContDiffAt ℝ n f x) (hx : f x ≠ 0) :
  TimesContDiffAt ℝ n (fun y => sqrt (f y)) x :=
  (times_cont_diff_at_sqrt hx).comp x hf

theorem TimesContDiffWithinAt.sqrt (hf : TimesContDiffWithinAt ℝ n f s x) (hx : f x ≠ 0) :
  TimesContDiffWithinAt ℝ n (fun y => sqrt (f y)) s x :=
  (times_cont_diff_at_sqrt hx).comp_times_cont_diff_within_at x hf

theorem TimesContDiffOn.sqrt (hf : TimesContDiffOn ℝ n f s) (hs : ∀ x _ : x ∈ s, f x ≠ 0) :
  TimesContDiffOn ℝ n (fun y => sqrt (f y)) s :=
  fun x hx => (hf x hx).sqrt (hs x hx)

theorem TimesContDiff.sqrt (hf : TimesContDiff ℝ n f) (h : ∀ x, f x ≠ 0) : TimesContDiff ℝ n fun y => sqrt (f y) :=
  times_cont_diff_iff_times_cont_diff_at.2$ fun x => hf.times_cont_diff_at.sqrt (h x)

end fderiv

