import Mathbin.Analysis.Calculus.TimesContDiff 
import Mathbin.Analysis.Complex.Conformal 
import Mathbin.Analysis.Calculus.Conformal.NormedSpace

/-! # Real differentiability of complex-differentiable functions

`has_deriv_at.real_of_complex` expresses that, if a function on `ℂ` is differentiable (over `ℂ`),
then its restriction to `ℝ` is differentiable over `ℝ`, with derivative the real part of the
complex derivative.

`differentiable_at.conformal_at` states that a real-differentiable function with a nonvanishing
differential from the complex plane into an arbitrary complex-normed space is conformal at a point
if it's holomorphic at that point. This is a version of Cauchy-Riemann equations.

`conformal_at_iff_differentiable_at_or_differentiable_at_comp_conj` proves that a real-differential
function with a nonvanishing differential between the complex plane is conformal at a point if and
only if it's holomorphic or antiholomorphic at that point.

## TODO

* The classical form of Cauchy-Riemann equations
* On a connected open set `u`, a function which is `conformal_at` each point is either holomorphic
throughout or antiholomorphic throughout.

## Warning

We do NOT require conformal functions to be orientation-preserving in this file.
-/


section RealDerivOfComplex

/-! ### Differentiability of the restriction to `ℝ` of complex functions -/


open Complex

variable{e : ℂ → ℂ}{e' : ℂ}{z : ℝ}

-- error in Analysis.Complex.RealDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a complex function is differentiable at a real point, then the induced real function is also
differentiable at this point, with a derivative equal to the real part of the complex derivative. -/
theorem has_strict_deriv_at.real_of_complex
(h : has_strict_deriv_at e e' z) : has_strict_deriv_at (λ x : exprℝ(), (e x).re) e'.re z :=
begin
  have [ident A] [":", expr has_strict_fderiv_at (coe : exprℝ() → exprℂ()) of_real_clm z] [":=", expr of_real_clm.has_strict_fderiv_at],
  have [ident B] [":", expr has_strict_fderiv_at e ((continuous_linear_map.smul_right 1 e' : «expr →L[ ] »(exprℂ(), exprℂ(), exprℂ())).restrict_scalars exprℝ()) (of_real_clm z)] [":=", expr h.has_strict_fderiv_at.restrict_scalars exprℝ()],
  have [ident C] [":", expr has_strict_fderiv_at re re_clm (e (of_real_clm z))] [":=", expr re_clm.has_strict_fderiv_at],
  simpa [] [] [] [] [] ["using", expr (C.comp z (B.comp z A)).has_strict_deriv_at]
end

-- error in Analysis.Complex.RealDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a complex function is differentiable at a real point, then the induced real function is also
differentiable at this point, with a derivative equal to the real part of the complex derivative. -/
theorem has_deriv_at.real_of_complex (h : has_deriv_at e e' z) : has_deriv_at (λ x : exprℝ(), (e x).re) e'.re z :=
begin
  have [ident A] [":", expr has_fderiv_at (coe : exprℝ() → exprℂ()) of_real_clm z] [":=", expr of_real_clm.has_fderiv_at],
  have [ident B] [":", expr has_fderiv_at e ((continuous_linear_map.smul_right 1 e' : «expr →L[ ] »(exprℂ(), exprℂ(), exprℂ())).restrict_scalars exprℝ()) (of_real_clm z)] [":=", expr h.has_fderiv_at.restrict_scalars exprℝ()],
  have [ident C] [":", expr has_fderiv_at re re_clm (e (of_real_clm z))] [":=", expr re_clm.has_fderiv_at],
  simpa [] [] [] [] [] ["using", expr (C.comp z (B.comp z A)).has_deriv_at]
end

-- error in Analysis.Complex.RealDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem times_cont_diff_at.real_of_complex
{n : with_top exprℕ()}
(h : times_cont_diff_at exprℂ() n e z) : times_cont_diff_at exprℝ() n (λ x : exprℝ(), (e x).re) z :=
begin
  have [ident A] [":", expr times_cont_diff_at exprℝ() n (coe : exprℝ() → exprℂ()) z] [],
  from [expr of_real_clm.times_cont_diff.times_cont_diff_at],
  have [ident B] [":", expr times_cont_diff_at exprℝ() n e z] [":=", expr h.restrict_scalars exprℝ()],
  have [ident C] [":", expr times_cont_diff_at exprℝ() n re (e z)] [],
  from [expr re_clm.times_cont_diff.times_cont_diff_at],
  exact [expr C.comp z (B.comp z A)]
end

-- error in Analysis.Complex.RealDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem times_cont_diff.real_of_complex
{n : with_top exprℕ()}
(h : times_cont_diff exprℂ() n e) : times_cont_diff exprℝ() n (λ x : exprℝ(), (e x).re) :=
«expr $ »(times_cont_diff_iff_times_cont_diff_at.2, λ x, h.times_cont_diff_at.real_of_complex)

variable{E : Type _}[NormedGroup E][NormedSpace ℂ E]

theorem HasStrictDerivAt.complex_to_real_fderiv' {f : ℂ → E} {x : ℂ} {f' : E} (h : HasStrictDerivAt f f' x) :
  HasStrictFderivAt f (re_clm.smulRight f'+I • im_clm.smulRight f') x :=
  by 
    simpa only [Complex.restrict_scalars_one_smul_right'] using h.has_strict_fderiv_at.restrict_scalars ℝ

theorem HasDerivAt.complex_to_real_fderiv' {f : ℂ → E} {x : ℂ} {f' : E} (h : HasDerivAt f f' x) :
  HasFderivAt f (re_clm.smulRight f'+I • im_clm.smulRight f') x :=
  by 
    simpa only [Complex.restrict_scalars_one_smul_right'] using h.has_fderiv_at.restrict_scalars ℝ

theorem HasDerivWithinAt.complex_to_real_fderiv' {f : ℂ → E} {s : Set ℂ} {x : ℂ} {f' : E}
  (h : HasDerivWithinAt f f' s x) : HasFderivWithinAt f (re_clm.smulRight f'+I • im_clm.smulRight f') s x :=
  by 
    simpa only [Complex.restrict_scalars_one_smul_right'] using h.has_fderiv_within_at.restrict_scalars ℝ

theorem HasStrictDerivAt.complex_to_real_fderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasStrictDerivAt f f' x) :
  HasStrictFderivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x :=
  by 
    simpa only [Complex.restrict_scalars_one_smul_right] using h.has_strict_fderiv_at.restrict_scalars ℝ

theorem HasDerivAt.complex_to_real_fderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasDerivAt f f' x) :
  HasFderivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x :=
  by 
    simpa only [Complex.restrict_scalars_one_smul_right] using h.has_fderiv_at.restrict_scalars ℝ

theorem HasDerivWithinAt.complex_to_real_fderiv {f : ℂ → ℂ} {s : Set ℂ} {f' x : ℂ} (h : HasDerivWithinAt f f' s x) :
  HasFderivWithinAt f (f' • (1 : ℂ →L[ℝ] ℂ)) s x :=
  by 
    simpa only [Complex.restrict_scalars_one_smul_right] using h.has_fderiv_within_at.restrict_scalars ℝ

end RealDerivOfComplex

section Conformality

/-! ### Conformality of real-differentiable complex maps -/


open Complex ContinuousLinearMap

open_locale ComplexConjugate

variable()

/-- A real differentiable function of the complex plane into some complex normed space `E` is
    conformal at a point `z` if it is holomorphic at that point with a nonvanishing differential.
    This is a version of the Cauchy-Riemann equations. -/
theorem DifferentiableAt.conformal_at {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {z : ℂ} {f : ℂ → E} (hf' : fderiv ℝ f z ≠ 0) (h : DifferentiableAt ℂ f z) : ConformalAt f z :=
  by 
    rw [conformal_at_iff_is_conformal_map_fderiv]
    rw [(h.has_fderiv_at.restrict_scalars ℝ).fderiv] at hf'⊢
    apply is_conformal_map_complex_linear 
    contrapose! hf' with w 
    simp [w]

-- error in Analysis.Complex.RealDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A complex function is conformal if and only if the function is holomorphic or antiholomorphic
    with a nonvanishing differential. -/
theorem conformal_at_iff_differentiable_at_or_differentiable_at_comp_conj
{f : exprℂ() → exprℂ()}
{z : exprℂ()} : «expr ↔ »(conformal_at f z, «expr ∧ »(«expr ∨ »(differentiable_at exprℂ() f z, differentiable_at exprℂ() «expr ∘ »(f, exprconj()) (exprconj() z)), «expr ≠ »(fderiv exprℝ() f z, 0))) :=
begin
  rw [expr conformal_at_iff_is_conformal_map_fderiv] [],
  rw [expr is_conformal_map_iff_is_complex_or_conj_linear] [],
  apply [expr and_congr_left],
  intros [ident h],
  have [ident h_diff] [] [":=", expr h.imp_symm fderiv_zero_of_not_differentiable_at],
  apply [expr or_congr],
  { rw [expr differentiable_at_iff_restrict_scalars exprℝ() h_diff] [] },
  rw ["<-", expr conj_conj z] ["at", ident h_diff],
  rw [expr differentiable_at_iff_restrict_scalars exprℝ() (h_diff.comp _ conj_cle.differentiable_at)] [],
  refine [expr exists_congr (λ g, rfl.congr _)],
  have [] [":", expr «expr = »(fderiv exprℝ() exprconj() (exprconj() z), _)] [":=", expr conj_cle.fderiv],
  simp [] [] [] ["[", expr fderiv.comp _ h_diff conj_cle.differentiable_at, ",", expr this, ",", expr conj_conj, "]"] [] []
end

end Conformality

