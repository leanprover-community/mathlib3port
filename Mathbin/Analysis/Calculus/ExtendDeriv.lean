/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Analysis.Calculus.MeanValue

#align_import analysis.calculus.extend_deriv from "leanprover-community/mathlib"@"af471b9e3ce868f296626d33189b4ce730fa4c00"

/-!
# Extending differentiability to the boundary

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We investigate how differentiable functions inside a set extend to differentiable functions
on the boundary. For this, it suffices that the function and its derivative admit limits there.
A general version of this statement is given in `has_fderiv_at_boundary_of_tendsto_fderiv`.

One-dimensional versions, in which one wants to obtain differentiability at the left endpoint or
the right endpoint of an interval, are given in
`has_deriv_at_interval_left_endpoint_of_tendsto_deriv` and
`has_deriv_at_interval_right_endpoint_of_tendsto_deriv`. These versions are formulated in terms
of the one-dimensional derivative `deriv ℝ f`.
-/


variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type _} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

open Filter Set Metric ContinuousLinearMap

open scoped Topology

attribute [local mono] prod_mono

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print has_fderiv_at_boundary_of_tendsto_fderiv /-
/-- If a function `f` is differentiable in a convex open set and continuous on its closure, and its
derivative converges to a limit `f'` at a point on the boundary, then `f` is differentiable there
with derivative `f'`. -/
theorem has_fderiv_at_boundary_of_tendsto_fderiv {f : E → F} {s : Set E} {x : E} {f' : E →L[ℝ] F}
    (f_diff : DifferentiableOn ℝ f s) (s_conv : Convex ℝ s) (s_open : IsOpen s)
    (f_cont : ∀ y ∈ closure s, ContinuousWithinAt f s y)
    (h : Tendsto (fun y => fderiv ℝ f y) (𝓝[s] x) (𝓝 f')) : HasFDerivWithinAt f f' (closure s) x :=
  by classical
#align has_fderiv_at_boundary_of_tendsto_fderiv has_fderiv_at_boundary_of_tendsto_fderiv
-/

#print has_deriv_at_interval_left_endpoint_of_tendsto_deriv /-
-- one can assume without loss of generality that `x` belongs to the closure of `s`, as the
-- statement is empty otherwise
/- One needs to show that `‖f y - f x - f' (y - x)‖ ≤ ε ‖y - x‖` for `y` close to `x` in `closure
  s`, where `ε` is an arbitrary positive constant. By continuity of the functions, it suffices to
  prove this for nearby points inside `s`. In a neighborhood of `x`, the derivative of `f` is
  arbitrarily close to `f'` by assumption. The mean value inequality completes the proof. -/
-- common start for both continuity proofs
/-- If a function is differentiable on the right of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the right at `a`. -/
theorem has_deriv_at_interval_left_endpoint_of_tendsto_deriv {s : Set ℝ} {e : E} {a : ℝ} {f : ℝ → E}
    (f_diff : DifferentiableOn ℝ f s) (f_lim : ContinuousWithinAt f s a) (hs : s ∈ 𝓝[>] a)
    (f_lim' : Tendsto (fun x => deriv f x) (𝓝[>] a) (𝓝 e)) : HasDerivWithinAt f e (Ici a) a :=
  by
  /- This is a specialization of `has_fderiv_at_boundary_of_tendsto_fderiv`. To be in the setting of
    this theorem, we need to work on an open interval with closure contained in `s ∪ {a}`, that we
    call `t = (a, b)`. Then, we check all the assumptions of this theorem and we apply it. -/
  obtain ⟨b, ab : a < b, sab : Ioc a b ⊆ s⟩ := mem_nhdsWithin_Ioi_iff_exists_Ioc_subset.1 hs
  let t := Ioo a b
  have ts : t ⊆ s := subset.trans Ioo_subset_Ioc_self sab
  have t_diff : DifferentiableOn ℝ f t := f_diff.mono ts
  have t_conv : Convex ℝ t := convex_Ioo a b
  have t_open : IsOpen t := isOpen_Ioo
  have t_closure : closure t = Icc a b := closure_Ioo ab.ne
  have t_cont : ∀ y ∈ closure t, ContinuousWithinAt f t y :=
    by
    rw [t_closure]
    intro y hy
    by_cases h : y = a
    · rw [h]; exact f_lim.mono ts
    · have : y ∈ s := sab ⟨lt_of_le_of_ne hy.1 (Ne.symm h), hy.2⟩
      exact (f_diff.continuous_on y this).mono ts
  have t_diff' : tendsto (fun x => fderiv ℝ f x) (𝓝[t] a) (𝓝 (smul_right 1 e)) :=
    by
    simp only [deriv_fderiv.symm]
    exact
      tendsto.comp
        (isBoundedBilinearMap_smulRight : IsBoundedBilinearMap ℝ _).continuous_right.ContinuousAt
        (tendsto_nhdsWithin_mono_left Ioo_subset_Ioi_self f_lim')
  -- now we can apply `has_fderiv_at_boundary_of_differentiable`
  have : HasDerivWithinAt f e (Icc a b) a :=
    by
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← t_closure]
    exact has_fderiv_at_boundary_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff'
  exact this.nhds_within (Icc_mem_nhdsWithin_Ici <| left_mem_Ico.2 ab)
#align has_deriv_at_interval_left_endpoint_of_tendsto_deriv has_deriv_at_interval_left_endpoint_of_tendsto_deriv
-/

#print has_deriv_at_interval_right_endpoint_of_tendsto_deriv /-
/-- If a function is differentiable on the left of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the left at `a`. -/
theorem has_deriv_at_interval_right_endpoint_of_tendsto_deriv {s : Set ℝ} {e : E} {a : ℝ}
    {f : ℝ → E} (f_diff : DifferentiableOn ℝ f s) (f_lim : ContinuousWithinAt f s a)
    (hs : s ∈ 𝓝[<] a) (f_lim' : Tendsto (fun x => deriv f x) (𝓝[<] a) (𝓝 e)) :
    HasDerivWithinAt f e (Iic a) a :=
  by
  /- This is a specialization of `has_fderiv_at_boundary_of_differentiable`. To be in the setting of
    this theorem, we need to work on an open interval with closure contained in `s ∪ {a}`, that we
    call `t = (b, a)`. Then, we check all the assumptions of this theorem and we apply it. -/
  obtain ⟨b, ba, sab⟩ : ∃ b ∈ Iio a, Ico b a ⊆ s := mem_nhdsWithin_Iio_iff_exists_Ico_subset.1 hs
  let t := Ioo b a
  have ts : t ⊆ s := subset.trans Ioo_subset_Ico_self sab
  have t_diff : DifferentiableOn ℝ f t := f_diff.mono ts
  have t_conv : Convex ℝ t := convex_Ioo b a
  have t_open : IsOpen t := isOpen_Ioo
  have t_closure : closure t = Icc b a := closure_Ioo (ne_of_lt ba)
  have t_cont : ∀ y ∈ closure t, ContinuousWithinAt f t y :=
    by
    rw [t_closure]
    intro y hy
    by_cases h : y = a
    · rw [h]; exact f_lim.mono ts
    · have : y ∈ s := sab ⟨hy.1, lt_of_le_of_ne hy.2 h⟩
      exact (f_diff.continuous_on y this).mono ts
  have t_diff' : tendsto (fun x => fderiv ℝ f x) (𝓝[t] a) (𝓝 (smul_right 1 e)) :=
    by
    simp only [deriv_fderiv.symm]
    exact
      tendsto.comp
        (isBoundedBilinearMap_smulRight : IsBoundedBilinearMap ℝ _).continuous_right.ContinuousAt
        (tendsto_nhdsWithin_mono_left Ioo_subset_Iio_self f_lim')
  -- now we can apply `has_fderiv_at_boundary_of_differentiable`
  have : HasDerivWithinAt f e (Icc b a) a :=
    by
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← t_closure]
    exact has_fderiv_at_boundary_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff'
  exact this.nhds_within (Icc_mem_nhdsWithin_Iic <| right_mem_Ioc.2 ba)
#align has_deriv_at_interval_right_endpoint_of_tendsto_deriv has_deriv_at_interval_right_endpoint_of_tendsto_deriv
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (y «expr ≠ » x) -/
#print hasDerivAt_of_hasDerivAt_of_ne /-
/-- If a real function `f` has a derivative `g` everywhere but at a point, and `f` and `g` are
continuous at this point, then `g` is also the derivative of `f` at this point. -/
theorem hasDerivAt_of_hasDerivAt_of_ne {f g : ℝ → E} {x : ℝ}
    (f_diff : ∀ (y) (_ : y ≠ x), HasDerivAt f (g y) y) (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) : HasDerivAt f (g x) x :=
  by
  have A : HasDerivWithinAt f (g x) (Ici x) x :=
    by
    have diff : DifferentiableOn ℝ f (Ioi x) := fun y hy =>
      (f_diff y (ne_of_gt hy)).DifferentiableAt.DifferentiableWithinAt
    -- next line is the nontrivial bit of this proof, appealing to differentiability
    -- extension results.
    apply
      has_deriv_at_interval_left_endpoint_of_tendsto_deriv diff hf.continuous_within_at
        self_mem_nhdsWithin
    have : tendsto g (𝓝[>] x) (𝓝 (g x)) := tendsto_inf_left hg
    apply this.congr' _
    apply mem_of_superset self_mem_nhdsWithin fun y hy => _
    exact (f_diff y (ne_of_gt hy)).deriv.symm
  have B : HasDerivWithinAt f (g x) (Iic x) x :=
    by
    have diff : DifferentiableOn ℝ f (Iio x) := fun y hy =>
      (f_diff y (ne_of_lt hy)).DifferentiableAt.DifferentiableWithinAt
    -- next line is the nontrivial bit of this proof, appealing to differentiability
    -- extension results.
    apply
      has_deriv_at_interval_right_endpoint_of_tendsto_deriv diff hf.continuous_within_at
        self_mem_nhdsWithin
    have : tendsto g (𝓝[<] x) (𝓝 (g x)) := tendsto_inf_left hg
    apply this.congr' _
    apply mem_of_superset self_mem_nhdsWithin fun y hy => _
    exact (f_diff y (ne_of_lt hy)).deriv.symm
  simpa using B.union A
#align has_deriv_at_of_has_deriv_at_of_ne hasDerivAt_of_hasDerivAt_of_ne
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (y «expr ≠ » x) -/
#print hasDerivAt_of_hasDerivAt_of_ne' /-
/-- If a real function `f` has a derivative `g` everywhere but at a point, and `f` and `g` are
continuous at this point, then `g` is the derivative of `f` everywhere. -/
theorem hasDerivAt_of_hasDerivAt_of_ne' {f g : ℝ → E} {x : ℝ}
    (f_diff : ∀ (y) (_ : y ≠ x), HasDerivAt f (g y) y) (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) (y : ℝ) : HasDerivAt f (g y) y :=
  by
  rcases eq_or_ne y x with (rfl | hne)
  · exact hasDerivAt_of_hasDerivAt_of_ne f_diff hf hg
  · exact f_diff y hne
#align has_deriv_at_of_has_deriv_at_of_ne' hasDerivAt_of_hasDerivAt_of_ne'
-/

