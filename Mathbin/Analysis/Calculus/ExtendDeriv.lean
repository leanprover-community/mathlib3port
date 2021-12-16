import Mathbin.Analysis.Calculus.MeanValue

/-!
# Extending differentiability to the boundary

We investigate how differentiable functions inside a set extend to differentiable functions
on the boundary. For this, it suffices that the function and its derivative admit limits there.
A general version of this statement is given in `has_fderiv_at_boundary_of_tendsto_fderiv`.

One-dimensional versions, in which one wants to obtain differentiability at the left endpoint or
the right endpoint of an interval, are given in
`has_deriv_at_interval_left_endpoint_of_tendsto_deriv` and
`has_deriv_at_interval_right_endpoint_of_tendsto_deriv`. These versions are formulated in terms
of the one-dimensional derivative `deriv ℝ f`.
-/


variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] {F : Type _} [NormedGroup F] [NormedSpace ℝ F]

open Filter Set Metric ContinuousLinearMap

open_locale TopologicalSpace

attribute [local mono] prod_mono

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (δ «expr > » 0)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » «expr ∩ »(B, closure s))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (z «expr ∈ » «expr ∩ »(B, s))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » closure s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » closure s)
/-- If a function `f` is differentiable in a convex open set and continuous on its closure, and its
derivative converges to a limit `f'` at a point on the boundary, then `f` is differentiable there
with derivative `f'`. -/
theorem has_fderiv_at_boundary_of_tendsto_fderiv {f : E → F} {s : Set E} {x : E} {f' : E →L[ℝ] F}
  (f_diff : DifferentiableOn ℝ f s) (s_conv : Convex ℝ s) (s_open : IsOpen s)
  (f_cont : ∀ y _ : y ∈ Closure s, ContinuousWithinAt f s y) (h : tendsto (fun y => fderiv ℝ f y) (𝓝[s] x) (𝓝 f')) :
  HasFderivWithinAt f f' (Closure s) x :=
  by 
    classical 
    byCases' hx : x ∉ Closure s
    ·
      rw [←closure_closure] at hx 
      exact has_fderiv_within_at_of_not_mem_closure hx 
    pushNeg  at hx 
    rw [HasFderivWithinAt, HasFderivAtFilter, Asymptotics.is_o_iff]
    intro ε ε_pos 
    obtain ⟨δ, δ_pos, hδ⟩ : ∃ (δ : _)(_ : δ > 0), ∀ y _ : y ∈ s, dist y x < δ → ∥fderiv ℝ f y - f'∥ < ε
    ·
      simpa [dist_zero_right] using tendsto_nhds_within_nhds.1 h ε ε_pos 
    set B := ball x δ 
    suffices  : ∀ y _ : y ∈ B ∩ Closure s, ∥f y - f x - (f' y - f' x)∥ ≤ ε*∥y - x∥
    exact
      mem_nhds_within_iff.2
        ⟨δ, δ_pos,
          fun y hy =>
            by 
              simpa using this y hy⟩
    suffices  : ∀ p : E × E, p ∈ Closure ((B ∩ s).Prod (B ∩ s)) → ∥f p.2 - f p.1 - (f' p.2 - f' p.1)∥ ≤ ε*∥p.2 - p.1∥
    ·
      rw [closure_prod_eq] at this 
      intro y y_in 
      apply this ⟨x, y⟩
      have  : B ∩ Closure s ⊆ Closure (B ∩ s)
      exact closure_inter_open is_open_ball 
      exact ⟨this ⟨mem_ball_self δ_pos, hx⟩, this y_in⟩
    have key : ∀ p : E × E, p ∈ (B ∩ s).Prod (B ∩ s) → ∥f p.2 - f p.1 - (f' p.2 - f' p.1)∥ ≤ ε*∥p.2 - p.1∥
    ·
      rintro ⟨u, v⟩ ⟨u_in, v_in⟩
      have conv : Convex ℝ (B ∩ s) := (convex_ball _ _).inter s_conv 
      have diff : DifferentiableOn ℝ f (B ∩ s) := f_diff.mono (inter_subset_right _ _)
      have bound : ∀ z _ : z ∈ B ∩ s, ∥fderivWithin ℝ f (B ∩ s) z - f'∥ ≤ ε
      ·
        intro z z_in 
        convert le_of_ltₓ (hδ _ z_in.2 z_in.1)
        have op : IsOpen (B ∩ s) := is_open_ball.inter s_open 
        rw [DifferentiableAt.fderiv_within _ (op.unique_diff_on z z_in)]
        exact (diff z z_in).DifferentiableAt (IsOpen.mem_nhds op z_in)
      simpa using conv.norm_image_sub_le_of_norm_fderiv_within_le' diff bound u_in v_in 
    rintro ⟨u, v⟩ uv_in 
    refine' ContinuousWithinAt.closure_le uv_in _ _ key 
    have f_cont' : ∀ y _ : y ∈ Closure s, ContinuousWithinAt (f - f') s y
    ·
      intro y y_in 
      exact tendsto.sub (f_cont y y_in) f'.cont.continuous_within_at 
    all_goals 
      have  : (B ∩ s).Prod (B ∩ s) ⊆ s.prod s
      ·
        mono <;> exact inter_subset_right _ _ 
      obtain ⟨u_in, v_in⟩ : u ∈ Closure s ∧ v ∈ Closure s
      ·
        simpa [closure_prod_eq] using closure_mono this uv_in 
      apply ContinuousWithinAt.mono _ this 
      simp only [ContinuousWithinAt]
    rw [nhds_within_prod_eq]
    ·
      have  : ∀ u v, f v - f u - (f' v - f' u) = f v - f' v - (f u - f' u) :=
        by 
          intros 
          abel 
      simp only [this]
      exact
        tendsto.comp continuous_norm.continuous_at
          ((tendsto.comp (f_cont' v v_in) tendsto_snd).sub$ tendsto.comp (f_cont' u u_in) tendsto_fst)
    ·
      apply tendsto_nhds_within_of_tendsto_nhds 
      rw [nhds_prod_eq]
      exact tendsto_const_nhds.mul (tendsto.comp continuous_norm.continuous_at$ tendsto_snd.sub tendsto_fst)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » Ioi a)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » closure t)
/-- If a function is differentiable on the right of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the right at `a`. -/
theorem has_deriv_at_interval_left_endpoint_of_tendsto_deriv {s : Set ℝ} {e : E} {a : ℝ} {f : ℝ → E}
  (f_diff : DifferentiableOn ℝ f s) (f_lim : ContinuousWithinAt f s a) (hs : s ∈ 𝓝[Ioi a] a)
  (f_lim' : tendsto (fun x => deriv f x) (𝓝[Ioi a] a) (𝓝 e)) : HasDerivWithinAt f e (Ici a) a :=
  by 
    obtain ⟨b, ab, sab⟩ : ∃ (b : _)(_ : b ∈ Ioi a), Ioc a b ⊆ s := mem_nhds_within_Ioi_iff_exists_Ioc_subset.1 hs 
    let t := Ioo a b 
    have ts : t ⊆ s := subset.trans Ioo_subset_Ioc_self sab 
    have t_diff : DifferentiableOn ℝ f t := f_diff.mono ts 
    have t_conv : Convex ℝ t := convex_Ioo a b 
    have t_open : IsOpen t := is_open_Ioo 
    have t_closure : Closure t = Icc a b := closure_Ioo ab 
    have t_cont : ∀ y _ : y ∈ Closure t, ContinuousWithinAt f t y
    ·
      rw [t_closure]
      intro y hy 
      byCases' h : y = a
      ·
        rw [h]
        exact f_lim.mono ts
      ·
        have  : y ∈ s := sab ⟨lt_of_le_of_neₓ hy.1 (Ne.symm h), hy.2⟩
        exact (f_diff.continuous_on y this).mono ts 
    have t_diff' : tendsto (fun x => fderiv ℝ f x) (𝓝[t] a) (𝓝 (smul_right 1 e))
    ·
      simp [deriv_fderiv.symm]
      refine' tendsto.comp is_bounded_bilinear_map_smul_right.continuous_right.continuous_at _ 
      exact tendsto_nhds_within_mono_left Ioo_subset_Ioi_self f_lim' 
    have  : HasDerivWithinAt f e (Icc a b) a
    ·
      rw [has_deriv_within_at_iff_has_fderiv_within_at, ←t_closure]
      exact has_fderiv_at_boundary_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff' 
    exact this.nhds_within (mem_nhds_within_Ici_iff_exists_Icc_subset.2 ⟨b, ab, subset.refl _⟩)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » Iio a)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » closure t)
/-- If a function is differentiable on the left of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the left at `a`. -/
theorem has_deriv_at_interval_right_endpoint_of_tendsto_deriv {s : Set ℝ} {e : E} {a : ℝ} {f : ℝ → E}
  (f_diff : DifferentiableOn ℝ f s) (f_lim : ContinuousWithinAt f s a) (hs : s ∈ 𝓝[Iio a] a)
  (f_lim' : tendsto (fun x => deriv f x) (𝓝[Iio a] a) (𝓝 e)) : HasDerivWithinAt f e (Iic a) a :=
  by 
    obtain ⟨b, ba, sab⟩ : ∃ (b : _)(_ : b ∈ Iio a), Ico b a ⊆ s := mem_nhds_within_Iio_iff_exists_Ico_subset.1 hs 
    let t := Ioo b a 
    have ts : t ⊆ s := subset.trans Ioo_subset_Ico_self sab 
    have t_diff : DifferentiableOn ℝ f t := f_diff.mono ts 
    have t_conv : Convex ℝ t := convex_Ioo b a 
    have t_open : IsOpen t := is_open_Ioo 
    have t_closure : Closure t = Icc b a := closure_Ioo ba 
    have t_cont : ∀ y _ : y ∈ Closure t, ContinuousWithinAt f t y
    ·
      rw [t_closure]
      intro y hy 
      byCases' h : y = a
      ·
        rw [h]
        exact f_lim.mono ts
      ·
        have  : y ∈ s := sab ⟨hy.1, lt_of_le_of_neₓ hy.2 h⟩
        exact (f_diff.continuous_on y this).mono ts 
    have t_diff' : tendsto (fun x => fderiv ℝ f x) (𝓝[t] a) (𝓝 (smul_right 1 e))
    ·
      simp [deriv_fderiv.symm]
      refine' tendsto.comp is_bounded_bilinear_map_smul_right.continuous_right.continuous_at _ 
      exact tendsto_nhds_within_mono_left Ioo_subset_Iio_self f_lim' 
    have  : HasDerivWithinAt f e (Icc b a) a
    ·
      rw [has_deriv_within_at_iff_has_fderiv_within_at, ←t_closure]
      exact has_fderiv_at_boundary_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff' 
    exact this.nhds_within (mem_nhds_within_Iic_iff_exists_Icc_subset.2 ⟨b, ba, subset.refl _⟩)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ≠ » x)
/-- If a real function `f` has a derivative `g` everywhere but at a point, and `f` and `g` are
continuous at this point, then `g` is also the derivative of `f` at this point. -/
theorem has_deriv_at_of_has_deriv_at_of_ne {f g : ℝ → E} {x : ℝ} (f_diff : ∀ y _ : y ≠ x, HasDerivAt f (g y) y)
  (hf : ContinuousAt f x) (hg : ContinuousAt g x) : HasDerivAt f (g x) x :=
  by 
    have A : HasDerivWithinAt f (g x) (Ici x) x
    ·
      have diff : DifferentiableOn ℝ f (Ioi x) :=
        fun y hy => (f_diff y (ne_of_gtₓ hy)).DifferentiableAt.DifferentiableWithinAt 
      apply has_deriv_at_interval_left_endpoint_of_tendsto_deriv diff hf.continuous_within_at self_mem_nhds_within 
      have  : tendsto g (𝓝[Ioi x] x) (𝓝 (g x)) := tendsto_inf_left hg 
      apply this.congr' _ 
      apply mem_of_superset self_mem_nhds_within fun y hy => _ 
      exact (f_diff y (ne_of_gtₓ hy)).deriv.symm 
    have B : HasDerivWithinAt f (g x) (Iic x) x
    ·
      have diff : DifferentiableOn ℝ f (Iio x) :=
        fun y hy => (f_diff y (ne_of_ltₓ hy)).DifferentiableAt.DifferentiableWithinAt 
      apply has_deriv_at_interval_right_endpoint_of_tendsto_deriv diff hf.continuous_within_at self_mem_nhds_within 
      have  : tendsto g (𝓝[Iio x] x) (𝓝 (g x)) := tendsto_inf_left hg 
      apply this.congr' _ 
      apply mem_of_superset self_mem_nhds_within fun y hy => _ 
      exact (f_diff y (ne_of_ltₓ hy)).deriv.symm 
    simpa using B.union A

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ≠ » x)
/-- If a real function `f` has a derivative `g` everywhere but at a point, and `f` and `g` are
continuous at this point, then `g` is the derivative of `f` everywhere. -/
theorem has_deriv_at_of_has_deriv_at_of_ne' {f g : ℝ → E} {x : ℝ} (f_diff : ∀ y _ : y ≠ x, HasDerivAt f (g y) y)
  (hf : ContinuousAt f x) (hg : ContinuousAt g x) (y : ℝ) : HasDerivAt f (g y) y :=
  by 
    rcases eq_or_ne y x with (rfl | hne)
    ·
      exact has_deriv_at_of_has_deriv_at_of_ne f_diff hf hg
    ·
      exact f_diff y hne

