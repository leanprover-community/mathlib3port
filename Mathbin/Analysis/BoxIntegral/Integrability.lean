import Mathbin.Analysis.BoxIntegral.Basic

/-!
# McShane integrability vs Bochner integrability

In this file we prove that any Bochner integrable function is McShane integrable (hence, it is
Henstock and `⊥` integrable) with the same integral. The proof is based on
[Russel A. Gordon, *The integrals of Lebesgue, Denjoy, Perron, and Henstock*][Gordon55].

## Tags

integral, McShane integral, Bochner integral
-/


open_locale Classical Nnreal Ennreal TopologicalSpace BigOperators

universe u v

variable{ι : Type u}{E : Type v}[Fintype ι][NormedGroup E][NormedSpace ℝ E]

open MeasureTheory Metric Set Finset Filter BoxIntegral

namespace BoxIntegral

-- error in Analysis.BoxIntegral.Integrability: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The indicator function of a measurable set is McShane integrable with respect to any
locally-finite measure. -/
theorem has_integral_indicator_const
(l : integration_params)
(hl : «expr = »(l.bRiemann, ff))
{s : set (ι → exprℝ())}
(hs : measurable_set s)
(I : box ι)
(y : E)
(μ : measure (ι → exprℝ()))
[is_locally_finite_measure μ] : has_integral.{u, v, v} I l (s.indicator (λ
  _, y)) μ.to_box_additive.to_smul «expr • »((μ «expr ∩ »(s, I)).to_real, y) :=
begin
  refine [expr has_integral_of_mul «expr∥ ∥»(y) (λ ε ε0, _)],
  lift [expr ε] ["to", expr «exprℝ≥0»()] ["using", expr ε0.le] [],
  rw [expr nnreal.coe_pos] ["at", ident ε0],
  have [ident A] [":", expr «expr ≠ »(μ «expr ∩ »(s, I.Icc), «expr∞»())] [],
  from [expr («expr $ »(measure_mono, set.inter_subset_right _ _).trans_lt (I.measure_Icc_lt_top μ)).ne],
  have [ident B] [":", expr «expr ≠ »(μ «expr ∩ »(s, I), «expr∞»())] [],
  from [expr («expr $ »(measure_mono, set.inter_subset_right _ _).trans_lt (I.measure_coe_lt_top μ)).ne],
  obtain ["⟨", ident F, ",", ident hFs, ",", ident hFc, ",", ident hμF, "⟩", ":", expr «expr∃ , »((F «expr ⊆ » «expr ∩ »(s, I.Icc)), «expr ∧ »(is_closed F, «expr < »(μ «expr \ »(«expr ∩ »(s, I.Icc), F), ε)))],
  from [expr (hs.inter I.measurable_set_Icc).exists_is_closed_diff_lt A (ennreal.coe_pos.2 ε0).ne'],
  obtain ["⟨", ident U, ",", ident hsU, ",", ident hUo, ",", ident hUt, ",", ident hμU, "⟩", ":", expr «expr∃ , »((U «expr ⊇ » «expr ∩ »(s, I.Icc)), «expr ∧ »(is_open U, «expr ∧ »(«expr < »(μ U, «expr∞»()), «expr < »(μ «expr \ »(U, «expr ∩ »(s, I.Icc)), ε))))],
  from [expr (hs.inter I.measurable_set_Icc).exists_is_open_diff_lt A (ennreal.coe_pos.2 ε0).ne'],
  have [] [":", expr ∀
   x «expr ∈ » «expr ∩ »(s, I.Icc), «expr∃ , »((r : Ioi (0 : exprℝ())), «expr ⊆ »(closed_ball x r, U))] [],
  from [expr λ x hx, subtype.exists'.1 (nhds_basis_closed_ball.mem_iff.1 «expr $ »(hUo.mem_nhds, hsU hx))],
  choose ["!"] [ident rs] [ident hrsU] [],
  have [] [":", expr ∀
   x «expr ∈ » «expr \ »(I.Icc, s), «expr∃ , »((r : Ioi (0 : exprℝ())), «expr ⊆ »(closed_ball x r, «expr ᶜ»(F)))] [],
  from [expr λ
   x
   hx, subtype.exists'.1 (nhds_basis_closed_ball.mem_iff.1 «expr $ »(hFc.is_open_compl.mem_nhds, λ
     hx', hx.2 (hFs hx').1))],
  choose ["!"] [ident rs'] [ident hrs'F] [],
  set [] [ident r] [":", expr (ι → exprℝ()) → Ioi (0 : exprℝ())] [":="] [expr s.piecewise rs rs'] [],
  refine [expr ⟨λ c, r, λ c, l.r_cond_of_bRiemann_eq_ff hl, λ c π hπ hπp, _⟩],
  rw [expr mul_comm] [],
  dsimp [] ["[", expr integral_sum, "]"] [] [],
  simp [] [] ["only"] ["[", expr mem_closed_ball, ",", expr dist_eq_norm, ",", "<-", expr indicator_smul_apply, ",", expr sum_indicator_eq_sum_filter, ",", "<-", expr sum_smul, ",", "<-", expr sub_smul, ",", expr norm_smul, ",", expr real.norm_eq_abs, ",", "<-", expr prepartition.filter_boxes, ",", "<-", expr prepartition.measure_Union_to_real, "]"] [] [],
  refine [expr mul_le_mul_of_nonneg_right _ (norm_nonneg y)],
  set [] [ident t] [] [":="] [expr (π.to_prepartition.filter (λ J, «expr ∈ »(π.tag J, s))).Union] [],
  change [expr «expr ≤ »(abs «expr - »((μ t).to_real, (μ «expr ∩ »(s, I)).to_real), ε)] [] [],
  have [ident htU] [":", expr «expr ⊆ »(t, «expr ∩ »(U, I))] [],
  { simp [] [] ["only"] ["[", expr t, ",", expr prepartition.Union_def, ",", expr Union_subset_iff, ",", expr prepartition.mem_filter, ",", expr and_imp, "]"] [] [],
    refine [expr λ J hJ hJs x hx, ⟨hrsU _ ⟨hJs, π.tag_mem_Icc J⟩ _, π.le_of_mem' J hJ hx⟩],
    simpa [] [] ["only"] ["[", expr r, ",", expr s.piecewise_eq_of_mem _ _ hJs, "]"] [] ["using", expr hπ.1 J hJ (box.coe_subset_Icc hx)] },
  refine [expr abs_sub_le_iff.2 ⟨_, _⟩],
  { refine [expr (ennreal.le_to_real_sub B).trans (ennreal.to_real_le_coe_of_le_coe _)],
    refine [expr (tsub_le_tsub (measure_mono htU) le_rfl).trans (le_measure_diff.trans _)],
    refine [expr «expr $ »(measure_mono, λ x hx, _).trans hμU.le],
    exact [expr ⟨hx.1.1, λ hx', hx.2 ⟨hx'.1, hx.1.2⟩⟩] },
  { have [ident hμt] [":", expr «expr ≠ »(μ t, «expr∞»())] [":=", expr ((measure_mono (htU.trans (inter_subset_left _ _))).trans_lt hUt).ne],
    refine [expr (ennreal.le_to_real_sub hμt).trans (ennreal.to_real_le_coe_of_le_coe _)],
    refine [expr le_measure_diff.trans ((measure_mono _).trans hμF.le)],
    rintro [ident x, "⟨", "⟨", ident hxs, ",", ident hxI, "⟩", ",", ident hxt, "⟩"],
    refine [expr ⟨⟨hxs, box.coe_subset_Icc hxI⟩, λ hxF, hxt _⟩],
    simp [] [] ["only"] ["[", expr t, ",", expr prepartition.Union_def, ",", expr prepartition.mem_filter, ",", expr set.mem_Union, ",", expr exists_prop, "]"] [] [],
    rcases [expr hπp x hxI, "with", "⟨", ident J, ",", ident hJπ, ",", ident hxJ, "⟩"],
    refine [expr ⟨J, ⟨hJπ, _⟩, hxJ⟩],
    contrapose [] [ident hxF],
    refine [expr hrs'F _ ⟨π.tag_mem_Icc J, hxF⟩ _],
    simpa [] [] ["only"] ["[", expr r, ",", expr s.piecewise_eq_of_not_mem _ _ hxF, "]"] [] ["using", expr hπ.1 J hJπ (box.coe_subset_Icc hxJ)] }
end

-- error in Analysis.BoxIntegral.Integrability: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` is a.e. equal to zero on a rectangular box, then it has McShane integral zero on this
box. -/
theorem has_integral_zero_of_ae_eq_zero
{l : integration_params}
{I : box ι}
{f : (ι → exprℝ()) → E}
{μ : measure (ι → exprℝ())}
[is_locally_finite_measure μ]
(hf : «expr =ᵐ[ ] »(f, μ.restrict I, 0))
(hl : «expr = »(l.bRiemann, ff)) : has_integral.{u, v, v} I l f μ.to_box_additive.to_smul 0 :=
begin
  refine [expr has_integral_iff.2 (λ ε ε0, _)],
  lift [expr ε] ["to", expr «exprℝ≥0»()] ["using", expr ε0.lt.le] [],
  rw ["[", expr gt_iff_lt, ",", expr nnreal.coe_pos, "]"] ["at", ident ε0],
  rcases [expr nnreal.exists_pos_sum_of_encodable ε0.ne' exprℕ(), "with", "⟨", ident δ, ",", ident δ0, ",", ident c, ",", ident hδc, ",", ident hcε, "⟩"],
  haveI [] [] [":=", expr fact.mk (I.measure_coe_lt_top μ)],
  change [expr «expr = »(μ.restrict I {x | «expr ≠ »(f x, 0)}, 0)] [] ["at", ident hf],
  set [] [ident N] [":", expr (ι → exprℝ()) → exprℕ()] [":="] [expr λ x, «expr⌈ ⌉₊»(«expr∥ ∥»(f x))] [],
  have [ident N0] [":", expr ∀ {x}, «expr ↔ »(«expr = »(N x, 0), «expr = »(f x, 0))] [],
  by { intro [ident x],
    simp [] [] [] ["[", expr N, "]"] [] [] },
  have [] [":", expr ∀
   n, «expr∃ , »((U «expr ⊇ » «expr ⁻¹' »(N, {n})), «expr ∧ »(is_open U, «expr < »(μ.restrict I U, «expr / »(δ n, n))))] [],
  { refine [expr λ n, «expr ⁻¹' »(N, {n}).exists_is_open_lt_of_lt _ _],
    cases [expr n] [],
    { simpa [] [] [] ["[", expr ennreal.div_zero (ennreal.coe_pos.2 (δ0 _)).ne', "]"] [] ["using", expr measure_lt_top (μ.restrict I) _] },
    { refine [expr (measure_mono_null _ hf).le.trans_lt _],
      { exact [expr λ x hxN hxf, n.succ_ne_zero «expr $ »((eq.symm hxN).trans, N0.2 hxf)] },
      { simp [] [] [] ["[", expr (δ0 _).ne', "]"] [] [] } } },
  choose [] [ident U] [ident hNU, ident hUo, ident hμU] [],
  have [] [":", expr ∀ x, «expr∃ , »((r : Ioi (0 : exprℝ())), «expr ⊆ »(closed_ball x r, U (N x)))] [],
  from [expr λ x, subtype.exists'.1 (nhds_basis_closed_ball.mem_iff.1 ((hUo _).mem_nhds (hNU _ rfl)))],
  choose [] [ident r] [ident hrU] [],
  refine [expr ⟨λ _, r, λ c, l.r_cond_of_bRiemann_eq_ff hl, λ c π hπ hπp, _⟩],
  rw ["[", expr dist_eq_norm, ",", expr sub_zero, ",", "<-", expr integral_sum_fiberwise (λ J, N (π.tag J)), "]"] [],
  refine [expr le_trans _ (nnreal.coe_lt_coe.2 hcε).le],
  refine [expr (norm_sum_le_of_le _ _).trans (sum_le_has_sum _ (λ n _, (δ n).2) (nnreal.has_sum_coe.2 hδc))],
  rintro [ident n, "-"],
  dsimp [] ["[", expr integral_sum, "]"] [] [],
  have [] [":", expr ∀
   J «expr ∈ » π.filter (λ
    J, «expr = »(N (π.tag J), n)), «expr ≤ »(«expr∥ ∥»(«expr • »((μ «expr↑ »(J)).to_real, f (π.tag J))), «expr * »((μ J).to_real, n))] [],
  { intros [ident J, ident hJ],
    rw [expr tagged_prepartition.mem_filter] ["at", ident hJ],
    rw ["[", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg ennreal.to_real_nonneg, "]"] [],
    exact [expr mul_le_mul_of_nonneg_left «expr ▸ »(hJ.2, nat.le_ceil _) ennreal.to_real_nonneg] },
  refine [expr (norm_sum_le_of_le _ this).trans _],
  clear [ident this],
  rw ["[", "<-", expr sum_mul, ",", "<-", expr prepartition.measure_Union_to_real, "]"] [],
  generalize [ident hm] [":"] [expr «expr = »(μ (π.filter (λ J, «expr = »(N (π.tag J), n))).Union, m)],
  have [] [":", expr «expr < »(m, «expr / »(δ n, n))] [],
  { simp [] [] ["only"] ["[", expr measure.restrict_apply (hUo _).measurable_set, "]"] [] ["at", ident hμU],
    refine [expr «expr ▸ »(hm, (measure_mono _).trans_lt (hμU _))],
    simp [] [] ["only"] ["[", expr set.subset_def, ",", expr tagged_prepartition.mem_Union, ",", expr exists_prop, ",", expr tagged_prepartition.mem_filter, "]"] [] [],
    rintro [ident x, "⟨", ident J, ",", "⟨", ident hJ, ",", ident rfl, "⟩", ",", ident hx, "⟩"],
    exact [expr ⟨hrU _ (hπ.1 _ hJ (box.coe_subset_Icc hx)), π.le_of_mem' J hJ hx⟩] },
  lift [expr m] ["to", expr «exprℝ≥0»()] ["using", expr ne_top_of_lt this] [],
  rw ["[", expr ennreal.coe_to_real, ",", "<-", expr nnreal.coe_nat_cast, ",", "<-", expr nnreal.coe_mul, ",", expr nnreal.coe_le_coe, ",", "<-", expr ennreal.coe_le_coe, ",", expr ennreal.coe_mul, ",", expr ennreal.coe_nat, ",", expr mul_comm, "]"] [],
  exact [expr (mul_le_mul_left' this.le _).trans ennreal.mul_div_le]
end

-- error in Analysis.BoxIntegral.Integrability: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` has integral `y` on a box `I` with respect to a locally finite measure `μ` and `g` is
a.e. equal to `f` on `I`, then `g` has the same integral on `I`.  -/
theorem has_integral.congr_ae
{l : integration_params}
{I : box ι}
{y : E}
{f g : (ι → exprℝ()) → E}
{μ : measure (ι → exprℝ())}
[is_locally_finite_measure μ]
(hf : has_integral.{u, v, v} I l f μ.to_box_additive.to_smul y)
(hfg : «expr =ᵐ[ ] »(f, μ.restrict I, g))
(hl : «expr = »(l.bRiemann, ff)) : has_integral.{u, v, v} I l g μ.to_box_additive.to_smul y :=
begin
  have [] [":", expr «expr =ᵐ[ ] »(«expr - »(g, f), μ.restrict I, 0)] [],
  from [expr hfg.mono (λ x hx, sub_eq_zero.2 hx.symm)],
  simpa [] [] [] [] [] ["using", expr hf.add (has_integral_zero_of_ae_eq_zero this hl)]
end

end BoxIntegral

namespace MeasureTheory

namespace SimpleFunc

-- error in Analysis.BoxIntegral.Integrability: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A simple function is McShane integrable w.r.t. any locally finite measure. -/
theorem has_box_integral
(f : simple_func (ι → exprℝ()) E)
(μ : measure (ι → exprℝ()))
[is_locally_finite_measure μ]
(I : box ι)
(l : integration_params)
(hl : «expr = »(l.bRiemann, ff)) : has_integral.{u, v, v} I l f μ.to_box_additive.to_smul (f.integral (μ.restrict I)) :=
begin
  induction [expr f] ["using", ident measure_theory.simple_func.induction] ["with", ident y, ident s, ident hs, ident f, ident g, ident hd, ident hfi, ident hgi] [],
  { simpa [] [] [] ["[", expr function.const, ",", expr measure.restrict_apply hs, "]"] [] ["using", expr box_integral.has_integral_indicator_const l hl hs I y μ] },
  { letI [] [] [":=", expr borel E],
    haveI [] [":", expr borel_space E] [":=", expr ⟨rfl⟩],
    haveI [] [] [":=", expr fact.mk (I.measure_coe_lt_top μ)],
    rw [expr integral_add] [],
    exacts ["[", expr hfi.add hgi, ",", expr «expr $ »(integrable_iff.2, λ
      _ _, measure_lt_top _ _), ",", expr «expr $ »(integrable_iff.2, λ _ _, measure_lt_top _ _), "]"] }
end

/-- For a simple function, its McShane (or Henstock, or `⊥`) box integral is equal to its
integral in the sense of `measure_theory.simple_func.integral`. -/
theorem box_integral_eq_integral (f : simple_func (ι → ℝ) E) (μ : Measureₓ (ι → ℝ)) [is_locally_finite_measure μ]
  (I : box ι) (l : integration_params) (hl : l.bRiemann = ff) :
  BoxIntegral.integral.{u, v, v} I l f μ.to_box_additive.to_smul = f.integral (μ.restrict I) :=
  (f.has_box_integral μ I l hl).integral_eq

end SimpleFunc

open TopologicalSpace

-- error in Analysis.BoxIntegral.Integrability: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f : ℝⁿ → E` is Bochner integrable w.r.t. a locally finite measure `μ` on a rectangular box
`I`, then it is McShane integrable on `I` with the same integral.  -/
theorem integrable_on.has_box_integral
[second_countable_topology E]
[measurable_space E]
[borel_space E]
[complete_space E]
{f : (ι → exprℝ()) → E}
{μ : measure (ι → exprℝ())}
[is_locally_finite_measure μ]
{I : box ι}
(hf : integrable_on f I μ)
(l : integration_params)
(hl : «expr = »(l.bRiemann, ff)) : has_integral.{u, v, v} I l f μ.to_box_additive.to_smul «expr∫ in , ∂ »((x), I, f x, μ) :=
begin
  rcases [expr hf.ae_measurable, "with", "⟨", ident g, ",", ident hg, ",", ident hfg, "⟩"],
  rw [expr integral_congr_ae hfg] [],
  have [ident hgi] [":", expr integrable_on g I μ] [":=", expr (integrable_congr hfg).1 hf],
  refine [expr box_integral.has_integral.congr_ae _ hfg.symm hl],
  clear_dependent [ident f],
  set [] [ident f] [":", expr exprℕ() → simple_func (ι → exprℝ()) E] [":="] [expr simple_func.approx_on g hg univ 0 trivial] [],
  have [ident hfi] [":", expr ∀ n, integrable_on (f n) I μ] [],
  from [expr simple_func.integrable_approx_on_univ hg hgi],
  have [ident hfi'] [] [":=", expr λ n, ((f n).has_box_integral μ I l hl).integrable],
  have [ident hfgi] [":", expr tendsto (λ
    n, (f n).integral (μ.restrict I)) at_top «expr $ »(expr𝓝(), «expr∫ in , ∂ »((x), I, g x, μ))] [],
  from [expr tendsto_integral_approx_on_univ_of_measurable hg hgi],
  have [ident hfg_mono] [":", expr ∀
   (x)
   {m n}, «expr ≤ »(m, n) → «expr ≤ »(«expr∥ ∥»(«expr - »(f n x, g x)), «expr∥ ∥»(«expr - »(f m x, g x)))] [],
  { intros [ident x, ident m, ident n, ident hmn],
    rw ["[", "<-", expr dist_eq_norm, ",", "<-", expr dist_eq_norm, ",", expr dist_nndist, ",", expr dist_nndist, ",", expr nnreal.coe_le_coe, ",", "<-", expr ennreal.coe_le_coe, ",", "<-", expr edist_nndist, ",", "<-", expr edist_nndist, "]"] [],
    exact [expr simple_func.edist_approx_on_mono hg _ x hmn] },
  refine [expr has_integral_of_mul «expr + »(«expr + »((μ I).to_real, 1), 1) (λ ε ε0, _)],
  lift [expr ε] ["to", expr «exprℝ≥0»()] ["using", expr ε0.le] [],
  rw [expr nnreal.coe_pos] ["at", ident ε0],
  have [ident ε0'] [] [":=", expr ennreal.coe_pos.2 ε0],
  obtain ["⟨", ident N₀, ",", ident hN₀, "⟩", ":", expr «expr∃ , »((N : exprℕ()), «expr ≤ »(«expr∫ in , ∂ »((x), I, «expr∥ ∥»(«expr - »(f N x, g x)), μ), ε))],
  { have [] [":", expr tendsto (λ
      n, «expr∫⁻ in , ∂ »((x), I, «expr∥ ∥₊»(«expr - »(f n x, g x)), μ)) at_top (expr𝓝() 0)] [],
    from [expr simple_func.tendsto_approx_on_univ_L1_nnnorm hg hgi],
    refine [expr (this.eventually (ge_mem_nhds ε0')).exists.imp (λ N hN, _)],
    exact [expr integral_coe_le_of_lintegral_coe_le hN] },
  have [] [":", expr ∀ x, «expr∃ , »((N₁), «expr ∧ »(«expr ≤ »(N₀, N₁), «expr ≤ »(dist (f N₁ x) (g x), ε)))] [],
  { intro [ident x],
    have [] [":", expr tendsto (λ n, f n x) at_top «expr $ »(expr𝓝(), g x)] [],
    from [expr simple_func.tendsto_approx_on hg _ (subset_closure trivial)],
    exact [expr «expr $ »((eventually_ge_at_top N₀).and, «expr $ »(this, closed_ball_mem_nhds _ ε0)).exists] },
  choose [] [ident Nx] [ident hNx, ident hNxε] [],
  rcases [expr nnreal.exists_pos_sum_of_encodable ε0.ne' exprℕ(), "with", "⟨", ident δ, ",", ident δ0, ",", ident c, ",", ident hδc, ",", ident hcε, "⟩"],
  set [] [ident r] [":", expr «exprℝ≥0»() → (ι → exprℝ()) → Ioi (0 : exprℝ())] [":="] [expr λ
   c x, «expr $ »(hfi', Nx x).convergence_r «expr $ »(δ, Nx x) c x] [],
  refine [expr ⟨r, λ c, l.r_cond_of_bRiemann_eq_ff hl, λ c π hπ hπp, _⟩],
  refine [expr (dist_triangle4 _ «expr∑ in , »((J), π.boxes, «expr • »((μ J).to_real, f «expr $ »(Nx, π.tag J) (π.tag J))) «expr∑ in , »((J), π.boxes, «expr∫ in , ∂ »((x), J, f «expr $ »(Nx, π.tag J) x, μ)) _).trans _],
  rw ["[", expr add_mul, ",", expr add_mul, ",", expr one_mul, "]"] [],
  refine [expr add_le_add_three _ _ _],
  { rw ["[", "<-", expr hπp.Union_eq, ",", expr π.to_prepartition.measure_Union_to_real, ",", expr sum_mul, ",", expr integral_sum, "]"] [],
    refine [expr dist_sum_sum_le_of_le _ (λ J hJ, _)],
    dsimp [] [] [] [],
    rw ["[", expr dist_eq_norm, ",", "<-", expr smul_sub, ",", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg ennreal.to_real_nonneg, "]"] [],
    refine [expr mul_le_mul_of_nonneg_left _ ennreal.to_real_nonneg],
    rw ["[", "<-", expr dist_eq_norm', "]"] [],
    exact [expr hNxε _] },
  { rw ["[", "<-", expr π.to_prepartition.sum_fiberwise (λ
      J, Nx (π.tag J)), ",", "<-", expr π.to_prepartition.sum_fiberwise (λ J, Nx (π.tag J)), "]"] [],
    refine [expr le_trans _ (nnreal.coe_lt_coe.2 hcε).le],
    refine [expr (dist_sum_sum_le_of_le _ (λ
       n hn, _)).trans (sum_le_has_sum _ (λ n _, (δ n).2) (nnreal.has_sum_coe.2 hδc))],
    have [ident hNxn] [":", expr ∀
     J «expr ∈ » π.filter (λ J, «expr = »(Nx (π.tag J), n)), «expr = »(Nx (π.tag J), n)] [],
    from [expr λ J hJ, (π.mem_filter.1 hJ).2],
    have [ident hrn] [":", expr ∀
     J «expr ∈ » π.filter (λ
      J, «expr = »(Nx (π.tag J), n)), «expr = »(r c (π.tag J), (hfi' n).convergence_r (δ n) c (π.tag J))] [],
    { intros [ident J, ident hJ],
      have [] [] [":=", expr hNxn J hJ],
      clear [ident hJ],
      subst [expr n] },
    have [] [":", expr l.mem_base_set I c ((hfi' n).convergence_r (δ n) c) (π.filter (λ
       J, «expr = »(Nx (π.tag J), n)))] [],
    from [expr (hπ.filter _).mono' _ le_rfl le_rfl (λ J hJ, (hrn J hJ).le)],
    convert [] [expr (hfi' n).dist_integral_sum_sum_integral_le_of_mem_base_set (δ0 _) this] ["using", 2],
    { refine [expr sum_congr rfl (λ J hJ, _)],
      simp [] [] [] ["[", expr hNxn J hJ, "]"] [] [] },
    { refine [expr sum_congr rfl (λ J hJ, _)],
      rw ["[", "<-", expr simple_func.integral_eq_integral, ",", expr simple_func.box_integral_eq_integral _ _ _ _ hl, ",", expr hNxn J hJ, "]"] [],
      exact [expr (hfi _).mono_set (prepartition.le_of_mem _ hJ)] } },
  { refine [expr le_trans _ hN₀],
    have [ident hfi] [":", expr ∀ (n) (J «expr ∈ » π), integrable_on (f n) «expr↑ »(J) μ] [],
    from [expr λ n J hJ, (hfi n).mono_set (π.le_of_mem' J hJ)],
    have [ident hgi] [":", expr ∀ J «expr ∈ » π, integrable_on g «expr↑ »(J) μ] [],
    from [expr λ J hJ, hgi.mono_set (π.le_of_mem' J hJ)],
    have [ident hfgi] [":", expr ∀ (n) (J «expr ∈ » π), integrable_on (λ x, «expr∥ ∥»(«expr - »(f n x, g x))) J μ] [],
    from [expr λ n J hJ, ((hfi n J hJ).sub (hgi J hJ)).norm],
    rw ["[", "<-", expr hπp.Union_eq, ",", expr prepartition.Union_def', ",", expr integral_finset_bUnion π.boxes (λ
      J
      hJ, J.measurable_set_coe) π.pairwise_disjoint hgi, ",", expr integral_finset_bUnion π.boxes (λ
      J hJ, J.measurable_set_coe) π.pairwise_disjoint (hfgi _), "]"] [],
    refine [expr dist_sum_sum_le_of_le _ (λ J hJ, _)],
    rw ["[", expr dist_eq_norm, ",", "<-", expr integral_sub (hfi _ J hJ) (hgi J hJ), "]"] [],
    refine [expr norm_integral_le_of_norm_le (hfgi _ J hJ) «expr $ »(eventually_of_forall, λ x, _)],
    exact [expr hfg_mono x (hNx (π.tag J))] }
end

end MeasureTheory

