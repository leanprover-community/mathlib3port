import Mathbin.MeasureTheory.Integral.Lebesgue 
import Mathbin.ProbabilityTheory.Independence

/-!
# Integration in Probability Theory

Integration results for independent random variables. Specifically, for two
independent random variables X and Y over the extended non-negative
reals, `E[X * Y] = E[X] * E[Y]`, and similar results.

## Implementation notes

Many lemmas in this file take two arguments of the same typeclass. It is worth remembering that lean
will always pick the later typeclass in this situation, and does not care whether the arguments are
`[]`, `{}`, or `()`. All of these use the `measurable_space` `M2` to define `μ`:

```lean
example {M1 : measurable_space α} [M2 : measurable_space α] {μ : measure α} : sorry := sorry
example [M1 : measurable_space α] {M2 : measurable_space α} {μ : measure α} : sorry := sorry
```

-/


noncomputable theory

open Set MeasureTheory

open_locale Ennreal

variable{α : Type _}

namespace ProbabilityTheory

-- error in ProbabilityTheory.Integration: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This (roughly) proves that if a random variable `f` is independent of an event `T`,
   then if you restrict the random variable to `T`, then
   `E[f * indicator T c 0]=E[f] * E[indicator T c 0]`. It is useful for
   `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space`. -/
theorem lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator
{Mf : measurable_space α}
[M : measurable_space α]
{μ : measure α}
(hMf : «expr ≤ »(Mf, M))
(c : «exprℝ≥0∞»())
{T : set α}
(h_meas_T : measurable_set T)
(h_ind : indep_sets Mf.measurable_set' {T} μ)
{f : α → «exprℝ≥0∞»()}
(h_meas_f : @measurable α «exprℝ≥0∞»() Mf _ f) : «expr = »(«expr∫⁻ , ∂ »((a), «expr * »(f a, T.indicator (λ
    _, c) a), μ), «expr * »(«expr∫⁻ , ∂ »((a), f a, μ), «expr∫⁻ , ∂ »((a), T.indicator (λ _, c) a, μ))) :=
begin
  revert [ident f],
  have [ident h_mul_indicator] [":", expr ∀
   g, measurable g → measurable (λ a, «expr * »(g a, T.indicator (λ x, c) a))] [],
  from [expr λ g h_mg, h_mg.mul (measurable_const.indicator h_meas_T)],
  apply [expr measurable.ennreal_induction],
  { intros [ident c', ident s', ident h_meas_s'],
    simp_rw ["[", "<-", expr inter_indicator_mul, "]"] [],
    rw ["[", expr lintegral_indicator _ (measurable_set.inter (hMf _ h_meas_s') h_meas_T), ",", expr lintegral_indicator _ (hMf _ h_meas_s'), ",", expr lintegral_indicator _ h_meas_T, "]"] [],
    simp [] [] ["only"] ["[", expr measurable_const, ",", expr lintegral_const, ",", expr univ_inter, ",", expr lintegral_const_mul, ",", expr measurable_set.univ, ",", expr measure.restrict_apply, "]"] [] [],
    ring_nf [] [] [],
    congr,
    rw ["[", expr mul_comm, ",", expr h_ind s' T h_meas_s' (set.mem_singleton _), "]"] [] },
  { intros [ident f', ident g, ident h_univ, ident h_meas_f', ident h_meas_g, ident h_ind_f', ident h_ind_g],
    have [ident h_measM_f'] [":", expr measurable f'] [],
    from [expr h_meas_f'.mono hMf le_rfl],
    have [ident h_measM_g] [":", expr measurable g] [],
    from [expr h_meas_g.mono hMf le_rfl],
    simp_rw ["[", expr pi.add_apply, ",", expr right_distrib, "]"] [],
    rw ["[", expr lintegral_add (h_mul_indicator _ h_measM_f') (h_mul_indicator _ h_measM_g), ",", expr lintegral_add h_measM_f' h_measM_g, ",", expr right_distrib, ",", expr h_ind_f', ",", expr h_ind_g, "]"] [] },
  { intros [ident f, ident h_meas_f, ident h_mono_f, ident h_ind_f],
    have [ident h_measM_f] [":", expr ∀ n, measurable (f n)] [],
    from [expr λ n, (h_meas_f n).mono hMf le_rfl],
    simp_rw ["[", expr ennreal.supr_mul, "]"] [],
    rw ["[", expr lintegral_supr h_measM_f h_mono_f, ",", expr lintegral_supr, ",", expr ennreal.supr_mul, "]"] [],
    { simp_rw ["[", "<-", expr h_ind_f, "]"] [] },
    { exact [expr λ n, h_mul_indicator _ (h_measM_f n)] },
    { exact [expr λ m n h_le a, ennreal.mul_le_mul (h_mono_f h_le a) le_rfl] } }
end

-- error in ProbabilityTheory.Integration: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- This (roughly) proves that if `f` and `g` are independent random variables,
   then `E[f * g] = E[f] * E[g]`. However, instead of directly using the independence
   of the random variables, it uses the independence of measurable spaces for the
   domains of `f` and `g`. This is similar to the sigma-algebra approach to
   independence. See `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_fn` for
   a more common variant of the product of independent variables. -/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space
{Mf Mg : measurable_space α}
[M : measurable_space α]
{μ : measure α}
(hMf : «expr ≤ »(Mf, M))
(hMg : «expr ≤ »(Mg, M))
(h_ind : indep Mf Mg μ)
{f g : α → «exprℝ≥0∞»()}
(h_meas_f : @measurable α «exprℝ≥0∞»() Mf _ f)
(h_meas_g : @measurable α «exprℝ≥0∞»() Mg _ g) : «expr = »(«expr∫⁻ , ∂ »((a), «expr * »(f a, g a), μ), «expr * »(«expr∫⁻ , ∂ »((a), f a, μ), «expr∫⁻ , ∂ »((a), g a, μ))) :=
begin
  revert [ident g],
  have [ident h_measM_f] [":", expr measurable f] [],
  from [expr h_meas_f.mono hMf le_rfl],
  apply [expr measurable.ennreal_induction],
  { intros [ident c, ident s, ident h_s],
    apply [expr lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator hMf _ (hMg _ h_s) _ h_meas_f],
    apply [expr indep_sets_of_indep_sets_of_le_right h_ind],
    rwa [expr singleton_subset_iff] [] },
  { intros [ident f', ident g, ident h_univ, ident h_measMg_f', ident h_measMg_g, ident h_ind_f', ident h_ind_g'],
    have [ident h_measM_f'] [":", expr measurable f'] [],
    from [expr h_measMg_f'.mono hMg le_rfl],
    have [ident h_measM_g] [":", expr measurable g] [],
    from [expr h_measMg_g.mono hMg le_rfl],
    simp_rw ["[", expr pi.add_apply, ",", expr left_distrib, "]"] [],
    rw ["[", expr lintegral_add h_measM_f' h_measM_g, ",", expr lintegral_add (h_measM_f.mul h_measM_f') (h_measM_f.mul h_measM_g), ",", expr left_distrib, ",", expr h_ind_f', ",", expr h_ind_g', "]"] [] },
  { intros [ident f', ident h_meas_f', ident h_mono_f', ident h_ind_f'],
    have [ident h_measM_f'] [":", expr ∀ n, measurable (f' n)] [],
    from [expr λ n, (h_meas_f' n).mono hMg le_rfl],
    simp_rw ["[", expr ennreal.mul_supr, "]"] [],
    rw ["[", expr lintegral_supr, ",", expr lintegral_supr h_measM_f' h_mono_f', ",", expr ennreal.mul_supr, "]"] [],
    { simp_rw ["[", "<-", expr h_ind_f', "]"] [] },
    { exact [expr λ n, h_measM_f.mul (h_measM_f' n)] },
    { exact [expr λ (n m) (h_le : «expr ≤ »(n, m)) (a), ennreal.mul_le_mul le_rfl (h_mono_f' h_le a)] } }
end

/-- This proves that if `f` and `g` are independent random variables,
   then `E[f * g] = E[f] * E[g]`. -/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun [MeasurableSpace α] {μ : Measureₓ α} {f g : α → ℝ≥0∞}
  (h_meas_f : Measurable f) (h_meas_g : Measurable g) (h_indep_fun : indep_fun f g μ) :
  (∫⁻a, (f*g) a ∂μ) = (∫⁻a, f a ∂μ)*∫⁻a, g a ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space (measurable_iff_comap_le.1 h_meas_f)
    (measurable_iff_comap_le.1 h_meas_g) h_indep_fun (Measurable.of_comap_le le_rfl) (Measurable.of_comap_le le_rfl)

end ProbabilityTheory

