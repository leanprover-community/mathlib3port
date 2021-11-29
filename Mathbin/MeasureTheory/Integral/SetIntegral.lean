import Mathbin.MeasureTheory.Integral.IntegrableOn 
import Mathbin.MeasureTheory.Integral.Bochner 
import Mathbin.Order.Filter.IndicatorFunction

/-!
# Set integral

In this file we prove some properties of `∫ x in s, f x ∂μ`. Recall that this notation
is defined as `∫ x, f x ∂(μ.restrict s)`. In `integral_indicator` we prove that for a measurable
function `f` and a measurable set `s` this definition coincides with another natural definition:
`∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ`, where `indicator s f x` is equal to `f x` for `x ∈ s`
and is zero otherwise.

Since `∫ x in s, f x ∂μ` is a notation, one can rewrite or apply any theorem about `∫ x, f x ∂μ`
directly. In this file we prove some theorems about dependence of `∫ x in s, f x ∂μ` on `s`, e.g.
`integral_union`, `integral_empty`, `integral_univ`.

We use the property `integrable_on f s μ := integrable f (μ.restrict s)`, defined in
`measure_theory.integrable_on`. We also defined in that same file a predicate
`integrable_at_filter (f : α → E) (l : filter α) (μ : measure α)` saying that `f` is integrable at
some set `s ∈ l`.

Finally, we prove a version of the
[Fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for set integral, see `filter.tendsto.integral_sub_linear_is_o_ae` and its corollaries.
Namely, consider a measurably generated filter `l`, a measure `μ` finite at this filter, and
a function `f` that has a finite limit `c` at `l ⊓ μ.ae`. Then `∫ x in s, f x ∂μ = μ s • c + o(μ s)`
as `s` tends to `l.lift' powerset`, i.e. for any `ε>0` there exists `t ∈ l` such that
`∥∫ x in s, f x ∂μ - μ s • c∥ ≤ ε * μ s` whenever `s ⊆ t`. We also formulate a version of this
theorem for a locally finite measure `μ` and a function `f` continuous at a point `a`.

## Notation

We provide the following notations for expressing the integral of a function on a set :
* `∫ a in s, f a ∂μ` is `measure_theory.integral (μ.restrict s) f`
* `∫ a in s, f a` is `∫ a in s, f a ∂volume`

Note that the set notations are defined in the file `measure_theory/integral/bochner`,
but we reference them here because all theorems about set integrals are in this file.

-/


noncomputable theory

open Set Filter TopologicalSpace MeasureTheory Function

open_locale Classical TopologicalSpace Interval BigOperators Filter Ennreal Nnreal MeasureTheory

variable {α β E F : Type _} [MeasurableSpace α]

namespace MeasureTheory

section NormedGroup

variable [NormedGroup E] [MeasurableSpace E] {f g : α → E} {s t : Set α} {μ ν : Measureₓ α} {l l' : Filter α}
  [BorelSpace E] [second_countable_topology E]

variable [CompleteSpace E] [NormedSpace ℝ E]

theorem set_integral_congr_ae (hs : MeasurableSet s) (h : ∀ᵐx ∂μ, x ∈ s → f x = g x) :
  (∫x in s, f x ∂μ) = ∫x in s, g x ∂μ :=
  integral_congr_ae ((ae_restrict_iff' hs).2 h)

theorem set_integral_congr (hs : MeasurableSet s) (h : eq_on f g s) : (∫x in s, f x ∂μ) = ∫x in s, g x ∂μ :=
  set_integral_congr_ae hs$ eventually_of_forall h

theorem set_integral_congr_set_ae (hst : s =ᵐ[μ] t) : (∫x in s, f x ∂μ) = ∫x in t, f x ∂μ :=
  by 
    rw [measure.restrict_congr_set hst]

theorem integral_union (hst : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t) (hfs : integrable_on f s μ)
  (hft : integrable_on f t μ) : (∫x in s ∪ t, f x ∂μ) = (∫x in s, f x ∂μ)+∫x in t, f x ∂μ :=
  by 
    simp only [integrable_on, measure.restrict_union hst hs ht, integral_add_measure hfs hft]

-- error in MeasureTheory.Integral.SetIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integral_union_ae
(hst : «expr =ᵐ[ ] »((«expr ∩ »(s, t) : set α), μ, («expr∅»() : set α)))
(hs : measurable_set s)
(ht : measurable_set t)
(hfs : integrable_on f s μ)
(hft : integrable_on f t μ) : «expr = »(«expr∫ in , ∂ »((x), «expr ∪ »(s, t), f x, μ), «expr + »(«expr∫ in , ∂ »((x), s, f x, μ), «expr∫ in , ∂ »((x), t, f x, μ))) :=
begin
  have [] [":", expr «expr =ᵐ[ ] »(s, μ, «expr \ »(s, t))] [],
  { refine [expr (hst.mem_iff.mono _).set_eq],
    simp [] [] [] [] [] [] },
  rw ["[", "<-", expr diff_union_self, ",", expr integral_union disjoint_diff.symm, ",", expr set_integral_congr_set_ae this, "]"] [],
  exacts ["[", expr hs.diff ht, ",", expr ht, ",", expr hfs.mono_set (diff_subset _ _), ",", expr hft, "]"]
end

theorem integral_diff (hs : MeasurableSet s) (ht : MeasurableSet t) (hfs : integrable_on f s μ)
  (hft : integrable_on f t μ) (hts : t ⊆ s) : (∫x in s \ t, f x ∂μ) = (∫x in s, f x ∂μ) - ∫x in t, f x ∂μ :=
  by 
    rw [eq_sub_iff_add_eq, ←integral_union, diff_union_of_subset hts]
    exacts[disjoint_diff.symm, hs.diff ht, ht, hfs.mono_set (diff_subset _ _), hft]

theorem integral_finset_bUnion {ι : Type _} (t : Finset ι) {s : ι → Set α} (hs : ∀ i _ : i ∈ t, MeasurableSet (s i))
  (h's : Set.Pairwise («expr↑ » t) (Disjoint on s)) (hf : ∀ i _ : i ∈ t, integrable_on f (s i) μ) :
  (∫x in ⋃(i : _)(_ : i ∈ t), s i, f x ∂μ) = ∑i in t, ∫x in s i, f x ∂μ :=
  by 
    induction' t using Finset.induction_on with a t hat IH hs h's
    ·
      simp 
    ·
      simp only [Finset.coe_insert, Finset.forall_mem_insert, Set.pairwise_insert, Finset.set_bUnion_insert] at hs hf
        h's⊢
      rw [integral_union _ hs.1 _ hf.1 (integrable_on_finset_Union.2 hf.2)]
      ·
        rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
      ·
        simp only [disjoint_Union_right]
        exact fun i hi => (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
      ·
        exact Finset.measurable_set_bUnion _ hs.2

theorem integral_fintype_Union {ι : Type _} [Fintype ι] {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i))
  (h's : Pairwise (Disjoint on s)) (hf : ∀ i, integrable_on f (s i) μ) :
  (∫x in ⋃i, s i, f x ∂μ) = ∑i, ∫x in s i, f x ∂μ :=
  by 
    convert integral_finset_bUnion Finset.univ (fun i hi => hs i) _ fun i _ => hf i
    ·
      simp 
    ·
      simp [pairwise_univ, h's]

theorem integral_empty : (∫x in ∅, f x ∂μ) = 0 :=
  by 
    rw [measure.restrict_empty, integral_zero_measure]

theorem integral_univ : (∫x in univ, f x ∂μ) = ∫x, f x ∂μ :=
  by 
    rw [measure.restrict_univ]

theorem integral_add_compl (hs : MeasurableSet s) (hfi : integrable f μ) :
  ((∫x in s, f x ∂μ)+∫x in «expr ᶜ» s, f x ∂μ) = ∫x, f x ∂μ :=
  by 
    rw [←integral_union (@disjoint_compl_right (Set α) _ _) hs hs.compl hfi.integrable_on hfi.integrable_on,
      union_compl_self, integral_univ]

/-- For a function `f` and a measurable set `s`, the integral of `indicator s f`
over the whole space is equal to `∫ x in s, f x ∂μ` defined as `∫ x, f x ∂(μ.restrict s)`. -/
theorem integral_indicator (hs : MeasurableSet s) : (∫x, indicator s f x ∂μ) = ∫x in s, f x ∂μ :=
  by 
    byCases' hf : AeMeasurable f (μ.restrict s)
    swap
    ·
      rw [integral_non_ae_measurable hf]
      rw [←ae_measurable_indicator_iff hs] at hf 
      exact integral_non_ae_measurable hf 
    byCases' hfi : integrable_on f s μ 
    swap
    ·
      rwa [integral_undef, integral_undef]
      rwa [integrable_indicator_iff hs]
    calc (∫x, indicator s f x ∂μ) = (∫x in s, indicator s f x ∂μ)+∫x in «expr ᶜ» s, indicator s f x ∂μ :=
      (integral_add_compl hs (hfi.indicator hs)).symm _ = (∫x in s, f x ∂μ)+∫x in «expr ᶜ» s, 0 ∂μ :=
      congr_arg2 (·+·) (integral_congr_ae (indicator_ae_eq_restrict hs))
        (integral_congr_ae (indicator_ae_eq_restrict_compl hs))_ = ∫x in s, f x ∂μ :=
      by 
        simp 

-- error in MeasureTheory.Integral.SetIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_set_integral_of_monotone
{ι : Type*}
[encodable ι]
[semilattice_sup ι]
{s : ι → set α}
{f : α → E}
(hsm : ∀ i, measurable_set (s i))
(h_mono : monotone s)
(hfi : integrable_on f «expr⋃ , »((n), s n) μ) : tendsto (λ
 i, «expr∫ in , ∂ »((a), s i, f a, μ)) at_top (expr𝓝() «expr∫ in , ∂ »((a), «expr⋃ , »((n), s n), f a, μ)) :=
begin
  have [ident hfi'] [":", expr «expr < »(«expr∫⁻ in , ∂ »((x), «expr⋃ , »((n), s n), «expr∥ ∥₊»(f x), μ), «expr∞»())] [":=", expr hfi.2],
  set [] [ident S] [] [":="] [expr «expr⋃ , »((i), s i)] [],
  have [ident hSm] [":", expr measurable_set S] [":=", expr measurable_set.Union hsm],
  have [ident hsub] [":", expr ∀ {i}, «expr ⊆ »(s i, S)] [],
  from [expr subset_Union s],
  rw ["[", "<-", expr with_density_apply _ hSm, "]"] ["at", ident hfi'],
  set [] [ident ν] [] [":="] [expr μ.with_density (λ x, «expr∥ ∥₊»(f x))] ["with", ident hν],
  refine [expr metric.nhds_basis_closed_ball.tendsto_right_iff.2 (λ ε ε0, _)],
  lift [expr ε] ["to", expr «exprℝ≥0»()] ["using", expr ε0.le] [],
  have [] [":", expr «expr∀ᶠ in , »((i), at_top, «expr ∈ »(ν (s i), Icc «expr - »(ν S, ε) «expr + »(ν S, ε)))] [],
  from [expr tendsto_measure_Union hsm h_mono (ennreal.Icc_mem_nhds hfi'.ne (ennreal.coe_pos.2 ε0).ne')],
  refine [expr this.mono (λ i hi, _)],
  rw ["[", expr mem_closed_ball_iff_norm', ",", "<-", expr integral_diff hSm (hsm i) hfi (hfi.mono_set hsub) hsub, ",", "<-", expr coe_nnnorm, ",", expr nnreal.coe_le_coe, ",", "<-", expr ennreal.coe_le_coe, "]"] [],
  refine [expr (ennnorm_integral_le_lintegral_ennnorm _).trans _],
  rw ["[", "<-", expr with_density_apply _ (hSm.diff (hsm _)), ",", "<-", expr hν, ",", expr measure_diff hsub hSm (hsm _), "]"] [],
  exacts ["[", expr tsub_le_iff_tsub_le.mp hi.1, ",", expr «expr $ »(hi.2.trans_lt, ennreal.add_lt_top.2 ⟨hfi', ennreal.coe_lt_top⟩).ne, "]"]
end

-- error in MeasureTheory.Integral.SetIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_sum_integral_Union
{ι : Type*}
[encodable ι]
{s : ι → set α}
{f : α → E}
(hm : ∀ i, measurable_set (s i))
(hd : pairwise «expr on »(disjoint, s))
(hfi : integrable_on f «expr⋃ , »((i), s i) μ) : has_sum (λ
 n, «expr∫ in , ∂ »((a), s n, f a, μ)) «expr∫ in , ∂ »((a), «expr⋃ , »((n), s n), f a, μ) :=
begin
  have [ident hfi'] [":", expr ∀ i, integrable_on f (s i) μ] [],
  from [expr λ i, hfi.mono_set (subset_Union _ _)],
  simp [] [] ["only"] ["[", expr has_sum, ",", "<-", expr integral_finset_bUnion _ (λ
    i _, hm i) (hd.set_pairwise _) (λ i _, hfi' i), "]"] [] [],
  rw [expr Union_eq_Union_finset] ["at", ident hfi, "⊢"],
  exact [expr tendsto_set_integral_of_monotone (λ
    t, t.measurable_set_bUnion (λ i _, hm i)) (λ t₁ t₂ h, bUnion_subset_bUnion_left h) hfi]
end

theorem integral_Union {ι : Type _} [Encodable ι] {s : ι → Set α} {f : α → E} (hm : ∀ i, MeasurableSet (s i))
  (hd : Pairwise (Disjoint on s)) (hfi : integrable_on f (⋃i, s i) μ) :
  (∫a in ⋃n, s n, f a ∂μ) = ∑'n, ∫a in s n, f a ∂μ :=
  (HasSum.tsum_eq (has_sum_integral_Union hm hd hfi)).symm

-- error in MeasureTheory.Integral.SetIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_sum_integral_Union_of_null_inter
{ι : Type*}
[encodable ι]
{s : ι → set α}
{f : α → E}
(hm : ∀ i, measurable_set (s i))
(hd : pairwise (λ i j, «expr = »(μ «expr ∩ »(s i, s j), 0)))
(hfi : integrable_on f «expr⋃ , »((i), s i) μ) : has_sum (λ
 n, «expr∫ in , ∂ »((a), s n, f a, μ)) «expr∫ in , ∂ »((a), «expr⋃ , »((n), s n), f a, μ) :=
begin
  rcases [expr exists_subordinate_pairwise_disjoint hm hd, "with", "⟨", ident t, ",", ident ht_sub, ",", ident ht_eq, ",", ident htm, ",", ident htd, "⟩"],
  have [ident htU_eq] [":", expr «expr =ᵐ[ ] »(«expr⋃ , »((i), s i), μ, «expr⋃ , »((i), t i))] [":=", expr eventually_eq.countable_Union ht_eq],
  simp [] [] ["only"] ["[", expr set_integral_congr_set_ae (ht_eq _), ",", expr set_integral_congr_set_ae htU_eq, ",", expr htU_eq, "]"] [] [],
  exact [expr has_sum_integral_Union htm htd (hfi.congr_set_ae htU_eq.symm)]
end

theorem integral_Union_of_null_inter {ι : Type _} [Encodable ι] {s : ι → Set α} {f : α → E}
  (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise fun i j => μ (s i ∩ s j) = 0) (hfi : integrable_on f (⋃i, s i) μ) :
  (∫a in ⋃n, s n, f a ∂μ) = ∑'n, ∫a in s n, f a ∂μ :=
  (HasSum.tsum_eq (has_sum_integral_Union_of_null_inter hm hd hfi)).symm

theorem set_integral_eq_zero_of_forall_eq_zero {f : α → E} (hf : Measurable f) (ht_eq : ∀ x _ : x ∈ t, f x = 0) :
  (∫x in t, f x ∂μ) = 0 :=
  by 
    refine' integral_eq_zero_of_ae _ 
    rw [eventually_eq, ae_restrict_iff (measurable_set_eq_fun hf measurable_zero)]
    refine' eventually_of_forall fun x hx => _ 
    rw [Pi.zero_apply]
    exact ht_eq x hx

private theorem set_integral_union_eq_left_of_disjoint {f : α → E} (hf : Measurable f) (hfi : integrable f μ)
  (hs : MeasurableSet s) (ht : MeasurableSet t) (ht_eq : ∀ x _ : x ∈ t, f x = 0) (hs_disj : Disjoint s t) :
  (∫x in s ∪ t, f x ∂μ) = ∫x in s, f x ∂μ :=
  by 
    rw [integral_union hs_disj hs ht hfi.integrable_on hfi.integrable_on,
      set_integral_eq_zero_of_forall_eq_zero hf ht_eq, add_zeroₓ]

theorem set_integral_union_eq_left {f : α → E} (hf : Measurable f) (hfi : integrable f μ) (hs : MeasurableSet s)
  (ht : MeasurableSet t) (ht_eq : ∀ x _ : x ∈ t, f x = 0) : (∫x in s ∪ t, f x ∂μ) = ∫x in s, f x ∂μ :=
  by 
    rw [←Set.union_diff_self, integral_union,
      set_integral_eq_zero_of_forall_eq_zero _ fun x hx => ht_eq x (diff_subset _ _ hx), add_zeroₓ]
    exacts[hf, disjoint_diff, hs, ht.diff hs, hfi.integrable_on, hfi.integrable_on]

-- error in MeasureTheory.Integral.SetIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem set_integral_neg_eq_set_integral_nonpos
[linear_order E]
[order_closed_topology E]
{f : α → E}
(hf : measurable f)
(hfi : integrable f μ) : «expr = »(«expr∫ in , ∂ »((x), {x | «expr < »(f x, 0)}, f x, μ), «expr∫ in , ∂ »((x), {x | «expr ≤ »(f x, 0)}, f x, μ)) :=
begin
  have [ident h_union] [":", expr «expr = »({x | «expr ≤ »(f x, 0)}, «expr ∪ »({x | «expr < »(f x, 0)}, {x | «expr = »(f x, 0)}))] [],
  by { ext [] [] [],
    simp_rw ["[", expr set.mem_union_eq, ",", expr set.mem_set_of_eq, "]"] [],
    exact [expr le_iff_lt_or_eq] },
  rw [expr h_union] [],
  exact [expr (set_integral_union_eq_left hf hfi (measurable_set_lt hf measurable_const) (measurable_set_eq_fun hf measurable_const) (λ
     x hx, hx)).symm]
end

theorem integral_norm_eq_pos_sub_neg {f : α → ℝ} (hf : Measurable f) (hfi : integrable f μ) :
  (∫x, ∥f x∥ ∂μ) = (∫x in { x | 0 ≤ f x }, f x ∂μ) - ∫x in { x | f x ≤ 0 }, f x ∂μ :=
  have h_meas : MeasurableSet { x | 0 ≤ f x } := measurable_set_le measurable_const hf 
  calc (∫x, ∥f x∥ ∂μ) = (∫x in { x | 0 ≤ f x }, ∥f x∥ ∂μ)+∫x in «expr ᶜ» { x | 0 ≤ f x }, ∥f x∥ ∂μ :=
    by 
      rw [←integral_add_compl h_meas hfi.norm]
    _ = (∫x in { x | 0 ≤ f x }, f x ∂μ)+∫x in «expr ᶜ» { x | 0 ≤ f x }, ∥f x∥ ∂μ :=
    by 
      congr 1
      refine' set_integral_congr h_meas fun x hx => _ 
      dsimp only 
      rw [Real.norm_eq_abs, abs_eq_self.mpr _]
      exact hx 
    _ = (∫x in { x | 0 ≤ f x }, f x ∂μ) - ∫x in «expr ᶜ» { x | 0 ≤ f x }, f x ∂μ :=
    by 
      congr 1
      rw [←integral_neg]
      refine' set_integral_congr h_meas.compl fun x hx => _ 
      dsimp only 
      rw [Real.norm_eq_abs, abs_eq_neg_self.mpr _]
      rw [Set.mem_compl_iff, Set.nmem_set_of_eq] at hx 
      linarith 
    _ = (∫x in { x | 0 ≤ f x }, f x ∂μ) - ∫x in { x | f x ≤ 0 }, f x ∂μ :=
    by 
      rw [←set_integral_neg_eq_set_integral_nonpos hf hfi]
      congr 
      ext1 x 
      simp 
    

theorem set_integral_const (c : E) : (∫x in s, c ∂μ) = (μ s).toReal • c :=
  by 
    rw [integral_const, measure.restrict_apply_univ]

@[simp]
theorem integral_indicator_const (e : E) ⦃s : Set α⦄ (s_meas : MeasurableSet s) :
  (∫a : α, s.indicator (fun x : α => e) a ∂μ) = (μ s).toReal • e :=
  by 
    rw [integral_indicator s_meas, ←set_integral_const]

theorem set_integral_indicator_const_Lp {p : ℝ≥0∞} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμt : μ t ≠ ∞)
  (x : E) : (∫a in s, indicator_const_Lp p ht hμt x a ∂μ) = (μ (t ∩ s)).toReal • x :=
  calc (∫a in s, indicator_const_Lp p ht hμt x a ∂μ) = ∫a in s, t.indicator (fun _ => x) a ∂μ :=
    by 
      rw [set_integral_congr_ae hs (indicator_const_Lp_coe_fn.mono fun x hx hxs => hx)]
    _ = (μ (t ∩ s)).toReal • x :=
    by 
      rw [integral_indicator_const _ ht, measure.restrict_apply ht]
    

theorem integral_indicator_const_Lp {p : ℝ≥0∞} (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (x : E) :
  (∫a, indicator_const_Lp p ht hμt x a ∂μ) = (μ t).toReal • x :=
  calc (∫a, indicator_const_Lp p ht hμt x a ∂μ) = ∫a in univ, indicator_const_Lp p ht hμt x a ∂μ :=
    by 
      rw [integral_univ]
    _ = (μ (t ∩ univ)).toReal • x := set_integral_indicator_const_Lp MeasurableSet.univ ht hμt x 
    _ = (μ t).toReal • x :=
    by 
      rw [inter_univ]
    

theorem set_integral_map {β} [MeasurableSpace β] {g : α → β} {f : β → E} {s : Set β} (hs : MeasurableSet s)
  (hf : AeMeasurable f (measure.map g μ)) (hg : Measurable g) :
  (∫y in s, f y ∂measure.map g μ) = ∫x in g ⁻¹' s, f (g x) ∂μ :=
  by 
    rw [measure.restrict_map hg hs, integral_map hg (hf.mono_measure _)]
    exact measure.map_mono g measure.restrict_le_self

theorem _root_.measurable_embedding.set_integral_map {β} {_ : MeasurableSpace β} {f : α → β}
  (hf : MeasurableEmbedding f) (g : β → E) (s : Set β) : (∫y in s, g y ∂measure.map f μ) = ∫x in f ⁻¹' s, g (f x) ∂μ :=
  by 
    rw [hf.restrict_map, hf.integral_map]

theorem _root_.closed_embedding.set_integral_map [TopologicalSpace α] [BorelSpace α] {β} [MeasurableSpace β]
  [TopologicalSpace β] [BorelSpace β] {g : α → β} {f : β → E} (s : Set β) (hg : ClosedEmbedding g) :
  (∫y in s, f y ∂measure.map g μ) = ∫x in g ⁻¹' s, f (g x) ∂μ :=
  hg.measurable_embedding.set_integral_map _ _

theorem measure_preserving.set_integral_preimage_emb {β} {_ : MeasurableSpace β} {f : α → β} {ν}
  (h₁ : measure_preserving f μ ν) (h₂ : MeasurableEmbedding f) (g : β → E) (s : Set β) :
  (∫x in f ⁻¹' s, g (f x) ∂μ) = ∫y in s, g y ∂ν :=
  (h₁.restrict_preimage_emb h₂ s).integral_comp h₂ _

theorem measure_preserving.set_integral_image_emb {β} {_ : MeasurableSpace β} {f : α → β} {ν}
  (h₁ : measure_preserving f μ ν) (h₂ : MeasurableEmbedding f) (g : β → E) (s : Set α) :
  (∫y in f '' s, g y ∂ν) = ∫x in s, g (f x) ∂μ :=
  Eq.symm$ (h₁.restrict_image_emb h₂ s).integral_comp h₂ _

theorem set_integral_map_equiv {β} [MeasurableSpace β] (e : α ≃ᵐ β) (f : β → E) (s : Set β) :
  (∫y in s, f y ∂measure.map e μ) = ∫x in e ⁻¹' s, f (e x) ∂μ :=
  e.measurable_embedding.set_integral_map f s

-- error in MeasureTheory.Integral.SetIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_set_integral_le_of_norm_le_const_ae
{C : exprℝ()}
(hs : «expr < »(μ s, «expr∞»()))
(hC : «expr∀ᵐ ∂ , »((x), μ.restrict s, «expr ≤ »(«expr∥ ∥»(f x), C))) : «expr ≤ »(«expr∥ ∥»(«expr∫ in , ∂ »((x), s, f x, μ)), «expr * »(C, (μ s).to_real)) :=
begin
  rw ["<-", expr measure.restrict_apply_univ] ["at", "*"],
  haveI [] [":", expr is_finite_measure (μ.restrict s)] [":=", expr ⟨«expr‹ ›»(_)⟩],
  exact [expr norm_integral_le_of_norm_le_const hC]
end

-- error in MeasureTheory.Integral.SetIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_set_integral_le_of_norm_le_const_ae'
{C : exprℝ()}
(hs : «expr < »(μ s, «expr∞»()))
(hC : «expr∀ᵐ ∂ , »((x), μ, «expr ∈ »(x, s) → «expr ≤ »(«expr∥ ∥»(f x), C)))
(hfm : ae_measurable f (μ.restrict s)) : «expr ≤ »(«expr∥ ∥»(«expr∫ in , ∂ »((x), s, f x, μ)), «expr * »(C, (μ s).to_real)) :=
begin
  apply [expr norm_set_integral_le_of_norm_le_const_ae hs],
  have [ident A] [":", expr «expr∀ᵐ ∂ , »((x : α), μ, «expr ∈ »(x, s) → «expr ≤ »(«expr∥ ∥»(ae_measurable.mk f hfm x), C))] [],
  { filter_upwards ["[", expr hC, ",", expr hfm.ae_mem_imp_eq_mk, "]"] [],
    assume [binders (a h1 h2 h3)],
    rw ["[", "<-", expr h2 h3, "]"] [],
    exact [expr h1 h3] },
  have [ident B] [":", expr measurable_set {x | «expr ≤ »(«expr∥ ∥»(hfm.mk f x), C)}] [":=", expr hfm.measurable_mk.norm measurable_set_Iic],
  filter_upwards ["[", expr hfm.ae_eq_mk, ",", expr (ae_restrict_iff B).2 A, "]"] [],
  assume [binders (a h1 h2)],
  rwa [expr h1] []
end

theorem norm_set_integral_le_of_norm_le_const_ae'' {C : ℝ} (hs : μ s < ∞) (hsm : MeasurableSet s)
  (hC : ∀ᵐx ∂μ, x ∈ s → ∥f x∥ ≤ C) : ∥∫x in s, f x ∂μ∥ ≤ C*(μ s).toReal :=
  norm_set_integral_le_of_norm_le_const_ae hs$
    by 
      rwa [ae_restrict_eq hsm, eventually_inf_principal]

theorem norm_set_integral_le_of_norm_le_const {C : ℝ} (hs : μ s < ∞) (hC : ∀ x _ : x ∈ s, ∥f x∥ ≤ C)
  (hfm : AeMeasurable f (μ.restrict s)) : ∥∫x in s, f x ∂μ∥ ≤ C*(μ s).toReal :=
  norm_set_integral_le_of_norm_le_const_ae' hs (eventually_of_forall hC) hfm

theorem norm_set_integral_le_of_norm_le_const' {C : ℝ} (hs : μ s < ∞) (hsm : MeasurableSet s)
  (hC : ∀ x _ : x ∈ s, ∥f x∥ ≤ C) : ∥∫x in s, f x ∂μ∥ ≤ C*(μ s).toReal :=
  norm_set_integral_le_of_norm_le_const_ae'' hs hsm$ eventually_of_forall hC

theorem set_integral_eq_zero_iff_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f) (hfi : integrable_on f s μ) :
  (∫x in s, f x ∂μ) = 0 ↔ f =ᵐ[μ.restrict s] 0 :=
  integral_eq_zero_iff_of_nonneg_ae hf hfi

theorem set_integral_pos_iff_support_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f) (hfi : integrable_on f s μ) :
  (0 < ∫x in s, f x ∂μ) ↔ 0 < μ (support f ∩ s) :=
  by 
    rw [integral_pos_iff_support_of_nonneg_ae hf hfi, measure.restrict_apply₀]
    rw [support_eq_preimage]
    exact hfi.ae_measurable.null_measurable (measurable_set_singleton 0).Compl

theorem set_integral_trim {α} {m m0 : MeasurableSpace α} {μ : Measureₓ α} (hm : m ≤ m0) {f : α → E}
  (hf_meas : @Measurable _ _ m _ f) {s : Set α} (hs : measurable_set[m] s) :
  (∫x in s, f x ∂μ) = ∫x in s, f x ∂μ.trim hm :=
  by 
    rwa [integral_trim hm hf_meas, restrict_trim hm μ]

end NormedGroup

section Mono

variable {μ : Measureₓ α} {f g : α → ℝ} {s t : Set α} (hf : integrable_on f s μ) (hg : integrable_on g s μ)

theorem set_integral_mono_ae_restrict (h : f ≤ᵐ[μ.restrict s] g) : (∫a in s, f a ∂μ) ≤ ∫a in s, g a ∂μ :=
  integral_mono_ae hf hg h

theorem set_integral_mono_ae (h : f ≤ᵐ[μ] g) : (∫a in s, f a ∂μ) ≤ ∫a in s, g a ∂μ :=
  set_integral_mono_ae_restrict hf hg (ae_restrict_of_ae h)

theorem set_integral_mono_on (hs : MeasurableSet s) (h : ∀ x _ : x ∈ s, f x ≤ g x) :
  (∫a in s, f a ∂μ) ≤ ∫a in s, g a ∂μ :=
  set_integral_mono_ae_restrict hf hg
    (by 
      simp [hs, eventually_le, eventually_inf_principal, ae_of_all _ h])

include hf hg

theorem set_integral_mono_on_ae (hs : MeasurableSet s) (h : ∀ᵐx ∂μ, x ∈ s → f x ≤ g x) :
  (∫a in s, f a ∂μ) ≤ ∫a in s, g a ∂μ :=
  by 
    refine' set_integral_mono_ae_restrict hf hg _ 
    rwa [eventually_le, ae_restrict_iff' hs]

omit hf hg

theorem set_integral_mono (h : f ≤ g) : (∫a in s, f a ∂μ) ≤ ∫a in s, g a ∂μ :=
  integral_mono hf hg h

theorem set_integral_mono_set (hfi : integrable f μ) (hf : 0 ≤ᵐ[μ] f) (hst : s ≤ᵐ[μ] t) :
  (∫x in s, f x ∂μ) ≤ ∫x in t, f x ∂μ :=
  by 
    repeat' 
      rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hf) (hfi.1.mono_measure measure.restrict_le_self)]
    rw
      [Ennreal.to_real_le_to_real
        (ne_of_ltₓ$ (has_finite_integral_iff_of_real (ae_restrict_of_ae hf)).mp hfi.integrable_on.2)
        (ne_of_ltₓ$ (has_finite_integral_iff_of_real (ae_restrict_of_ae hf)).mp hfi.integrable_on.2)]
    exact lintegral_mono_set' hst

end Mono

section Nonneg

variable {μ : Measureₓ α} {f : α → ℝ} {s : Set α}

theorem set_integral_nonneg_of_ae_restrict (hf : 0 ≤ᵐ[μ.restrict s] f) : 0 ≤ ∫a in s, f a ∂μ :=
  integral_nonneg_of_ae hf

theorem set_integral_nonneg_of_ae (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ∫a in s, f a ∂μ :=
  set_integral_nonneg_of_ae_restrict (ae_restrict_of_ae hf)

theorem set_integral_nonneg (hs : MeasurableSet s) (hf : ∀ a, a ∈ s → 0 ≤ f a) : 0 ≤ ∫a in s, f a ∂μ :=
  set_integral_nonneg_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))

theorem set_integral_nonneg_ae (hs : MeasurableSet s) (hf : ∀ᵐa ∂μ, a ∈ s → 0 ≤ f a) : 0 ≤ ∫a in s, f a ∂μ :=
  set_integral_nonneg_of_ae_restrict$
    by 
      rwa [eventually_le, ae_restrict_iff' hs]

theorem set_integral_le_nonneg {s : Set α} (hs : MeasurableSet s) (hf : Measurable f) (hfi : integrable f μ) :
  (∫x in s, f x ∂μ) ≤ ∫x in { y | 0 ≤ f y }, f x ∂μ :=
  by 
    rw [←integral_indicator hs, ←integral_indicator (measurable_set_le measurable_const hf)]
    exact
      integral_mono (hfi.indicator hs) (hfi.indicator (measurable_set_le measurable_const hf))
        (indicator_le_indicator_nonneg s f)

theorem set_integral_nonpos_of_ae_restrict (hf : f ≤ᵐ[μ.restrict s] 0) : (∫a in s, f a ∂μ) ≤ 0 :=
  integral_nonpos_of_ae hf

theorem set_integral_nonpos_of_ae (hf : f ≤ᵐ[μ] 0) : (∫a in s, f a ∂μ) ≤ 0 :=
  set_integral_nonpos_of_ae_restrict (ae_restrict_of_ae hf)

theorem set_integral_nonpos (hs : MeasurableSet s) (hf : ∀ a, a ∈ s → f a ≤ 0) : (∫a in s, f a ∂μ) ≤ 0 :=
  set_integral_nonpos_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))

theorem set_integral_nonpos_ae (hs : MeasurableSet s) (hf : ∀ᵐa ∂μ, a ∈ s → f a ≤ 0) : (∫a in s, f a ∂μ) ≤ 0 :=
  set_integral_nonpos_of_ae_restrict$
    by 
      rwa [eventually_le, ae_restrict_iff' hs]

theorem set_integral_nonpos_le {s : Set α} (hs : MeasurableSet s) {f : α → ℝ} (hf : Measurable f)
  (hfi : integrable f μ) : (∫x in { y | f y ≤ 0 }, f x ∂μ) ≤ ∫x in s, f x ∂μ :=
  by 
    rw [←integral_indicator hs, ←integral_indicator (measurable_set_le hf measurable_const)]
    exact
      integral_mono (hfi.indicator (measurable_set_le hf measurable_const)) (hfi.indicator hs)
        (indicator_nonpos_le_indicator s f)

end Nonneg

section TendstoMono

variable {μ : Measureₓ α} [MeasurableSpace E] [NormedGroup E] [BorelSpace E] [CompleteSpace E] [NormedSpace ℝ E]
  [second_countable_topology E] {s : ℕ → Set α} {f : α → E}

-- error in MeasureTheory.Integral.SetIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem _root_.antitone.tendsto_set_integral
(hsm : ∀ i, measurable_set (s i))
(h_anti : antitone s)
(hfi : integrable_on f (s 0) μ) : tendsto (λ
 i, «expr∫ in , ∂ »((a), s i, f a, μ)) at_top (expr𝓝() «expr∫ in , ∂ »((a), «expr⋂ , »((n), s n), f a, μ)) :=
begin
  let [ident bound] [":", expr α → exprℝ()] [":=", expr indicator (s 0) (λ a, «expr∥ ∥»(f a))],
  have [ident h_int_eq] [":", expr «expr = »(λ
    i, «expr∫ in , ∂ »((a), s i, f a, μ), λ i, «expr∫ , ∂ »((a), (s i).indicator f a, μ))] [],
  from [expr funext (λ i, (integral_indicator (hsm i)).symm)],
  rw [expr h_int_eq] [],
  rw ["<-", expr integral_indicator (measurable_set.Inter hsm)] [],
  refine [expr tendsto_integral_of_dominated_convergence bound _ _ _ _],
  { intro [ident n],
    rw [expr ae_measurable_indicator_iff (hsm n)] [],
    exact [expr (integrable_on.mono_set hfi (h_anti (zero_le n))).1] },
  { rw [expr integrable_indicator_iff (hsm 0)] [],
    exact [expr hfi.norm] },
  { simp_rw [expr norm_indicator_eq_indicator_norm] [],
    refine [expr λ n, eventually_of_forall (λ x, _)],
    exact [expr indicator_le_indicator_of_subset (h_anti (zero_le n)) (λ a, norm_nonneg _) _] },
  { filter_upwards ["[", "]"] [expr λ a, le_trans (h_anti.tendsto_indicator _ _ _) (pure_le_nhds _)] }
end

end TendstoMono

/-! ### Continuity of the set integral

We prove that for any set `s`, the function `λ f : α →₁[μ] E, ∫ x in s, f x ∂μ` is continuous. -/


section ContinuousSetIntegral

variable [NormedGroup E] [MeasurableSpace E] [second_countable_topology E] [BorelSpace E] {𝕜 : Type _} [IsROrC 𝕜]
  [NormedGroup F] [MeasurableSpace F] [second_countable_topology F] [BorelSpace F] [NormedSpace 𝕜 F] {p : ℝ≥0∞}
  {μ : Measureₓ α}

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.mem_ℒp f).restrict s).to_Lp f`. This map is additive. -/
theorem Lp_to_Lp_restrict_add (f g : Lp E p μ) (s : Set α) :
  ((Lp.mem_ℒp (f+g)).restrict s).toLp («expr⇑ » (f+g)) =
    ((Lp.mem_ℒp f).restrict s).toLp f+((Lp.mem_ℒp g).restrict s).toLp g :=
  by 
    ext1 
    refine' (ae_restrict_of_ae (Lp.coe_fn_add f g)).mp _ 
    refine'
      (Lp.coe_fn_add (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s)) (mem_ℒp.to_Lp g ((Lp.mem_ℒp g).restrict s))).mp _ 
    refine' (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _ 
    refine' (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp g).restrict s)).mp _ 
    refine' (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (f+g)).restrict s)).mono fun x hx1 hx2 hx3 hx4 hx5 => _ 
    rw [hx4, hx1, Pi.add_apply, hx2, hx3, hx5, Pi.add_apply]

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.mem_ℒp f).restrict s).to_Lp f`. This map commutes with scalar multiplication. -/
theorem Lp_to_Lp_restrict_smul (c : 𝕜) (f : Lp F p μ) (s : Set α) :
  ((Lp.mem_ℒp (c • f)).restrict s).toLp («expr⇑ » (c • f)) = c • ((Lp.mem_ℒp f).restrict s).toLp f :=
  by 
    ext1 
    refine' (ae_restrict_of_ae (Lp.coe_fn_smul c f)).mp _ 
    refine' (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _ 
    refine' (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (c • f)).restrict s)).mp _ 
    refine' (Lp.coe_fn_smul c (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s))).mono fun x hx1 hx2 hx3 hx4 => _ 
    rw [hx2, hx1, Pi.smul_apply, hx3, hx4, Pi.smul_apply]

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.mem_ℒp f).restrict s).to_Lp f`. This map is non-expansive. -/
theorem norm_Lp_to_Lp_restrict_le (s : Set α) (f : Lp E p μ) : ∥((Lp.mem_ℒp f).restrict s).toLp f∥ ≤ ∥f∥ :=
  by 
    rw [Lp.norm_def, Lp.norm_def, Ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _)]
    refine' (le_of_eqₓ _).trans (snorm_mono_measure _ measure.restrict_le_self)
    ·
      exact s 
    exact snorm_congr_ae (mem_ℒp.coe_fn_to_Lp _)

variable (α F 𝕜)

/-- Continuous linear map sending a function of `Lp F p μ` to the same function in
`Lp F p (μ.restrict s)`. -/
def Lp_to_Lp_restrict_clm (μ : Measureₓ α) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (s : Set α) :
  Lp F p μ →L[𝕜] Lp F p (μ.restrict s) :=
  @LinearMap.mkContinuous 𝕜 𝕜 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _ _ (RingHom.id 𝕜)
    ⟨fun f => mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s), fun f g => Lp_to_Lp_restrict_add f g s,
      fun c f => Lp_to_Lp_restrict_smul c f s⟩
    1
    (by 
      intro f 
      rw [one_mulₓ]
      exact norm_Lp_to_Lp_restrict_le s f)

variable {α F 𝕜}

variable (𝕜)

theorem Lp_to_Lp_restrict_clm_coe_fn [hp : Fact (1 ≤ p)] (s : Set α) (f : Lp F p μ) :
  Lp_to_Lp_restrict_clm α F 𝕜 μ p s f =ᵐ[μ.restrict s] f :=
  mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)

variable {𝕜}

-- error in MeasureTheory.Integral.SetIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[continuity #[]]
theorem continuous_set_integral
[normed_space exprℝ() E]
[complete_space E]
(s : set α) : continuous (λ f : «expr →₁[ ] »(α, μ, E), «expr∫ in , ∂ »((x), s, f x, μ)) :=
begin
  haveI [] [":", expr fact «expr ≤ »((1 : «exprℝ≥0∞»()), 1)] [":=", expr ⟨le_rfl⟩],
  have [ident h_comp] [":", expr «expr = »(λ
    f : «expr →₁[ ] »(α, μ, E), «expr∫ in , ∂ »((x), s, f x, μ), «expr ∘ »(integral (μ.restrict s), λ
     f, Lp_to_Lp_restrict_clm α E exprℝ() μ 1 s f))] [],
  { ext1 [] [ident f],
    rw ["[", expr function.comp_apply, ",", expr integral_congr_ae (Lp_to_Lp_restrict_clm_coe_fn exprℝ() s f), "]"] [] },
  rw [expr h_comp] [],
  exact [expr continuous_integral.comp (Lp_to_Lp_restrict_clm α E exprℝ() μ 1 s).continuous]
end

end ContinuousSetIntegral

end MeasureTheory

open MeasureTheory Asymptotics Metric

variable {ι : Type _} [MeasurableSpace E] [NormedGroup E]

-- error in MeasureTheory.Integral.SetIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Fundamental theorem of calculus for set integrals: if `μ` is a measure that is finite at a
filter `l` and `f` is a measurable function that has a finite limit `b` at `l ⊓ μ.ae`, then `∫ x in
s i, f x ∂μ = μ (s i) • b + o(μ (s i))` at a filter `li` provided that `s i` tends to `l.lift'
powerset` along `li`. Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in the
actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
theorem filter.tendsto.integral_sub_linear_is_o_ae
[normed_space exprℝ() E]
[second_countable_topology E]
[complete_space E]
[borel_space E]
{μ : measure α}
{l : filter α}
[l.is_measurably_generated]
{f : α → E}
{b : E}
(h : tendsto f «expr ⊓ »(l, μ.ae) (expr𝓝() b))
(hfm : measurable_at_filter f l μ)
(hμ : μ.finite_at_filter l)
{s : ι → set α}
{li : filter ι}
(hs : tendsto s li (l.lift' powerset))
(m : ι → exprℝ() := λ i, (μ (s i)).to_real)
(hsμ : «expr =ᶠ[ ] »(λ
  i, (μ (s i)).to_real, li, m) . tactic.interactive.refl) : is_o (λ
 i, «expr - »(«expr∫ in , ∂ »((x), s i, f x, μ), «expr • »(m i, b))) m li :=
begin
  suffices [] [":", expr is_o (λ
    s, «expr - »(«expr∫ in , ∂ »((x), s, f x, μ), «expr • »((μ s).to_real, b))) (λ
    s, (μ s).to_real) (l.lift' powerset)],
  from [expr (this.comp_tendsto hs).congr' «expr $ »(hsμ.mono, λ a ha, «expr ▸ »(ha, rfl)) hsμ],
  refine [expr is_o_iff.2 (λ ε ε₀, _)],
  have [] [":", expr «expr∀ᶠ in , »((s), l.lift' powerset, «expr∀ᶠ in , »((x), μ.ae, «expr ∈ »(x, s) → «expr ∈ »(f x, closed_ball b ε)))] [":=", expr eventually_lift'_powerset_eventually.2 «expr $ »(h.eventually, closed_ball_mem_nhds _ ε₀)],
  filter_upwards ["[", expr hμ.eventually, ",", expr (hμ.integrable_at_filter_of_tendsto_ae hfm h).eventually, ",", expr hfm.eventually, ",", expr this, "]"] [],
  simp [] [] ["only"] ["[", expr mem_closed_ball, ",", expr dist_eq_norm, "]"] [] [],
  intros [ident s, ident hμs, ident h_integrable, ident hfm, ident h_norm],
  rw ["[", "<-", expr set_integral_const, ",", "<-", expr integral_sub h_integrable «expr $ »(integrable_on_const.2, or.inr hμs), ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg ennreal.to_real_nonneg, "]"] [],
  exact [expr norm_set_integral_le_of_norm_le_const_ae' hμs h_norm (hfm.sub ae_measurable_const)]
end

-- error in MeasureTheory.Integral.SetIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Fundamental theorem of calculus for set integrals, `nhds_within` version: if `μ` is a locally
finite measure and `f` is an almost everywhere measurable function that is continuous at a point `a`
within a measurable set `t`, then `∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at a filter `li`
provided that `s i` tends to `(𝓝[t] a).lift' powerset` along `li`.  Since `μ (s i)` is an `ℝ≥0∞`
number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
theorem continuous_within_at.integral_sub_linear_is_o_ae
[topological_space α]
[opens_measurable_space α]
[normed_space exprℝ() E]
[second_countable_topology E]
[complete_space E]
[borel_space E]
{μ : measure α}
[is_locally_finite_measure μ]
{a : α}
{t : set α}
{f : α → E}
(ha : continuous_within_at f t a)
(ht : measurable_set t)
(hfm : measurable_at_filter f «expr𝓝[ ] »(t, a) μ)
{s : ι → set α}
{li : filter ι}
(hs : tendsto s li («expr𝓝[ ] »(t, a).lift' powerset))
(m : ι → exprℝ() := λ i, (μ (s i)).to_real)
(hsμ : «expr =ᶠ[ ] »(λ
  i, (μ (s i)).to_real, li, m) . tactic.interactive.refl) : is_o (λ
 i, «expr - »(«expr∫ in , ∂ »((x), s i, f x, μ), «expr • »(m i, f a))) m li :=
by haveI [] [":", expr «expr𝓝[ ] »(t, a).is_measurably_generated] [":=", expr ht.nhds_within_is_measurably_generated _]; exact [expr (ha.mono_left inf_le_left).integral_sub_linear_is_o_ae hfm (μ.finite_at_nhds_within a t) hs m hsμ]

/-- Fundamental theorem of calculus for set integrals, `nhds` version: if `μ` is a locally finite
measure and `f` is an almost everywhere measurable function that is continuous at a point `a`, then
`∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at `li` provided that `s` tends to `(𝓝 a).lift'
powerset` along `li.  Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in the
actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
theorem ContinuousAt.integral_sub_linear_is_o_ae [TopologicalSpace α] [OpensMeasurableSpace α] [NormedSpace ℝ E]
  [second_countable_topology E] [CompleteSpace E] [BorelSpace E] {μ : Measureₓ α} [is_locally_finite_measure μ] {a : α}
  {f : α → E} (ha : ContinuousAt f a) (hfm : MeasurableAtFilter f (𝓝 a) μ) {s : ι → Set α} {li : Filter ι}
  (hs : tendsto s li ((𝓝 a).lift' powerset)) (m : ι → ℝ := fun i => (μ (s i)).toReal)
  (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m :=  by 
    runTac 
      tactic.interactive.refl) :
  is_o (fun i => (∫x in s i, f x ∂μ) - m i • f a) m li :=
  (ha.mono_left inf_le_left).integral_sub_linear_is_o_ae hfm (μ.finite_at_nhds a) hs m hsμ

/-- If a function is continuous on an open set `s`, then it is measurable at the filter `𝓝 x` for
  all `x ∈ s`. -/
theorem ContinuousOn.measurable_at_filter [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSpace β]
  [TopologicalSpace β] [BorelSpace β] {f : α → β} {s : Set α} {μ : Measureₓ α} (hs : IsOpen s) (hf : ContinuousOn f s) :
  ∀ x _ : x ∈ s, MeasurableAtFilter f (𝓝 x) μ :=
  fun x hx => ⟨s, IsOpen.mem_nhds hs hx, hf.ae_measurable hs.measurable_set⟩

theorem ContinuousAt.measurable_at_filter [TopologicalSpace α] [OpensMeasurableSpace α] [BorelSpace E] {f : α → E}
  {s : Set α} {μ : Measureₓ α} (hs : IsOpen s) (hf : ∀ x _ : x ∈ s, ContinuousAt f x) :
  ∀ x _ : x ∈ s, MeasurableAtFilter f (𝓝 x) μ :=
  ContinuousOn.measurable_at_filter hs$ ContinuousAt.continuous_on hf

theorem Continuous.measurable_at_filter [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSpace β]
  [TopologicalSpace β] [BorelSpace β] {f : α → β} (hf : Continuous f) (μ : Measureₓ α) (l : Filter α) :
  MeasurableAtFilter f l μ :=
  hf.measurable.measurable_at_filter

/-- If a function is continuous on a measurable set `s`, then it is measurable at the filter
  `𝓝[s] x` for all `x`. -/
theorem ContinuousOn.measurable_at_filter_nhds_within {α β : Type _} [MeasurableSpace α] [TopologicalSpace α]
  [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β] [BorelSpace β] {f : α → β} {s : Set α}
  {μ : Measureₓ α} (hf : ContinuousOn f s) (hs : MeasurableSet s) (x : α) : MeasurableAtFilter f (𝓝[s] x) μ :=
  ⟨s, self_mem_nhds_within, hf.ae_measurable hs⟩

/-- Fundamental theorem of calculus for set integrals, `nhds_within` version: if `μ` is a locally
finite measure, `f` is continuous on a measurable set `t`, and `a ∈ t`, then `∫ x in (s i), f x ∂μ =
μ (s i) • f a + o(μ (s i))` at `li` provided that `s i` tends to `(𝓝[t] a).lift' powerset` along
`li`.  Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).to_real` in the actual statement.

Often there is a good formula for `(μ (s i)).to_real`, so the formalization can take an optional
argument `m` with this formula and a proof `of `(λ i, (μ (s i)).to_real) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).to_real` is used in the output. -/
theorem ContinuousOn.integral_sub_linear_is_o_ae [TopologicalSpace α] [OpensMeasurableSpace α] [NormedSpace ℝ E]
  [second_countable_topology E] [CompleteSpace E] [BorelSpace E] {μ : Measureₓ α} [is_locally_finite_measure μ] {a : α}
  {t : Set α} {f : α → E} (hft : ContinuousOn f t) (ha : a ∈ t) (ht : MeasurableSet t) {s : ι → Set α} {li : Filter ι}
  (hs : tendsto s li ((𝓝[t] a).lift' powerset)) (m : ι → ℝ := fun i => (μ (s i)).toReal)
  (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m :=  by 
    runTac 
      tactic.interactive.refl) :
  is_o (fun i => (∫x in s i, f x ∂μ) - m i • f a) m li :=
  (hft a ha).integral_sub_linear_is_o_ae ht ⟨t, self_mem_nhds_within, hft.ae_measurable ht⟩ hs m hsμ

section 

/-! ### Continuous linear maps composed with integration

The goal of this section is to prove that integration commutes with continuous linear maps.
This holds for simple functions. The general result follows from the continuity of all involved
operations on the space `L¹`. Note that composition by a continuous linear map on `L¹` is not just
the composition, as we are dealing with classes of functions, but it has already been defined
as `continuous_linear_map.comp_Lp`. We take advantage of this construction here.
-/


open_locale ComplexConjugate

variable {μ : Measureₓ α} {𝕜 : Type _} [IsROrC 𝕜] [NormedSpace 𝕜 E] [NormedGroup F] [NormedSpace 𝕜 F] {p : Ennreal}

attribute [local instance] fact_one_le_one_ennreal

namespace ContinuousLinearMap

variable [MeasurableSpace F] [BorelSpace F]

variable [second_countable_topology F] [CompleteSpace F] [BorelSpace E] [second_countable_topology E] [NormedSpace ℝ F]

theorem integral_comp_Lp (L : E →L[𝕜] F) (φ : Lp E p μ) : (∫a, (L.comp_Lp φ) a ∂μ) = ∫a, L (φ a) ∂μ :=
  integral_congr_ae$ coe_fn_comp_Lp _ _

theorem set_integral_comp_Lp (L : E →L[𝕜] F) (φ : Lp E p μ) {s : Set α} (hs : MeasurableSet s) :
  (∫a in s, (L.comp_Lp φ) a ∂μ) = ∫a in s, L (φ a) ∂μ :=
  set_integral_congr_ae hs ((L.coe_fn_comp_Lp φ).mono fun x hx hx2 => hx)

theorem continuous_integral_comp_L1 (L : E →L[𝕜] F) : Continuous fun φ : α →₁[μ] E => ∫a : α, L (φ a) ∂μ :=
  by 
    rw [←funext L.integral_comp_Lp]
    exact continuous_integral.comp (L.comp_LpL 1 μ).Continuous

variable [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [IsScalarTower ℝ 𝕜 F]

theorem integral_comp_comm (L : E →L[𝕜] F) {φ : α → E} (φ_int : integrable φ μ) : (∫a, L (φ a) ∂μ) = L (∫a, φ a ∂μ) :=
  by 
    apply integrable.induction fun φ => (∫a, L (φ a) ∂μ) = L (∫a, φ a ∂μ)
    ·
      intro e s s_meas s_finite 
      rw [integral_indicator_const e s_meas, ←@smul_one_smul E ℝ 𝕜 _ _ _ _ _ (μ s).toReal e,
        ContinuousLinearMap.map_smul, @smul_one_smul F ℝ 𝕜 _ _ _ _ _ (μ s).toReal (L e),
        ←integral_indicator_const (L e) s_meas]
      congr 1 with a 
      rw [Set.indicator_comp_of_zero L.map_zero]
    ·
      intro f g H f_int g_int hf hg 
      simp [L.map_add, integral_add f_int g_int, integral_add (L.integrable_comp f_int) (L.integrable_comp g_int), hf,
        hg]
    ·
      exact is_closed_eq L.continuous_integral_comp_L1 (L.continuous.comp continuous_integral)
    ·
      intro f g hfg f_int hf 
      convert hf using 1 <;> clear hf
      ·
        exact integral_congr_ae (hfg.fun_comp L).symm
      ·
        rw [integral_congr_ae hfg.symm]
    all_goals 
      assumption

theorem integral_apply {H : Type _} [NormedGroup H] [NormedSpace 𝕜 H] [second_countable_topology$ H →L[𝕜] E]
  {φ : α → H →L[𝕜] E} (φ_int : integrable φ μ) (v : H) : (∫a, φ a ∂μ) v = ∫a, φ a v ∂μ :=
  ((ContinuousLinearMap.apply 𝕜 E v).integral_comp_comm φ_int).symm

-- error in MeasureTheory.Integral.SetIntegral: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integral_comp_comm'
(L : «expr →L[ ] »(E, 𝕜, F))
{K}
(hL : antilipschitz_with K L)
(φ : α → E) : «expr = »(«expr∫ , ∂ »((a), L (φ a), μ), L «expr∫ , ∂ »((a), φ a, μ)) :=
begin
  by_cases [expr h, ":", expr integrable φ μ],
  { exact [expr integral_comp_comm L h] },
  have [] [":", expr «expr¬ »(integrable «expr ∘ »(L, φ) μ)] [],
  by rwa [expr lipschitz_with.integrable_comp_iff_of_antilipschitz L.lipschitz hL L.map_zero] [],
  simp [] [] [] ["[", expr integral_undef, ",", expr h, ",", expr this, "]"] [] []
end

theorem integral_comp_L1_comm (L : E →L[𝕜] F) (φ : α →₁[μ] E) : (∫a, L (φ a) ∂μ) = L (∫a, φ a ∂μ) :=
  L.integral_comp_comm (L1.integrable_coe_fn φ)

end ContinuousLinearMap

namespace LinearIsometry

variable [MeasurableSpace F] [BorelSpace F] [second_countable_topology F] [CompleteSpace F] [NormedSpace ℝ F]
  [IsScalarTower ℝ 𝕜 F] [BorelSpace E] [second_countable_topology E] [CompleteSpace E] [NormedSpace ℝ E]
  [IsScalarTower ℝ 𝕜 E]

theorem integral_comp_comm (L : E →ₗᵢ[𝕜] F) (φ : α → E) : (∫a, L (φ a) ∂μ) = L (∫a, φ a ∂μ) :=
  L.to_continuous_linear_map.integral_comp_comm' L.antilipschitz _

end LinearIsometry

variable [BorelSpace E] [second_countable_topology E] [CompleteSpace E] [NormedSpace ℝ E] [MeasurableSpace F]
  [BorelSpace F] [second_countable_topology F] [CompleteSpace F] [NormedSpace ℝ F]

@[normCast]
theorem integral_of_real {f : α → ℝ} : (∫a, (f a : 𝕜) ∂μ) = «expr↑ » (∫a, f a ∂μ) :=
  (@IsROrC.ofRealLi 𝕜 _).integral_comp_comm f

theorem integral_re {f : α → 𝕜} (hf : integrable f μ) : (∫a, IsROrC.re (f a) ∂μ) = IsROrC.re (∫a, f a ∂μ) :=
  (@IsROrC.reClm 𝕜 _).integral_comp_comm hf

theorem integral_im {f : α → 𝕜} (hf : integrable f μ) : (∫a, IsROrC.im (f a) ∂μ) = IsROrC.im (∫a, f a ∂μ) :=
  (@IsROrC.imClm 𝕜 _).integral_comp_comm hf

theorem integral_conj {f : α → 𝕜} : (∫a, conj (f a) ∂μ) = conj (∫a, f a ∂μ) :=
  (@IsROrC.conjLie 𝕜 _).toLinearIsometry.integral_comp_comm f

theorem integral_coe_re_add_coe_im {f : α → 𝕜} (hf : integrable f μ) :
  ((∫x, (IsROrC.re (f x) : 𝕜) ∂μ)+(∫x, IsROrC.im (f x) ∂μ)*IsROrC.i) = ∫x, f x ∂μ :=
  by 
    rw [mul_commₓ, ←smul_eq_mul, ←integral_smul, ←integral_add]
    ·
      congr 
      ext1 x 
      rw [smul_eq_mul, mul_commₓ, IsROrC.re_add_im]
    ·
      exact hf.re.of_real
    ·
      exact hf.im.of_real.smul IsROrC.i

theorem integral_re_add_im {f : α → 𝕜} (hf : integrable f μ) :
  (((∫x, IsROrC.re (f x) ∂μ : ℝ) : 𝕜)+(∫x, IsROrC.im (f x) ∂μ : ℝ)*IsROrC.i) = ∫x, f x ∂μ :=
  by 
    rw [←integral_of_real, ←integral_of_real, integral_coe_re_add_coe_im hf]

theorem set_integral_re_add_im {f : α → 𝕜} {i : Set α} (hf : integrable_on f i μ) :
  (((∫x in i, IsROrC.re (f x) ∂μ : ℝ) : 𝕜)+(∫x in i, IsROrC.im (f x) ∂μ : ℝ)*IsROrC.i) = ∫x in i, f x ∂μ :=
  integral_re_add_im hf

theorem fst_integral {f : α → E × F} (hf : integrable f μ) : (∫x, f x ∂μ).1 = ∫x, (f x).1 ∂μ :=
  ((ContinuousLinearMap.fst ℝ E F).integral_comp_comm hf).symm

theorem snd_integral {f : α → E × F} (hf : integrable f μ) : (∫x, f x ∂μ).2 = ∫x, (f x).2 ∂μ :=
  ((ContinuousLinearMap.snd ℝ E F).integral_comp_comm hf).symm

theorem integral_pair {f : α → E} {g : α → F} (hf : integrable f μ) (hg : integrable g μ) :
  (∫x, (f x, g x) ∂μ) = (∫x, f x ∂μ, ∫x, g x ∂μ) :=
  have  := hf.prod_mk hg 
  Prod.extₓ (fst_integral this) (snd_integral this)

theorem integral_smul_const {𝕜 : Type _} [IsROrC 𝕜] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E] [MeasurableSpace 𝕜]
  [BorelSpace 𝕜] (f : α → 𝕜) (c : E) : (∫x, f x • c ∂μ) = (∫x, f x ∂μ) • c :=
  by 
    byCases' hf : integrable f μ
    ·
      exact ((1 : 𝕜 →L[𝕜] 𝕜).smulRight c).integral_comp_comm hf
    ·
      byCases' hc : c = 0
      ·
        simp only [hc, integral_zero, smul_zero]
      rw [integral_undef hf, integral_undef, zero_smul]
      simpRw [integrable_smul_const hc, hf, not_false_iff]

section Inner

variable {E' : Type _} [InnerProductSpace 𝕜 E'] [MeasurableSpace E'] [BorelSpace E'] [second_countable_topology E']
  [CompleteSpace E'] [NormedSpace ℝ E'] [IsScalarTower ℝ 𝕜 E']

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E' _ x y

theorem integral_inner {f : α → E'} (hf : integrable f μ) (c : E') : (∫x, ⟪c, f x⟫ ∂μ) = ⟪c, ∫x, f x ∂μ⟫ :=
  ((@innerRight 𝕜 E' _ _ c).restrictScalars ℝ).integral_comp_comm hf

theorem integral_eq_zero_of_forall_integral_inner_eq_zero (f : α → E') (hf : integrable f μ)
  (hf_int : ∀ c : E', (∫x, ⟪c, f x⟫ ∂μ) = 0) : (∫x, f x ∂μ) = 0 :=
  by 
    specialize hf_int (∫x, f x ∂μ)
    rwa [integral_inner hf, inner_self_eq_zero] at hf_int

end Inner

end 

