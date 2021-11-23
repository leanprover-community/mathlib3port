import Mathbin.MeasureTheory.Constructions.BorelSpace

/-!
# Measurability criterion for ennreal-valued functions

Consider a function `f : α → ℝ≥0∞`. If the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p` and `q` are finite numbers satisfying
`p < q`, then `f` is almost-everywhere measurable. This is proved in
`ennreal.ae_measurable_of_exist_almost_disjoint_supersets`, and deduced from an analogous statement
for any target space which is a complete linear dense order, called
`measure_theory.ae_measurable_of_exist_almost_disjoint_supersets`.

Note that it should be enough to assume that the space is a conditionally complete linear order,
but the proof would be more painful. Since our only use for now is for `ℝ≥0∞`, we keep it as simple
as possible.
-/


open MeasureTheory Set TopologicalSpace

open_locale Classical Ennreal Nnreal

-- error in MeasureTheory.Function.AeMeasurableOrder: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function `f : α → β` is such that the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p < q`, then `f` is almost-everywhere
measurable. It is even enough to have this for `p` and `q` in a countable dense set. -/
theorem measure_theory.ae_measurable_of_exist_almost_disjoint_supersets
{α : Type*}
{m : measurable_space α}
(μ : measure α)
{β : Type*}
[complete_linear_order β]
[densely_ordered β]
[topological_space β]
[order_topology β]
[second_countable_topology β]
[measurable_space β]
[borel_space β]
(s : set β)
(s_count : countable s)
(s_dense : dense s)
(f : α → β)
(h : ∀
 (p «expr ∈ » s)
 (q «expr ∈ » s), «expr < »(p, q) → «expr∃ , »((u
   v), «expr ∧ »(measurable_set u, «expr ∧ »(measurable_set v, «expr ∧ »(«expr ⊆ »({x | «expr < »(f x, p)}, u), «expr ∧ »(«expr ⊆ »({x | «expr < »(q, f x)}, v), «expr = »(μ «expr ∩ »(u, v), 0))))))) : ae_measurable f μ :=
begin
  haveI [] [":", expr encodable s] [":=", expr s_count.to_encodable],
  have [ident h'] [":", expr ∀
   p
   q, «expr∃ , »((u
     v), «expr ∧ »(measurable_set u, «expr ∧ »(measurable_set v, «expr ∧ »(«expr ⊆ »({x | «expr < »(f x, p)}, u), «expr ∧ »(«expr ⊆ »({x | «expr < »(q, f x)}, v), «expr ∈ »(p, s) → «expr ∈ »(q, s) → «expr < »(p, q) → «expr = »(μ «expr ∩ »(u, v), 0))))))] [],
  { assume [binders (p q)],
    by_cases [expr H, ":", expr «expr ∧ »(«expr ∈ »(p, s), «expr ∧ »(«expr ∈ »(q, s), «expr < »(p, q)))],
    { rcases [expr h p H.1 q H.2.1 H.2.2, "with", "⟨", ident u, ",", ident v, ",", ident hu, ",", ident hv, ",", ident h'u, ",", ident h'v, ",", ident hμ, "⟩"],
      exact [expr ⟨u, v, hu, hv, h'u, h'v, λ ps qs pq, hμ⟩] },
    { refine [expr ⟨univ, univ, measurable_set.univ, measurable_set.univ, subset_univ _, subset_univ _, λ ps qs pq, _⟩],
      simp [] [] ["only"] ["[", expr not_and, "]"] [] ["at", ident H],
      exact [expr (H ps qs pq).elim] } },
  choose ["!"] [ident u] [ident v, ident huv] ["using", expr h'],
  let [ident u'] [":", expr β → set α] [":=", expr λ p, «expr⋂ , »((q «expr ∈ » «expr ∩ »(s, Ioi p)), u p q)],
  have [ident u'_meas] [":", expr ∀ i, measurable_set (u' i)] [],
  { assume [binders (i)],
    exact [expr measurable_set.bInter (s_count.mono (inter_subset_left _ _)) (λ b hb, (huv i b).1)] },
  let [ident f'] [":", expr α → β] [":=", expr λ
   x, «expr⨅ , »((i : s), piecewise (u' i) (λ x, (i : β)) (λ x, («expr⊤»() : β)) x)],
  have [ident f'_meas] [":", expr measurable f'] [],
  { apply [expr measurable_infi],
    exact [expr λ i, measurable.piecewise (u'_meas i) measurable_const measurable_const] },
  let [ident t] [] [":=", expr «expr⋃ , »((p : s) (q : «expr ∩ »(s, Ioi p)), «expr ∩ »(u' p, v p q))],
  have [ident μt] [":", expr «expr ≤ »(μ t, 0)] [":=", expr calc
     «expr ≤ »(μ t, «expr∑' , »((p : s) (q : «expr ∩ »(s, Ioi p)), μ «expr ∩ »(u' p, v p q))) : begin
       refine [expr (measure_Union_le _).trans _],
       apply [expr ennreal.tsum_le_tsum (λ p, _)],
       apply [expr measure_Union_le _],
       exact [expr (s_count.mono (inter_subset_left _ _)).to_encodable]
     end
     «expr ≤ »(..., «expr∑' , »((p : s) (q : «expr ∩ »(s, Ioi p)), μ «expr ∩ »(u p q, v p q))) : begin
       apply [expr ennreal.tsum_le_tsum (λ p, _)],
       refine [expr ennreal.tsum_le_tsum (λ q, measure_mono _)],
       exact [expr inter_subset_inter_left _ (bInter_subset_of_mem q.2)]
     end
     «expr = »(..., «expr∑' , »((p : s) (q : «expr ∩ »(s, Ioi p)), (0 : «exprℝ≥0∞»()))) : by { congr,
       ext1 [] [ident p],
       congr,
       ext1 [] [ident q],
       exact [expr (huv p q).2.2.2.2 p.2 q.2.1 q.2.2] }
     «expr = »(..., 0) : by simp [] [] ["only"] ["[", expr tsum_zero, "]"] [] []],
  have [ident ff'] [":", expr «expr∀ᵐ ∂ , »((x), μ, «expr = »(f x, f' x))] [],
  { have [] [":", expr «expr∀ᵐ ∂ , »((x), μ, «expr ∉ »(x, t))] [],
    { have [] [":", expr «expr = »(μ t, 0)] [":=", expr le_antisymm μt bot_le],
      change [expr «expr = »(μ _, 0)] [] [],
      convert [] [expr this] [],
      ext [] [ident y] [],
      simp [] [] ["only"] ["[", expr not_exists, ",", expr exists_prop, ",", expr mem_set_of_eq, ",", expr mem_compl_eq, ",", expr not_not_mem, "]"] [] [] },
    filter_upwards ["[", expr this, "]"] [],
    assume [binders (x hx)],
    apply [expr (infi_eq_of_forall_ge_of_forall_gt_exists_lt _ _).symm],
    { assume [binders (i)],
      by_cases [expr H, ":", expr «expr ∈ »(x, u' i)],
      swap,
      { simp [] [] ["only"] ["[", expr H, ",", expr le_top, ",", expr not_false_iff, ",", expr piecewise_eq_of_not_mem, "]"] [] [] },
      simp [] [] ["only"] ["[", expr H, ",", expr piecewise_eq_of_mem, "]"] [] [],
      contrapose ["!"] [ident hx],
      obtain ["⟨", ident r, ",", "⟨", ident xr, ",", ident rq, "⟩", ",", ident rs, "⟩", ":", expr «expr∃ , »((r), «expr ∈ »(r, «expr ∩ »(Ioo (i : β) (f x), s))), ":=", expr dense_iff_inter_open.1 s_dense (Ioo i (f x)) is_open_Ioo (nonempty_Ioo.2 hx)],
      have [ident A] [":", expr «expr ∈ »(x, v i r)] [":=", expr (huv i r).2.2.2.1 rq],
      apply [expr mem_Union.2 ⟨i, _⟩],
      refine [expr mem_Union.2 ⟨⟨r, ⟨rs, xr⟩⟩, _⟩],
      exact [expr ⟨H, A⟩] },
    { assume [binders (q hq)],
      obtain ["⟨", ident r, ",", "⟨", ident xr, ",", ident rq, "⟩", ",", ident rs, "⟩", ":", expr «expr∃ , »((r), «expr ∈ »(r, «expr ∩ »(Ioo (f x) q, s))), ":=", expr dense_iff_inter_open.1 s_dense (Ioo (f x) q) is_open_Ioo (nonempty_Ioo.2 hq)],
      refine [expr ⟨⟨r, rs⟩, _⟩],
      have [ident A] [":", expr «expr ∈ »(x, u' r)] [":=", expr mem_bInter (λ i hi, (huv r i).2.2.1 xr)],
      simp [] [] ["only"] ["[", expr A, ",", expr rq, ",", expr piecewise_eq_of_mem, ",", expr subtype.coe_mk, "]"] [] [] } },
  exact [expr ⟨f', f'_meas, ff'⟩]
end

-- error in MeasureTheory.Function.AeMeasurableOrder: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function `f : α → ℝ≥0∞` is such that the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p` and `q` are finite numbers satisfying
`p < q`, then `f` is almost-everywhere measurable. -/
theorem ennreal.ae_measurable_of_exist_almost_disjoint_supersets
{α : Type*}
{m : measurable_space α}
(μ : measure α)
(f : α → «exprℝ≥0∞»())
(h : ∀
 (p : «exprℝ≥0»())
 (q : «exprℝ≥0»()), «expr < »(p, q) → «expr∃ , »((u
   v), «expr ∧ »(measurable_set u, «expr ∧ »(measurable_set v, «expr ∧ »(«expr ⊆ »({x | «expr < »(f x, p)}, u), «expr ∧ »(«expr ⊆ »({x | «expr < »((q : «exprℝ≥0∞»()), f x)}, v), «expr = »(μ «expr ∩ »(u, v), 0))))))) : ae_measurable f μ :=
begin
  obtain ["⟨", ident s, ",", ident s_count, ",", ident s_dense, ",", ident s_zero, ",", ident s_top, "⟩", ":", expr «expr∃ , »((s : set «exprℝ≥0∞»()), «expr ∧ »(countable s, «expr ∧ »(dense s, «expr ∧ »(«expr ∉ »(0, s), «expr ∉ »(«expr∞»(), s))))), ":=", expr ennreal.exists_countable_dense_no_zero_top],
  have [ident I] [":", expr ∀ x «expr ∈ » s, «expr ≠ »(x, «expr∞»())] [":=", expr λ x xs hx, s_top «expr ▸ »(hx, xs)],
  apply [expr measure_theory.ae_measurable_of_exist_almost_disjoint_supersets μ s s_count s_dense _],
  rintros [ident p, ident hp, ident q, ident hq, ident hpq],
  lift [expr p] ["to", expr «exprℝ≥0»()] ["using", expr I p hp] [],
  lift [expr q] ["to", expr «exprℝ≥0»()] ["using", expr I q hq] [],
  exact [expr h p q (ennreal.coe_lt_coe.1 hpq)]
end

