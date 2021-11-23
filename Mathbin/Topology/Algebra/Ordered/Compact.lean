import Mathbin.Topology.Algebra.Ordered.IntermediateValue

/-!
# Compactness of a closed interval

In this file we prove that a closed interval in a conditionally complete linear ordered type with
order topology (or a product of such types) is compact. We also prove the extreme value theorem
(`is_compact.exists_forall_le`, `is_compact.exists_forall_ge`): a continuous function on a compact
set takes its minimum and maximum values.

We also prove that the image of a closed interval under a continuous map is a closed interval, see
`continuous_on.image_Icc`.

## Tags

compact, extreme value theorem
-/


open Classical Filter OrderDual TopologicalSpace Function Set

/-!
### Compactness of a closed interval

In this section we define a typeclass `compact_Icc_space α` saying that all closed intervals in `α`
are compact. Then we provide an instance for a `conditionally_complete_linear_order` and prove that
the product (both `α × β` and an indexed product) of spaces with this property inherits the
property.

We also prove some simple lemmas about spaces with this property.
-/


/-- This typeclass says that all closed intervals in `α` are compact. This is true for all
conditionally complete linear orders with order topology and products (finite or infinite)
of such spaces. -/
class CompactIccSpace(α : Type _)[TopologicalSpace α][Preorderₓ α] : Prop where 
  is_compact_Icc : ∀ {a b : α}, IsCompact (Icc a b)

export CompactIccSpace(is_compact_Icc)

-- error in Topology.Algebra.Ordered.Compact: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A closed interval in a conditionally complete linear order is compact. -/
@[priority 100]
instance conditionally_complete_linear_order.to_compact_Icc_space
(α : Type*)
[conditionally_complete_linear_order α]
[topological_space α]
[order_topology α] : compact_Icc_space α :=
begin
  refine [expr ⟨λ a b, _⟩],
  cases [expr le_or_lt a b] ["with", ident hab, ident hab],
  swap,
  { simp [] [] [] ["[", expr hab, "]"] [] [] },
  refine [expr is_compact_iff_ultrafilter_le_nhds.2 (λ f hf, _)],
  contrapose ["!"] [ident hf],
  rw ["[", expr le_principal_iff, "]"] [],
  have [ident hpt] [":", expr ∀ x «expr ∈ » Icc a b, «expr ∉ »({x}, f)] [],
  from [expr λ x hx hxf, hf x hx ((le_pure_iff.2 hxf).trans (pure_le_nhds x))],
  set [] [ident s] [] [":="] [expr {x ∈ Icc a b | «expr ∉ »(Icc a x, f)}] [],
  have [ident hsb] [":", expr «expr ∈ »(b, upper_bounds s)] [],
  from [expr λ x hx, hx.1.2],
  have [ident sbd] [":", expr bdd_above s] [],
  from [expr ⟨b, hsb⟩],
  have [ident ha] [":", expr «expr ∈ »(a, s)] [],
  by simp [] [] [] ["[", expr hpt, ",", expr hab, "]"] [] [],
  rcases [expr hab.eq_or_lt, "with", ident rfl, "|", ident hlt],
  { exact [expr ha.2] },
  set [] [ident c] [] [":="] [expr Sup s] [],
  have [ident hsc] [":", expr is_lub s c] [],
  from [expr is_lub_cSup ⟨a, ha⟩ sbd],
  have [ident hc] [":", expr «expr ∈ »(c, Icc a b)] [],
  from [expr ⟨hsc.1 ha, hsc.2 hsb⟩],
  specialize [expr hf c hc],
  have [ident hcs] [":", expr «expr ∈ »(c, s)] [],
  { cases [expr hc.1.eq_or_lt] ["with", ident heq, ident hlt],
    { rwa ["<-", expr heq] [] },
    refine [expr ⟨hc, λ hcf, hf (λ U hU, _)⟩],
    rcases [expr (mem_nhds_within_Iic_iff_exists_Ioc_subset' hlt).1 (mem_nhds_within_of_mem_nhds hU), "with", "⟨", ident x, ",", ident hxc, ",", ident hxU, "⟩"],
    rcases [expr ((hsc.frequently_mem ⟨a, ha⟩).and_eventually (Ioc_mem_nhds_within_Iic ⟨hxc, le_rfl⟩)).exists, "with", "⟨", ident y, ",", "⟨", ident hyab, ",", ident hyf, "⟩", ",", ident hy, "⟩"],
    refine [expr mem_of_superset (f.diff_mem_iff.2 ⟨hcf, hyf⟩) (subset.trans _ hxU)],
    rw [expr diff_subset_iff] [],
    exact [expr subset.trans Icc_subset_Icc_union_Ioc «expr $ »(union_subset_union subset.rfl, Ioc_subset_Ioc_left hy.1.le)] },
  cases [expr hc.2.eq_or_lt] ["with", ident heq, ident hlt],
  { rw ["<-", expr heq] [],
    exact [expr hcs.2] },
  contrapose ["!"] [ident hf],
  intros [ident U, ident hU],
  rcases [expr (mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset hlt).1 (mem_nhds_within_of_mem_nhds hU), "with", "⟨", ident y, ",", ident hxy, ",", ident hyU, "⟩"],
  refine [expr mem_of_superset _ hyU],
  clear_dependent [ident U],
  have [ident hy] [":", expr «expr ∈ »(y, Icc a b)] [],
  from [expr ⟨hc.1.trans hxy.1.le, hxy.2⟩],
  by_cases [expr hay, ":", expr «expr ∈ »(Icc a y, f)],
  { refine [expr mem_of_superset (f.diff_mem_iff.2 ⟨f.diff_mem_iff.2 ⟨hay, hcs.2⟩, hpt y hy⟩) _],
    rw ["[", expr diff_subset_iff, ",", expr union_comm, ",", expr Ico_union_right hxy.1.le, ",", expr diff_subset_iff, "]"] [],
    exact [expr Icc_subset_Icc_union_Icc] },
  { exact [expr ((hsc.1 ⟨hy, hay⟩).not_lt hxy.1).elim] }
end

instance  {ι : Type _} {α : ι → Type _} [∀ i, Preorderₓ (α i)] [∀ i, TopologicalSpace (α i)]
  [∀ i, CompactIccSpace (α i)] : CompactIccSpace (∀ i, α i) :=
  ⟨fun a b => pi_univ_Icc a b ▸ is_compact_univ_pi$ fun i => is_compact_Icc⟩

instance Pi.compact_Icc_space' {α β : Type _} [Preorderₓ β] [TopologicalSpace β] [CompactIccSpace β] :
  CompactIccSpace (α → β) :=
  Pi.compact_Icc_space

instance  {α β : Type _} [Preorderₓ α] [TopologicalSpace α] [CompactIccSpace α] [Preorderₓ β] [TopologicalSpace β]
  [CompactIccSpace β] : CompactIccSpace (α × β) :=
  ⟨fun a b => (Icc_prod_eq a b).symm ▸ is_compact_Icc.Prod is_compact_Icc⟩

/-- An unordered closed interval in a conditionally complete linear order is compact. -/
theorem is_compact_interval {α : Type _} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  {a b : α} : IsCompact (interval a b) :=
  is_compact_Icc

/-- A complete linear order is a compact space.

We do not register an instance for a `[compact_Icc_space α]` because this would only add instances
for products (indexed or not) of complete linear orders, and we have instances with higher priority
that cover these cases. -/
instance (priority := 100)compact_space_of_complete_linear_order {α : Type _} [CompleteLinearOrder α]
  [TopologicalSpace α] [OrderTopology α] : CompactSpace α :=
  ⟨by 
      simp only [←Icc_bot_top, is_compact_Icc]⟩

section 

variable{α : Type _}[Preorderₓ α][TopologicalSpace α][CompactIccSpace α]

instance compact_space_Icc (a b : α) : CompactSpace (Icc a b) :=
  is_compact_iff_compact_space.mp is_compact_Icc

end 

/-!
### Min and max elements of a compact set
-/


variable{α β : Type _}[ConditionallyCompleteLinearOrder α][TopologicalSpace α][OrderTopology α][TopologicalSpace β]

theorem IsCompact.Inf_mem {s : Set α} (hs : IsCompact s) (ne_s : s.nonempty) : Inf s ∈ s :=
  hs.is_closed.cInf_mem ne_s hs.bdd_below

theorem IsCompact.Sup_mem {s : Set α} (hs : IsCompact s) (ne_s : s.nonempty) : Sup s ∈ s :=
  @IsCompact.Inf_mem (OrderDual α) _ _ _ _ hs ne_s

theorem IsCompact.is_glb_Inf {s : Set α} (hs : IsCompact s) (ne_s : s.nonempty) : IsGlb s (Inf s) :=
  is_glb_cInf ne_s hs.bdd_below

theorem IsCompact.is_lub_Sup {s : Set α} (hs : IsCompact s) (ne_s : s.nonempty) : IsLub s (Sup s) :=
  @IsCompact.is_glb_Inf (OrderDual α) _ _ _ _ hs ne_s

theorem IsCompact.is_least_Inf {s : Set α} (hs : IsCompact s) (ne_s : s.nonempty) : IsLeast s (Inf s) :=
  ⟨hs.Inf_mem ne_s, (hs.is_glb_Inf ne_s).1⟩

theorem IsCompact.is_greatest_Sup {s : Set α} (hs : IsCompact s) (ne_s : s.nonempty) : IsGreatest s (Sup s) :=
  @IsCompact.is_least_Inf (OrderDual α) _ _ _ _ hs ne_s

theorem IsCompact.exists_is_least {s : Set α} (hs : IsCompact s) (ne_s : s.nonempty) : ∃ x, IsLeast s x :=
  ⟨_, hs.is_least_Inf ne_s⟩

theorem IsCompact.exists_is_greatest {s : Set α} (hs : IsCompact s) (ne_s : s.nonempty) : ∃ x, IsGreatest s x :=
  ⟨_, hs.is_greatest_Sup ne_s⟩

theorem IsCompact.exists_is_glb {s : Set α} (hs : IsCompact s) (ne_s : s.nonempty) : ∃ (x : _)(_ : x ∈ s), IsGlb s x :=
  ⟨_, hs.Inf_mem ne_s, hs.is_glb_Inf ne_s⟩

theorem IsCompact.exists_is_lub {s : Set α} (hs : IsCompact s) (ne_s : s.nonempty) : ∃ (x : _)(_ : x ∈ s), IsLub s x :=
  ⟨_, hs.Sup_mem ne_s, hs.is_lub_Sup ne_s⟩

theorem IsCompact.exists_Inf_image_eq {s : Set β} (hs : IsCompact s) (ne_s : s.nonempty) {f : β → α}
  (hf : ContinuousOn f s) : ∃ (x : _)(_ : x ∈ s), Inf (f '' s) = f x :=
  let ⟨x, hxs, hx⟩ := (hs.image_of_continuous_on hf).Inf_mem (ne_s.image f)
  ⟨x, hxs, hx.symm⟩

theorem IsCompact.exists_Sup_image_eq :
  ∀ {s : Set β},
    IsCompact s → s.nonempty → ∀ {f : β → α}, ContinuousOn f s → ∃ (x : _)(_ : x ∈ s), Sup (f '' s) = f x :=
  @IsCompact.exists_Inf_image_eq (OrderDual α) _ _ _ _ _

theorem eq_Icc_of_connected_compact {s : Set α} (h₁ : IsConnected s) (h₂ : IsCompact s) : s = Icc (Inf s) (Sup s) :=
  eq_Icc_cInf_cSup_of_connected_bdd_closed h₁ h₂.bdd_below h₂.bdd_above h₂.is_closed

/-!
### Extreme value theorem
-/


/-- The **extreme value theorem**: a continuous function realizes its minimum on a compact set. -/
theorem IsCompact.exists_forall_le {s : Set β} (hs : IsCompact s) (ne_s : s.nonempty) {f : β → α}
  (hf : ContinuousOn f s) : ∃ (x : _)(_ : x ∈ s), ∀ y _ : y ∈ s, f x ≤ f y :=
  by 
    rcases(hs.image_of_continuous_on hf).exists_is_least (ne_s.image f) with ⟨_, ⟨x, hxs, rfl⟩, hx⟩
    exact ⟨x, hxs, ball_image_iff.1 hx⟩

/-- The **extreme value theorem**: a continuous function realizes its maximum on a compact set. -/
theorem IsCompact.exists_forall_ge :
  ∀ {s : Set β},
    IsCompact s → s.nonempty → ∀ {f : β → α}, ContinuousOn f s → ∃ (x : _)(_ : x ∈ s), ∀ y _ : y ∈ s, f y ≤ f x :=
  @IsCompact.exists_forall_le (OrderDual α) _ _ _ _ _

/-- The **extreme value theorem**: if a continuous function `f` tends to infinity away from compact
sets, then it has a global minimum. -/
theorem Continuous.exists_forall_le [Nonempty β] {f : β → α} (hf : Continuous f)
  (hlim : tendsto f (cocompact β) at_top) : ∃ x, ∀ y, f x ≤ f y :=
  by 
    inhabit β 
    obtain ⟨s : Set β, hsc : IsCompact s, hsf : ∀ x _ : x ∉ s, f (default β) ≤ f x⟩ :=
      (has_basis_cocompact.tendsto_iff at_top_basis).1 hlim (f$ default β) trivialₓ 
    obtain ⟨x, -, hx⟩ : ∃ (x : _)(_ : x ∈ insert (default β) s), ∀ y _ : y ∈ insert (default β) s, f x ≤ f y :=
      (hsc.insert (default β)).exists_forall_le (nonempty_insert _ _) hf.continuous_on 
    refine' ⟨x, fun y => _⟩
    byCases' hy : y ∈ s 
    exacts[hx y (Or.inr hy), (hx _ (Or.inl rfl)).trans (hsf y hy)]

/-- The **extreme value theorem**: if a continuous function `f` tends to negative infinity away from
compact sets, then it has a global maximum. -/
theorem Continuous.exists_forall_ge [Nonempty β] {f : β → α} (hf : Continuous f)
  (hlim : tendsto f (cocompact β) at_bot) : ∃ x, ∀ y, f y ≤ f x :=
  @Continuous.exists_forall_le (OrderDual α) _ _ _ _ _ _ _ hf hlim

/-!
### Image of a closed interval
-/


variable[DenselyOrdered α][ConditionallyCompleteLinearOrder β][OrderTopology β]{f : α → β}{a b x y : α}

open_locale Interval

theorem ContinuousOn.image_Icc (hab : a ≤ b) (h : ContinuousOn f$ Icc a b) :
  f '' Icc a b = Icc (Inf$ f '' Icc a b) (Sup$ f '' Icc a b) :=
  eq_Icc_of_connected_compact ⟨(nonempty_Icc.2 hab).Image f, is_preconnected_Icc.Image f h⟩
    (is_compact_Icc.image_of_continuous_on h)

-- error in Topology.Algebra.Ordered.Compact: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem continuous_on.image_interval_eq_Icc
(h : «expr $ »(continuous_on f, «expr[ , ]»(a, b))) : «expr = »(«expr '' »(f, «expr[ , ]»(a, b)), Icc (Inf «expr '' »(f, «expr[ , ]»(a, b))) (Sup «expr '' »(f, «expr[ , ]»(a, b)))) :=
begin
  cases [expr le_total a b] ["with", ident h2, ident h2],
  { simp_rw ["[", expr interval_of_le h2, "]"] ["at", ident h, "⊢"],
    exact [expr h.image_Icc h2] },
  { simp_rw ["[", expr interval_of_ge h2, "]"] ["at", ident h, "⊢"],
    exact [expr h.image_Icc h2] }
end

-- error in Topology.Algebra.Ordered.Compact: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem continuous_on.image_interval
(h : «expr $ »(continuous_on f, «expr[ , ]»(a, b))) : «expr = »(«expr '' »(f, «expr[ , ]»(a, b)), «expr[ , ]»(Inf «expr '' »(f, «expr[ , ]»(a, b)), Sup «expr '' »(f, «expr[ , ]»(a, b)))) :=
begin
  refine [expr h.image_interval_eq_Icc.trans (interval_of_le _).symm],
  refine [expr cInf_le_cSup _ _ (nonempty_interval.image _)]; rw [expr h.image_interval_eq_Icc] [],
  exacts ["[", expr bdd_below_Icc, ",", expr bdd_above_Icc, "]"]
end

