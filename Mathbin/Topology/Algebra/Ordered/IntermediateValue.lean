import Mathbin.Topology.Algebra.Ordered.Basic

/-!
# Intermediate Value Theorem

In this file we prove the Intermediate Value Theorem: if `f : α → β` is a function defined on a
connected set `s` that takes both values `≤ a` and values `≥ a` on `s`, then it is equal to `a` at
some point of `s`. We also prove that intervals in a dense conditionally complete order are
preconnected and any preconnected set is an interval. Then we specialize IVT to functions continuous
on intervals.

## Main results

* `is_preconnected_I??` : all intervals `I??` are preconnected,
* `is_preconnected.intermediate_value`, `intermediate_value_univ` : Intermediate Value Theorem for
  connected sets and connected spaces, respectively;
* `intermediate_value_Icc`, `intermediate_value_Icc'`: Intermediate Value Theorem for functions
  on closed intervals.

### Miscellaneous facts

* `is_closed.Icc_subset_of_forall_mem_nhds_within` : “Continuous induction” principle;
  if `s ∩ [a, b]` is closed, `a ∈ s`, and for each `x ∈ [a, b) ∩ s` some of its right neighborhoods
  is included `s`, then `[a, b] ⊆ s`.
* `is_closed.Icc_subset_of_forall_exists_gt`, `is_closed.mem_of_ge_of_forall_exists_gt` : two
  other versions of the “continuous induction” principle.

## Tags

intermediate value theorem, connected space, connected set
-/


open Filter OrderDual TopologicalSpace Function Set

open_locale TopologicalSpace Filter

universe u v w

/-!
### Intermediate value theorem on a (pre)connected space

In this section we prove the following theorem (see `is_preconnected.intermediate_value₂`): if `f`
and `g` are two functions continuous on a preconnected set `s`, `f a ≤ g a` at some `a ∈ s` and
`g b ≤ f b` at some `b ∈ s`, then `f c = g c` at some `c ∈ s`. We prove several versions of this
statement, including the classical IVT that corresponds to a constant function `g`.
-/


section 

variable{X : Type u}{α : Type v}[TopologicalSpace X][LinearOrderₓ α][TopologicalSpace α][OrderClosedTopology α]

/-- Intermediate value theorem for two functions: if `f` and `g` are two continuous functions
on a preconnected space and `f a ≤ g a` and `g b ≤ f b`, then for some `x` we have `f x = g x`. -/
theorem intermediate_value_univ₂ [PreconnectedSpace X] {a b : X} {f g : X → α} (hf : Continuous f) (hg : Continuous g)
  (ha : f a ≤ g a) (hb : g b ≤ f b) : ∃ x, f x = g x :=
  by 
    obtain ⟨x, h, hfg, hgf⟩ : (univ ∩ { x | f x ≤ g x ∧ g x ≤ f x }).Nonempty 
    exact
      is_preconnected_closed_iff.1 PreconnectedSpace.is_preconnected_univ _ _ (is_closed_le hf hg) (is_closed_le hg hf)
        (fun x hx => le_totalₓ _ _) ⟨a, trivialₓ, ha⟩ ⟨b, trivialₓ, hb⟩
    exact ⟨x, le_antisymmₓ hfg hgf⟩

theorem intermediate_value_univ₂_eventually₁ [PreconnectedSpace X] {a : X} {l : Filter X} [ne_bot l] {f g : X → α}
  (hf : Continuous f) (hg : Continuous g) (ha : f a ≤ g a) (he : g ≤ᶠ[l] f) : ∃ x, f x = g x :=
  let ⟨c, hc⟩ := he.frequently.exists 
  intermediate_value_univ₂ hf hg ha hc

theorem intermediate_value_univ₂_eventually₂ [PreconnectedSpace X] {l₁ l₂ : Filter X} [ne_bot l₁] [ne_bot l₂]
  {f g : X → α} (hf : Continuous f) (hg : Continuous g) (he₁ : f ≤ᶠ[l₁] g) (he₂ : g ≤ᶠ[l₂] f) : ∃ x, f x = g x :=
  let ⟨c₁, hc₁⟩ := he₁.frequently.exists 
  let ⟨c₂, hc₂⟩ := he₂.frequently.exists 
  intermediate_value_univ₂ hf hg hc₁ hc₂

/-- Intermediate value theorem for two functions: if `f` and `g` are two functions continuous
on a preconnected set `s` and for some `a b ∈ s` we have `f a ≤ g a` and `g b ≤ f b`,
then for some `x ∈ s` we have `f x = g x`. -/
theorem IsPreconnected.intermediate_value₂ {s : Set X} (hs : IsPreconnected s) {a b : X} (ha : a ∈ s) (hb : b ∈ s)
  {f g : X → α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) (ha' : f a ≤ g a) (hb' : g b ≤ f b) :
  ∃ (x : _)(_ : x ∈ s), f x = g x :=
  let ⟨x, hx⟩ :=
    @intermediate_value_univ₂ s α _ _ _ _ (Subtype.preconnected_space hs) ⟨a, ha⟩ ⟨b, hb⟩ _ _
      (continuous_on_iff_continuous_restrict.1 hf) (continuous_on_iff_continuous_restrict.1 hg) ha' hb'
  ⟨x, x.2, hx⟩

theorem IsPreconnected.intermediate_value₂_eventually₁ {s : Set X} (hs : IsPreconnected s) {a : X} {l : Filter X}
  (ha : a ∈ s) [ne_bot l] (hl : l ≤ 𝓟 s) {f g : X → α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) (ha' : f a ≤ g a)
  (he : g ≤ᶠ[l] f) : ∃ (x : _)(_ : x ∈ s), f x = g x :=
  by 
    rw [continuous_on_iff_continuous_restrict] at hf hg 
    obtain ⟨b, h⟩ :=
      @intermediate_value_univ₂_eventually₁ _ _ _ _ _ _ (Subtype.preconnected_space hs) ⟨a, ha⟩ _
        (comap_coe_ne_bot_of_le_principal hl) _ _ hf hg ha' (eventually_comap' he)
    exact ⟨b, b.prop, h⟩

theorem IsPreconnected.intermediate_value₂_eventually₂ {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X}
  [ne_bot l₁] [ne_bot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f g : X → α} (hf : ContinuousOn f s)
  (hg : ContinuousOn g s) (he₁ : f ≤ᶠ[l₁] g) (he₂ : g ≤ᶠ[l₂] f) : ∃ (x : _)(_ : x ∈ s), f x = g x :=
  by 
    rw [continuous_on_iff_continuous_restrict] at hf hg 
    obtain ⟨b, h⟩ :=
      @intermediate_value_univ₂_eventually₂ _ _ _ _ _ _ (Subtype.preconnected_space hs) _ _
        (comap_coe_ne_bot_of_le_principal hl₁) (comap_coe_ne_bot_of_le_principal hl₂) _ _ hf hg (eventually_comap' he₁)
        (eventually_comap' he₂)
    exact ⟨b, b.prop, h⟩

/-- **Intermediate Value Theorem** for continuous functions on connected sets. -/
theorem IsPreconnected.intermediate_value {s : Set X} (hs : IsPreconnected s) {a b : X} (ha : a ∈ s) (hb : b ∈ s)
  {f : X → α} (hf : ContinuousOn f s) : Icc (f a) (f b) ⊆ f '' s :=
  fun x hx => mem_image_iff_bex.2$ hs.intermediate_value₂ ha hb hf continuous_on_const hx.1 hx.2

theorem IsPreconnected.intermediate_value_Ico {s : Set X} (hs : IsPreconnected s) {a : X} {l : Filter X} (ha : a ∈ s)
  [ne_bot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α} (ht : tendsto f l (𝓝 v)) :
  Ico (f a) v ⊆ f '' s :=
  fun y h =>
    bex_def.1$ hs.intermediate_value₂_eventually₁ ha hl hf continuous_on_const h.1 (eventually_ge_of_tendsto_gt h.2 ht)

theorem IsPreconnected.intermediate_value_Ioc {s : Set X} (hs : IsPreconnected s) {a : X} {l : Filter X} (ha : a ∈ s)
  [ne_bot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α} (ht : tendsto f l (𝓝 v)) :
  Ioc v (f a) ⊆ f '' s :=
  fun y h =>
    bex_def.1$
      (Bex.imp_right fun x _ => Eq.symm)$
        hs.intermediate_value₂_eventually₁ ha hl continuous_on_const hf h.2 (eventually_le_of_tendsto_lt h.1 ht)

theorem IsPreconnected.intermediate_value_Ioo {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X} [ne_bot l₁]
  [ne_bot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v₁ v₂ : α}
  (ht₁ : tendsto f l₁ (𝓝 v₁)) (ht₂ : tendsto f l₂ (𝓝 v₂)) : Ioo v₁ v₂ ⊆ f '' s :=
  fun y h =>
    bex_def.1$
      hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuous_on_const (eventually_le_of_tendsto_lt h.1 ht₁)
        (eventually_ge_of_tendsto_gt h.2 ht₂)

theorem IsPreconnected.intermediate_value_Ici {s : Set X} (hs : IsPreconnected s) {a : X} {l : Filter X} (ha : a ∈ s)
  [ne_bot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) (ht : tendsto f l at_top) : Ici (f a) ⊆ f '' s :=
  fun y h => bex_def.1$ hs.intermediate_value₂_eventually₁ ha hl hf continuous_on_const h (tendsto_at_top.1 ht y)

theorem IsPreconnected.intermediate_value_Iic {s : Set X} (hs : IsPreconnected s) {a : X} {l : Filter X} (ha : a ∈ s)
  [ne_bot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) (ht : tendsto f l at_bot) : Iic (f a) ⊆ f '' s :=
  fun y h =>
    bex_def.1$
      (Bex.imp_right fun x _ => Eq.symm)$
        hs.intermediate_value₂_eventually₁ ha hl continuous_on_const hf h (tendsto_at_bot.1 ht y)

theorem IsPreconnected.intermediate_value_Ioi {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X} [ne_bot l₁]
  [ne_bot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α} (ht₁ : tendsto f l₁ (𝓝 v))
  (ht₂ : tendsto f l₂ at_top) : Ioi v ⊆ f '' s :=
  fun y h =>
    bex_def.1$
      hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuous_on_const (eventually_le_of_tendsto_lt h ht₁)
        (tendsto_at_top.1 ht₂ y)

theorem IsPreconnected.intermediate_value_Iio {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X} [ne_bot l₁]
  [ne_bot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α} (ht₁ : tendsto f l₁ at_bot)
  (ht₂ : tendsto f l₂ (𝓝 v)) : Iio v ⊆ f '' s :=
  fun y h =>
    bex_def.1$
      hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuous_on_const (tendsto_at_bot.1 ht₁ y)
        (eventually_ge_of_tendsto_gt h ht₂)

theorem IsPreconnected.intermediate_value_Iii {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X} [ne_bot l₁]
  [ne_bot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) (ht₁ : tendsto f l₁ at_bot)
  (ht₂ : tendsto f l₂ at_top) : univ ⊆ f '' s :=
  fun y h =>
    bex_def.1$
      hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuous_on_const (tendsto_at_bot.1 ht₁ y)
        (tendsto_at_top.1 ht₂ y)

/-- **Intermediate Value Theorem** for continuous functions on connected spaces. -/
theorem intermediate_value_univ [PreconnectedSpace X] (a b : X) {f : X → α} (hf : Continuous f) :
  Icc (f a) (f b) ⊆ range f :=
  fun x hx => intermediate_value_univ₂ hf continuous_const hx.1 hx.2

/-- **Intermediate Value Theorem** for continuous functions on connected spaces. -/
theorem mem_range_of_exists_le_of_exists_ge [PreconnectedSpace X] {c : α} {f : X → α} (hf : Continuous f)
  (h₁ : ∃ a, f a ≤ c) (h₂ : ∃ b, c ≤ f b) : c ∈ range f :=
  let ⟨a, ha⟩ := h₁ 
  let ⟨b, hb⟩ := h₂ 
  intermediate_value_univ a b hf ⟨ha, hb⟩

/-!
### (Pre)connected sets in a linear order

In this section we prove the following results:

* `is_preconnected.ord_connected`: any preconnected set `s` in a linear order is `ord_connected`,
  i.e. `a ∈ s` and `b ∈ s` imply `Icc a b ⊆ s`;

* `is_preconnected.mem_intervals`: any preconnected set `s` in a conditionally complete linear order
  is one of the intervals `set.Icc`, `set.`Ico`, `set.Ioc`, `set.Ioo`, ``set.Ici`, `set.Iic`,
  `set.Ioi`, `set.Iio`; note that this is false for non-complete orders: e.g., in `ℝ \ {0}`, the set
  of positive numbers cannot be represented as `set.Ioi _`.

-/


/-- If a preconnected set contains endpoints of an interval, then it includes the whole interval. -/
theorem IsPreconnected.Icc_subset {s : Set α} (hs : IsPreconnected s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  Icc a b ⊆ s :=
  by 
    simpa only [image_id] using hs.intermediate_value ha hb continuous_on_id

theorem IsPreconnected.ord_connected {s : Set α} (h : IsPreconnected s) : ord_connected s :=
  ⟨fun x hx y hy => h.Icc_subset hx hy⟩

/-- If a preconnected set contains endpoints of an interval, then it includes the whole interval. -/
theorem IsConnected.Icc_subset {s : Set α} (hs : IsConnected s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : Icc a b ⊆ s :=
  hs.2.Icc_subset ha hb

/-- If preconnected set in a linear order space is unbounded below and above, then it is the whole
space. -/
theorem IsPreconnected.eq_univ_of_unbounded {s : Set α} (hs : IsPreconnected s) (hb : ¬BddBelow s) (ha : ¬BddAbove s) :
  s = univ :=
  by 
    refine' eq_univ_of_forall fun x => _ 
    obtain ⟨y, ys, hy⟩ : ∃ (y : _)(_ : y ∈ s), y < x := not_bdd_below_iff.1 hb x 
    obtain ⟨z, zs, hz⟩ : ∃ (z : _)(_ : z ∈ s), x < z := not_bdd_above_iff.1 ha x 
    exact hs.Icc_subset ys zs ⟨le_of_ltₓ hy, le_of_ltₓ hz⟩

end 

variable{α :
    Type
      u}{β :
    Type
      v}{γ :
    Type
      w}[ConditionallyCompleteLinearOrder
      α][TopologicalSpace
      α][OrderTopology α][ConditionallyCompleteLinearOrder β][TopologicalSpace β][OrderTopology β][Nonempty γ]

/-- A bounded connected subset of a conditionally complete linear order includes the open interval
`(Inf s, Sup s)`. -/
theorem IsConnected.Ioo_cInf_cSup_subset {s : Set α} (hs : IsConnected s) (hb : BddBelow s) (ha : BddAbove s) :
  Ioo (Inf s) (Sup s) ⊆ s :=
  fun x hx =>
    let ⟨y, ys, hy⟩ := (is_glb_lt_iff (is_glb_cInf hs.nonempty hb)).1 hx.1
    let ⟨z, zs, hz⟩ := (lt_is_lub_iff (is_lub_cSup hs.nonempty ha)).1 hx.2
    hs.Icc_subset ys zs ⟨le_of_ltₓ hy, le_of_ltₓ hz⟩

theorem eq_Icc_cInf_cSup_of_connected_bdd_closed {s : Set α} (hc : IsConnected s) (hb : BddBelow s) (ha : BddAbove s)
  (hcl : IsClosed s) : s = Icc (Inf s) (Sup s) :=
  subset.antisymm (subset_Icc_cInf_cSup hb ha)$
    hc.Icc_subset (hcl.cInf_mem hc.nonempty hb) (hcl.cSup_mem hc.nonempty ha)

-- error in Topology.Algebra.Ordered.IntermediateValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_preconnected.Ioi_cInf_subset
{s : set α}
(hs : is_preconnected s)
(hb : bdd_below s)
(ha : «expr¬ »(bdd_above s)) : «expr ⊆ »(Ioi (Inf s), s) :=
begin
  have [ident sne] [":", expr s.nonempty] [":=", expr @nonempty_of_not_bdd_above α _ s ⟨Inf «expr∅»()⟩ ha],
  intros [ident x, ident hx],
  obtain ["⟨", ident y, ",", ident ys, ",", ident hy, "⟩", ":", expr «expr∃ , »((y «expr ∈ » s), «expr < »(y, x)), ":=", expr (is_glb_lt_iff (is_glb_cInf sne hb)).1 hx],
  obtain ["⟨", ident z, ",", ident zs, ",", ident hz, "⟩", ":", expr «expr∃ , »((z «expr ∈ » s), «expr < »(x, z)), ":=", expr not_bdd_above_iff.1 ha x],
  exact [expr hs.Icc_subset ys zs ⟨le_of_lt hy, le_of_lt hz⟩]
end

theorem IsPreconnected.Iio_cSup_subset {s : Set α} (hs : IsPreconnected s) (hb : ¬BddBelow s) (ha : BddAbove s) :
  Iio (Sup s) ⊆ s :=
  @IsPreconnected.Ioi_cInf_subset (OrderDual α) _ _ _ s hs ha hb

-- error in Topology.Algebra.Ordered.IntermediateValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A preconnected set in a conditionally complete linear order is either one of the intervals
`[Inf s, Sup s]`, `[Inf s, Sup s)`, `(Inf s, Sup s]`, `(Inf s, Sup s)`, `[Inf s, +∞)`,
`(Inf s, +∞)`, `(-∞, Sup s]`, `(-∞, Sup s)`, `(-∞, +∞)`, or `∅`. The converse statement requires
`α` to be densely ordererd. -/
theorem is_preconnected.mem_intervals
{s : set α}
(hs : is_preconnected s) : «expr ∈ »(s, ({Icc (Inf s) (Sup s), Ico (Inf s) (Sup s), Ioc (Inf s) (Sup s), Ioo (Inf s) (Sup s), Ici (Inf s), Ioi (Inf s), Iic (Sup s), Iio (Sup s), univ, «expr∅»()} : set (set α))) :=
begin
  rcases [expr s.eq_empty_or_nonempty, "with", ident rfl, "|", ident hne],
  { apply_rules ["[", expr or.inr, ",", expr mem_singleton, "]"] },
  have [ident hs'] [":", expr is_connected s] [":=", expr ⟨hne, hs⟩],
  by_cases [expr hb, ":", expr bdd_below s]; by_cases [expr ha, ":", expr bdd_above s],
  { rcases [expr mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset (hs'.Ioo_cInf_cSup_subset hb ha) (subset_Icc_cInf_cSup hb ha), "with", ident hs, "|", ident hs, "|", ident hs, "|", ident hs],
    { exact [expr or.inl hs] },
    { exact [expr «expr $ »(or.inr, or.inl hs)] },
    { exact [expr «expr $ »(or.inr, «expr $ »(or.inr, or.inl hs))] },
    { exact [expr «expr $ »(or.inr, «expr $ »(or.inr, «expr $ »(or.inr, or.inl hs)))] } },
  { refine [expr «expr $ »(or.inr, «expr $ »(or.inr, «expr $ »(or.inr, or.inr _)))],
    cases [expr mem_Ici_Ioi_of_subset_of_subset (hs.Ioi_cInf_subset hb ha) (λ
      x hx, cInf_le hb hx)] ["with", ident hs, ident hs],
    { exact [expr or.inl hs] },
    { exact [expr or.inr (or.inl hs)] } },
  { iterate [6] { apply [expr or.inr] },
    cases [expr mem_Iic_Iio_of_subset_of_subset (hs.Iio_cSup_subset hb ha) (λ
      x hx, le_cSup ha hx)] ["with", ident hs, ident hs],
    { exact [expr or.inl hs] },
    { exact [expr or.inr (or.inl hs)] } },
  { iterate [8] { apply [expr or.inr] },
    exact [expr or.inl (hs.eq_univ_of_unbounded hb ha)] }
end

/-- A preconnected set is either one of the intervals `Icc`, `Ico`, `Ioc`, `Ioo`, `Ici`, `Ioi`,
`Iic`, `Iio`, or `univ`, or `∅`. The converse statement requires `α` to be densely ordered. Though
one can represent `∅` as `(Inf s, Inf s)`, we include it into the list of possible cases to improve
readability. -/
theorem set_of_is_preconnected_subset_of_ordered :
  { s:Set α | IsPreconnected s } ⊆
    range (uncurry Icc) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range (uncurry Ioo) ∪
      (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅}) :=
  by 
    intro s hs 
    rcases hs.mem_intervals with (hs | hs | hs | hs | hs | hs | hs | hs | hs | hs)
    ·
      exact Or.inl$ Or.inl$ Or.inl$ Or.inl ⟨(Inf s, Sup s), hs.symm⟩
    ·
      exact Or.inl$ Or.inl$ Or.inl$ Or.inr ⟨(Inf s, Sup s), hs.symm⟩
    ·
      exact Or.inl$ Or.inl$ Or.inr ⟨(Inf s, Sup s), hs.symm⟩
    ·
      exact Or.inl$ Or.inr ⟨(Inf s, Sup s), hs.symm⟩
    ·
      exact Or.inr$ Or.inl$ Or.inl$ Or.inl$ Or.inl ⟨Inf s, hs.symm⟩
    ·
      exact Or.inr$ Or.inl$ Or.inl$ Or.inl$ Or.inr ⟨Inf s, hs.symm⟩
    ·
      exact Or.inr$ Or.inl$ Or.inl$ Or.inr ⟨Sup s, hs.symm⟩
    ·
      exact Or.inr$ Or.inl$ Or.inr ⟨Sup s, hs.symm⟩
    ·
      exact Or.inr$ Or.inr$ Or.inl hs
    ·
      exact Or.inr$ Or.inr$ Or.inr hs

/-!
### Intervals are connected

In this section we prove that a closed interval (hence, any `ord_connected` set) in a dense
conditionally complete linear order is preconnected.
-/


-- error in Topology.Algebra.Ordered.IntermediateValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and the set `s ∩ [a, b)` has no maximal point, then `b ∈ s`. -/
theorem is_closed.mem_of_ge_of_forall_exists_gt
{a b : α}
{s : set α}
(hs : is_closed «expr ∩ »(s, Icc a b))
(ha : «expr ∈ »(a, s))
(hab : «expr ≤ »(a, b))
(hgt : ∀ x «expr ∈ » «expr ∩ »(s, Ico a b), «expr ∩ »(s, Ioc x b).nonempty) : «expr ∈ »(b, s) :=
begin
  let [ident S] [] [":=", expr «expr ∩ »(s, Icc a b)],
  replace [ident ha] [":", expr «expr ∈ »(a, S)] [],
  from [expr ⟨ha, left_mem_Icc.2 hab⟩],
  have [ident Sbd] [":", expr bdd_above S] [],
  from [expr ⟨b, λ z hz, hz.2.2⟩],
  let [ident c] [] [":=", expr Sup «expr ∩ »(s, Icc a b)],
  have [ident c_mem] [":", expr «expr ∈ »(c, S)] [],
  from [expr hs.cSup_mem ⟨_, ha⟩ Sbd],
  have [ident c_le] [":", expr «expr ≤ »(c, b)] [],
  from [expr cSup_le ⟨_, ha⟩ (λ x hx, hx.2.2)],
  cases [expr eq_or_lt_of_le c_le] ["with", ident hc, ident hc],
  from [expr «expr ▸ »(hc, c_mem.1)],
  exfalso,
  rcases [expr hgt c ⟨c_mem.1, c_mem.2.1, hc⟩, "with", "⟨", ident x, ",", ident xs, ",", ident cx, ",", ident xb, "⟩"],
  exact [expr not_lt_of_le (le_cSup Sbd ⟨xs, le_trans (le_cSup Sbd ha) (le_of_lt cx), xb⟩) cx]
end

-- error in Topology.Algebra.Ordered.IntermediateValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and for any `a ≤ x < y ≤ b`, `x ∈ s`, the set `s ∩ (x, y]`
is not empty, then `[a, b] ⊆ s`. -/
theorem is_closed.Icc_subset_of_forall_exists_gt
{a b : α}
{s : set α}
(hs : is_closed «expr ∩ »(s, Icc a b))
(ha : «expr ∈ »(a, s))
(hgt : ∀
 x «expr ∈ » «expr ∩ »(s, Ico a b), ∀ y «expr ∈ » Ioi x, «expr ∩ »(s, Ioc x y).nonempty) : «expr ⊆ »(Icc a b, s) :=
begin
  assume [binders (y hy)],
  have [] [":", expr is_closed «expr ∩ »(s, Icc a y)] [],
  { suffices [] [":", expr «expr = »(«expr ∩ »(s, Icc a y), «expr ∩ »(«expr ∩ »(s, Icc a b), Icc a y))],
    { rw [expr this] [],
      exact [expr is_closed.inter hs is_closed_Icc] },
    rw ["[", expr inter_assoc, "]"] [],
    congr,
    exact [expr «expr $ »(inter_eq_self_of_subset_right, Icc_subset_Icc_right hy.2).symm] },
  exact [expr is_closed.mem_of_ge_of_forall_exists_gt this ha hy.1 (λ
    x hx, hgt x ⟨hx.1, Ico_subset_Ico_right hy.2 hx.2⟩ y hx.2.2)]
end

variable[DenselyOrdered α]{a b : α}

-- error in Topology.Algebra.Ordered.IntermediateValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and for any `x ∈ s ∩ [a, b)` the set `s` includes some open
neighborhood of `x` within `(x, +∞)`, then `[a, b] ⊆ s`. -/
theorem is_closed.Icc_subset_of_forall_mem_nhds_within
{a b : α}
{s : set α}
(hs : is_closed «expr ∩ »(s, Icc a b))
(ha : «expr ∈ »(a, s))
(hgt : ∀ x «expr ∈ » «expr ∩ »(s, Ico a b), «expr ∈ »(s, «expr𝓝[ ] »(Ioi x, x))) : «expr ⊆ »(Icc a b, s) :=
begin
  apply [expr hs.Icc_subset_of_forall_exists_gt ha],
  rintros [ident x, "⟨", ident hxs, ",", ident hxab, "⟩", ident y, ident hyxb],
  have [] [":", expr «expr ∈ »(«expr ∩ »(s, Ioc x y), «expr𝓝[ ] »(Ioi x, x))] [],
  from [expr inter_mem (hgt x ⟨hxs, hxab⟩) (Ioc_mem_nhds_within_Ioi ⟨le_refl _, hyxb⟩)],
  exact [expr (nhds_within_Ioi_self_ne_bot' hxab.2).nonempty_of_mem this]
end

-- error in Topology.Algebra.Ordered.IntermediateValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A closed interval in a densely ordered conditionally complete linear order is preconnected. -/
theorem is_preconnected_Icc : is_preconnected (Icc a b) :=
is_preconnected_closed_iff.2 (begin
   rintros [ident s, ident t, ident hs, ident ht, ident hab, "⟨", ident x, ",", ident hx, "⟩", "⟨", ident y, ",", ident hy, "⟩"],
   wlog [ident hxy] [":", expr «expr ≤ »(x, y)] [":=", expr le_total x y] ["using", "[", ident x, ident y, ident s, ident t, ",", ident y, ident x, ident t, ident s, "]"],
   have [ident xyab] [":", expr «expr ⊆ »(Icc x y, Icc a b)] [":=", expr Icc_subset_Icc hx.1.1 hy.1.2],
   by_contradiction [ident hst],
   suffices [] [":", expr «expr ⊆ »(Icc x y, s)],
   from [expr hst ⟨y, «expr $ »(xyab, right_mem_Icc.2 hxy), «expr $ »(this, right_mem_Icc.2 hxy), hy.2⟩],
   apply [expr (is_closed.inter hs is_closed_Icc).Icc_subset_of_forall_mem_nhds_within hx.2],
   rintros [ident z, "⟨", ident zs, ",", ident hz, "⟩"],
   have [ident zt] [":", expr «expr ∈ »(z, «expr ᶜ»(t))] [],
   from [expr λ zt, hst ⟨z, «expr $ »(xyab, Ico_subset_Icc_self hz), zs, zt⟩],
   have [] [":", expr «expr ∈ »(«expr ∩ »(«expr ᶜ»(t), Ioc z y), «expr𝓝[ ] »(Ioi z, z))] [],
   { rw ["[", "<-", expr nhds_within_Ioc_eq_nhds_within_Ioi hz.2, "]"] [],
     exact [expr mem_nhds_within.2 ⟨«expr ᶜ»(t), ht.is_open_compl, zt, subset.refl _⟩] },
   apply [expr mem_of_superset this],
   have [] [":", expr «expr ⊆ »(Ioc z y, «expr ∪ »(s, t))] [],
   from [expr λ w hw, hab (xyab ⟨le_trans hz.1 (le_of_lt hw.1), hw.2⟩)],
   exact [expr λ (w) ⟨wt, wzy⟩, (this wzy).elim id (λ h, (wt h).elim)]
 end)

theorem is_preconnected_interval : IsPreconnected (interval a b) :=
  is_preconnected_Icc

theorem Set.OrdConnected.is_preconnected {s : Set α} (h : s.ord_connected) : IsPreconnected s :=
  is_preconnected_of_forall_pair$
    fun x y hx hy =>
      ⟨interval x y, h.interval_subset hx hy, left_mem_interval, right_mem_interval, is_preconnected_interval⟩

theorem is_preconnected_iff_ord_connected {s : Set α} : IsPreconnected s ↔ ord_connected s :=
  ⟨IsPreconnected.ord_connected, Set.OrdConnected.is_preconnected⟩

theorem is_preconnected_Ici : IsPreconnected (Ici a) :=
  ord_connected_Ici.IsPreconnected

theorem is_preconnected_Iic : IsPreconnected (Iic a) :=
  ord_connected_Iic.IsPreconnected

theorem is_preconnected_Iio : IsPreconnected (Iio a) :=
  ord_connected_Iio.IsPreconnected

theorem is_preconnected_Ioi : IsPreconnected (Ioi a) :=
  ord_connected_Ioi.IsPreconnected

theorem is_preconnected_Ioo : IsPreconnected (Ioo a b) :=
  ord_connected_Ioo.IsPreconnected

theorem is_preconnected_Ioc : IsPreconnected (Ioc a b) :=
  ord_connected_Ioc.IsPreconnected

theorem is_preconnected_Ico : IsPreconnected (Ico a b) :=
  ord_connected_Ico.IsPreconnected

instance (priority := 100)ordered_connected_space : PreconnectedSpace α :=
  ⟨ord_connected_univ.IsPreconnected⟩

/-- In a dense conditionally complete linear order, the set of preconnected sets is exactly
the set of the intervals `Icc`, `Ico`, `Ioc`, `Ioo`, `Ici`, `Ioi`, `Iic`, `Iio`, `(-∞, +∞)`,
or `∅`. Though one can represent `∅` as `(Inf s, Inf s)`, we include it into the list of
possible cases to improve readability. -/
theorem set_of_is_preconnected_eq_of_ordered :
  { s:Set α | IsPreconnected s } =
    range (uncurry Icc) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range (uncurry Ioo) ∪
      (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅}) :=
  by 
    refine' subset.antisymm set_of_is_preconnected_subset_of_ordered _ 
    simp only [subset_def, -mem_range, forall_range_iff, uncurry, or_imp_distrib, forall_and_distrib, mem_union,
      mem_set_of_eq, insert_eq, mem_singleton_iff, forall_eq, forall_true_iff, and_trueₓ, is_preconnected_Icc,
      is_preconnected_Ico, is_preconnected_Ioc, is_preconnected_Ioo, is_preconnected_Ioi, is_preconnected_Iio,
      is_preconnected_Ici, is_preconnected_Iic, is_preconnected_univ, is_preconnected_empty]

/-!
### Intermediate Value Theorem on an interval

In this section we prove several versions of the Intermediate Value Theorem for a function
continuous on an interval.
-/


variable{δ : Type _}[LinearOrderₓ δ][TopologicalSpace δ][OrderClosedTopology δ]

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, case
`f a ≤ t ≤ f b`.-/
theorem intermediate_value_Icc {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
  Icc (f a) (f b) ⊆ f '' Icc a b :=
  is_preconnected_Icc.intermediate_value (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hf

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, case
`f a ≥ t ≥ f b`.-/
theorem intermediate_value_Icc' {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
  Icc (f b) (f a) ⊆ f '' Icc a b :=
  is_preconnected_Icc.intermediate_value (right_mem_Icc.2 hab) (left_mem_Icc.2 hab) hf

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, unordered case. -/
theorem intermediate_value_interval {a b : α} {f : α → δ} (hf : ContinuousOn f (interval a b)) :
  interval (f a) (f b) ⊆ f '' interval a b :=
  by 
    cases le_totalₓ (f a) (f b) <;> simp [is_preconnected_interval.intermediate_value]

theorem intermediate_value_Ico {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
  Ico (f a) (f b) ⊆ f '' Ico a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he y h => absurd h.2 (not_lt_of_le (he ▸ h.1)))
    fun hlt =>
      @IsPreconnected.intermediate_value_Ico _ _ _ _ _ _ _ is_preconnected_Ico _ _ ⟨refl a, hlt⟩
        (right_nhds_within_Ico_ne_bot hlt) inf_le_right _ (hf.mono Ico_subset_Icc_self) _
        ((hf.continuous_within_at ⟨hab, refl b⟩).mono Ico_subset_Icc_self)

theorem intermediate_value_Ico' {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
  Ioc (f b) (f a) ⊆ f '' Ico a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he y h => absurd h.1 (not_lt_of_le (he ▸ h.2)))
    fun hlt =>
      @IsPreconnected.intermediate_value_Ioc _ _ _ _ _ _ _ is_preconnected_Ico _ _ ⟨refl a, hlt⟩
        (right_nhds_within_Ico_ne_bot hlt) inf_le_right _ (hf.mono Ico_subset_Icc_self) _
        ((hf.continuous_within_at ⟨hab, refl b⟩).mono Ico_subset_Icc_self)

theorem intermediate_value_Ioc {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
  Ioc (f a) (f b) ⊆ f '' Ioc a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he y h => absurd h.2 (not_le_of_lt (he ▸ h.1)))
    fun hlt =>
      @IsPreconnected.intermediate_value_Ioc _ _ _ _ _ _ _ is_preconnected_Ioc _ _ ⟨hlt, refl b⟩
        (left_nhds_within_Ioc_ne_bot hlt) inf_le_right _ (hf.mono Ioc_subset_Icc_self) _
        ((hf.continuous_within_at ⟨refl a, hab⟩).mono Ioc_subset_Icc_self)

theorem intermediate_value_Ioc' {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
  Ico (f b) (f a) ⊆ f '' Ioc a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he y h => absurd h.1 (not_le_of_lt (he ▸ h.2)))
    fun hlt =>
      @IsPreconnected.intermediate_value_Ico _ _ _ _ _ _ _ is_preconnected_Ioc _ _ ⟨hlt, refl b⟩
        (left_nhds_within_Ioc_ne_bot hlt) inf_le_right _ (hf.mono Ioc_subset_Icc_self) _
        ((hf.continuous_within_at ⟨refl a, hab⟩).mono Ioc_subset_Icc_self)

theorem intermediate_value_Ioo {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
  Ioo (f a) (f b) ⊆ f '' Ioo a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he y h => absurd h.2 (not_lt_of_lt (he ▸ h.1)))
    fun hlt =>
      @IsPreconnected.intermediate_value_Ioo _ _ _ _ _ _ _ is_preconnected_Ioo _ _ (left_nhds_within_Ioo_ne_bot hlt)
        (right_nhds_within_Ioo_ne_bot hlt) inf_le_right inf_le_right _ (hf.mono Ioo_subset_Icc_self) _ _
        ((hf.continuous_within_at ⟨refl a, hab⟩).mono Ioo_subset_Icc_self)
        ((hf.continuous_within_at ⟨hab, refl b⟩).mono Ioo_subset_Icc_self)

theorem intermediate_value_Ioo' {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
  Ioo (f b) (f a) ⊆ f '' Ioo a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he y h => absurd h.1 (not_lt_of_lt (he ▸ h.2)))
    fun hlt =>
      @IsPreconnected.intermediate_value_Ioo _ _ _ _ _ _ _ is_preconnected_Ioo _ _ (right_nhds_within_Ioo_ne_bot hlt)
        (left_nhds_within_Ioo_ne_bot hlt) inf_le_right inf_le_right _ (hf.mono Ioo_subset_Icc_self) _ _
        ((hf.continuous_within_at ⟨hab, refl b⟩).mono Ioo_subset_Icc_self)
        ((hf.continuous_within_at ⟨refl a, hab⟩).mono Ioo_subset_Icc_self)

/-- **Intermediate value theorem**: if `f` is continuous on an order-connected set `s` and `a`,
`b` are two points of this set, then `f` sends `s` to a superset of `Icc (f x) (f y)`. -/
theorem ContinuousOn.surj_on_Icc {s : Set α} [hs : ord_connected s] {f : α → δ} (hf : ContinuousOn f s) {a b : α}
  (ha : a ∈ s) (hb : b ∈ s) : surj_on f s (Icc (f a) (f b)) :=
  hs.is_preconnected.intermediate_value ha hb hf

/-- **Intermediate value theorem**: if `f` is continuous on an order-connected set `s` and `a`,
`b` are two points of this set, then `f` sends `s` to a superset of `[f x, f y]`. -/
theorem ContinuousOn.surj_on_interval {s : Set α} [hs : ord_connected s] {f : α → δ} (hf : ContinuousOn f s) {a b : α}
  (ha : a ∈ s) (hb : b ∈ s) : surj_on f s (interval (f a) (f b)) :=
  by 
    cases' le_totalₓ (f a) (f b) with hab hab <;> simp [hf.surj_on_Icc]

/-- A continuous function which tendsto `at_top` `at_top` and to `at_bot` `at_bot` is surjective. -/
theorem Continuous.surjective {f : α → δ} (hf : Continuous f) (h_top : tendsto f at_top at_top)
  (h_bot : tendsto f at_bot at_bot) : Function.Surjective f :=
  fun p =>
    mem_range_of_exists_le_of_exists_ge hf (h_bot.eventually (eventually_le_at_bot p)).exists
      (h_top.eventually (eventually_ge_at_top p)).exists

/-- A continuous function which tendsto `at_bot` `at_top` and to `at_top` `at_bot` is surjective. -/
theorem Continuous.surjective' {f : α → δ} (hf : Continuous f) (h_top : tendsto f at_bot at_top)
  (h_bot : tendsto f at_top at_bot) : Function.Surjective f :=
  @Continuous.surjective (OrderDual α) _ _ _ _ _ _ _ _ _ hf h_top h_bot

-- error in Topology.Algebra.Ordered.IntermediateValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function `f : α → β` is continuous on a nonempty interval `s`, its restriction to `s`
tends to `at_bot : filter β` along `at_bot : filter ↥s` and tends to `at_top : filter β` along
`at_top : filter ↥s`, then the restriction of `f` to `s` is surjective. We formulate the
conclusion as `surj_on f s univ`. -/
theorem continuous_on.surj_on_of_tendsto
{f : α → δ}
{s : set α}
[ord_connected s]
(hs : s.nonempty)
(hf : continuous_on f s)
(hbot : tendsto (λ x : s, f x) at_bot at_bot)
(htop : tendsto (λ x : s, f x) at_top at_top) : surj_on f s univ :=
by haveI [] [] [":=", expr classical.inhabited_of_nonempty hs.to_subtype]; exact [expr «expr $ »(surj_on_iff_surjective.2, (continuous_on_iff_continuous_restrict.1 hf).surjective htop hbot)]

-- error in Topology.Algebra.Ordered.IntermediateValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- If a function `f : α → β` is continuous on a nonempty interval `s`, its restriction to `s`
tends to `at_top : filter β` along `at_bot : filter ↥s` and tends to `at_bot : filter β` along
`at_top : filter ↥s`, then the restriction of `f` to `s` is surjective. We formulate the
conclusion as `surj_on f s univ`. -/
theorem continuous_on.surj_on_of_tendsto'
{f : α → δ}
{s : set α}
[ord_connected s]
(hs : s.nonempty)
(hf : continuous_on f s)
(hbot : tendsto (λ x : s, f x) at_bot at_top)
(htop : tendsto (λ x : s, f x) at_top at_bot) : surj_on f s univ :=
@continuous_on.surj_on_of_tendsto α _ _ _ _ (order_dual δ) _ _ _ _ _ _ hs hf hbot htop

