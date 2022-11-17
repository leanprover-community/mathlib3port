/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Alistair Tucker
-/
import Mathbin.Order.CompleteLatticeIntervals
import Mathbin.Topology.Algebra.Order.Basic

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

open TopologicalSpace Filter

universe u v w

/-!
### Intermediate value theorem on a (pre)connected space

In this section we prove the following theorem (see `is_preconnected.intermediate_value₂`): if `f`
and `g` are two functions continuous on a preconnected set `s`, `f a ≤ g a` at some `a ∈ s` and
`g b ≤ f b` at some `b ∈ s`, then `f c = g c` at some `c ∈ s`. We prove several versions of this
statement, including the classical IVT that corresponds to a constant function `g`.
-/


section

variable {X : Type u} {α : Type v} [TopologicalSpace X] [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]

/-- Intermediate value theorem for two functions: if `f` and `g` are two continuous functions
on a preconnected space and `f a ≤ g a` and `g b ≤ f b`, then for some `x` we have `f x = g x`. -/
theorem intermediate_value_univ₂ [PreconnectedSpace X] {a b : X} {f g : X → α} (hf : Continuous f) (hg : Continuous g)
    (ha : f a ≤ g a) (hb : g b ≤ f b) : ∃ x, f x = g x := by
  obtain ⟨x, h, hfg, hgf⟩ : (univ ∩ { x | f x ≤ g x ∧ g x ≤ f x }).Nonempty
  exact
    is_preconnected_closed_iff.1 PreconnectedSpace.is_preconnected_univ _ _ (isClosedLe hf hg) (isClosedLe hg hf)
      (fun x hx => le_total _ _) ⟨a, trivial, ha⟩ ⟨b, trivial, hb⟩
  exact ⟨x, le_antisymm hfg hgf⟩
#align intermediate_value_univ₂ intermediate_value_univ₂

theorem intermediate_value_univ₂_eventually₁ [PreconnectedSpace X] {a : X} {l : Filter X} [NeBot l] {f g : X → α}
    (hf : Continuous f) (hg : Continuous g) (ha : f a ≤ g a) (he : g ≤ᶠ[l] f) : ∃ x, f x = g x :=
  let ⟨c, hc⟩ := he.Frequently.exists
  intermediate_value_univ₂ hf hg ha hc
#align intermediate_value_univ₂_eventually₁ intermediate_value_univ₂_eventually₁

theorem intermediate_value_univ₂_eventually₂ [PreconnectedSpace X] {l₁ l₂ : Filter X} [NeBot l₁] [NeBot l₂]
    {f g : X → α} (hf : Continuous f) (hg : Continuous g) (he₁ : f ≤ᶠ[l₁] g) (he₂ : g ≤ᶠ[l₂] f) : ∃ x, f x = g x :=
  let ⟨c₁, hc₁⟩ := he₁.Frequently.exists
  let ⟨c₂, hc₂⟩ := he₂.Frequently.exists
  intermediate_value_univ₂ hf hg hc₁ hc₂
#align intermediate_value_univ₂_eventually₂ intermediate_value_univ₂_eventually₂

/-- Intermediate value theorem for two functions: if `f` and `g` are two functions continuous
on a preconnected set `s` and for some `a b ∈ s` we have `f a ≤ g a` and `g b ≤ f b`,
then for some `x ∈ s` we have `f x = g x`. -/
theorem IsPreconnected.intermediate_value₂ {s : Set X} (hs : IsPreconnected s) {a b : X} (ha : a ∈ s) (hb : b ∈ s)
    {f g : X → α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) (ha' : f a ≤ g a) (hb' : g b ≤ f b) :
    ∃ x ∈ s, f x = g x :=
  let ⟨x, hx⟩ :=
    @intermediate_value_univ₂ s α _ _ _ _ (Subtype.preconnected_space hs) ⟨a, ha⟩ ⟨b, hb⟩ _ _
      (continuous_on_iff_continuous_restrict.1 hf) (continuous_on_iff_continuous_restrict.1 hg) ha' hb'
  ⟨x, x.2, hx⟩
#align is_preconnected.intermediate_value₂ IsPreconnected.intermediate_value₂

theorem IsPreconnected.intermediate_value₂_eventually₁ {s : Set X} (hs : IsPreconnected s) {a : X} {l : Filter X}
    (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f g : X → α} (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (ha' : f a ≤ g a) (he : g ≤ᶠ[l] f) : ∃ x ∈ s, f x = g x := by
  rw [continuous_on_iff_continuous_restrict] at hf hg
  obtain ⟨b, h⟩ :=
    @intermediate_value_univ₂_eventually₁ _ _ _ _ _ _ (Subtype.preconnected_space hs) ⟨a, ha⟩ _
      (comap_coe_ne_bot_of_le_principal hl) _ _ hf hg ha' (he.comap _)
  exact ⟨b, b.prop, h⟩
#align is_preconnected.intermediate_value₂_eventually₁ IsPreconnected.intermediate_value₂_eventually₁

theorem IsPreconnected.intermediate_value₂_eventually₂ {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X} [NeBot l₁]
    [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f g : X → α} (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (he₁ : f ≤ᶠ[l₁] g) (he₂ : g ≤ᶠ[l₂] f) : ∃ x ∈ s, f x = g x := by
  rw [continuous_on_iff_continuous_restrict] at hf hg
  obtain ⟨b, h⟩ :=
    @intermediate_value_univ₂_eventually₂ _ _ _ _ _ _ (Subtype.preconnected_space hs) _ _
      (comap_coe_ne_bot_of_le_principal hl₁) (comap_coe_ne_bot_of_le_principal hl₂) _ _ hf hg (he₁.comap _)
      (he₂.comap _)
  exact ⟨b, b.prop, h⟩
#align is_preconnected.intermediate_value₂_eventually₂ IsPreconnected.intermediate_value₂_eventually₂

/-- **Intermediate Value Theorem** for continuous functions on connected sets. -/
theorem IsPreconnected.intermediate_value {s : Set X} (hs : IsPreconnected s) {a b : X} (ha : a ∈ s) (hb : b ∈ s)
    {f : X → α} (hf : ContinuousOn f s) : icc (f a) (f b) ⊆ f '' s := fun x hx =>
  mem_image_iff_bex.2 $ hs.intermediate_value₂ ha hb hf continuous_on_const hx.1 hx.2
#align is_preconnected.intermediate_value IsPreconnected.intermediate_value

theorem IsPreconnected.intermediate_value_Ico {s : Set X} (hs : IsPreconnected s) {a : X} {l : Filter X} (ha : a ∈ s)
    [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α} (ht : Tendsto f l (𝓝 v)) :
    ico (f a) v ⊆ f '' s := fun y h =>
  bex_def.1 $ hs.intermediate_value₂_eventually₁ ha hl hf continuous_on_const h.1 (eventually_ge_of_tendsto_gt h.2 ht)
#align is_preconnected.intermediate_value_Ico IsPreconnected.intermediate_value_Ico

theorem IsPreconnected.intermediate_value_Ioc {s : Set X} (hs : IsPreconnected s) {a : X} {l : Filter X} (ha : a ∈ s)
    [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α} (ht : Tendsto f l (𝓝 v)) :
    ioc v (f a) ⊆ f '' s := fun y h =>
  bex_def.1 $
    (BEx.imp_right fun x _ => Eq.symm) $
      hs.intermediate_value₂_eventually₁ ha hl continuous_on_const hf h.2 (eventually_le_of_tendsto_lt h.1 ht)
#align is_preconnected.intermediate_value_Ioc IsPreconnected.intermediate_value_Ioc

theorem IsPreconnected.intermediate_value_Ioo {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X} [NeBot l₁]
    [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v₁ v₂ : α}
    (ht₁ : Tendsto f l₁ (𝓝 v₁)) (ht₂ : Tendsto f l₂ (𝓝 v₂)) : ioo v₁ v₂ ⊆ f '' s := fun y h =>
  bex_def.1 $
    hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuous_on_const (eventually_le_of_tendsto_lt h.1 ht₁)
      (eventually_ge_of_tendsto_gt h.2 ht₂)
#align is_preconnected.intermediate_value_Ioo IsPreconnected.intermediate_value_Ioo

theorem IsPreconnected.intermediate_value_Ici {s : Set X} (hs : IsPreconnected s) {a : X} {l : Filter X} (ha : a ∈ s)
    [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) (ht : Tendsto f l atTop) : ici (f a) ⊆ f '' s :=
  fun y h => bex_def.1 $ hs.intermediate_value₂_eventually₁ ha hl hf continuous_on_const h (tendsto_at_top.1 ht y)
#align is_preconnected.intermediate_value_Ici IsPreconnected.intermediate_value_Ici

theorem IsPreconnected.intermediate_value_Iic {s : Set X} (hs : IsPreconnected s) {a : X} {l : Filter X} (ha : a ∈ s)
    [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) (ht : Tendsto f l atBot) : iic (f a) ⊆ f '' s :=
  fun y h =>
  bex_def.1 $
    (BEx.imp_right fun x _ => Eq.symm) $
      hs.intermediate_value₂_eventually₁ ha hl continuous_on_const hf h (tendsto_at_bot.1 ht y)
#align is_preconnected.intermediate_value_Iic IsPreconnected.intermediate_value_Iic

theorem IsPreconnected.intermediate_value_Ioi {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X} [NeBot l₁]
    [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α} (ht₁ : Tendsto f l₁ (𝓝 v))
    (ht₂ : Tendsto f l₂ atTop) : ioi v ⊆ f '' s := fun y h =>
  bex_def.1 $
    hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuous_on_const (eventually_le_of_tendsto_lt h ht₁)
      (tendsto_at_top.1 ht₂ y)
#align is_preconnected.intermediate_value_Ioi IsPreconnected.intermediate_value_Ioi

theorem IsPreconnected.intermediate_value_Iio {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X} [NeBot l₁]
    [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α} (ht₁ : Tendsto f l₁ atBot)
    (ht₂ : Tendsto f l₂ (𝓝 v)) : iio v ⊆ f '' s := fun y h =>
  bex_def.1 $
    hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuous_on_const (tendsto_at_bot.1 ht₁ y)
      (eventually_ge_of_tendsto_gt h ht₂)
#align is_preconnected.intermediate_value_Iio IsPreconnected.intermediate_value_Iio

theorem IsPreconnected.intermediate_value_Iii {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X} [NeBot l₁]
    [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) (ht₁ : Tendsto f l₁ atBot)
    (ht₂ : Tendsto f l₂ atTop) : univ ⊆ f '' s := fun y h =>
  bex_def.1 $
    hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuous_on_const (tendsto_at_bot.1 ht₁ y) (tendsto_at_top.1 ht₂ y)
#align is_preconnected.intermediate_value_Iii IsPreconnected.intermediate_value_Iii

/-- **Intermediate Value Theorem** for continuous functions on connected spaces. -/
theorem intermediate_value_univ [PreconnectedSpace X] (a b : X) {f : X → α} (hf : Continuous f) :
    icc (f a) (f b) ⊆ range f := fun x hx => intermediate_value_univ₂ hf continuous_const hx.1 hx.2
#align intermediate_value_univ intermediate_value_univ

/-- **Intermediate Value Theorem** for continuous functions on connected spaces. -/
theorem mem_range_of_exists_le_of_exists_ge [PreconnectedSpace X] {c : α} {f : X → α} (hf : Continuous f)
    (h₁ : ∃ a, f a ≤ c) (h₂ : ∃ b, c ≤ f b) : c ∈ range f :=
  let ⟨a, ha⟩ := h₁
  let ⟨b, hb⟩ := h₂
  intermediate_value_univ a b hf ⟨ha, hb⟩
#align mem_range_of_exists_le_of_exists_ge mem_range_of_exists_le_of_exists_ge

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
    icc a b ⊆ s := by simpa only [image_id] using hs.intermediate_value ha hb continuous_on_id
#align is_preconnected.Icc_subset IsPreconnected.Icc_subset

theorem IsPreconnected.ord_connected {s : Set α} (h : IsPreconnected s) : OrdConnected s :=
  ⟨fun x hx y hy => h.Icc_subset hx hy⟩
#align is_preconnected.ord_connected IsPreconnected.ord_connected

/-- If a preconnected set contains endpoints of an interval, then it includes the whole interval. -/
theorem IsConnected.Icc_subset {s : Set α} (hs : IsConnected s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : icc a b ⊆ s :=
  hs.2.Icc_subset ha hb
#align is_connected.Icc_subset IsConnected.Icc_subset

/-- If preconnected set in a linear order space is unbounded below and above, then it is the whole
space. -/
theorem IsPreconnected.eq_univ_of_unbounded {s : Set α} (hs : IsPreconnected s) (hb : ¬BddBelow s) (ha : ¬BddAbove s) :
    s = univ := by
  refine' eq_univ_of_forall fun x => _
  obtain ⟨y, ys, hy⟩ : ∃ y ∈ s, y < x := not_bdd_below_iff.1 hb x
  obtain ⟨z, zs, hz⟩ : ∃ z ∈ s, x < z := not_bdd_above_iff.1 ha x
  exact hs.Icc_subset ys zs ⟨le_of_lt hy, le_of_lt hz⟩
#align is_preconnected.eq_univ_of_unbounded IsPreconnected.eq_univ_of_unbounded

end

variable {α : Type u} {β : Type v} {γ : Type w} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] [Nonempty γ]

/-- A bounded connected subset of a conditionally complete linear order includes the open interval
`(Inf s, Sup s)`. -/
theorem IsConnected.Ioo_cInf_cSup_subset {s : Set α} (hs : IsConnected s) (hb : BddBelow s) (ha : BddAbove s) :
    ioo (inf s) (sup s) ⊆ s := fun x hx =>
  let ⟨y, ys, hy⟩ := (is_glb_lt_iff (is_glb_cInf hs.Nonempty hb)).1 hx.1
  let ⟨z, zs, hz⟩ := (lt_is_lub_iff (is_lub_cSup hs.Nonempty ha)).1 hx.2
  hs.Icc_subset ys zs ⟨le_of_lt hy, le_of_lt hz⟩
#align is_connected.Ioo_cInf_cSup_subset IsConnected.Ioo_cInf_cSup_subset

theorem eq_Icc_cInf_cSup_of_connected_bdd_closed {s : Set α} (hc : IsConnected s) (hb : BddBelow s) (ha : BddAbove s)
    (hcl : IsClosed s) : s = icc (inf s) (sup s) :=
  Subset.antisymm (subset_Icc_cInf_cSup hb ha) $
    hc.Icc_subset (hcl.cInf_mem hc.Nonempty hb) (hcl.cSup_mem hc.Nonempty ha)
#align eq_Icc_cInf_cSup_of_connected_bdd_closed eq_Icc_cInf_cSup_of_connected_bdd_closed

theorem IsPreconnected.Ioi_cInf_subset {s : Set α} (hs : IsPreconnected s) (hb : BddBelow s) (ha : ¬BddAbove s) :
    ioi (inf s) ⊆ s := by
  have sne : s.nonempty := @nonempty_of_not_bdd_above α _ s ⟨Inf ∅⟩ ha
  intro x hx
  obtain ⟨y, ys, hy⟩ : ∃ y ∈ s, y < x := (is_glb_lt_iff (is_glb_cInf sne hb)).1 hx
  obtain ⟨z, zs, hz⟩ : ∃ z ∈ s, x < z := not_bdd_above_iff.1 ha x
  exact hs.Icc_subset ys zs ⟨le_of_lt hy, le_of_lt hz⟩
#align is_preconnected.Ioi_cInf_subset IsPreconnected.Ioi_cInf_subset

theorem IsPreconnected.Iio_cSup_subset {s : Set α} (hs : IsPreconnected s) (hb : ¬BddBelow s) (ha : BddAbove s) :
    iio (sup s) ⊆ s :=
  @IsPreconnected.Ioi_cInf_subset αᵒᵈ _ _ _ s hs ha hb
#align is_preconnected.Iio_cSup_subset IsPreconnected.Iio_cSup_subset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:38: in apply_rules #[["[", expr or.inr, ",", expr mem_singleton, "]"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error -/
/-- A preconnected set in a conditionally complete linear order is either one of the intervals
`[Inf s, Sup s]`, `[Inf s, Sup s)`, `(Inf s, Sup s]`, `(Inf s, Sup s)`, `[Inf s, +∞)`,
`(Inf s, +∞)`, `(-∞, Sup s]`, `(-∞, Sup s)`, `(-∞, +∞)`, or `∅`. The converse statement requires
`α` to be densely ordererd. -/
theorem IsPreconnected.mem_intervals {s : Set α} (hs : IsPreconnected s) :
    s ∈
      ({icc (inf s) (sup s), ico (inf s) (sup s), ioc (inf s) (sup s), ioo (inf s) (sup s), ici (inf s), ioi (inf s),
          iic (sup s), iio (sup s), univ, ∅} :
        Set (Set α)) :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:38: in apply_rules #[[\"[\", expr or.inr, \",\", expr mem_singleton, \"]\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error"
    
  have hs' : IsConnected s := ⟨hne, hs⟩
  by_cases hb:BddBelow s <;> by_cases ha:BddAbove s
  · rcases mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset (hs'.Ioo_cInf_cSup_subset hb ha) (subset_Icc_cInf_cSup hb ha) with
      (hs | hs | hs | hs)
    · exact Or.inl hs
      
    · exact Or.inr $ Or.inl hs
      
    · exact Or.inr $ Or.inr $ Or.inl hs
      
    · exact Or.inr $ Or.inr $ Or.inr $ Or.inl hs
      
    
  · refine' Or.inr $ Or.inr $ Or.inr $ Or.inr _
    cases' mem_Ici_Ioi_of_subset_of_subset (hs.Ioi_cInf_subset hb ha) fun x hx => cInf_le hb hx with hs hs
    · exact Or.inl hs
      
    · exact Or.inr (Or.inl hs)
      
    
  · iterate 6 apply Or.inr
    cases' mem_Iic_Iio_of_subset_of_subset (hs.Iio_cSup_subset hb ha) fun x hx => le_cSup ha hx with hs hs
    · exact Or.inl hs
      
    · exact Or.inr (Or.inl hs)
      
    
  · iterate 8 apply Or.inr
    exact Or.inl (hs.eq_univ_of_unbounded hb ha)
    
#align is_preconnected.mem_intervals IsPreconnected.mem_intervals

/-- A preconnected set is either one of the intervals `Icc`, `Ico`, `Ioc`, `Ioo`, `Ici`, `Ioi`,
`Iic`, `Iio`, or `univ`, or `∅`. The converse statement requires `α` to be densely ordered. Though
one can represent `∅` as `(Inf s, Inf s)`, we include it into the list of possible cases to improve
readability. -/
theorem set_of_is_preconnected_subset_of_ordered :
    { s : Set α | IsPreconnected s } ⊆-- bounded intervals
                range
                (uncurry icc) ∪
              range (uncurry ico) ∪
            range (uncurry ioc) ∪
          range (uncurry ioo) ∪
        (-- unbounded intervals and `univ`
                  range
                  ici ∪
                range ioi ∪
              range iic ∪
            range iio ∪
          {univ, ∅}) :=
  by
  intro s hs
  rcases hs.mem_intervals with (hs | hs | hs | hs | hs | hs | hs | hs | hs | hs)
  · exact Or.inl $ Or.inl $ Or.inl $ Or.inl ⟨(Inf s, Sup s), hs.symm⟩
    
  · exact Or.inl $ Or.inl $ Or.inl $ Or.inr ⟨(Inf s, Sup s), hs.symm⟩
    
  · exact Or.inl $ Or.inl $ Or.inr ⟨(Inf s, Sup s), hs.symm⟩
    
  · exact Or.inl $ Or.inr ⟨(Inf s, Sup s), hs.symm⟩
    
  · exact Or.inr $ Or.inl $ Or.inl $ Or.inl $ Or.inl ⟨Inf s, hs.symm⟩
    
  · exact Or.inr $ Or.inl $ Or.inl $ Or.inl $ Or.inr ⟨Inf s, hs.symm⟩
    
  · exact Or.inr $ Or.inl $ Or.inl $ Or.inr ⟨Sup s, hs.symm⟩
    
  · exact Or.inr $ Or.inl $ Or.inr ⟨Sup s, hs.symm⟩
    
  · exact Or.inr $ Or.inr $ Or.inl hs
    
  · exact Or.inr $ Or.inr $ Or.inr hs
    
#align set_of_is_preconnected_subset_of_ordered set_of_is_preconnected_subset_of_ordered

/-!
### Intervals are connected

In this section we prove that a closed interval (hence, any `ord_connected` set) in a dense
conditionally complete linear order is preconnected.
-/


/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and the set `s ∩ [a, b)` has no maximal point, then `b ∈ s`. -/
theorem IsClosed.mem_of_ge_of_forall_exists_gt {a b : α} {s : Set α} (hs : IsClosed (s ∩ icc a b)) (ha : a ∈ s)
    (hab : a ≤ b) (hgt : ∀ x ∈ s ∩ ico a b, (s ∩ ioc x b).Nonempty) : b ∈ s := by
  let S := s ∩ Icc a b
  replace ha : a ∈ S
  exact ⟨ha, left_mem_Icc.2 hab⟩
  have Sbd : BddAbove S := ⟨b, fun z hz => hz.2.2⟩
  let c := Sup (s ∩ Icc a b)
  have c_mem : c ∈ S := hs.cSup_mem ⟨_, ha⟩ Sbd
  have c_le : c ≤ b := cSup_le ⟨_, ha⟩ fun x hx => hx.2.2
  cases' eq_or_lt_of_le c_le with hc hc
  exact hc ▸ c_mem.1
  exfalso
  rcases hgt c ⟨c_mem.1, c_mem.2.1, hc⟩ with ⟨x, xs, cx, xb⟩
  exact not_lt_of_le (le_cSup Sbd ⟨xs, le_trans (le_cSup Sbd ha) (le_of_lt cx), xb⟩) cx
#align is_closed.mem_of_ge_of_forall_exists_gt IsClosed.mem_of_ge_of_forall_exists_gt

/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and for any `a ≤ x < y ≤ b`, `x ∈ s`, the set `s ∩ (x, y]`
is not empty, then `[a, b] ⊆ s`. -/
theorem IsClosed.Icc_subset_of_forall_exists_gt {a b : α} {s : Set α} (hs : IsClosed (s ∩ icc a b)) (ha : a ∈ s)
    (hgt : ∀ x ∈ s ∩ ico a b, ∀ y ∈ ioi x, (s ∩ ioc x y).Nonempty) : icc a b ⊆ s := by
  intro y hy
  have : IsClosed (s ∩ Icc a y) := by
    suffices s ∩ Icc a y = s ∩ Icc a b ∩ Icc a y by
      rw [this]
      exact IsClosed.inter hs isClosedIcc
    rw [inter_assoc]
    congr
    exact (inter_eq_self_of_subset_right $ Icc_subset_Icc_right hy.2).symm
  exact
    IsClosed.mem_of_ge_of_forall_exists_gt this ha hy.1 fun x hx =>
      hgt x ⟨hx.1, Ico_subset_Ico_right hy.2 hx.2⟩ y hx.2.2
#align is_closed.Icc_subset_of_forall_exists_gt IsClosed.Icc_subset_of_forall_exists_gt

variable [DenselyOrdered α] {a b : α}

/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and for any `x ∈ s ∩ [a, b)` the set `s` includes some open
neighborhood of `x` within `(x, +∞)`, then `[a, b] ⊆ s`. -/
theorem IsClosed.Icc_subset_of_forall_mem_nhds_within {a b : α} {s : Set α} (hs : IsClosed (s ∩ icc a b)) (ha : a ∈ s)
    (hgt : ∀ x ∈ s ∩ ico a b, s ∈ 𝓝[>] x) : icc a b ⊆ s := by
  apply hs.Icc_subset_of_forall_exists_gt ha
  rintro x ⟨hxs, hxab⟩ y hyxb
  have : s ∩ Ioc x y ∈ 𝓝[>] x := inter_mem (hgt x ⟨hxs, hxab⟩) (Ioc_mem_nhds_within_Ioi ⟨le_rfl, hyxb⟩)
  exact (nhdsWithinIoiSelfNeBot' ⟨b, hxab.2⟩).nonempty_of_mem this
#align is_closed.Icc_subset_of_forall_mem_nhds_within IsClosed.Icc_subset_of_forall_mem_nhds_within

theorem is_preconnected_Icc_aux (x y : α) (s t : Set α) (hxy : x ≤ y) (hs : IsClosed s) (ht : IsClosed t)
    (hab : icc a b ⊆ s ∪ t) (hx : x ∈ icc a b ∩ s) (hy : y ∈ icc a b ∩ t) : (icc a b ∩ (s ∩ t)).Nonempty := by
  have xyab : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1.1 hy.1.2
  by_contra hst
  suffices : Icc x y ⊆ s
  exact hst ⟨y, xyab $ right_mem_Icc.2 hxy, this $ right_mem_Icc.2 hxy, hy.2⟩
  apply (IsClosed.inter hs isClosedIcc).Icc_subset_of_forall_mem_nhds_within hx.2
  rintro z ⟨zs, hz⟩
  have zt : z ∈ tᶜ := fun zt => hst ⟨z, xyab $ Ico_subset_Icc_self hz, zs, zt⟩
  have : tᶜ ∩ Ioc z y ∈ 𝓝[>] z := by
    rw [← nhds_within_Ioc_eq_nhds_within_Ioi hz.2]
    exact mem_nhds_within.2 ⟨tᶜ, ht.is_open_compl, zt, subset.refl _⟩
  apply mem_of_superset this
  have : Ioc z y ⊆ s ∪ t := fun w hw => hab (xyab ⟨le_trans hz.1 (le_of_lt hw.1), hw.2⟩)
  exact fun w ⟨wt, wzy⟩ => (this wzy).elim id fun h => (wt h).elim
#align is_preconnected_Icc_aux is_preconnected_Icc_aux

/-- A closed interval in a densely ordered conditionally complete linear order is preconnected. -/
theorem is_preconnected_Icc : IsPreconnected (icc a b) :=
  is_preconnected_closed_iff.2
    (by
      rintro s t hs ht hab ⟨x, hx⟩ ⟨y, hy⟩
      -- This used to use `wlog`, but it was causing timeouts.
      cases le_total x y
      · exact is_preconnected_Icc_aux x y s t h hs ht hab hx hy
        
      · rw [inter_comm s t]
        rw [union_comm s t] at hab
        exact is_preconnected_Icc_aux y x t s h ht hs hab hy hx
        )
#align is_preconnected_Icc is_preconnected_Icc

theorem is_preconnected_interval : IsPreconnected (interval a b) :=
  is_preconnected_Icc
#align is_preconnected_interval is_preconnected_interval

theorem Set.OrdConnected.is_preconnected {s : Set α} (h : s.OrdConnected) : IsPreconnected s :=
  is_preconnected_of_forall_pair $ fun x hx y hy =>
    ⟨interval x y, h.interval_subset hx hy, left_mem_interval, right_mem_interval, is_preconnected_interval⟩
#align set.ord_connected.is_preconnected Set.OrdConnected.is_preconnected

theorem is_preconnected_iff_ord_connected {s : Set α} : IsPreconnected s ↔ OrdConnected s :=
  ⟨IsPreconnected.ord_connected, Set.OrdConnected.is_preconnected⟩
#align is_preconnected_iff_ord_connected is_preconnected_iff_ord_connected

theorem is_preconnected_Ici : IsPreconnected (ici a) :=
  ord_connected_Ici.IsPreconnected
#align is_preconnected_Ici is_preconnected_Ici

theorem is_preconnected_Iic : IsPreconnected (iic a) :=
  ord_connected_Iic.IsPreconnected
#align is_preconnected_Iic is_preconnected_Iic

theorem is_preconnected_Iio : IsPreconnected (iio a) :=
  ord_connected_Iio.IsPreconnected
#align is_preconnected_Iio is_preconnected_Iio

theorem is_preconnected_Ioi : IsPreconnected (ioi a) :=
  ord_connected_Ioi.IsPreconnected
#align is_preconnected_Ioi is_preconnected_Ioi

theorem is_preconnected_Ioo : IsPreconnected (ioo a b) :=
  ord_connected_Ioo.IsPreconnected
#align is_preconnected_Ioo is_preconnected_Ioo

theorem is_preconnected_Ioc : IsPreconnected (ioc a b) :=
  ord_connected_Ioc.IsPreconnected
#align is_preconnected_Ioc is_preconnected_Ioc

theorem is_preconnected_Ico : IsPreconnected (ico a b) :=
  ord_connected_Ico.IsPreconnected
#align is_preconnected_Ico is_preconnected_Ico

theorem is_connected_Ici : IsConnected (ici a) :=
  ⟨nonempty_Ici, is_preconnected_Ici⟩
#align is_connected_Ici is_connected_Ici

theorem is_connected_Iic : IsConnected (iic a) :=
  ⟨nonempty_Iic, is_preconnected_Iic⟩
#align is_connected_Iic is_connected_Iic

theorem is_connected_Ioi [NoMaxOrder α] : IsConnected (ioi a) :=
  ⟨nonempty_Ioi, is_preconnected_Ioi⟩
#align is_connected_Ioi is_connected_Ioi

theorem is_connected_Iio [NoMinOrder α] : IsConnected (iio a) :=
  ⟨nonempty_Iio, is_preconnected_Iio⟩
#align is_connected_Iio is_connected_Iio

theorem is_connected_Icc (h : a ≤ b) : IsConnected (icc a b) :=
  ⟨nonempty_Icc.2 h, is_preconnected_Icc⟩
#align is_connected_Icc is_connected_Icc

theorem is_connected_Ioo (h : a < b) : IsConnected (ioo a b) :=
  ⟨nonempty_Ioo.2 h, is_preconnected_Ioo⟩
#align is_connected_Ioo is_connected_Ioo

theorem is_connected_Ioc (h : a < b) : IsConnected (ioc a b) :=
  ⟨nonempty_Ioc.2 h, is_preconnected_Ioc⟩
#align is_connected_Ioc is_connected_Ioc

theorem is_connected_Ico (h : a < b) : IsConnected (ico a b) :=
  ⟨nonempty_Ico.2 h, is_preconnected_Ico⟩
#align is_connected_Ico is_connected_Ico

instance (priority := 100) ordered_connected_space : PreconnectedSpace α :=
  ⟨ord_connected_univ.IsPreconnected⟩
#align ordered_connected_space ordered_connected_space

/-- In a dense conditionally complete linear order, the set of preconnected sets is exactly
the set of the intervals `Icc`, `Ico`, `Ioc`, `Ioo`, `Ici`, `Ioi`, `Iic`, `Iio`, `(-∞, +∞)`,
or `∅`. Though one can represent `∅` as `(Inf s, Inf s)`, we include it into the list of
possible cases to improve readability. -/
theorem set_of_is_preconnected_eq_of_ordered :
    { s : Set α | IsPreconnected s } =-- bounded intervals
                range
                (uncurry icc) ∪
              range (uncurry ico) ∪
            range (uncurry ioc) ∪
          range (uncurry ioo) ∪
        (-- unbounded intervals and `univ`
                  range
                  ici ∪
                range ioi ∪
              range iic ∪
            range iio ∪
          {univ, ∅}) :=
  by
  refine' subset.antisymm set_of_is_preconnected_subset_of_ordered _
  simp only [subset_def, -mem_range, forall_range_iff, uncurry, or_imp, forall_and, mem_union, mem_set_of_eq, insert_eq,
    mem_singleton_iff, forall_eq, forall_true_iff, and_true_iff, is_preconnected_Icc, is_preconnected_Ico,
    is_preconnected_Ioc, is_preconnected_Ioo, is_preconnected_Ioi, is_preconnected_Iio, is_preconnected_Ici,
    is_preconnected_Iic, is_preconnected_univ, is_preconnected_empty]
#align set_of_is_preconnected_eq_of_ordered set_of_is_preconnected_eq_of_ordered

/-!
### Intermediate Value Theorem on an interval

In this section we prove several versions of the Intermediate Value Theorem for a function
continuous on an interval.
-/


variable {δ : Type _} [LinearOrder δ] [TopologicalSpace δ] [OrderClosedTopology δ]

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, case
`f a ≤ t ≤ f b`.-/
theorem intermediate_value_Icc {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (icc a b)) :
    icc (f a) (f b) ⊆ f '' icc a b :=
  is_preconnected_Icc.intermediate_value (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hf
#align intermediate_value_Icc intermediate_value_Icc

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, case
`f a ≥ t ≥ f b`.-/
theorem intermediate_value_Icc' {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (icc a b)) :
    icc (f b) (f a) ⊆ f '' icc a b :=
  is_preconnected_Icc.intermediate_value (right_mem_Icc.2 hab) (left_mem_Icc.2 hab) hf
#align intermediate_value_Icc' intermediate_value_Icc'

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, unordered case. -/
theorem intermediate_value_interval {a b : α} {f : α → δ} (hf : ContinuousOn f (interval a b)) :
    interval (f a) (f b) ⊆ f '' interval a b := by
  cases le_total (f a) (f b) <;> simp [*, is_preconnected_interval.intermediate_value]
#align intermediate_value_interval intermediate_value_interval

theorem intermediate_value_Ico {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (icc a b)) :
    ico (f a) (f b) ⊆ f '' ico a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he y h => absurd h.2 (not_lt_of_le (he ▸ h.1))) fun hlt =>
    @IsPreconnected.intermediate_value_Ico _ _ _ _ _ _ _ is_preconnected_Ico _ _ ⟨refl a, hlt⟩
      (rightNhdsWithinIcoNeBot hlt) inf_le_right _ (hf.mono Ico_subset_Icc_self) _
      ((hf.ContinuousWithinAt ⟨hab, refl b⟩).mono Ico_subset_Icc_self)
#align intermediate_value_Ico intermediate_value_Ico

theorem intermediate_value_Ico' {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (icc a b)) :
    ioc (f b) (f a) ⊆ f '' ico a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he y h => absurd h.1 (not_lt_of_le (he ▸ h.2))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioc _ _ _ _ _ _ _ is_preconnected_Ico _ _ ⟨refl a, hlt⟩
      (rightNhdsWithinIcoNeBot hlt) inf_le_right _ (hf.mono Ico_subset_Icc_self) _
      ((hf.ContinuousWithinAt ⟨hab, refl b⟩).mono Ico_subset_Icc_self)
#align intermediate_value_Ico' intermediate_value_Ico'

theorem intermediate_value_Ioc {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (icc a b)) :
    ioc (f a) (f b) ⊆ f '' ioc a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he y h => absurd h.2 (not_le_of_lt (he ▸ h.1))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioc _ _ _ _ _ _ _ is_preconnected_Ioc _ _ ⟨hlt, refl b⟩
      (leftNhdsWithinIocNeBot hlt) inf_le_right _ (hf.mono Ioc_subset_Icc_self) _
      ((hf.ContinuousWithinAt ⟨refl a, hab⟩).mono Ioc_subset_Icc_self)
#align intermediate_value_Ioc intermediate_value_Ioc

theorem intermediate_value_Ioc' {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (icc a b)) :
    ico (f b) (f a) ⊆ f '' ioc a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he y h => absurd h.1 (not_le_of_lt (he ▸ h.2))) fun hlt =>
    @IsPreconnected.intermediate_value_Ico _ _ _ _ _ _ _ is_preconnected_Ioc _ _ ⟨hlt, refl b⟩
      (leftNhdsWithinIocNeBot hlt) inf_le_right _ (hf.mono Ioc_subset_Icc_self) _
      ((hf.ContinuousWithinAt ⟨refl a, hab⟩).mono Ioc_subset_Icc_self)
#align intermediate_value_Ioc' intermediate_value_Ioc'

theorem intermediate_value_Ioo {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (icc a b)) :
    ioo (f a) (f b) ⊆ f '' ioo a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he y h => absurd h.2 (not_lt_of_lt (he ▸ h.1))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioo _ _ _ _ _ _ _ is_preconnected_Ioo _ _ (leftNhdsWithinIooNeBot hlt)
      (rightNhdsWithinIooNeBot hlt) inf_le_right inf_le_right _ (hf.mono Ioo_subset_Icc_self) _ _
      ((hf.ContinuousWithinAt ⟨refl a, hab⟩).mono Ioo_subset_Icc_self)
      ((hf.ContinuousWithinAt ⟨hab, refl b⟩).mono Ioo_subset_Icc_self)
#align intermediate_value_Ioo intermediate_value_Ioo

theorem intermediate_value_Ioo' {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (icc a b)) :
    ioo (f b) (f a) ⊆ f '' ioo a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he y h => absurd h.1 (not_lt_of_lt (he ▸ h.2))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioo _ _ _ _ _ _ _ is_preconnected_Ioo _ _ (rightNhdsWithinIooNeBot hlt)
      (leftNhdsWithinIooNeBot hlt) inf_le_right inf_le_right _ (hf.mono Ioo_subset_Icc_self) _ _
      ((hf.ContinuousWithinAt ⟨hab, refl b⟩).mono Ioo_subset_Icc_self)
      ((hf.ContinuousWithinAt ⟨refl a, hab⟩).mono Ioo_subset_Icc_self)
#align intermediate_value_Ioo' intermediate_value_Ioo'

/-- **Intermediate value theorem**: if `f` is continuous on an order-connected set `s` and `a`,
`b` are two points of this set, then `f` sends `s` to a superset of `Icc (f x) (f y)`. -/
theorem ContinuousOn.surj_on_Icc {s : Set α} [hs : OrdConnected s] {f : α → δ} (hf : ContinuousOn f s) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) : SurjOn f s (icc (f a) (f b)) :=
  hs.IsPreconnected.intermediate_value ha hb hf
#align continuous_on.surj_on_Icc ContinuousOn.surj_on_Icc

/-- **Intermediate value theorem**: if `f` is continuous on an order-connected set `s` and `a`,
`b` are two points of this set, then `f` sends `s` to a superset of `[f x, f y]`. -/
theorem ContinuousOn.surj_on_interval {s : Set α} [hs : OrdConnected s] {f : α → δ} (hf : ContinuousOn f s) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) : SurjOn f s (interval (f a) (f b)) := by
  cases' le_total (f a) (f b) with hab hab <;> simp [hf.surj_on_Icc, *]
#align continuous_on.surj_on_interval ContinuousOn.surj_on_interval

/-- A continuous function which tendsto `at_top` `at_top` and to `at_bot` `at_bot` is surjective. -/
theorem Continuous.surjective {f : α → δ} (hf : Continuous f) (h_top : Tendsto f atTop atTop)
    (h_bot : Tendsto f atBot atBot) : Function.Surjective f := fun p =>
  mem_range_of_exists_le_of_exists_ge hf (h_bot.Eventually (eventually_le_at_bot p)).exists
    (h_top.Eventually (eventually_ge_at_top p)).exists
#align continuous.surjective Continuous.surjective

/-- A continuous function which tendsto `at_bot` `at_top` and to `at_top` `at_bot` is surjective. -/
theorem Continuous.surjective' {f : α → δ} (hf : Continuous f) (h_top : Tendsto f atBot atTop)
    (h_bot : Tendsto f atTop atBot) : Function.Surjective f :=
  @Continuous.surjective αᵒᵈ _ _ _ _ _ _ _ _ _ hf h_top h_bot
#align continuous.surjective' Continuous.surjective'

/-- If a function `f : α → β` is continuous on a nonempty interval `s`, its restriction to `s`
tends to `at_bot : filter β` along `at_bot : filter ↥s` and tends to `at_top : filter β` along
`at_top : filter ↥s`, then the restriction of `f` to `s` is surjective. We formulate the
conclusion as `surj_on f s univ`. -/
theorem ContinuousOn.surj_on_of_tendsto {f : α → δ} {s : Set α} [OrdConnected s] (hs : s.Nonempty)
    (hf : ContinuousOn f s) (hbot : Tendsto (fun x : s => f x) atBot atBot)
    (htop : Tendsto (fun x : s => f x) atTop atTop) : SurjOn f s univ :=
  haveI := Classical.inhabitedOfNonempty hs.to_subtype
  surj_on_iff_surjective.2 $ (continuous_on_iff_continuous_restrict.1 hf).Surjective htop hbot
#align continuous_on.surj_on_of_tendsto ContinuousOn.surj_on_of_tendsto

/-- If a function `f : α → β` is continuous on a nonempty interval `s`, its restriction to `s`
tends to `at_top : filter β` along `at_bot : filter ↥s` and tends to `at_bot : filter β` along
`at_top : filter ↥s`, then the restriction of `f` to `s` is surjective. We formulate the
conclusion as `surj_on f s univ`. -/
theorem ContinuousOn.surj_on_of_tendsto' {f : α → δ} {s : Set α} [OrdConnected s] (hs : s.Nonempty)
    (hf : ContinuousOn f s) (hbot : Tendsto (fun x : s => f x) atBot atTop)
    (htop : Tendsto (fun x : s => f x) atTop atBot) : SurjOn f s univ :=
  @ContinuousOn.surj_on_of_tendsto α _ _ _ _ δᵒᵈ _ _ _ _ _ _ hs hf hbot htop
#align continuous_on.surj_on_of_tendsto' ContinuousOn.surj_on_of_tendsto'

