/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
import Mathbin.Topology.Algebra.Order.IntermediateValue

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
class CompactIccSpace (α : Type _) [TopologicalSpace α] [Preorderₓ α] : Prop where
  is_compact_Icc : ∀ {a b : α}, IsCompact (Icc a b)

export CompactIccSpace (is_compact_Icc)

/-- A closed interval in a conditionally complete linear order is compact. -/
instance (priority := 100) ConditionallyCompleteLinearOrder.to_compact_Icc_space (α : Type _)
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] : CompactIccSpace α := by
  refine' ⟨fun a b => _⟩
  cases' le_or_ltₓ a b with hab hab
  swap
  · simp [hab]
    
  refine' is_compact_iff_ultrafilter_le_nhds.2 fun f hf => _
  contrapose! hf
  rw [le_principal_iff]
  have hpt : ∀, ∀ x ∈ Icc a b, ∀, {x} ∉ f := fun x hx hxf => hf x hx ((le_pure_iff.2 hxf).trans (pure_le_nhds x))
  set s := { x ∈ Icc a b | Icc a x ∉ f }
  have hsb : b ∈ UpperBounds s := fun x hx => hx.1.2
  have sbd : BddAbove s := ⟨b, hsb⟩
  have ha : a ∈ s := by
    simp [hpt, hab]
  rcases hab.eq_or_lt with (rfl | hlt)
  · exact ha.2
    
  set c := Sup s
  have hsc : IsLub s c := is_lub_cSup ⟨a, ha⟩ sbd
  have hc : c ∈ Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  specialize hf c hc
  have hcs : c ∈ s := by
    cases' hc.1.eq_or_lt with heq hlt
    · rwa [← HEq]
      
    refine' ⟨hc, fun hcf => hf fun U hU => _⟩
    rcases(mem_nhds_within_Iic_iff_exists_Ioc_subset' hlt).1 (mem_nhds_within_of_mem_nhds hU) with ⟨x, hxc, hxU⟩
    rcases((hsc.frequently_mem ⟨a, ha⟩).and_eventually (Ioc_mem_nhds_within_Iic ⟨hxc, le_rfl⟩)).exists with
      ⟨y, ⟨hyab, hyf⟩, hy⟩
    refine' mem_of_superset (f.diff_mem_iff.2 ⟨hcf, hyf⟩) (subset.trans _ hxU)
    rw [diff_subset_iff]
    exact subset.trans Icc_subset_Icc_union_Ioc (union_subset_union subset.rfl <| Ioc_subset_Ioc_left hy.1.le)
  cases' hc.2.eq_or_lt with heq hlt
  · rw [← HEq]
    exact hcs.2
    
  contrapose! hf
  intro U hU
  rcases(mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset hlt).1 (mem_nhds_within_of_mem_nhds hU) with ⟨y, hxy, hyU⟩
  refine' mem_of_superset _ hyU
  clear! U
  have hy : y ∈ Icc a b := ⟨hc.1.trans hxy.1.le, hxy.2⟩
  by_cases' hay : Icc a y ∈ f
  · refine' mem_of_superset (f.diff_mem_iff.2 ⟨f.diff_mem_iff.2 ⟨hay, hcs.2⟩, hpt y hy⟩) _
    rw [diff_subset_iff, union_comm, Ico_union_right hxy.1.le, diff_subset_iff]
    exact Icc_subset_Icc_union_Icc
    
  · exact ((hsc.1 ⟨hy, hay⟩).not_lt hxy.1).elim
    

instance {ι : Type _} {α : ι → Type _} [∀ i, Preorderₓ (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, CompactIccSpace (α i)] : CompactIccSpace (∀ i, α i) :=
  ⟨fun a b => (pi_univ_Icc a b ▸ is_compact_univ_pi) fun i => is_compact_Icc⟩

instance Pi.compact_Icc_space' {α β : Type _} [Preorderₓ β] [TopologicalSpace β] [CompactIccSpace β] :
    CompactIccSpace (α → β) :=
  Pi.compact_Icc_space

instance {α β : Type _} [Preorderₓ α] [TopologicalSpace α] [CompactIccSpace α] [Preorderₓ β] [TopologicalSpace β]
    [CompactIccSpace β] : CompactIccSpace (α × β) :=
  ⟨fun a b => (Icc_prod_eq a b).symm ▸ is_compact_Icc.Prod is_compact_Icc⟩

/-- An unordered closed interval is compact. -/
theorem is_compact_interval {α : Type _} [LinearOrderₓ α] [TopologicalSpace α] [CompactIccSpace α] {a b : α} :
    IsCompact (Interval a b) :=
  is_compact_Icc

/-- A complete linear order is a compact space.

We do not register an instance for a `[compact_Icc_space α]` because this would only add instances
for products (indexed or not) of complete linear orders, and we have instances with higher priority
that cover these cases. -/
-- See note [lower instance priority]
instance (priority := 100) compact_space_of_complete_linear_order {α : Type _} [CompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] : CompactSpace α :=
  ⟨by
    simp only [← Icc_bot_top, is_compact_Icc]⟩

section

variable {α : Type _} [Preorderₓ α] [TopologicalSpace α] [CompactIccSpace α]

instance compact_space_Icc (a b : α) : CompactSpace (Icc a b) :=
  is_compact_iff_compact_space.mp is_compact_Icc

end

/-!
### Min and max elements of a compact set
-/


variable {α β : Type _} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [TopologicalSpace β]

theorem IsCompact.Inf_mem {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : inf s ∈ s :=
  hs.IsClosed.cInf_mem ne_s hs.BddBelow

theorem IsCompact.Sup_mem {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : sup s ∈ s :=
  @IsCompact.Inf_mem (OrderDual α) _ _ _ _ hs ne_s

theorem IsCompact.is_glb_Inf {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsGlb s (inf s) :=
  is_glb_cInf ne_s hs.BddBelow

theorem IsCompact.is_lub_Sup {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsLub s (sup s) :=
  @IsCompact.is_glb_Inf (OrderDual α) _ _ _ _ hs ne_s

theorem IsCompact.is_least_Inf {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsLeast s (inf s) :=
  ⟨hs.Inf_mem ne_s, (hs.is_glb_Inf ne_s).1⟩

theorem IsCompact.is_greatest_Sup {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsGreatest s (sup s) :=
  @IsCompact.is_least_Inf (OrderDual α) _ _ _ _ hs ne_s

theorem IsCompact.exists_is_least {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : ∃ x, IsLeast s x :=
  ⟨_, hs.is_least_Inf ne_s⟩

theorem IsCompact.exists_is_greatest {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : ∃ x, IsGreatest s x :=
  ⟨_, hs.is_greatest_Sup ne_s⟩

theorem IsCompact.exists_is_glb {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : ∃ x ∈ s, IsGlb s x :=
  ⟨_, hs.Inf_mem ne_s, hs.is_glb_Inf ne_s⟩

theorem IsCompact.exists_is_lub {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : ∃ x ∈ s, IsLub s x :=
  ⟨_, hs.Sup_mem ne_s, hs.is_lub_Sup ne_s⟩

theorem IsCompact.exists_Inf_image_eq {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α}
    (hf : ContinuousOn f s) : ∃ x ∈ s, inf (f '' s) = f x :=
  let ⟨x, hxs, hx⟩ := (hs.image_of_continuous_on hf).Inf_mem (ne_s.Image f)
  ⟨x, hxs, hx.symm⟩

theorem IsCompact.exists_Sup_image_eq :
    ∀ {s : Set β}, IsCompact s → s.Nonempty → ∀ {f : β → α}, ContinuousOn f s → ∃ x ∈ s, sup (f '' s) = f x :=
  @IsCompact.exists_Inf_image_eq (OrderDual α) _ _ _ _ _

theorem eq_Icc_of_connected_compact {s : Set α} (h₁ : IsConnected s) (h₂ : IsCompact s) : s = Icc (inf s) (sup s) :=
  eq_Icc_cInf_cSup_of_connected_bdd_closed h₁ h₂.BddBelow h₂.BddAbove h₂.IsClosed

/-!
### Extreme value theorem
-/


/-- The **extreme value theorem**: a continuous function realizes its minimum on a compact set. -/
theorem IsCompact.exists_forall_le {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α}
    (hf : ContinuousOn f s) : ∃ x ∈ s, ∀, ∀ y ∈ s, ∀, f x ≤ f y := by
  rcases(hs.image_of_continuous_on hf).exists_is_least (ne_s.image f) with ⟨_, ⟨x, hxs, rfl⟩, hx⟩
  exact ⟨x, hxs, ball_image_iff.1 hx⟩

/-- The **extreme value theorem**: a continuous function realizes its maximum on a compact set. -/
theorem IsCompact.exists_forall_ge :
    ∀ {s : Set β}, IsCompact s → s.Nonempty → ∀ {f : β → α}, ContinuousOn f s → ∃ x ∈ s, ∀, ∀ y ∈ s, ∀, f y ≤ f x :=
  @IsCompact.exists_forall_le (OrderDual α) _ _ _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (x «expr ∉ » K)
/-- The **extreme value theorem**: if a continuous function `f` is larger than a value in its range
away from compact sets, then it has a global minimum. -/
theorem _root_.continuous.exists_forall_le' {f : β → α} (hf : Continuous f) (x₀ : β)
    (h : ∀ᶠ x in cocompact β, f x₀ ≤ f x) : ∃ x : β, ∀ y : β, f x ≤ f y := by
  obtain ⟨K : Set β, hK : IsCompact K, hKf : ∀ x _ : x ∉ K, f x₀ ≤ f x⟩ := has_basis_cocompact.eventually_iff.mp h
  obtain ⟨x, -, hx⟩ : ∃ x ∈ insert x₀ K, ∀, ∀ y ∈ insert x₀ K, ∀, f x ≤ f y :=
    (hK.insert x₀).exists_forall_le (nonempty_insert _ _) hf.continuous_on
  refine' ⟨x, fun y => _⟩
  by_cases' hy : y ∈ K
  exacts[hx y (Or.inr hy), (hx _ (Or.inl rfl)).trans (hKf y hy)]

/-- The **extreme value theorem**: if a continuous function `f` is smaller than a value in its range
away from compact sets, then it has a global maximum. -/
theorem _root_.continuous.exists_forall_ge' {f : β → α} (hf : Continuous f) (x₀ : β)
    (h : ∀ᶠ x in cocompact β, f x ≤ f x₀) : ∃ x : β, ∀ y : β, f y ≤ f x :=
  @Continuous.exists_forall_le' (OrderDual α) _ _ _ _ _ _ hf x₀ h

/-- The **extreme value theorem**: if a continuous function `f` tends to infinity away from compact
sets, then it has a global minimum. -/
theorem _root_.continuous.exists_forall_le [Nonempty β] {f : β → α} (hf : Continuous f)
    (hlim : Tendsto f (cocompact β) atTop) : ∃ x, ∀ y, f x ≤ f y := by
  inhabit β
  exact hf.exists_forall_le' default (hlim.eventually <| eventually_ge_at_top _)

/-- The **extreme value theorem**: if a continuous function `f` tends to negative infinity away from
compact sets, then it has a global maximum. -/
theorem Continuous.exists_forall_ge [Nonempty β] {f : β → α} (hf : Continuous f)
    (hlim : Tendsto f (cocompact β) atBot) : ∃ x, ∀ y, f y ≤ f x :=
  @Continuous.exists_forall_le (OrderDual α) _ _ _ _ _ _ _ hf hlim

/-- A continuous function with compact support has a global minimum. -/
@[to_additive]
theorem _root_.continuous.exists_forall_le_of_has_compact_mul_support [Nonempty β] [One α] {f : β → α}
    (hf : Continuous f) (h : HasCompactMulSupport f) : ∃ x : β, ∀ y : β, f x ≤ f y := by
  -- Proof sketch: we use `continuous.exists_forall_le'` with as `x₀` any element outside the
  -- support of `f`, if such an element exists (and otherwise an arbitrary element).
  refine'
    hf.exists_forall_le' (Classical.epsilon fun x => f x = 1) ((eventually_of_mem h.compl_mem_cocompact) fun x hx => _)
  have : f x = 1 := nmem_mul_support.mp (mt (fun h2x => subset_closure h2x) hx)
  exact ((Classical.epsilon_spec ⟨x, this⟩).trans this.symm).le

/-- A continuous function with compact support has a global maximum. -/
@[to_additive]
theorem Continuous.exists_forall_ge_of_has_compact_mul_support [Nonempty β] [One α] {f : β → α} (hf : Continuous f)
    (h : HasCompactMulSupport f) : ∃ x : β, ∀ y : β, f y ≤ f x :=
  @Continuous.exists_forall_le_of_has_compact_mul_support (OrderDual α) _ _ _ _ _ _ _ _ hf h

/-- A continuous function with compact support is bounded below. -/
@[to_additive]
theorem Continuous.bdd_below_range_of_has_compact_mul_support [One α] {f : β → α} (hf : Continuous f)
    (h : HasCompactMulSupport f) : BddBelow (Range f) := by
  cases' is_empty_or_nonempty β with hβ hβ
  · rw [range_eq_empty_iff.mpr]
    exact bdd_below_empty
    exact hβ
    
  obtain ⟨x, hx⟩ := hf.exists_forall_le_of_has_compact_mul_support h
  refine' ⟨f x, _⟩
  rintro _ ⟨x', rfl⟩
  exact hx x'

/-- A continuous function with compact support is bounded above. -/
@[to_additive]
theorem Continuous.bdd_above_range_of_has_compact_mul_support [One α] {f : β → α} (hf : Continuous f)
    (h : HasCompactMulSupport f) : BddAbove (Range f) :=
  @Continuous.bdd_below_range_of_has_compact_mul_support (OrderDual α) _ _ _ _ _ _ _ hf h

/-- A continuous function is bounded below on a compact set. -/
theorem IsCompact.bdd_below_image {f : β → α} {K : Set β} (hK : IsCompact K) (hf : ContinuousOn f K) :
    BddBelow (f '' K) := by
  rcases eq_empty_or_nonempty K with (rfl | h)
  · rw [image_empty]
    exact bdd_below_empty
    
  obtain ⟨c, -, hc⟩ := hK.exists_forall_le h hf
  refine' ⟨f c, _⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hc x hx

/-- A continuous function is bounded above on a compact set. -/
theorem IsCompact.bdd_above_image {f : β → α} {K : Set β} (hK : IsCompact K) (hf : ContinuousOn f K) :
    BddAbove (f '' K) :=
  @IsCompact.bdd_below_image (OrderDual α) _ _ _ _ _ _ _ hK hf

/-!
### Image of a closed interval
-/


variable [DenselyOrdered α] [ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α → β} {a b x y : α}

open_locale Interval

theorem ContinuousOn.image_Icc (hab : a ≤ b) (h : ContinuousOn f <| Icc a b) :
    f '' Icc a b = Icc (Inf <| f '' Icc a b) (Sup <| f '' Icc a b) :=
  eq_Icc_of_connected_compact ⟨(nonempty_Icc.2 hab).Image f, is_preconnected_Icc.Image f h⟩
    (is_compact_Icc.image_of_continuous_on h)

-- ././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)
theorem ContinuousOn.image_interval_eq_Icc
    (h : ContinuousOn f <| "././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)") :
    f '' "././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)" =
      Icc (inf (f '' "././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)"))
        (sup (f '' "././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)")) :=
  by
  cases' le_totalₓ a b with h2 h2
  · simp_rw [interval_of_le h2]  at h⊢
    exact h.image_Icc h2
    
  · simp_rw [interval_of_ge h2]  at h⊢
    exact h.image_Icc h2
    

-- ././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)
theorem ContinuousOn.image_interval
    (h : ContinuousOn f <| "././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)") :
    f '' "././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)" =
      "././Mathport/Syntax/Translate/Basic.lean:814:47: unsupported (impossible)" :=
  by
  refine' h.image_interval_eq_Icc.trans (interval_of_le _).symm
  refine' cInf_le_cSup _ _ (nonempty_interval.image _) <;> rw [h.image_interval_eq_Icc]
  exacts[bdd_below_Icc, bdd_above_Icc]

