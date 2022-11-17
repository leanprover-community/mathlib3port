/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
import Mathbin.Topology.Algebra.Order.IntermediateValue
import Mathbin.Topology.LocalExtr

/-!
# Compactness of a closed interval

In this file we prove that a closed interval in a conditionally complete linear ordered type with
order topology (or a product of such types) is compact.

We prove the extreme value theorem (`is_compact.exists_forall_le`, `is_compact.exists_forall_ge`):
a continuous function on a compact set takes its minimum and maximum values. We provide many
variations of this theorem.

We also prove that the image of a closed interval under a continuous map is a closed interval, see
`continuous_on.image_Icc`.

## Tags

compact, extreme value theorem
-/


open Filter OrderDual TopologicalSpace Function Set

open Filter TopologicalSpace

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
class CompactIccSpace (α : Type _) [TopologicalSpace α] [Preorder α] : Prop where
  is_compact_Icc : ∀ {a b : α}, IsCompact (icc a b)
#align compact_Icc_space CompactIccSpace

export CompactIccSpace (is_compact_Icc)

/-- A closed interval in a conditionally complete linear order is compact. -/
instance (priority := 100) ConditionallyCompleteLinearOrder.to_compact_Icc_space (α : Type _)
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] : CompactIccSpace α := by
  refine' ⟨fun a b => _⟩
  cases' le_or_lt a b with hab hab
  swap
  · simp [hab]
    
  refine' is_compact_iff_ultrafilter_le_nhds.2 fun f hf => _
  contrapose! hf
  rw [le_principal_iff]
  have hpt : ∀ x ∈ Icc a b, {x} ∉ f := fun x hx hxf => hf x hx ((le_pure_iff.2 hxf).trans (pure_le_nhds x))
  set s := { x ∈ Icc a b | Icc a x ∉ f }
  have hsb : b ∈ upperBounds s := fun x hx => hx.1.2
  have sbd : BddAbove s := ⟨b, hsb⟩
  have ha : a ∈ s := by simp [hpt, hab]
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
    exact subset.trans Icc_subset_Icc_union_Ioc (union_subset_union subset.rfl $ Ioc_subset_Ioc_left hy.1.le)
  cases' hc.2.eq_or_lt with heq hlt
  · rw [← HEq]
    exact hcs.2
    
  contrapose! hf
  intro U hU
  rcases(mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset hlt).1 (mem_nhds_within_of_mem_nhds hU) with ⟨y, hxy, hyU⟩
  refine' mem_of_superset _ hyU
  clear! U
  have hy : y ∈ Icc a b := ⟨hc.1.trans hxy.1.le, hxy.2⟩
  by_cases hay:Icc a y ∈ f
  · refine' mem_of_superset (f.diff_mem_iff.2 ⟨f.diff_mem_iff.2 ⟨hay, hcs.2⟩, hpt y hy⟩) _
    rw [diff_subset_iff, union_comm, Ico_union_right hxy.1.le, diff_subset_iff]
    exact Icc_subset_Icc_union_Icc
    
  · exact ((hsc.1 ⟨hy, hay⟩).not_lt hxy.1).elim
    
#align conditionally_complete_linear_order.to_compact_Icc_space ConditionallyCompleteLinearOrder.to_compact_Icc_space

instance {ι : Type _} {α : ι → Type _} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, CompactIccSpace (α i)] : CompactIccSpace (∀ i, α i) :=
  ⟨fun a b => pi_univ_Icc a b ▸ is_compact_univ_pi $ fun i => is_compact_Icc⟩

instance Pi.compact_Icc_space' {α β : Type _} [Preorder β] [TopologicalSpace β] [CompactIccSpace β] :
    CompactIccSpace (α → β) :=
  Pi.compact_Icc_space
#align pi.compact_Icc_space' Pi.compact_Icc_space'

instance {α β : Type _} [Preorder α] [TopologicalSpace α] [CompactIccSpace α] [Preorder β] [TopologicalSpace β]
    [CompactIccSpace β] : CompactIccSpace (α × β) :=
  ⟨fun a b => (Icc_prod_eq a b).symm ▸ is_compact_Icc.Prod is_compact_Icc⟩

/-- An unordered closed interval is compact. -/
theorem is_compact_interval {α : Type _} [LinearOrder α] [TopologicalSpace α] [CompactIccSpace α] {a b : α} :
    IsCompact (interval a b) :=
  is_compact_Icc
#align is_compact_interval is_compact_interval

-- See note [lower instance priority]
/-- A complete linear order is a compact space.

We do not register an instance for a `[compact_Icc_space α]` because this would only add instances
for products (indexed or not) of complete linear orders, and we have instances with higher priority
that cover these cases. -/
instance (priority := 100) compact_space_of_complete_linear_order {α : Type _} [CompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] : CompactSpace α :=
  ⟨by simp only [← Icc_bot_top, is_compact_Icc]⟩
#align compact_space_of_complete_linear_order compact_space_of_complete_linear_order

section

variable {α : Type _} [Preorder α] [TopologicalSpace α] [CompactIccSpace α]

instance compact_space_Icc (a b : α) : CompactSpace (icc a b) :=
  is_compact_iff_compact_space.mp is_compact_Icc
#align compact_space_Icc compact_space_Icc

end

/-!
### Min and max elements of a compact set
-/


variable {α β γ : Type _} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [TopologicalSpace β] [TopologicalSpace γ]

theorem IsCompact.Inf_mem {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : inf s ∈ s :=
  hs.IsClosed.cInf_mem ne_s hs.BddBelow
#align is_compact.Inf_mem IsCompact.Inf_mem

theorem IsCompact.Sup_mem {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : sup s ∈ s :=
  @IsCompact.Inf_mem αᵒᵈ _ _ _ _ hs ne_s
#align is_compact.Sup_mem IsCompact.Sup_mem

theorem IsCompact.is_glb_Inf {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsGlb s (inf s) :=
  is_glb_cInf ne_s hs.BddBelow
#align is_compact.is_glb_Inf IsCompact.is_glb_Inf

theorem IsCompact.is_lub_Sup {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsLub s (sup s) :=
  @IsCompact.is_glb_Inf αᵒᵈ _ _ _ _ hs ne_s
#align is_compact.is_lub_Sup IsCompact.is_lub_Sup

theorem IsCompact.is_least_Inf {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsLeast s (inf s) :=
  ⟨hs.Inf_mem ne_s, (hs.is_glb_Inf ne_s).1⟩
#align is_compact.is_least_Inf IsCompact.is_least_Inf

theorem IsCompact.is_greatest_Sup {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsGreatest s (sup s) :=
  @IsCompact.is_least_Inf αᵒᵈ _ _ _ _ hs ne_s
#align is_compact.is_greatest_Sup IsCompact.is_greatest_Sup

theorem IsCompact.exists_is_least {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : ∃ x, IsLeast s x :=
  ⟨_, hs.is_least_Inf ne_s⟩
#align is_compact.exists_is_least IsCompact.exists_is_least

theorem IsCompact.exists_is_greatest {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : ∃ x, IsGreatest s x :=
  ⟨_, hs.is_greatest_Sup ne_s⟩
#align is_compact.exists_is_greatest IsCompact.exists_is_greatest

theorem IsCompact.exists_is_glb {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : ∃ x ∈ s, IsGlb s x :=
  ⟨_, hs.Inf_mem ne_s, hs.is_glb_Inf ne_s⟩
#align is_compact.exists_is_glb IsCompact.exists_is_glb

theorem IsCompact.exists_is_lub {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : ∃ x ∈ s, IsLub s x :=
  ⟨_, hs.Sup_mem ne_s, hs.is_lub_Sup ne_s⟩
#align is_compact.exists_is_lub IsCompact.exists_is_lub

theorem IsCompact.exists_Inf_image_eq_and_le {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α}
    (hf : ContinuousOn f s) : ∃ x ∈ s, inf (f '' s) = f x ∧ ∀ y ∈ s, f x ≤ f y :=
  let ⟨x, hxs, hx⟩ := (hs.image_of_continuous_on hf).Inf_mem (ne_s.image f)
  ⟨x, hxs, hx.symm, fun y hy => hx.trans_le $ cInf_le (hs.image_of_continuous_on hf).BddBelow $ mem_image_of_mem f hy⟩
#align is_compact.exists_Inf_image_eq_and_le IsCompact.exists_Inf_image_eq_and_le

theorem IsCompact.exists_Sup_image_eq_and_ge {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α}
    (hf : ContinuousOn f s) : ∃ x ∈ s, sup (f '' s) = f x ∧ ∀ y ∈ s, f y ≤ f x :=
  @IsCompact.exists_Inf_image_eq_and_le αᵒᵈ _ _ _ _ _ _ hs ne_s _ hf
#align is_compact.exists_Sup_image_eq_and_ge IsCompact.exists_Sup_image_eq_and_ge

theorem IsCompact.exists_Inf_image_eq {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α}
    (hf : ContinuousOn f s) : ∃ x ∈ s, inf (f '' s) = f x :=
  let ⟨x, hxs, hx, _⟩ := hs.exists_Inf_image_eq_and_le ne_s hf
  ⟨x, hxs, hx⟩
#align is_compact.exists_Inf_image_eq IsCompact.exists_Inf_image_eq

theorem IsCompact.exists_Sup_image_eq :
    ∀ {s : Set β}, IsCompact s → s.Nonempty → ∀ {f : β → α}, ContinuousOn f s → ∃ x ∈ s, sup (f '' s) = f x :=
  @IsCompact.exists_Inf_image_eq αᵒᵈ _ _ _ _ _
#align is_compact.exists_Sup_image_eq IsCompact.exists_Sup_image_eq

theorem eq_Icc_of_connected_compact {s : Set α} (h₁ : IsConnected s) (h₂ : IsCompact s) : s = icc (inf s) (sup s) :=
  eq_Icc_cInf_cSup_of_connected_bdd_closed h₁ h₂.BddBelow h₂.BddAbove h₂.IsClosed
#align eq_Icc_of_connected_compact eq_Icc_of_connected_compact

/-!
### Extreme value theorem
-/


/-- The **extreme value theorem**: a continuous function realizes its minimum on a compact set. -/
theorem IsCompact.exists_forall_le {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α}
    (hf : ContinuousOn f s) : ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y := by
  rcases(hs.image_of_continuous_on hf).exists_is_least (ne_s.image f) with ⟨_, ⟨x, hxs, rfl⟩, hx⟩
  exact ⟨x, hxs, ball_image_iff.1 hx⟩
#align is_compact.exists_forall_le IsCompact.exists_forall_le

/-- The **extreme value theorem**: a continuous function realizes its maximum on a compact set. -/
theorem IsCompact.exists_forall_ge :
    ∀ {s : Set β}, IsCompact s → s.Nonempty → ∀ {f : β → α}, ContinuousOn f s → ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  @IsCompact.exists_forall_le αᵒᵈ _ _ _ _ _
#align is_compact.exists_forall_ge IsCompact.exists_forall_ge

/-- The **extreme value theorem**: if a function `f` is continuous on a closed set `s` and it is
larger than a value in its image away from compact sets, then it has a minimum on this set. -/
theorem ContinuousOn.exists_forall_le' {s : Set β} {f : β → α} (hf : ContinuousOn f s) (hsc : IsClosed s) {x₀ : β}
    (h₀ : x₀ ∈ s) (hc : ∀ᶠ x in cocompact β ⊓ 𝓟 s, f x₀ ≤ f x) : ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y := by
  rcases(has_basis_cocompact.inf_principal _).eventually_iff.1 hc with ⟨K, hK, hKf⟩
  have hsub : insert x₀ (K ∩ s) ⊆ s := insert_subset.2 ⟨h₀, inter_subset_right _ _⟩
  obtain ⟨x, hx, hxf⟩ : ∃ x ∈ insert x₀ (K ∩ s), ∀ y ∈ insert x₀ (K ∩ s), f x ≤ f y :=
    ((hK.inter_right hsc).insert x₀).exists_forall_le (insert_nonempty _ _) (hf.mono hsub)
  refine' ⟨x, hsub hx, fun y hy => _⟩
  by_cases hyK:y ∈ K
  exacts[hxf _ (Or.inr ⟨hyK, hy⟩), (hxf _ (Or.inl rfl)).trans (hKf ⟨hyK, hy⟩)]
#align continuous_on.exists_forall_le' ContinuousOn.exists_forall_le'

/-- The **extreme value theorem**: if a function `f` is continuous on a closed set `s` and it is
smaller than a value in its image away from compact sets, then it has a maximum on this set. -/
theorem ContinuousOn.exists_forall_ge' {s : Set β} {f : β → α} (hf : ContinuousOn f s) (hsc : IsClosed s) {x₀ : β}
    (h₀ : x₀ ∈ s) (hc : ∀ᶠ x in cocompact β ⊓ 𝓟 s, f x ≤ f x₀) : ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  @ContinuousOn.exists_forall_le' αᵒᵈ _ _ _ _ _ _ _ hf hsc _ h₀ hc
#align continuous_on.exists_forall_ge' ContinuousOn.exists_forall_ge'

/-- The **extreme value theorem**: if a continuous function `f` is larger than a value in its range
away from compact sets, then it has a global minimum. -/
theorem _root_.continuous.exists_forall_le' {f : β → α} (hf : Continuous f) (x₀ : β)
    (h : ∀ᶠ x in cocompact β, f x₀ ≤ f x) : ∃ x : β, ∀ y : β, f x ≤ f y :=
  let ⟨x, _, hx⟩ := hf.ContinuousOn.exists_forall_le' isClosedUniv (mem_univ x₀) (by rwa [principal_univ, inf_top_eq])
  ⟨x, fun y => hx y (mem_univ y)⟩
#align _root_.continuous.exists_forall_le' _root_.continuous.exists_forall_le'

/-- The **extreme value theorem**: if a continuous function `f` is smaller than a value in its range
away from compact sets, then it has a global maximum. -/
theorem _root_.continuous.exists_forall_ge' {f : β → α} (hf : Continuous f) (x₀ : β)
    (h : ∀ᶠ x in cocompact β, f x ≤ f x₀) : ∃ x : β, ∀ y : β, f y ≤ f x :=
  @Continuous.exists_forall_le' αᵒᵈ _ _ _ _ _ _ hf x₀ h
#align _root_.continuous.exists_forall_ge' _root_.continuous.exists_forall_ge'

/-- The **extreme value theorem**: if a continuous function `f` tends to infinity away from compact
sets, then it has a global minimum. -/
theorem _root_.continuous.exists_forall_le [Nonempty β] {f : β → α} (hf : Continuous f)
    (hlim : Tendsto f (cocompact β) atTop) : ∃ x, ∀ y, f x ≤ f y := by
  inhabit β
  exact hf.exists_forall_le' default (hlim.eventually $ eventually_ge_at_top _)
#align _root_.continuous.exists_forall_le _root_.continuous.exists_forall_le

/-- The **extreme value theorem**: if a continuous function `f` tends to negative infinity away from
compact sets, then it has a global maximum. -/
theorem Continuous.exists_forall_ge [Nonempty β] {f : β → α} (hf : Continuous f)
    (hlim : Tendsto f (cocompact β) atBot) : ∃ x, ∀ y, f y ≤ f x :=
  @Continuous.exists_forall_le αᵒᵈ _ _ _ _ _ _ _ hf hlim
#align continuous.exists_forall_ge Continuous.exists_forall_ge

theorem IsCompact.Sup_lt_iff_of_continuous {f : β → α} {K : Set β} (hK : IsCompact K) (h0K : K.Nonempty)
    (hf : ContinuousOn f K) (y : α) : sup (f '' K) < y ↔ ∀ x ∈ K, f x < y := by
  refine' ⟨fun h x hx => (le_cSup (hK.bdd_above_image hf) $ mem_image_of_mem f hx).trans_lt h, fun h => _⟩
  obtain ⟨x, hx, h2x⟩ := hK.exists_forall_ge h0K hf
  refine' (cSup_le (h0K.image f) _).trans_lt (h x hx)
  rintro _ ⟨x', hx', rfl⟩
  exact h2x x' hx'
#align is_compact.Sup_lt_iff_of_continuous IsCompact.Sup_lt_iff_of_continuous

theorem IsCompact.lt_Inf_iff_of_continuous {α β : Type _} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [TopologicalSpace β] {f : β → α} {K : Set β} (hK : IsCompact K) (h0K : K.Nonempty)
    (hf : ContinuousOn f K) (y : α) : y < inf (f '' K) ↔ ∀ x ∈ K, y < f x :=
  @IsCompact.Sup_lt_iff_of_continuous αᵒᵈ β _ _ _ _ _ _ hK h0K hf y
#align is_compact.lt_Inf_iff_of_continuous IsCompact.lt_Inf_iff_of_continuous

/-- A continuous function with compact support has a global minimum. -/
@[to_additive "A continuous function with compact support has a global minimum."]
theorem Continuous.exists_forall_le_of_has_compact_mul_support [Nonempty β] [One α] {f : β → α} (hf : Continuous f)
    (h : HasCompactMulSupport f) : ∃ x : β, ∀ y : β, f x ≤ f y := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := (h.is_compact_range hf).exists_is_least (range_nonempty _)
  rw [mem_lower_bounds, forall_range_iff] at hx
  exact ⟨x, hx⟩
#align continuous.exists_forall_le_of_has_compact_mul_support Continuous.exists_forall_le_of_has_compact_mul_support

/-- A continuous function with compact support has a global maximum. -/
@[to_additive "A continuous function with compact support has a global maximum."]
theorem Continuous.exists_forall_ge_of_has_compact_mul_support [Nonempty β] [One α] {f : β → α} (hf : Continuous f)
    (h : HasCompactMulSupport f) : ∃ x : β, ∀ y : β, f y ≤ f x :=
  @Continuous.exists_forall_le_of_has_compact_mul_support αᵒᵈ _ _ _ _ _ _ _ _ hf h
#align continuous.exists_forall_ge_of_has_compact_mul_support Continuous.exists_forall_ge_of_has_compact_mul_support

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem IsCompact.continuous_Sup {f : γ → β → α} {K : Set β} (hK : IsCompact K) (hf : Continuous ↿f) :
    Continuous fun x => sup (f x '' K) := by
  rcases eq_empty_or_nonempty K with (rfl | h0K)
  · simp_rw [image_empty]
    exact continuous_const
    
  rw [continuous_iff_continuous_at]
  intro x
  obtain ⟨y, hyK, h2y, hy⟩ :=
    hK.exists_Sup_image_eq_and_ge h0K (show Continuous fun y => f x y from hf.comp $ Continuous.Prod.mk x).ContinuousOn
  rw [ContinuousAt, h2y, tendsto_order]
  have :=
    tendsto_order.mp ((show Continuous fun x => f x y from hf.comp $ continuous_id.prod_mk continuous_const).Tendsto x)
  refine' ⟨fun z hz => _, fun z hz => _⟩
  · refine' (this.1 z hz).mono fun x' hx' => hx'.trans_le $ le_cSup _ $ mem_image_of_mem (f x') hyK
    exact hK.bdd_above_image (hf.comp $ Continuous.Prod.mk x').ContinuousOn
    
  · have h : ({x} : Set γ) ×ˢ K ⊆ ↿f ⁻¹' Iio z := by
      rintro ⟨x', y'⟩ ⟨hx', hy'⟩
      cases hx'
      exact (hy y' hy').trans_lt hz
    obtain ⟨u, v, hu, hv, hxu, hKv, huv⟩ := generalized_tube_lemma is_compact_singleton hK (is_open_Iio.preimage hf) h
    refine' eventually_of_mem (hu.mem_nhds (singleton_subset_iff.mp hxu)) fun x' hx' => _
    rw [hK.Sup_lt_iff_of_continuous h0K (show Continuous (f x') from hf.comp $ Continuous.Prod.mk x').ContinuousOn]
    exact fun y' hy' => huv (mk_mem_prod hx' (hKv hy'))
    
#align is_compact.continuous_Sup IsCompact.continuous_Sup

theorem IsCompact.continuous_Inf {f : γ → β → α} {K : Set β} (hK : IsCompact K) (hf : Continuous ↿f) :
    Continuous fun x => inf (f x '' K) :=
  @IsCompact.continuous_Sup αᵒᵈ β γ _ _ _ _ _ _ _ hK hf
#align is_compact.continuous_Inf IsCompact.continuous_Inf

namespace ContinuousOn

/-!
### Image of a closed interval
-/


variable [DenselyOrdered α] [ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α → β} {a b c : α}

open Interval

theorem image_Icc (hab : a ≤ b) (h : ContinuousOn f $ icc a b) :
    f '' icc a b = icc (Inf $ f '' icc a b) (Sup $ f '' icc a b) :=
  eq_Icc_of_connected_compact ⟨(nonempty_Icc.2 hab).image f, is_preconnected_Icc.image f h⟩
    (is_compact_Icc.image_of_continuous_on h)
#align continuous_on.image_Icc ContinuousOn.image_Icc

theorem image_interval_eq_Icc (h : ContinuousOn f $ [a, b]) :
    f '' [a, b] = icc (inf (f '' [a, b])) (sup (f '' [a, b])) := by
  cases' le_total a b with h2 h2
  · simp_rw [interval_of_le h2] at h⊢
    exact h.image_Icc h2
    
  · simp_rw [interval_of_ge h2] at h⊢
    exact h.image_Icc h2
    
#align continuous_on.image_interval_eq_Icc ContinuousOn.image_interval_eq_Icc

theorem image_interval (h : ContinuousOn f $ [a, b]) : f '' [a, b] = [inf (f '' [a, b]), sup (f '' [a, b])] := by
  refine' h.image_interval_eq_Icc.trans (interval_of_le _).symm
  refine' cInf_le_cSup _ _ (nonempty_interval.image _) <;> rw [h.image_interval_eq_Icc]
  exacts[bdd_below_Icc, bdd_above_Icc]
#align continuous_on.image_interval ContinuousOn.image_interval

theorem Inf_image_Icc_le (h : ContinuousOn f $ icc a b) (hc : c ∈ icc a b) : inf (f '' icc a b) ≤ f c := by
  rw [h.image_Icc (nonempty_Icc.mp (Set.nonempty_of_mem hc))]
  exact
    cInf_le bdd_below_Icc
      (mem_Icc.mpr
        ⟨cInf_le (is_compact_Icc.bdd_below_image h) ⟨c, hc, rfl⟩,
          le_cSup (is_compact_Icc.bdd_above_image h) ⟨c, hc, rfl⟩⟩)
#align continuous_on.Inf_image_Icc_le ContinuousOn.Inf_image_Icc_le

theorem le_Sup_image_Icc (h : ContinuousOn f $ icc a b) (hc : c ∈ icc a b) : f c ≤ sup (f '' icc a b) := by
  rw [h.image_Icc (nonempty_Icc.mp (Set.nonempty_of_mem hc))]
  exact
    le_cSup bdd_above_Icc
      (mem_Icc.mpr
        ⟨cInf_le (is_compact_Icc.bdd_below_image h) ⟨c, hc, rfl⟩,
          le_cSup (is_compact_Icc.bdd_above_image h) ⟨c, hc, rfl⟩⟩)
#align continuous_on.le_Sup_image_Icc ContinuousOn.le_Sup_image_Icc

end ContinuousOn

theorem IsCompact.exists_local_min_on_mem_subset {f : β → α} {s t : Set β} {z : β} (ht : IsCompact t)
    (hf : ContinuousOn f t) (hz : z ∈ t) (hfz : ∀ z' ∈ t \ s, f z < f z') : ∃ x ∈ s, IsLocalMinOn f t x := by
  obtain ⟨x, hx, hfx⟩ : ∃ x ∈ t, ∀ y ∈ t, f x ≤ f y := ht.exists_forall_le ⟨z, hz⟩ hf
  have key : ∀ ⦃y⦄, y ∈ t → (∀ z' ∈ t \ s, f y < f z') → y ∈ s := fun y hy hfy => by
    by_contra <;> simpa using hfy y ((mem_diff y).mpr ⟨hy, h⟩)
  have h1 : ∀ z' ∈ t \ s, f x < f z' := fun z' hz' => (hfx z hz).trans_lt (hfz z' hz')
  have h2 : x ∈ s := key hx h1
  refine' ⟨x, h2, eventually_nhds_within_of_forall hfx⟩
#align is_compact.exists_local_min_on_mem_subset IsCompact.exists_local_min_on_mem_subset

theorem IsCompact.exists_local_min_mem_open {f : β → α} {s t : Set β} {z : β} (ht : IsCompact t) (hst : s ⊆ t)
    (hf : ContinuousOn f t) (hz : z ∈ t) (hfz : ∀ z' ∈ t \ s, f z < f z') (hs : IsOpen s) : ∃ x ∈ s, IsLocalMin f x :=
  by
  obtain ⟨x, hx, hfx⟩ := ht.exists_local_min_on_mem_subset hf hz hfz
  exact ⟨x, hx, hfx.is_local_min (Filter.mem_of_superset (hs.mem_nhds hx) hst)⟩
#align is_compact.exists_local_min_mem_open IsCompact.exists_local_min_mem_open

