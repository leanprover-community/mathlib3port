/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Order.Filter.Basic
import Data.Set.Countable

#align_import order.filter.countable_Inter from "leanprover-community/mathlib"@"b9e46fe101fc897fb2e7edaf0bf1f09ea49eb81a"

/-!
# Filters with countable intersection property

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `countable_Inter_filter` to be the class of filters with the following
property: for any countable collection of sets `s ∈ l` their intersection belongs to `l` as well.

Two main examples are the `residual` filter defined in `topology.G_delta` and
the `measure.ae` filter defined in `measure_theory.measure_space`.

We reformulate the definition in terms of indexed intersection and in terms of `filter.eventually`
and provide instances for some basic constructions (`⊥`, `⊤`, `filter.principal`, `filter.map`,
`filter.comap`, `has_inf.inf`). We also provide a custom constructor `filter.of_countable_Inter`
that deduces two axioms of a `filter` from the countable intersection property.

## Tags
filter, countable
-/


open Set Filter

open scoped Filter

variable {ι : Sort _} {α β : Type _}

#print CountableInterFilter /-
/-- A filter `l` has the countable intersection property if for any countable collection
of sets `s ∈ l` their intersection belongs to `l` as well. -/
class CountableInterFilter (l : Filter α) : Prop where
  countable_sInter_mem' : ∀ {S : Set (Set α)} (hSc : S.Countable) (hS : ∀ s ∈ S, s ∈ l), ⋂₀ S ∈ l
#align countable_Inter_filter CountableInterFilter
-/

variable {l : Filter α} [CountableInterFilter l]

#print countable_sInter_mem /-
theorem countable_sInter_mem {S : Set (Set α)} (hSc : S.Countable) : ⋂₀ S ∈ l ↔ ∀ s ∈ S, s ∈ l :=
  ⟨fun hS s hs => mem_of_superset hS (sInter_subset_of_mem hs),
    CountableInterFilter.countable_sInter_mem' hSc⟩
#align countable_sInter_mem countable_sInter_mem
-/

#print countable_iInter_mem /-
theorem countable_iInter_mem [Countable ι] {s : ι → Set α} : (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l :=
  sInter_range s ▸ (countable_sInter_mem (countable_range _)).trans forall_range_iff
#align countable_Inter_mem countable_iInter_mem
-/

#print countable_bInter_mem /-
theorem countable_bInter_mem {ι : Type _} {S : Set ι} (hS : S.Countable) {s : ∀ i ∈ S, Set α} :
    (⋂ i ∈ S, s i ‹_›) ∈ l ↔ ∀ i ∈ S, s i ‹_› ∈ l :=
  by
  rw [bInter_eq_Inter]
  haveI := hS.to_encodable
  exact countable_Inter_mem.trans Subtype.forall
#align countable_bInter_mem countable_bInter_mem
-/

#print eventually_countable_forall /-
theorem eventually_countable_forall [Countable ι] {p : α → ι → Prop} :
    (∀ᶠ x in l, ∀ i, p x i) ↔ ∀ i, ∀ᶠ x in l, p x i := by
  simpa only [Filter.Eventually, set_of_forall] using
    @countable_iInter_mem _ _ l _ _ fun i => {x | p x i}
#align eventually_countable_forall eventually_countable_forall
-/

#print eventually_countable_ball /-
theorem eventually_countable_ball {ι : Type _} {S : Set ι} (hS : S.Countable)
    {p : ∀ (x : α), ∀ i ∈ S, Prop} :
    (∀ᶠ x in l, ∀ i ∈ S, p x i ‹_›) ↔ ∀ i ∈ S, ∀ᶠ x in l, p x i ‹_› := by
  simpa only [Filter.Eventually, set_of_forall] using
    @countable_bInter_mem _ l _ _ _ hS fun i hi => {x | p x i hi}
#align eventually_countable_ball eventually_countable_ball
-/

#print EventuallyLE.countable_iUnion /-
theorem EventuallyLE.countable_iUnion [Countable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
    (⋃ i, s i) ≤ᶠ[l] ⋃ i, t i :=
  (eventually_countable_forall.2 h).mono fun x hst hs => mem_iUnion.2 <| (mem_iUnion.1 hs).imp hst
#align eventually_le.countable_Union EventuallyLE.countable_iUnion
-/

#print EventuallyEq.countable_iUnion /-
theorem EventuallyEq.countable_iUnion [Countable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
    (⋃ i, s i) =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.countable_iUnion fun i => (h i).le).antisymm
    (EventuallyLE.countable_iUnion fun i => (h i).symm.le)
#align eventually_eq.countable_Union EventuallyEq.countable_iUnion
-/

#print EventuallyLE.countable_bUnion /-
theorem EventuallyLE.countable_bUnion {ι : Type _} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i ∈ S, s i ‹_› ≤ᶠ[l] t i ‹_›) :
    (⋃ i ∈ S, s i ‹_›) ≤ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
  by
  simp only [bUnion_eq_Union]
  haveI := hS.to_encodable
  exact EventuallyLE.countable_iUnion fun i => h i i.2
#align eventually_le.countable_bUnion EventuallyLE.countable_bUnion
-/

#print EventuallyEq.countable_bUnion /-
theorem EventuallyEq.countable_bUnion {ι : Type _} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i ∈ S, s i ‹_› =ᶠ[l] t i ‹_›) :
    (⋃ i ∈ S, s i ‹_›) =ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
  (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).symm.le)
#align eventually_eq.countable_bUnion EventuallyEq.countable_bUnion
-/

#print EventuallyLE.countable_iInter /-
theorem EventuallyLE.countable_iInter [Countable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
    (⋂ i, s i) ≤ᶠ[l] ⋂ i, t i :=
  (eventually_countable_forall.2 h).mono fun x hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)
#align eventually_le.countable_Inter EventuallyLE.countable_iInter
-/

#print EventuallyEq.countable_iInter /-
theorem EventuallyEq.countable_iInter [Countable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
    (⋂ i, s i) =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.countable_iInter fun i => (h i).le).antisymm
    (EventuallyLE.countable_iInter fun i => (h i).symm.le)
#align eventually_eq.countable_Inter EventuallyEq.countable_iInter
-/

#print EventuallyLE.countable_bInter /-
theorem EventuallyLE.countable_bInter {ι : Type _} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i ∈ S, s i ‹_› ≤ᶠ[l] t i ‹_›) :
    (⋂ i ∈ S, s i ‹_›) ≤ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
  by
  simp only [bInter_eq_Inter]
  haveI := hS.to_encodable
  exact EventuallyLE.countable_iInter fun i => h i i.2
#align eventually_le.countable_bInter EventuallyLE.countable_bInter
-/

#print EventuallyEq.countable_bInter /-
theorem EventuallyEq.countable_bInter {ι : Type _} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i ∈ S, s i ‹_› =ᶠ[l] t i ‹_›) :
    (⋂ i ∈ S, s i ‹_›) =ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
  (EventuallyLE.countable_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bInter hS fun i hi => (h i hi).symm.le)
#align eventually_eq.countable_bInter EventuallyEq.countable_bInter
-/

#print Filter.ofCountableInter /-
/-- Construct a filter with countable intersection property. This constructor deduces
`filter.univ_sets` and `filter.inter_sets` from the countable intersection property. -/
def Filter.ofCountableInter (l : Set (Set α))
    (hp : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α
    where
  sets := l
  univ_sets := @sInter_empty α ▸ hp _ countable_empty (empty_subset _)
  sets_of_superset := h_mono
  inter_sets s t hs ht :=
    sInter_pair s t ▸
      hp _ ((countable_singleton _).insert _) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)
#align filter.of_countable_Inter Filter.ofCountableInter
-/

#print Filter.countable_Inter_ofCountableInter /-
instance Filter.countable_Inter_ofCountableInter (l : Set (Set α))
    (hp : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
    CountableInterFilter (Filter.ofCountableInter l hp h_mono) :=
  ⟨hp⟩
#align filter.countable_Inter_of_countable_Inter Filter.countable_Inter_ofCountableInter
-/

#print Filter.mem_ofCountableInter /-
@[simp]
theorem Filter.mem_ofCountableInter {l : Set (Set α)}
    (hp : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l) (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l)
    {s : Set α} : s ∈ Filter.ofCountableInter l hp h_mono ↔ s ∈ l :=
  Iff.rfl
#align filter.mem_of_countable_Inter Filter.mem_ofCountableInter
-/

#print countableInterFilter_principal /-
instance countableInterFilter_principal (s : Set α) : CountableInterFilter (𝓟 s) :=
  ⟨fun S hSc hS => subset_sInter hS⟩
#align countable_Inter_filter_principal countableInterFilter_principal
-/

#print countableInterFilter_bot /-
instance countableInterFilter_bot : CountableInterFilter (⊥ : Filter α) := by
  rw [← principal_empty]; apply countableInterFilter_principal
#align countable_Inter_filter_bot countableInterFilter_bot
-/

#print countableInterFilter_top /-
instance countableInterFilter_top : CountableInterFilter (⊤ : Filter α) := by rw [← principal_univ];
  apply countableInterFilter_principal
#align countable_Inter_filter_top countableInterFilter_top
-/

instance (l : Filter β) [CountableInterFilter l] (f : α → β) : CountableInterFilter (comap f l) :=
  by
  refine' ⟨fun S hSc hS => _⟩
  choose! t htl ht using hS
  have : (⋂ s ∈ S, t s) ∈ l := (countable_bInter_mem hSc).2 htl
  refine' ⟨_, this, _⟩
  simpa [preimage_Inter] using Inter₂_mono ht

instance (l : Filter α) [CountableInterFilter l] (f : α → β) : CountableInterFilter (map f l) :=
  by
  constructor; intro S hSc hS
  simp only [mem_map, sInter_eq_bInter, preimage_Inter₂] at hS ⊢
  exact (countable_bInter_mem hSc).2 hS

#print countableInterFilter_inf /-
/-- Infimum of two `countable_Inter_filter`s is a `countable_Inter_filter`. This is useful, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`. -/
instance countableInterFilter_inf (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊓ l₂) :=
  by
  refine' ⟨fun S hSc hS => _⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i ∈ S, s i ‹_›) ∈ l₁ := (countable_bInter_mem hSc).2 hs
  replace ht : (⋂ i ∈ S, t i ‹_›) ∈ l₂ := (countable_bInter_mem hSc).2 ht
  refine' mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => _)
  rw [hst i hi]
  apply inter_subset_inter <;> exact Inter_subset_of_subset i (Inter_subset _ _)
#align countable_Inter_filter_inf countableInterFilter_inf
-/

#print countableInterFilter_sup /-
/-- Supremum of two `countable_Inter_filter`s is a `countable_Inter_filter`. -/
instance countableInterFilter_sup (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊔ l₂) :=
  by
  refine' ⟨fun S hSc hS => ⟨_, _⟩⟩ <;> refine' (countable_sInter_mem hSc).2 fun s hs => _
  exacts [(hS s hs).1, (hS s hs).2]
#align countable_Inter_filter_sup countableInterFilter_sup
-/

namespace Filter

variable (g : Set (Set α))

#print Filter.CountableGenerateSets /-
/-- `filter.countable_generate_sets g` is the (sets of the)
greatest `countable_Inter_filter` containing `g`.-/
inductive CountableGenerateSets : Set α → Prop
  | basic {s : Set α} : s ∈ g → countable_generate_sets s
  | univ : countable_generate_sets univ
  | Superset {s t : Set α} : countable_generate_sets s → s ⊆ t → countable_generate_sets t
  |
  Inter {S : Set (Set α)} :
    S.Countable → (∀ s ∈ S, countable_generate_sets s) → countable_generate_sets (⋂₀ S)
#align filter.countable_generate_sets Filter.CountableGenerateSets
-/

#print Filter.countableGenerate /-
/-- `filter.countable_generate g` is the greatest `countable_Inter_filter` containing `g`.-/
def countableGenerate : Filter α :=
  ofCountableInter (CountableGenerateSets g) (fun S => CountableGenerateSets.sInter) fun s t =>
    CountableGenerateSets.superset
deriving CountableInterFilter
#align filter.countable_generate Filter.countableGenerate
-/

variable {g}

#print Filter.mem_countableGenerate_iff /-
/-- A set is in the `countable_Inter_filter` generated by `g` if and only if
it contains a countable intersection of elements of `g`. -/
theorem mem_countableGenerate_iff {s : Set α} :
    s ∈ countableGenerate g ↔ ∃ S : Set (Set α), S ⊆ g ∧ S.Countable ∧ ⋂₀ S ⊆ s :=
  by
  constructor <;> intro h
  · induction' h with s hs s t hs st ih S Sct hS ih
    · exact ⟨{s}, by simp [hs]⟩
    · exact ⟨∅, by simp⟩
    · refine' Exists.imp (fun S => _) ih
      tauto
    choose T Tg Tct hT using ih
    refine' ⟨⋃ (s) (H : s ∈ S), T s H, by simpa, Sct.bUnion Tct, _⟩
    apply subset_sInter
    intro s H
    refine' subset_trans (sInter_subset_sInter (subset_Union₂ s H)) (hT s H)
  rcases h with ⟨S, Sg, Sct, hS⟩
  refine' mem_of_superset ((countable_sInter_mem Sct).mpr _) hS
  intro s H
  exact countable_generate_sets.basic (Sg H)
#align filter.mem_countable_generate_iff Filter.mem_countableGenerate_iff
-/

#print Filter.le_countableGenerate_iff_of_countableInterFilter /-
theorem le_countableGenerate_iff_of_countableInterFilter {f : Filter α} [CountableInterFilter f] :
    f ≤ countableGenerate g ↔ g ⊆ f.sets :=
  by
  constructor <;> intro h
  · exact subset_trans (fun s => countable_generate_sets.basic) h
  intro s hs
  induction' hs with s hs s t hs st ih S Sct hS ih
  · exact h hs
  · exact univ_mem
  · exact mem_of_superset ih st
  exact (countable_sInter_mem Sct).mpr ih
#align filter.le_countable_generate_iff_of_countable_Inter_filter Filter.le_countableGenerate_iff_of_countableInterFilter
-/

variable (g)

#print Filter.countableGenerate_isGreatest /-
/-- `countable_generate g` is the greatest `countable_Inter_filter` containing `g`.-/
theorem countableGenerate_isGreatest :
    IsGreatest {f : Filter α | CountableInterFilter f ∧ g ⊆ f.sets} (countableGenerate g) :=
  by
  refine' ⟨⟨inferInstance, fun s => countable_generate_sets.basic⟩, _⟩
  rintro f ⟨fct, hf⟩
  rwa [@le_countable_generate_iff_of_countable_Inter_filter _ _ _ fct]
#align filter.countable_generate_is_greatest Filter.countableGenerate_isGreatest
-/

end Filter

