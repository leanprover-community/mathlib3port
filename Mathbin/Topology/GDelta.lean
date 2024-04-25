/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Topology.UniformSpace.Basic
import Topology.Separation
import Order.Filter.CountableInter

#align_import topology.G_delta from "leanprover-community/mathlib"@"b9e46fe101fc897fb2e7edaf0bf1f09ea49eb81a"

/-!
# `Gδ` sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `Gδ` sets and prove their basic properties.

## Main definitions

* `is_Gδ`: a set `s` is a `Gδ` set if it can be represented as an intersection
  of countably many open sets;

* `residual`: the σ-filter of residual sets. A set `s` is called *residual* if it includes a
  countable intersection of dense open sets.

## Main results

We prove that finite or countable intersections of Gδ sets is a Gδ set. We also prove that the
continuity set of a function from a topological space to an (e)metric space is a Gδ set.

## Tags

Gδ set, residual set
-/


noncomputable section

open scoped Classical Topology Filter uniformity

open Filter Encodable Set

variable {α : Type _} {β : Type _} {γ : Type _} {ι : Type _}

section IsGδ

variable [TopologicalSpace α]

#print IsGδ /-
/-- A Gδ set is a countable intersection of open sets. -/
def IsGδ (s : Set α) : Prop :=
  ∃ T : Set (Set α), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T
#align is_Gδ IsGδ
-/

#print IsOpen.isGδ /-
/-- An open set is a Gδ set. -/
theorem IsOpen.isGδ {s : Set α} (h : IsOpen s) : IsGδ s :=
  ⟨{s}, by simp [h], countable_singleton _, (Set.sInter_singleton _).symm⟩
#align is_open.is_Gδ IsOpen.isGδ
-/

#print IsGδ.empty /-
@[simp]
theorem IsGδ.empty : IsGδ (∅ : Set α) :=
  isOpen_empty.IsGδ
#align is_Gδ_empty IsGδ.empty
-/

#print IsGδ.univ /-
@[simp]
theorem IsGδ.univ : IsGδ (univ : Set α) :=
  isOpen_univ.IsGδ
#align is_Gδ_univ IsGδ.univ
-/

#print IsGδ.biInter_of_isOpen /-
theorem IsGδ.biInter_of_isOpen {I : Set ι} (hI : I.Countable) {f : ι → Set α}
    (hf : ∀ i ∈ I, IsOpen (f i)) : IsGδ (⋂ i ∈ I, f i) :=
  ⟨f '' I, by rwa [ball_image_iff], hI.image _, by rw [sInter_image]⟩
#align is_Gδ_bInter_of_open IsGδ.biInter_of_isOpen
-/

#print IsGδ.iInter_of_isOpen /-
theorem IsGδ.iInter_of_isOpen [Encodable ι] {f : ι → Set α} (hf : ∀ i, IsOpen (f i)) :
    IsGδ (⋂ i, f i) :=
  ⟨range f, by rwa [forall_range_iff], countable_range _, by rw [sInter_range]⟩
#align is_Gδ_Inter_of_open IsGδ.iInter_of_isOpen
-/

#print IsGδ.iInter /-
/-- The intersection of an encodable family of Gδ sets is a Gδ set. -/
theorem IsGδ.iInter [Encodable ι] {s : ι → Set α} (hs : ∀ i, IsGδ (s i)) : IsGδ (⋂ i, s i) :=
  by
  choose T hTo hTc hTs using hs
  obtain rfl : s = fun i => ⋂₀ T i := funext hTs
  refine' ⟨⋃ i, T i, _, countable_Union hTc, (sInter_Union _).symm⟩
  simpa [@forall_swap ι] using hTo
#align is_Gδ_Inter IsGδ.iInter
-/

#print IsGδ.biInter /-
theorem IsGδ.biInter {s : Set ι} (hs : s.Countable) {t : ∀ i ∈ s, Set α}
    (ht : ∀ i ∈ s, IsGδ (t i ‹_›)) : IsGδ (⋂ i ∈ s, t i ‹_›) :=
  by
  rw [bInter_eq_Inter]
  haveI := hs.to_encodable
  exact IsGδ.iInter fun x => ht x x.2
#align is_Gδ_bInter IsGδ.biInter
-/

#print IsGδ.sInter /-
/-- A countable intersection of Gδ sets is a Gδ set. -/
theorem IsGδ.sInter {S : Set (Set α)} (h : ∀ s ∈ S, IsGδ s) (hS : S.Countable) : IsGδ (⋂₀ S) := by
  simpa only [sInter_eq_bInter] using IsGδ.biInter hS h
#align is_Gδ_sInter IsGδ.sInter
-/

#print IsGδ.inter /-
theorem IsGδ.inter {s t : Set α} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∩ t) := by
  rw [inter_eq_Inter]; exact IsGδ.iInter (Bool.forall_bool.2 ⟨ht, hs⟩)
#align is_Gδ.inter IsGδ.inter
-/

#print IsGδ.union /-
/-- The union of two Gδ sets is a Gδ set. -/
theorem IsGδ.union {s t : Set α} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∪ t) :=
  by
  rcases hs with ⟨S, Sopen, Scount, rfl⟩
  rcases ht with ⟨T, Topen, Tcount, rfl⟩
  rw [sInter_union_sInter]
  apply IsGδ.biInter_of_isOpen (Scount.prod Tcount)
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  exact (Sopen a ha).union (Topen b hb)
#align is_Gδ.union IsGδ.union
-/

#print IsGδ.biUnion /-
/-- The union of finitely many Gδ sets is a Gδ set. -/
theorem IsGδ.biUnion {s : Set ι} (hs : s.Finite) {f : ι → Set α} (h : ∀ i ∈ s, IsGδ (f i)) :
    IsGδ (⋃ i ∈ s, f i) := by
  refine' finite.induction_on hs (by simp) _ h
  simp only [ball_insert_iff, bUnion_insert]
  exact fun a s _ _ ihs H => H.1.union (ihs H.2)
#align is_Gδ_bUnion IsGδ.biUnion
-/

#print IsClosed.isGδ /-
theorem IsClosed.isGδ {α} [UniformSpace α] [IsCountablyGenerated (𝓤 α)] {s : Set α}
    (hs : IsClosed s) : IsGδ s :=
  by
  rcases(@uniformity_hasBasis_open α _).exists_antitone_subbasis with ⟨U, hUo, hU, -⟩
  rw [← hs.closure_eq, ← hU.bInter_bUnion_ball]
  refine' IsGδ.biInter (to_countable _) fun n hn => IsOpen.isGδ _
  exact isOpen_biUnion fun x hx => UniformSpace.isOpen_ball _ (hUo _).2
#align is_closed.is_Gδ IsClosed.isGδ
-/

section T1Space

variable [T1Space α]

#print IsGδ.compl_singleton /-
theorem IsGδ.compl_singleton (a : α) : IsGδ ({a}ᶜ : Set α) :=
  isOpen_compl_singleton.IsGδ
#align is_Gδ_compl_singleton IsGδ.compl_singleton
-/

#print Set.Countable.isGδ_compl /-
theorem Set.Countable.isGδ_compl {s : Set α} (hs : s.Countable) : IsGδ (sᶜ) :=
  by
  rw [← bUnion_of_singleton s, compl_Union₂]
  exact IsGδ.biInter hs fun x _ => IsGδ.compl_singleton x
#align set.countable.is_Gδ_compl Set.Countable.isGδ_compl
-/

#print Set.Finite.isGδ_compl /-
theorem Set.Finite.isGδ_compl {s : Set α} (hs : s.Finite) : IsGδ (sᶜ) :=
  hs.Countable.isGδ_compl
#align set.finite.is_Gδ_compl Set.Finite.isGδ_compl
-/

#print Set.Subsingleton.isGδ_compl /-
theorem Set.Subsingleton.isGδ_compl {s : Set α} (hs : s.Subsingleton) : IsGδ (sᶜ) :=
  hs.Finite.isGδ_compl
#align set.subsingleton.is_Gδ_compl Set.Subsingleton.isGδ_compl
-/

#print Finset.isGδ_compl /-
theorem Finset.isGδ_compl (s : Finset α) : IsGδ (sᶜ : Set α) :=
  s.finite_toSet.isGδ_compl
#align finset.is_Gδ_compl Finset.isGδ_compl
-/

open TopologicalSpace

variable [FirstCountableTopology α]

#print IsGδ.singleton /-
theorem IsGδ.singleton (a : α) : IsGδ ({a} : Set α) :=
  by
  rcases(nhds_basis_opens a).exists_antitone_subbasis with ⟨U, hU, h_basis⟩
  rw [← biInter_basis_nhds h_basis.to_has_basis]
  exact IsGδ.biInter (to_countable _) fun n hn => (hU n).2.IsGδ
#align is_Gδ_singleton IsGδ.singleton
-/

#print Set.Finite.isGδ /-
theorem Set.Finite.isGδ {s : Set α} (hs : s.Finite) : IsGδ s :=
  Finite.induction_on hs IsGδ.empty fun a s _ _ hs => (IsGδ.singleton a).union hs
#align set.finite.is_Gδ Set.Finite.isGδ
-/

end T1Space

end IsGδ

section ContinuousAt

open TopologicalSpace

open scoped uniformity

variable [TopologicalSpace α]

#print IsGδ.setOf_continuousAt /-
/-- The set of points where a function is continuous is a Gδ set. -/
theorem IsGδ.setOf_continuousAt [UniformSpace β] [IsCountablyGenerated (𝓤 β)] (f : α → β) :
    IsGδ {x | ContinuousAt f x} :=
  by
  obtain ⟨U, hUo, hU⟩ := (@uniformity_hasBasis_open_symmetric β _).exists_antitone_subbasis
  simp only [Uniform.continuousAt_iff_prod, nhds_prod_eq]
  simp only [(nhds_basis_opens _).prod_self.tendsto_iffₓ hU.to_has_basis, forall_prop_of_true,
    set_of_forall, id]
  refine' IsGδ.iInter fun k => IsOpen.isGδ <| isOpen_iff_mem_nhds.2 fun x => _
  rintro ⟨s, ⟨hsx, hso⟩, hsU⟩
  filter_upwards [IsOpen.mem_nhds hso hsx] with _ hy using ⟨s, ⟨hy, hso⟩, hsU⟩
#align is_Gδ_set_of_continuous_at IsGδ.setOf_continuousAt
-/

end ContinuousAt

section residual

variable [TopologicalSpace α]

#print residual /-
/-- A set `s` is called *residual* if it includes a countable intersection of dense open sets. -/
def residual (α : Type _) [TopologicalSpace α] : Filter α :=
  Filter.countableGenerate {t | IsOpen t ∧ Dense t}
deriving CountableInterFilter
#align residual residual
-/

#print countableInterFilter_residual /-
instance countableInterFilter_residual : CountableInterFilter (residual α) := by
  rw [residual] <;> infer_instance
#align countable_Inter_filter_residual countableInterFilter_residual
-/

#print residual_of_dense_open /-
/-- Dense open sets are residual. -/
theorem residual_of_dense_open {s : Set α} (ho : IsOpen s) (hd : Dense s) : s ∈ residual α :=
  CountableGenerateSets.basic ⟨ho, hd⟩
#align residual_of_dense_open residual_of_dense_open
-/

#print residual_of_dense_Gδ /-
/-- Dense Gδ sets are residual. -/
theorem residual_of_dense_Gδ {s : Set α} (ho : IsGδ s) (hd : Dense s) : s ∈ residual α :=
  by
  rcases ho with ⟨T, To, Tct, rfl⟩
  exact
    (countable_sInter_mem Tct).mpr fun t tT =>
      residual_of_dense_open (To t tT) (hd.mono (sInter_subset_of_mem tT))
#align residual_of_dense_Gδ residual_of_dense_Gδ
-/

#print mem_residual_iff /-
/-- A set is residual iff it includes a countable intersection of dense open sets. -/
theorem mem_residual_iff {s : Set α} :
    s ∈ residual α ↔
      ∃ S : Set (Set α), (∀ t ∈ S, IsOpen t) ∧ (∀ t ∈ S, Dense t) ∧ S.Countable ∧ ⋂₀ S ⊆ s :=
  mem_countableGenerate_iff.trans <| by simp_rw [subset_def, mem_set_of, forall_and, and_assoc]
#align mem_residual_iff mem_residual_iff
-/

end residual

