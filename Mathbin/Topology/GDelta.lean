/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module topology.G_delta
! leanprover-community/mathlib commit e001509c11c4d0f549d91d89da95b4a0b43c714f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.Basic
import Mathbin.Topology.Separation

/-!
# `Gδ` sets

In this file we define `Gδ` sets and prove their basic properties.

## Main definitions

* `is_Gδ`: a set `s` is a `Gδ` set if it can be represented as an intersection
  of countably many open sets;

* `residual`: the filter of residual sets. A set `s` is called *residual* if it includes a dense
  `Gδ` set. In a Baire space (e.g., in a complete (e)metric space), residual sets form a filter.

  For technical reasons, we define `residual` in any topological space but the definition agrees
  with the description above only in Baire spaces.

## Main results

We prove that finite or countable intersections of Gδ sets is a Gδ set. We also prove that the
continuity set of a function from a topological space to an (e)metric space is a Gδ set.

## Tags

Gδ set, residual set
-/


noncomputable section

open Classical TopologicalSpace Filter uniformity

open Filter Encodable Set

variable {α : Type _} {β : Type _} {γ : Type _} {ι : Type _}

section IsGδ

variable [TopologicalSpace α]

/-- A Gδ set is a countable intersection of open sets. -/
def IsGδ (s : Set α) : Prop :=
  ∃ T : Set (Set α), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T
#align is_Gδ IsGδ

/-- An open set is a Gδ set. -/
theorem IsOpen.is_Gδ {s : Set α} (h : IsOpen s) : IsGδ s :=
  ⟨{s}, by simp [h], countable_singleton _, (Set.interₛ_singleton _).symm⟩
#align is_open.is_Gδ IsOpen.is_Gδ

@[simp]
theorem is_Gδ_empty : IsGδ (∅ : Set α) :=
  is_open_empty.IsGδ
#align is_Gδ_empty is_Gδ_empty

@[simp]
theorem is_Gδ_univ : IsGδ (univ : Set α) :=
  is_open_univ.IsGδ
#align is_Gδ_univ is_Gδ_univ

theorem is_Gδ_bInter_of_open {I : Set ι} (hI : I.Countable) {f : ι → Set α}
    (hf : ∀ i ∈ I, IsOpen (f i)) : IsGδ (⋂ i ∈ I, f i) :=
  ⟨f '' I, by rwa [ball_image_iff], hI.image _, by rw [sInter_image]⟩
#align is_Gδ_bInter_of_open is_Gδ_bInter_of_open

theorem is_Gδ_Inter_of_open [Encodable ι] {f : ι → Set α} (hf : ∀ i, IsOpen (f i)) :
    IsGδ (⋂ i, f i) :=
  ⟨range f, by rwa [forall_range_iff], countable_range _, by rw [sInter_range]⟩
#align is_Gδ_Inter_of_open is_Gδ_Inter_of_open

/-- The intersection of an encodable family of Gδ sets is a Gδ set. -/
theorem is_Gδ_Inter [Encodable ι] {s : ι → Set α} (hs : ∀ i, IsGδ (s i)) : IsGδ (⋂ i, s i) :=
  by
  choose T hTo hTc hTs using hs
  obtain rfl : s = fun i => ⋂₀ T i := funext hTs
  refine' ⟨⋃ i, T i, _, countable_Union hTc, (sInter_Union _).symm⟩
  simpa [@forall_swap ι] using hTo
#align is_Gδ_Inter is_Gδ_Inter

theorem is_Gδ_bInter {s : Set ι} (hs : s.Countable) {t : ∀ i ∈ s, Set α}
    (ht : ∀ i ∈ s, IsGδ (t i ‹_›)) : IsGδ (⋂ i ∈ s, t i ‹_›) :=
  by
  rw [bInter_eq_Inter]
  haveI := hs.to_encodable
  exact is_Gδ_Inter fun x => ht x x.2
#align is_Gδ_bInter is_Gδ_bInter

/-- A countable intersection of Gδ sets is a Gδ set. -/
theorem is_Gδ_sInter {S : Set (Set α)} (h : ∀ s ∈ S, IsGδ s) (hS : S.Countable) : IsGδ (⋂₀ S) := by
  simpa only [sInter_eq_bInter] using is_Gδ_bInter hS h
#align is_Gδ_sInter is_Gδ_sInter

theorem IsGδ.inter {s t : Set α} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∩ t) :=
  by
  rw [inter_eq_Inter]
  exact is_Gδ_Inter (Bool.forall_bool.2 ⟨ht, hs⟩)
#align is_Gδ.inter IsGδ.inter

/-- The union of two Gδ sets is a Gδ set. -/
theorem IsGδ.union {s t : Set α} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∪ t) :=
  by
  rcases hs with ⟨S, Sopen, Scount, rfl⟩
  rcases ht with ⟨T, Topen, Tcount, rfl⟩
  rw [sInter_union_sInter]
  apply is_Gδ_bInter_of_open (Scount.prod Tcount)
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  exact (Sopen a ha).union (Topen b hb)
#align is_Gδ.union IsGδ.union

/-- The union of finitely many Gδ sets is a Gδ set. -/
theorem is_Gδ_bUnion {s : Set ι} (hs : s.Finite) {f : ι → Set α} (h : ∀ i ∈ s, IsGδ (f i)) :
    IsGδ (⋃ i ∈ s, f i) := by
  refine' finite.induction_on hs (by simp) _ h
  simp only [ball_insert_iff, bUnion_insert]
  exact fun a s _ _ ihs H => H.1.union (ihs H.2)
#align is_Gδ_bUnion is_Gδ_bUnion

theorem IsClosed.is_Gδ {α} [UniformSpace α] [IsCountablyGenerated (𝓤 α)] {s : Set α}
    (hs : IsClosed s) : IsGδ s :=
  by
  rcases(@uniformity_has_basis_open α _).exists_antitone_subbasis with ⟨U, hUo, hU, -⟩
  rw [← hs.closure_eq, ← hU.bInter_bUnion_ball]
  refine' is_Gδ_bInter (to_countable _) fun n hn => IsOpen.is_Gδ _
  exact is_open_bUnion fun x hx => UniformSpace.is_open_ball _ (hUo _).2
#align is_closed.is_Gδ IsClosed.is_Gδ

section T1Space

variable [T1Space α]

theorem is_Gδ_compl_singleton (a : α) : IsGδ ({a}ᶜ : Set α) :=
  is_open_compl_singleton.IsGδ
#align is_Gδ_compl_singleton is_Gδ_compl_singleton

theorem Set.Countable.is_Gδ_compl {s : Set α} (hs : s.Countable) : IsGδ (sᶜ) :=
  by
  rw [← bUnion_of_singleton s, compl_Union₂]
  exact is_Gδ_bInter hs fun x _ => is_Gδ_compl_singleton x
#align set.countable.is_Gδ_compl Set.Countable.is_Gδ_compl

theorem Set.Finite.is_Gδ_compl {s : Set α} (hs : s.Finite) : IsGδ (sᶜ) :=
  hs.Countable.is_Gδ_compl
#align set.finite.is_Gδ_compl Set.Finite.is_Gδ_compl

theorem Set.Subsingleton.is_Gδ_compl {s : Set α} (hs : s.Subsingleton) : IsGδ (sᶜ) :=
  hs.Finite.is_Gδ_compl
#align set.subsingleton.is_Gδ_compl Set.Subsingleton.is_Gδ_compl

theorem Finset.is_Gδ_compl (s : Finset α) : IsGδ (sᶜ : Set α) :=
  s.finite_to_set.is_Gδ_compl
#align finset.is_Gδ_compl Finset.is_Gδ_compl

open TopologicalSpace

variable [FirstCountableTopology α]

theorem is_Gδ_singleton (a : α) : IsGδ ({a} : Set α) :=
  by
  rcases(nhds_basis_opens a).exists_antitone_subbasis with ⟨U, hU, h_basis⟩
  rw [← bInter_basis_nhds h_basis.to_has_basis]
  exact is_Gδ_bInter (to_countable _) fun n hn => (hU n).2.IsGδ
#align is_Gδ_singleton is_Gδ_singleton

theorem Set.Finite.is_Gδ {s : Set α} (hs : s.Finite) : IsGδ s :=
  (Finite.induction_on hs is_Gδ_empty) fun a s _ _ hs => (is_Gδ_singleton a).union hs
#align set.finite.is_Gδ Set.Finite.is_Gδ

end T1Space

end IsGδ

section ContinuousAt

open TopologicalSpace

open uniformity

variable [TopologicalSpace α]

/-- The set of points where a function is continuous is a Gδ set. -/
theorem is_Gδ_set_of_continuous_at [UniformSpace β] [IsCountablyGenerated (𝓤 β)] (f : α → β) :
    IsGδ { x | ContinuousAt f x } :=
  by
  obtain ⟨U, hUo, hU⟩ := (@uniformity_has_basis_open_symmetric β _).exists_antitone_subbasis
  simp only [Uniform.continuous_at_iff_prod, nhds_prod_eq]
  simp only [(nhds_basis_opens _).prod_self.tendsto_iff hU.to_has_basis, forall_prop_of_true,
    set_of_forall, id]
  refine' is_Gδ_Inter fun k => IsOpen.is_Gδ <| is_open_iff_mem_nhds.2 fun x => _
  rintro ⟨s, ⟨hsx, hso⟩, hsU⟩
  filter_upwards [IsOpen.mem_nhds hso hsx] with _ hy using⟨s, ⟨hy, hso⟩, hsU⟩
#align is_Gδ_set_of_continuous_at is_Gδ_set_of_continuous_at

end ContinuousAt

/-- A set `s` is called *residual* if it includes a dense `Gδ` set. If `α` is a Baire space
(e.g., a complete metric space), then residual sets form a filter, see `mem_residual`.

For technical reasons we define the filter `residual` in any topological space but in a non-Baire
space it is not useful because it may contain some non-residual sets. -/
def residual (α : Type _) [TopologicalSpace α] : Filter α :=
  ⨅ (t) (ht : IsGδ t) (ht' : Dense t), 𝓟 t
#align residual residual

