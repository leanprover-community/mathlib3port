/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module topology.bases
! leanprover-community/mathlib commit f16e7a22e11fc09c71f25446ac1db23a24e8a0bd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Constructions
import Mathbin.Topology.ContinuousOn

/-!
# Bases of topologies. Countability axioms.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A topological basis on a topological space `t` is a collection of sets,
such that all open sets can be generated as unions of these sets, without the need to take
finite intersections of them. This file introduces a framework for dealing with these collections,
and also what more we can say under certain countability conditions on bases,
which are referred to as first- and second-countable.
We also briefly cover the theory of separable spaces, which are those with a countable, dense
subset. If a space is second-countable, and also has a countably generated uniformity filter
(for example, if `t` is a metric space), it will automatically be separable (and indeed, these
conditions are equivalent in this case).

## Main definitions

* `is_topological_basis s`: The topological space `t` has basis `s`.
* `separable_space α`: The topological space `t` has a countable, dense subset.
* `is_separable s`: The set `s` is contained in the closure of a countable set.
* `first_countable_topology α`: A topology in which `𝓝 x` is countably generated for every `x`.
* `second_countable_topology α`: A topology which has a topological basis which is countable.

## Main results

* `first_countable_topology.tendsto_subseq`: In a first-countable space,
  cluster points are limits of subsequences.
* `second_countable_topology.is_open_Union_countable`: In a second-countable space, the union of
  arbitrarily-many open sets is equal to a sub-union of only countably many of these sets.
* `second_countable_topology.countable_cover_nhds`: Consider `f : α → set α` with the property that
  `f x ∈ 𝓝 x` for all `x`. Then there is some countable set `s` whose image covers the space.

## Implementation Notes
For our applications we are interested that there exists a countable basis, but we do not need the
concrete basis itself. This allows us to declare these type classes as `Prop` to use them as mixins.

### TODO:
More fine grained instances for `first_countable_topology`, `separable_space`, `t2_space`, and more
(see the comment below `subtype.second_countable_topology`.)
-/


open Set Filter Function

open Topology Filter

noncomputable section

namespace TopologicalSpace

universe u

variable {α : Type u} [t : TopologicalSpace α]

include t

#print TopologicalSpace.IsTopologicalBasis /-
/-- A topological basis is one that satisfies the necessary conditions so that
  it suffices to take unions of the basis sets to get a topology (without taking
  finite intersections as well). -/
structure IsTopologicalBasis (s : Set (Set α)) : Prop where
  exists_subset_inter : ∀ t₁ ∈ s, ∀ t₂ ∈ s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃ ∈ s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂
  sUnion_eq : ⋃₀ s = univ
  eq_generateFrom : t = generateFrom s
#align topological_space.is_topological_basis TopologicalSpace.IsTopologicalBasis
-/

#print TopologicalSpace.IsTopologicalBasis.insert_empty /-
theorem IsTopologicalBasis.insert_empty {s : Set (Set α)} (h : IsTopologicalBasis s) :
    IsTopologicalBasis (insert ∅ s) :=
  by
  refine' ⟨_, by rw [sUnion_insert, empty_union, h.sUnion_eq], _⟩
  · rintro t₁ (rfl | h₁) t₂ (rfl | h₂) x ⟨hx₁, hx₂⟩
    · cases hx₁
    · cases hx₁
    · cases hx₂
    obtain ⟨t₃, h₃, hs⟩ := h.exists_subset_inter _ h₁ _ h₂ x ⟨hx₁, hx₂⟩
    exact ⟨t₃, Or.inr h₃, hs⟩
  · rw [h.eq_generate_from]
    refine' le_antisymm (le_generateFrom fun t => _) (generate_from_anti <| subset_insert ∅ s)
    rintro (rfl | ht)
    · convert isOpen_empty
    · exact generate_open.basic t ht
#align topological_space.is_topological_basis.insert_empty TopologicalSpace.IsTopologicalBasis.insert_empty
-/

/- warning: topological_space.is_topological_basis.diff_empty -> TopologicalSpace.IsTopologicalBasis.diff_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {s : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t s) -> (TopologicalSpace.IsTopologicalBasis.{u1} α t (SDiff.sdiff.{u1} (Set.{u1} (Set.{u1} α)) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} (Set.{u1} α)) (Set.booleanAlgebra.{u1} (Set.{u1} α))) s (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasSingleton.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {s : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t s) -> (TopologicalSpace.IsTopologicalBasis.{u1} α t (SDiff.sdiff.{u1} (Set.{u1} (Set.{u1} α)) (Set.instSDiffSet.{u1} (Set.{u1} α)) s (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instSingletonSet.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.diff_empty TopologicalSpace.IsTopologicalBasis.diff_emptyₓ'. -/
theorem IsTopologicalBasis.diff_empty {s : Set (Set α)} (h : IsTopologicalBasis s) :
    IsTopologicalBasis (s \ {∅}) :=
  by
  refine' ⟨_, by rw [sUnion_diff_singleton_empty, h.sUnion_eq], _⟩
  · rintro t₁ ⟨h₁, -⟩ t₂ ⟨h₂, -⟩ x hx
    obtain ⟨t₃, h₃, hs⟩ := h.exists_subset_inter _ h₁ _ h₂ x hx
    exact ⟨t₃, ⟨h₃, nonempty.ne_empty ⟨x, hs.1⟩⟩, hs⟩
  · rw [h.eq_generate_from]
    refine' le_antisymm (generate_from_anti <| diff_subset s _) (le_generateFrom fun t ht => _)
    obtain rfl | he := eq_or_ne t ∅
    · convert isOpen_empty
    exact generate_open.basic t ⟨ht, he⟩
#align topological_space.is_topological_basis.diff_empty TopologicalSpace.IsTopologicalBasis.diff_empty

#print TopologicalSpace.isTopologicalBasis_of_subbasis /-
/-- If a family of sets `s` generates the topology, then intersections of finite
subcollections of `s` form a topological basis. -/
theorem isTopologicalBasis_of_subbasis {s : Set (Set α)} (hs : t = generateFrom s) :
    IsTopologicalBasis ((fun f => ⋂₀ f) '' { f : Set (Set α) | f.Finite ∧ f ⊆ s }) :=
  by
  refine' ⟨_, _, hs.trans (le_antisymm (le_generateFrom _) <| generate_from_anti fun t ht => _)⟩
  · rintro _ ⟨t₁, ⟨hft₁, ht₁b⟩, rfl⟩ _ ⟨t₂, ⟨hft₂, ht₂b⟩, rfl⟩ x h
    exact ⟨_, ⟨_, ⟨hft₁.union hft₂, union_subset ht₁b ht₂b⟩, sInter_union t₁ t₂⟩, h, subset.rfl⟩
  · rw [sUnion_image, Union₂_eq_univ_iff]
    exact fun x => ⟨∅, ⟨finite_empty, empty_subset _⟩, sInter_empty.substr <| mem_univ x⟩
  · rintro _ ⟨t, ⟨hft, htb⟩, rfl⟩
    apply isOpen_sInter
    exacts[hft, fun s hs => generate_open.basic _ <| htb hs]
  · rw [← sInter_singleton t]
    exact ⟨{t}, ⟨finite_singleton t, singleton_subset_iff.2 ht⟩, rfl⟩
#align topological_space.is_topological_basis_of_subbasis TopologicalSpace.isTopologicalBasis_of_subbasis
-/

/- warning: topological_space.is_topological_basis_of_open_of_nhds -> TopologicalSpace.isTopologicalBasis_of_open_of_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {s : Set.{u1} (Set.{u1} α)}, (forall (u : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) u s) -> (IsOpen.{u1} α t u)) -> (forall (a : α) (u : Set.{u1} α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a u) -> (IsOpen.{u1} α t u) -> (Exists.{succ u1} (Set.{u1} α) (fun (v : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) v s) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) v s) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a v) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) v u))))) -> (TopologicalSpace.IsTopologicalBasis.{u1} α t s)
but is expected to have type
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {s : Set.{u1} (Set.{u1} α)}, (forall (u : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) u s) -> (IsOpen.{u1} α t u)) -> (forall (a : α) (u : Set.{u1} α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a u) -> (IsOpen.{u1} α t u) -> (Exists.{succ u1} (Set.{u1} α) (fun (v : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) v s) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a v) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) v u))))) -> (TopologicalSpace.IsTopologicalBasis.{u1} α t s)
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis_of_open_of_nhds TopologicalSpace.isTopologicalBasis_of_open_of_nhdsₓ'. -/
/-- If a family of open sets `s` is such that every open neighbourhood contains some
member of `s`, then `s` is a topological basis. -/
theorem isTopologicalBasis_of_open_of_nhds {s : Set (Set α)} (h_open : ∀ u ∈ s, IsOpen u)
    (h_nhds : ∀ (a : α) (u : Set α), a ∈ u → IsOpen u → ∃ v ∈ s, a ∈ v ∧ v ⊆ u) :
    IsTopologicalBasis s :=
  by
  refine'
    ⟨fun t₁ ht₁ t₂ ht₂ x hx => h_nhds _ _ hx (IsOpen.inter (h_open _ ht₁) (h_open _ ht₂)), _, _⟩
  · refine' sUnion_eq_univ_iff.2 fun a => _
    rcases h_nhds a univ trivial isOpen_univ with ⟨u, h₁, h₂, -⟩
    exact ⟨u, h₁, h₂⟩
  · refine' (le_generateFrom h_open).antisymm fun u hu => _
    refine' (@isOpen_iff_nhds α (generate_from s) u).mpr fun a ha => _
    rcases h_nhds a u ha hu with ⟨v, hvs, hav, hvu⟩
    rw [nhds_generate_from]
    exact iInf₂_le_of_le v ⟨hav, hvs⟩ (le_principal_iff.2 hvu)
#align topological_space.is_topological_basis_of_open_of_nhds TopologicalSpace.isTopologicalBasis_of_open_of_nhds

/- warning: topological_space.is_topological_basis.mem_nhds_iff -> TopologicalSpace.IsTopologicalBasis.mem_nhds_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α} {b : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t b) -> (Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α t a)) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t b) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t b) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s)))))
but is expected to have type
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {a : α} {s : Set.{u1} α} {b : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t b) -> (Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhds.{u1} α t a)) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t b) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s)))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.mem_nhds_iff TopologicalSpace.IsTopologicalBasis.mem_nhds_iffₓ'. -/
/-- A set `s` is in the neighbourhood of `a` iff there is some basis set `t`, which
contains `a` and is itself contained in `s`. -/
theorem IsTopologicalBasis.mem_nhds_iff {a : α} {s : Set α} {b : Set (Set α)}
    (hb : IsTopologicalBasis b) : s ∈ 𝓝 a ↔ ∃ t ∈ b, a ∈ t ∧ t ⊆ s :=
  by
  change s ∈ (𝓝 a).sets ↔ ∃ t ∈ b, a ∈ t ∧ t ⊆ s
  rw [hb.eq_generate_from, nhds_generate_from, binfi_sets_eq]
  · simp [and_assoc', and_left_comm]
  ·
    exact fun s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩ =>
      have : a ∈ s ∩ t := ⟨hs₁, ht₁⟩
      let ⟨u, hu₁, hu₂, hu₃⟩ := hb.1 _ hs₂ _ ht₂ _ this
      ⟨u, ⟨hu₂, hu₁⟩, le_principal_iff.2 (subset.trans hu₃ (inter_subset_left _ _)),
        le_principal_iff.2 (subset.trans hu₃ (inter_subset_right _ _))⟩
  · rcases eq_univ_iff_forall.1 hb.sUnion_eq a with ⟨i, h1, h2⟩
    exact ⟨i, h2, h1⟩
#align topological_space.is_topological_basis.mem_nhds_iff TopologicalSpace.IsTopologicalBasis.mem_nhds_iff

/- warning: topological_space.is_topological_basis.is_open_iff -> TopologicalSpace.IsTopologicalBasis.isOpen_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {s : Set.{u1} α} {b : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t b) -> (Iff (IsOpen.{u1} α t s) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t b) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t b) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s))))))
but is expected to have type
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {s : Set.{u1} α} {b : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t b) -> (Iff (IsOpen.{u1} α t s) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t b) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s))))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.is_open_iff TopologicalSpace.IsTopologicalBasis.isOpen_iffₓ'. -/
theorem IsTopologicalBasis.isOpen_iff {s : Set α} {b : Set (Set α)} (hb : IsTopologicalBasis b) :
    IsOpen s ↔ ∀ a ∈ s, ∃ t ∈ b, a ∈ t ∧ t ⊆ s := by simp [isOpen_iff_mem_nhds, hb.mem_nhds_iff]
#align topological_space.is_topological_basis.is_open_iff TopologicalSpace.IsTopologicalBasis.isOpen_iff

#print TopologicalSpace.IsTopologicalBasis.nhds_hasBasis /-
theorem IsTopologicalBasis.nhds_hasBasis {b : Set (Set α)} (hb : IsTopologicalBasis b) {a : α} :
    (𝓝 a).HasBasis (fun t : Set α => t ∈ b ∧ a ∈ t) fun t => t :=
  ⟨fun s => hb.mem_nhds_iffₓ.trans <| by simp only [exists_prop, and_assoc']⟩
#align topological_space.is_topological_basis.nhds_has_basis TopologicalSpace.IsTopologicalBasis.nhds_hasBasis
-/

#print TopologicalSpace.IsTopologicalBasis.isOpen /-
protected theorem IsTopologicalBasis.isOpen {s : Set α} {b : Set (Set α)}
    (hb : IsTopologicalBasis b) (hs : s ∈ b) : IsOpen s :=
  by
  rw [hb.eq_generate_from]
  exact generate_open.basic s hs
#align topological_space.is_topological_basis.is_open TopologicalSpace.IsTopologicalBasis.isOpen
-/

#print TopologicalSpace.IsTopologicalBasis.mem_nhds /-
protected theorem IsTopologicalBasis.mem_nhds {a : α} {s : Set α} {b : Set (Set α)}
    (hb : IsTopologicalBasis b) (hs : s ∈ b) (ha : a ∈ s) : s ∈ 𝓝 a :=
  (hb.IsOpen hs).mem_nhds ha
#align topological_space.is_topological_basis.mem_nhds TopologicalSpace.IsTopologicalBasis.mem_nhds
-/

/- warning: topological_space.is_topological_basis.exists_subset_of_mem_open -> TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {b : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t b) -> (forall {a : α} {u : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a u) -> (IsOpen.{u1} α t u) -> (Exists.{succ u1} (Set.{u1} α) (fun (v : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) v b) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) v b) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a v) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) v u)))))
but is expected to have type
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {b : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t b) -> (forall {a : α} {u : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a u) -> (IsOpen.{u1} α t u) -> (Exists.{succ u1} (Set.{u1} α) (fun (v : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) v b) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a v) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) v u)))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.exists_subset_of_mem_open TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_openₓ'. -/
theorem IsTopologicalBasis.exists_subset_of_mem_open {b : Set (Set α)} (hb : IsTopologicalBasis b)
    {a : α} {u : Set α} (au : a ∈ u) (ou : IsOpen u) : ∃ v ∈ b, a ∈ v ∧ v ⊆ u :=
  hb.mem_nhds_iffₓ.1 <| IsOpen.mem_nhds ou au
#align topological_space.is_topological_basis.exists_subset_of_mem_open TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open

#print TopologicalSpace.IsTopologicalBasis.open_eq_sUnion' /-
/-- Any open set is the union of the basis sets contained in it. -/
theorem IsTopologicalBasis.open_eq_sUnion' {B : Set (Set α)} (hB : IsTopologicalBasis B) {u : Set α}
    (ou : IsOpen u) : u = ⋃₀ { s ∈ B | s ⊆ u } :=
  ext fun a =>
    ⟨fun ha =>
      let ⟨b, hb, ab, bu⟩ := hB.exists_subset_of_mem_open ha ou
      ⟨b, ⟨hb, bu⟩, ab⟩,
      fun ⟨b, ⟨hb, bu⟩, ab⟩ => bu ab⟩
#align topological_space.is_topological_basis.open_eq_sUnion' TopologicalSpace.IsTopologicalBasis.open_eq_sUnion'
-/

/- warning: topological_space.is_topological_basis.open_eq_sUnion -> TopologicalSpace.IsTopologicalBasis.open_eq_sUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {B : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t B) -> (forall {u : Set.{u1} α}, (IsOpen.{u1} α t u) -> (Exists.{succ u1} (Set.{u1} (Set.{u1} α)) (fun (S : Set.{u1} (Set.{u1} α)) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasSubset.{u1} (Set.{u1} α)) S B) (fun (H : HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasSubset.{u1} (Set.{u1} α)) S B) => Eq.{succ u1} (Set.{u1} α) u (Set.sUnion.{u1} α S)))))
but is expected to have type
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {B : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t B) -> (forall {u : Set.{u1} α}, (IsOpen.{u1} α t u) -> (Exists.{succ u1} (Set.{u1} (Set.{u1} α)) (fun (S : Set.{u1} (Set.{u1} α)) => And (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.instHasSubsetSet.{u1} (Set.{u1} α)) S B) (Eq.{succ u1} (Set.{u1} α) u (Set.sUnion.{u1} α S)))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.open_eq_sUnion TopologicalSpace.IsTopologicalBasis.open_eq_sUnionₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (S «expr ⊆ » B) -/
theorem IsTopologicalBasis.open_eq_sUnion {B : Set (Set α)} (hB : IsTopologicalBasis B) {u : Set α}
    (ou : IsOpen u) : ∃ (S : _)(_ : S ⊆ B), u = ⋃₀ S :=
  ⟨{ s ∈ B | s ⊆ u }, fun s h => h.1, hB.open_eq_sUnion' ou⟩
#align topological_space.is_topological_basis.open_eq_sUnion TopologicalSpace.IsTopologicalBasis.open_eq_sUnion

/- warning: topological_space.is_topological_basis.open_iff_eq_sUnion -> TopologicalSpace.IsTopologicalBasis.open_iff_eq_sUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {B : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t B) -> (forall {u : Set.{u1} α}, Iff (IsOpen.{u1} α t u) (Exists.{succ u1} (Set.{u1} (Set.{u1} α)) (fun (S : Set.{u1} (Set.{u1} α)) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasSubset.{u1} (Set.{u1} α)) S B) (fun (H : HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasSubset.{u1} (Set.{u1} α)) S B) => Eq.{succ u1} (Set.{u1} α) u (Set.sUnion.{u1} α S)))))
but is expected to have type
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {B : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t B) -> (forall {u : Set.{u1} α}, Iff (IsOpen.{u1} α t u) (Exists.{succ u1} (Set.{u1} (Set.{u1} α)) (fun (S : Set.{u1} (Set.{u1} α)) => And (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.instHasSubsetSet.{u1} (Set.{u1} α)) S B) (Eq.{succ u1} (Set.{u1} α) u (Set.sUnion.{u1} α S)))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.open_iff_eq_sUnion TopologicalSpace.IsTopologicalBasis.open_iff_eq_sUnionₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (S «expr ⊆ » B) -/
theorem IsTopologicalBasis.open_iff_eq_sUnion {B : Set (Set α)} (hB : IsTopologicalBasis B)
    {u : Set α} : IsOpen u ↔ ∃ (S : _)(_ : S ⊆ B), u = ⋃₀ S :=
  ⟨hB.open_eq_sUnion, fun ⟨S, hSB, hu⟩ => hu.symm ▸ isOpen_sUnion fun s hs => hB.IsOpen (hSB hs)⟩
#align topological_space.is_topological_basis.open_iff_eq_sUnion TopologicalSpace.IsTopologicalBasis.open_iff_eq_sUnion

#print TopologicalSpace.IsTopologicalBasis.open_eq_iUnion /-
theorem IsTopologicalBasis.open_eq_iUnion {B : Set (Set α)} (hB : IsTopologicalBasis B) {u : Set α}
    (ou : IsOpen u) : ∃ (β : Type u)(f : β → Set α), (u = ⋃ i, f i) ∧ ∀ i, f i ∈ B :=
  ⟨↥({ s ∈ B | s ⊆ u }), coe, by
    rw [← sUnion_eq_Union]
    apply hB.open_eq_sUnion' ou, fun s => And.left s.2⟩
#align topological_space.is_topological_basis.open_eq_Union TopologicalSpace.IsTopologicalBasis.open_eq_iUnion
-/

/- warning: topological_space.is_topological_basis.mem_closure_iff -> TopologicalSpace.IsTopologicalBasis.mem_closure_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {b : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t b) -> (forall {s : Set.{u1} α} {a : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (closure.{u1} α t s)) (forall (o : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) o b) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a o) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) o s))))
but is expected to have type
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {b : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t b) -> (forall {s : Set.{u1} α} {a : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (closure.{u1} α t s)) (forall (o : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) o b) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a o) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) o s))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.mem_closure_iff TopologicalSpace.IsTopologicalBasis.mem_closure_iffₓ'. -/
/-- A point `a` is in the closure of `s` iff all basis sets containing `a` intersect `s`. -/
theorem IsTopologicalBasis.mem_closure_iff {b : Set (Set α)} (hb : IsTopologicalBasis b) {s : Set α}
    {a : α} : a ∈ closure s ↔ ∀ o ∈ b, a ∈ o → (o ∩ s).Nonempty :=
  (mem_closure_iff_nhds_basis' hb.nhds_hasBasis).trans <| by simp only [and_imp]
#align topological_space.is_topological_basis.mem_closure_iff TopologicalSpace.IsTopologicalBasis.mem_closure_iff

/- warning: topological_space.is_topological_basis.dense_iff -> TopologicalSpace.IsTopologicalBasis.dense_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {b : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t b) -> (forall {s : Set.{u1} α}, Iff (Dense.{u1} α t s) (forall (o : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) o b) -> (Set.Nonempty.{u1} α o) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) o s))))
but is expected to have type
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {b : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t b) -> (forall {s : Set.{u1} α}, Iff (Dense.{u1} α t s) (forall (o : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) o b) -> (Set.Nonempty.{u1} α o) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) o s))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.dense_iff TopologicalSpace.IsTopologicalBasis.dense_iffₓ'. -/
/-- A set is dense iff it has non-trivial intersection with all basis sets. -/
theorem IsTopologicalBasis.dense_iff {b : Set (Set α)} (hb : IsTopologicalBasis b) {s : Set α} :
    Dense s ↔ ∀ o ∈ b, Set.Nonempty o → (o ∩ s).Nonempty :=
  by
  simp only [Dense, hb.mem_closure_iff]
  exact ⟨fun h o hb ⟨a, ha⟩ => h a o hb ha, fun h a o hb ha => h o hb ⟨a, ha⟩⟩
#align topological_space.is_topological_basis.dense_iff TopologicalSpace.IsTopologicalBasis.dense_iff

/- warning: topological_space.is_topological_basis.is_open_map_iff -> TopologicalSpace.IsTopologicalBasis.isOpenMap_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {B : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t B) -> (forall {f : α -> β}, Iff (IsOpenMap.{u1, u2} α β t _inst_1 f) (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s B) -> (IsOpen.{u2} β _inst_1 (Set.image.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u2}} [t : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} β] {B : Set.{u2} (Set.{u2} α)}, (TopologicalSpace.IsTopologicalBasis.{u2} α t B) -> (forall {f : α -> β}, Iff (IsOpenMap.{u2, u1} α β t _inst_1 f) (forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s B) -> (IsOpen.{u1} β _inst_1 (Set.image.{u2, u1} α β f s))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.is_open_map_iff TopologicalSpace.IsTopologicalBasis.isOpenMap_iffₓ'. -/
theorem IsTopologicalBasis.isOpenMap_iff {β} [TopologicalSpace β] {B : Set (Set α)}
    (hB : IsTopologicalBasis B) {f : α → β} : IsOpenMap f ↔ ∀ s ∈ B, IsOpen (f '' s) :=
  by
  refine' ⟨fun H o ho => H _ (hB.is_open ho), fun hf o ho => _⟩
  rw [hB.open_eq_sUnion' ho, sUnion_eq_Union, image_Union]
  exact isOpen_iUnion fun s => hf s s.2.1
#align topological_space.is_topological_basis.is_open_map_iff TopologicalSpace.IsTopologicalBasis.isOpenMap_iff

/- warning: topological_space.is_topological_basis.exists_nonempty_subset -> TopologicalSpace.IsTopologicalBasis.exists_nonempty_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {B : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t B) -> (forall {u : Set.{u1} α}, (Set.Nonempty.{u1} α u) -> (IsOpen.{u1} α t u) -> (Exists.{succ u1} (Set.{u1} α) (fun (v : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) v B) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) v B) => And (Set.Nonempty.{u1} α v) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) v u)))))
but is expected to have type
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {B : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t B) -> (forall {u : Set.{u1} α}, (Set.Nonempty.{u1} α u) -> (IsOpen.{u1} α t u) -> (Exists.{succ u1} (Set.{u1} α) (fun (v : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) v B) (And (Set.Nonempty.{u1} α v) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) v u)))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.exists_nonempty_subset TopologicalSpace.IsTopologicalBasis.exists_nonempty_subsetₓ'. -/
theorem IsTopologicalBasis.exists_nonempty_subset {B : Set (Set α)} (hb : IsTopologicalBasis B)
    {u : Set α} (hu : u.Nonempty) (ou : IsOpen u) : ∃ v ∈ B, Set.Nonempty v ∧ v ⊆ u :=
  by
  cases' hu with x hx
  rw [hb.open_eq_sUnion' ou, mem_sUnion] at hx
  rcases hx with ⟨v, hv, hxv⟩
  exact ⟨v, hv.1, ⟨x, hxv⟩, hv.2⟩
#align topological_space.is_topological_basis.exists_nonempty_subset TopologicalSpace.IsTopologicalBasis.exists_nonempty_subset

#print TopologicalSpace.isTopologicalBasis_opens /-
theorem isTopologicalBasis_opens : IsTopologicalBasis { U : Set α | IsOpen U } :=
  isTopologicalBasis_of_open_of_nhds (by tauto) (by tauto)
#align topological_space.is_topological_basis_opens TopologicalSpace.isTopologicalBasis_opens
-/

/- warning: topological_space.is_topological_basis.prod -> TopologicalSpace.IsTopologicalBasis.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {B₁ : Set.{u1} (Set.{u1} α)} {B₂ : Set.{u2} (Set.{u2} β)}, (TopologicalSpace.IsTopologicalBasis.{u1} α t B₁) -> (TopologicalSpace.IsTopologicalBasis.{u2} β _inst_1 B₂) -> (TopologicalSpace.IsTopologicalBasis.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β t _inst_1) (Set.image2.{u1, u2, max u1 u2} (Set.{u1} α) (Set.{u2} β) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β) B₁ B₂))
but is expected to have type
  forall {α : Type.{u2}} [t : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} β] {B₁ : Set.{u2} (Set.{u2} α)} {B₂ : Set.{u1} (Set.{u1} β)}, (TopologicalSpace.IsTopologicalBasis.{u2} α t B₁) -> (TopologicalSpace.IsTopologicalBasis.{u1} β _inst_1 B₂) -> (TopologicalSpace.IsTopologicalBasis.{max u1 u2} (Prod.{u2, u1} α β) (instTopologicalSpaceProd.{u2, u1} α β t _inst_1) (Set.image2.{u2, u1, max u1 u2} (Set.{u2} α) (Set.{u1} β) (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β) B₁ B₂))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.prod TopologicalSpace.IsTopologicalBasis.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:228:8: unsupported: ambiguous notation -/
protected theorem IsTopologicalBasis.prod {β} [TopologicalSpace β] {B₁ : Set (Set α)}
    {B₂ : Set (Set β)} (h₁ : IsTopologicalBasis B₁) (h₂ : IsTopologicalBasis B₂) :
    IsTopologicalBasis (image2 (· ×ˢ ·) B₁ B₂) :=
  by
  refine' is_topological_basis_of_open_of_nhds _ _
  · rintro _ ⟨u₁, u₂, hu₁, hu₂, rfl⟩
    exact (h₁.is_open hu₁).Prod (h₂.is_open hu₂)
  · rintro ⟨a, b⟩ u hu uo
    rcases(h₁.nhds_has_basis.prod_nhds h₂.nhds_has_basis).mem_iff.1 (IsOpen.mem_nhds uo hu) with
      ⟨⟨s, t⟩, ⟨⟨hs, ha⟩, ht, hb⟩, hu⟩
    exact ⟨s ×ˢ t, mem_image2_of_mem hs ht, ⟨ha, hb⟩, hu⟩
#align topological_space.is_topological_basis.prod TopologicalSpace.IsTopologicalBasis.prod

/- warning: topological_space.is_topological_basis.inducing -> TopologicalSpace.IsTopologicalBasis.inducing is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {f : α -> β} {T : Set.{u2} (Set.{u2} β)}, (Inducing.{u1, u2} α β t _inst_1 f) -> (TopologicalSpace.IsTopologicalBasis.{u2} β _inst_1 T) -> (TopologicalSpace.IsTopologicalBasis.{u1} α t (Set.image.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Set.preimage.{u1, u2} α β f) T))
but is expected to have type
  forall {α : Type.{u2}} [t : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} β] {f : α -> β} {T : Set.{u1} (Set.{u1} β)}, (Inducing.{u2, u1} α β t _inst_1 f) -> (TopologicalSpace.IsTopologicalBasis.{u1} β _inst_1 T) -> (TopologicalSpace.IsTopologicalBasis.{u2} α t (Set.image.{u1, u2} (Set.{u1} β) (Set.{u2} α) (Set.preimage.{u2, u1} α β f) T))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.inducing TopologicalSpace.IsTopologicalBasis.inducingₓ'. -/
protected theorem IsTopologicalBasis.inducing {β} [TopologicalSpace β] {f : α → β} {T : Set (Set β)}
    (hf : Inducing f) (h : IsTopologicalBasis T) : IsTopologicalBasis (image (preimage f) T) :=
  by
  refine' is_topological_basis_of_open_of_nhds _ _
  · rintro _ ⟨V, hV, rfl⟩
    rwa [hf.is_open_iff]
    refine' ⟨V, h.is_open hV, rfl⟩
  · intro a U ha hU
    rw [hf.is_open_iff] at hU
    obtain ⟨V, hV, rfl⟩ := hU
    obtain ⟨S, hS, rfl⟩ := h.open_eq_sUnion hV
    obtain ⟨W, hW, ha⟩ := ha
    refine' ⟨f ⁻¹' W, ⟨_, hS hW, rfl⟩, ha, Set.preimage_mono <| Set.subset_sUnion_of_mem hW⟩
#align topological_space.is_topological_basis.inducing TopologicalSpace.IsTopologicalBasis.inducing

/- warning: topological_space.is_topological_basis_of_cover -> TopologicalSpace.isTopologicalBasis_of_cover is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {ι : Sort.{u2}} {U : ι -> (Set.{u1} α)}, (forall (i : ι), IsOpen.{u1} α t (U i)) -> (Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, u2} α ι (fun (i : ι) => U i)) (Set.univ.{u1} α)) -> (forall {b : forall (i : ι), Set.{u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (U i)))}, (forall (i : ι), TopologicalSpace.IsTopologicalBasis.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (U i)) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (U i)) t) (b i)) -> (TopologicalSpace.IsTopologicalBasis.{u1} α t (Set.iUnion.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => Set.image.{u1, u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (U i))) (Set.{u1} α) (Set.image.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (U i)) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (U i)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (U i)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (U i)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (U i)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (U i)))))))) (b i)))))
but is expected to have type
  forall {α : Type.{u2}} [t : TopologicalSpace.{u2} α] {ι : Sort.{u1}} {U : ι -> (Set.{u2} α)}, (forall (i : ι), IsOpen.{u2} α t (U i)) -> (Eq.{succ u2} (Set.{u2} α) (Set.iUnion.{u2, u1} α ι (fun (i : ι) => U i)) (Set.univ.{u2} α)) -> (forall {b : forall (i : ι), Set.{u2} (Set.{u2} (Set.Elem.{u2} α (U i)))}, (forall (i : ι), TopologicalSpace.IsTopologicalBasis.{u2} (Set.Elem.{u2} α (U i)) (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (U i)) t) (b i)) -> (TopologicalSpace.IsTopologicalBasis.{u2} α t (Set.iUnion.{u2, u1} (Set.{u2} α) ι (fun (i : ι) => Set.image.{u2, u2} (Set.{u2} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (U i)))) (Set.{u2} α) (Set.image.{u2, u2} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (U i))) α (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (U i)))) (b i)))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis_of_cover TopologicalSpace.isTopologicalBasis_of_coverₓ'. -/
theorem isTopologicalBasis_of_cover {ι} {U : ι → Set α} (Uo : ∀ i, IsOpen (U i))
    (Uc : (⋃ i, U i) = univ) {b : ∀ i, Set (Set (U i))} (hb : ∀ i, IsTopologicalBasis (b i)) :
    IsTopologicalBasis (⋃ i : ι, image (coe : U i → α) '' b i) :=
  by
  refine' is_topological_basis_of_open_of_nhds (fun u hu => _) _
  · simp only [mem_Union, mem_image] at hu
    rcases hu with ⟨i, s, sb, rfl⟩
    exact (Uo i).isOpenMap_subtype_val _ ((hb i).IsOpen sb)
  · intro a u ha uo
    rcases Union_eq_univ_iff.1 Uc a with ⟨i, hi⟩
    lift a to ↥(U i) using hi
    rcases(hb i).exists_subset_of_mem_open ha (uo.preimage continuous_subtype_val) with
      ⟨v, hvb, hav, hvu⟩
    exact
      ⟨coe '' v, mem_Union.2 ⟨i, mem_image_of_mem _ hvb⟩, mem_image_of_mem _ hav,
        image_subset_iff.2 hvu⟩
#align topological_space.is_topological_basis_of_cover TopologicalSpace.isTopologicalBasis_of_cover

/- warning: topological_space.is_topological_basis.continuous -> TopologicalSpace.IsTopologicalBasis.continuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {B : Set.{u2} (Set.{u2} β)}, (TopologicalSpace.IsTopologicalBasis.{u2} β _inst_1 B) -> (forall (f : α -> β), (forall (s : Set.{u2} β), (Membership.Mem.{u2, u2} (Set.{u2} β) (Set.{u2} (Set.{u2} β)) (Set.hasMem.{u2} (Set.{u2} β)) s B) -> (IsOpen.{u1} α t (Set.preimage.{u1, u2} α β f s))) -> (Continuous.{u1, u2} α β t _inst_1 f))
but is expected to have type
  forall {α : Type.{u2}} [t : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} β] {B : Set.{u1} (Set.{u1} β)}, (TopologicalSpace.IsTopologicalBasis.{u1} β _inst_1 B) -> (forall (f : α -> β), (forall (s : Set.{u1} β), (Membership.mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.instMembershipSet.{u1} (Set.{u1} β)) s B) -> (IsOpen.{u2} α t (Set.preimage.{u2, u1} α β f s))) -> (Continuous.{u2, u1} α β t _inst_1 f))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.continuous TopologicalSpace.IsTopologicalBasis.continuousₓ'. -/
protected theorem IsTopologicalBasis.continuous {β : Type _} [TopologicalSpace β] {B : Set (Set β)}
    (hB : IsTopologicalBasis B) (f : α → β) (hf : ∀ s ∈ B, IsOpen (f ⁻¹' s)) : Continuous f := by
  rw [hB.eq_generate_from]; exact continuous_generateFrom hf
#align topological_space.is_topological_basis.continuous TopologicalSpace.IsTopologicalBasis.continuous

variable (α)

#print TopologicalSpace.SeparableSpace /-
/-- A separable space is one with a countable dense subset, available through
`topological_space.exists_countable_dense`. If `α` is also known to be nonempty, then
`topological_space.dense_seq` provides a sequence `ℕ → α` with dense range, see
`topological_space.dense_range_dense_seq`.

If `α` is a uniform space with countably generated uniformity filter (e.g., an `emetric_space`),
then this condition is equivalent to `topological_space.second_countable_topology α`. In this case
the latter should be used as a typeclass argument in theorems because Lean can automatically deduce
`separable_space` from `second_countable_topology` but it can't deduce `second_countable_topology`
and `emetric_space`. -/
class SeparableSpace : Prop where
  exists_countable_dense : ∃ s : Set α, s.Countable ∧ Dense s
#align topological_space.separable_space TopologicalSpace.SeparableSpace
-/

#print TopologicalSpace.exists_countable_dense /-
theorem exists_countable_dense [SeparableSpace α] : ∃ s : Set α, s.Countable ∧ Dense s :=
  SeparableSpace.exists_countable_dense
#align topological_space.exists_countable_dense TopologicalSpace.exists_countable_dense
-/

#print TopologicalSpace.exists_dense_seq /-
/-- A nonempty separable space admits a sequence with dense range. Instead of running `cases` on the
conclusion of this lemma, you might want to use `topological_space.dense_seq` and
`topological_space.dense_range_dense_seq`.

If `α` might be empty, then `exists_countable_dense` is the main way to use separability of `α`. -/
theorem exists_dense_seq [SeparableSpace α] [Nonempty α] : ∃ u : ℕ → α, DenseRange u :=
  by
  obtain ⟨s : Set α, hs, s_dense⟩ := exists_countable_dense α
  cases' set.countable_iff_exists_subset_range.mp hs with u hu
  exact ⟨u, s_dense.mono hu⟩
#align topological_space.exists_dense_seq TopologicalSpace.exists_dense_seq
-/

#print TopologicalSpace.denseSeq /-
/-- A dense sequence in a non-empty separable topological space.

If `α` might be empty, then `exists_countable_dense` is the main way to use separability of `α`. -/
def denseSeq [SeparableSpace α] [Nonempty α] : ℕ → α :=
  Classical.choose (exists_dense_seq α)
#align topological_space.dense_seq TopologicalSpace.denseSeq
-/

#print TopologicalSpace.denseRange_denseSeq /-
/-- The sequence `dense_seq α` has dense range. -/
@[simp]
theorem denseRange_denseSeq [SeparableSpace α] [Nonempty α] : DenseRange (denseSeq α) :=
  Classical.choose_spec (exists_dense_seq α)
#align topological_space.dense_range_dense_seq TopologicalSpace.denseRange_denseSeq
-/

variable {α}

#print TopologicalSpace.Countable.to_separableSpace /-
instance (priority := 100) Countable.to_separableSpace [Countable α] : SeparableSpace α
    where exists_countable_dense := ⟨Set.univ, Set.countable_univ, dense_univ⟩
#align topological_space.countable.to_separable_space TopologicalSpace.Countable.to_separableSpace
-/

/- warning: topological_space.separable_space_of_dense_range -> TopologicalSpace.separableSpace_of_denseRange is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {ι : Type.{u2}} [_inst_1 : Countable.{succ u2} ι] (u : ι -> α), (DenseRange.{u1, u2} α t ι u) -> (TopologicalSpace.SeparableSpace.{u1} α t)
but is expected to have type
  forall {α : Type.{u2}} [t : TopologicalSpace.{u2} α] {ι : Type.{u1}} [_inst_1 : Countable.{succ u1} ι] (u : ι -> α), (DenseRange.{u2, u1} α t ι u) -> (TopologicalSpace.SeparableSpace.{u2} α t)
Case conversion may be inaccurate. Consider using '#align topological_space.separable_space_of_dense_range TopologicalSpace.separableSpace_of_denseRangeₓ'. -/
theorem separableSpace_of_denseRange {ι : Type _} [Countable ι] (u : ι → α) (hu : DenseRange u) :
    SeparableSpace α :=
  ⟨⟨range u, countable_range u, hu⟩⟩
#align topological_space.separable_space_of_dense_range TopologicalSpace.separableSpace_of_denseRange

/- warning: set.pairwise_disjoint.countable_of_is_open -> Set.PairwiseDisjoint.countable_of_isOpen is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] [_inst_1 : TopologicalSpace.SeparableSpace.{u1} α t] {ι : Type.{u2}} {s : ι -> (Set.{u1} α)} {a : Set.{u2} ι}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) a s) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i a) -> (IsOpen.{u1} α t (s i))) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i a) -> (Set.Nonempty.{u1} α (s i))) -> (Set.Countable.{u2} ι a)
but is expected to have type
  forall {α : Type.{u2}} [t : TopologicalSpace.{u2} α] [_inst_1 : TopologicalSpace.SeparableSpace.{u2} α t] {ι : Type.{u1}} {s : ι -> (Set.{u2} α)} {a : Set.{u1} ι}, (Set.PairwiseDisjoint.{u2, u1} (Set.{u2} α) ι (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) a s) -> (forall (i : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i a) -> (IsOpen.{u2} α t (s i))) -> (forall (i : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i a) -> (Set.Nonempty.{u2} α (s i))) -> (Set.Countable.{u1} ι a)
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.countable_of_is_open Set.PairwiseDisjoint.countable_of_isOpenₓ'. -/
/-- In a separable space, a family of nonempty disjoint open sets is countable. -/
theorem Set.PairwiseDisjoint.countable_of_isOpen [SeparableSpace α] {ι : Type _} {s : ι → Set α}
    {a : Set ι} (h : a.PairwiseDisjoint s) (ha : ∀ i ∈ a, IsOpen (s i))
    (h'a : ∀ i ∈ a, (s i).Nonempty) : a.Countable :=
  by
  rcases exists_countable_dense α with ⟨u, ⟨u_encodable⟩, u_dense⟩
  have : ∀ i : a, ∃ y, y ∈ s i ∩ u := fun i =>
    dense_iff_inter_open.1 u_dense (s i) (ha i i.2) (h'a i i.2)
  choose f hfs hfu using this
  lift f to a → u using hfu
  have f_inj : injective f :=
    by
    refine'
      injective_iff_pairwise_ne.mpr ((h.subtype _ _).mono fun i j hij hfij => hij.le_bot ⟨hfs i, _⟩)
    simp only [congr_arg coe hfij, hfs j]
  exact ⟨@Encodable.ofInj _ _ u_encodable f f_inj⟩
#align set.pairwise_disjoint.countable_of_is_open Set.PairwiseDisjoint.countable_of_isOpen

/- warning: set.pairwise_disjoint.countable_of_nonempty_interior -> Set.PairwiseDisjoint.countable_of_nonempty_interior is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] [_inst_1 : TopologicalSpace.SeparableSpace.{u1} α t] {ι : Type.{u2}} {s : ι -> (Set.{u1} α)} {a : Set.{u2} ι}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) a s) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i a) -> (Set.Nonempty.{u1} α (interior.{u1} α t (s i)))) -> (Set.Countable.{u2} ι a)
but is expected to have type
  forall {α : Type.{u2}} [t : TopologicalSpace.{u2} α] [_inst_1 : TopologicalSpace.SeparableSpace.{u2} α t] {ι : Type.{u1}} {s : ι -> (Set.{u2} α)} {a : Set.{u1} ι}, (Set.PairwiseDisjoint.{u2, u1} (Set.{u2} α) ι (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) a s) -> (forall (i : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i a) -> (Set.Nonempty.{u2} α (interior.{u2} α t (s i)))) -> (Set.Countable.{u1} ι a)
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.countable_of_nonempty_interior Set.PairwiseDisjoint.countable_of_nonempty_interiorₓ'. -/
/-- In a separable space, a family of disjoint sets with nonempty interiors is countable. -/
theorem Set.PairwiseDisjoint.countable_of_nonempty_interior [SeparableSpace α] {ι : Type _}
    {s : ι → Set α} {a : Set ι} (h : a.PairwiseDisjoint s)
    (ha : ∀ i ∈ a, (interior (s i)).Nonempty) : a.Countable :=
  (h.mono fun i => interior_subset).countable_of_isOpen (fun i hi => isOpen_interior) ha
#align set.pairwise_disjoint.countable_of_nonempty_interior Set.PairwiseDisjoint.countable_of_nonempty_interior

#print TopologicalSpace.IsSeparable /-
/-- A set `s` in a topological space is separable if it is contained in the closure of a
countable set `c`. Beware that this definition does not require that `c` is contained in `s` (to
express the latter, use `separable_space s` or `is_separable (univ : set s))`. In metric spaces,
the two definitions are equivalent, see `topological_space.is_separable.separable_space`. -/
def IsSeparable (s : Set α) :=
  ∃ c : Set α, c.Countable ∧ s ⊆ closure c
#align topological_space.is_separable TopologicalSpace.IsSeparable
-/

#print TopologicalSpace.IsSeparable.mono /-
theorem IsSeparable.mono {s u : Set α} (hs : IsSeparable s) (hu : u ⊆ s) : IsSeparable u :=
  by
  rcases hs with ⟨c, c_count, hs⟩
  exact ⟨c, c_count, hu.trans hs⟩
#align topological_space.is_separable.mono TopologicalSpace.IsSeparable.mono
-/

/- warning: topological_space.is_separable.union -> TopologicalSpace.IsSeparable.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {s : Set.{u1} α} {u : Set.{u1} α}, (TopologicalSpace.IsSeparable.{u1} α t s) -> (TopologicalSpace.IsSeparable.{u1} α t u) -> (TopologicalSpace.IsSeparable.{u1} α t (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u))
but is expected to have type
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {s : Set.{u1} α} {u : Set.{u1} α}, (TopologicalSpace.IsSeparable.{u1} α t s) -> (TopologicalSpace.IsSeparable.{u1} α t u) -> (TopologicalSpace.IsSeparable.{u1} α t (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u))
Case conversion may be inaccurate. Consider using '#align topological_space.is_separable.union TopologicalSpace.IsSeparable.unionₓ'. -/
theorem IsSeparable.union {s u : Set α} (hs : IsSeparable s) (hu : IsSeparable u) :
    IsSeparable (s ∪ u) := by
  rcases hs with ⟨cs, cs_count, hcs⟩
  rcases hu with ⟨cu, cu_count, hcu⟩
  refine' ⟨cs ∪ cu, cs_count.union cu_count, _⟩
  exact
    union_subset (hcs.trans (closure_mono (subset_union_left _ _)))
      (hcu.trans (closure_mono (subset_union_right _ _)))
#align topological_space.is_separable.union TopologicalSpace.IsSeparable.union

#print TopologicalSpace.IsSeparable.closure /-
theorem IsSeparable.closure {s : Set α} (hs : IsSeparable s) : IsSeparable (closure s) :=
  by
  rcases hs with ⟨c, c_count, hs⟩
  exact ⟨c, c_count, by simpa using closure_mono hs⟩
#align topological_space.is_separable.closure TopologicalSpace.IsSeparable.closure
-/

/- warning: topological_space.is_separable_Union -> TopologicalSpace.isSeparable_iUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {ι : Type.{u2}} [_inst_1 : Countable.{succ u2} ι] {s : ι -> (Set.{u1} α)}, (forall (i : ι), TopologicalSpace.IsSeparable.{u1} α t (s i)) -> (TopologicalSpace.IsSeparable.{u1} α t (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => s i)))
but is expected to have type
  forall {α : Type.{u2}} [t : TopologicalSpace.{u2} α] {ι : Type.{u1}} [_inst_1 : Countable.{succ u1} ι] {s : ι -> (Set.{u2} α)}, (forall (i : ι), TopologicalSpace.IsSeparable.{u2} α t (s i)) -> (TopologicalSpace.IsSeparable.{u2} α t (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => s i)))
Case conversion may be inaccurate. Consider using '#align topological_space.is_separable_Union TopologicalSpace.isSeparable_iUnionₓ'. -/
theorem isSeparable_iUnion {ι : Type _} [Countable ι] {s : ι → Set α}
    (hs : ∀ i, IsSeparable (s i)) : IsSeparable (⋃ i, s i) :=
  by
  choose c hc h'c using hs
  refine' ⟨⋃ i, c i, countable_Union hc, Union_subset_iff.2 fun i => _⟩
  exact (h'c i).trans (closure_mono (subset_Union _ i))
#align topological_space.is_separable_Union TopologicalSpace.isSeparable_iUnion

#print Set.Countable.isSeparable /-
theorem Set.Countable.isSeparable {s : Set α} (hs : s.Countable) : IsSeparable s :=
  ⟨s, hs, subset_closure⟩
#align set.countable.is_separable Set.Countable.isSeparable
-/

#print Set.Finite.isSeparable /-
theorem Set.Finite.isSeparable {s : Set α} (hs : s.Finite) : IsSeparable s :=
  hs.Countable.IsSeparable
#align set.finite.is_separable Set.Finite.isSeparable
-/

#print TopologicalSpace.isSeparable_univ_iff /-
theorem isSeparable_univ_iff : IsSeparable (univ : Set α) ↔ SeparableSpace α :=
  by
  constructor
  · rintro ⟨c, c_count, hc⟩
    refine' ⟨⟨c, c_count, by rwa [dense_iff_closure_eq, ← univ_subset_iff]⟩⟩
  · intro h
    rcases exists_countable_dense α with ⟨c, c_count, hc⟩
    exact ⟨c, c_count, by rwa [univ_subset_iff, ← dense_iff_closure_eq]⟩
#align topological_space.is_separable_univ_iff TopologicalSpace.isSeparable_univ_iff
-/

#print TopologicalSpace.isSeparable_of_separableSpace /-
theorem isSeparable_of_separableSpace [h : SeparableSpace α] (s : Set α) : IsSeparable s :=
  IsSeparable.mono (isSeparable_univ_iff.2 h) (subset_univ _)
#align topological_space.is_separable_of_separable_space TopologicalSpace.isSeparable_of_separableSpace
-/

/- warning: topological_space.is_separable.image -> TopologicalSpace.IsSeparable.image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {s : Set.{u1} α}, (TopologicalSpace.IsSeparable.{u1} α t s) -> (forall {f : α -> β}, (Continuous.{u1, u2} α β t _inst_1 f) -> (TopologicalSpace.IsSeparable.{u2} β _inst_1 (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} [t : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} β] {s : Set.{u2} α}, (TopologicalSpace.IsSeparable.{u2} α t s) -> (forall {f : α -> β}, (Continuous.{u2, u1} α β t _inst_1 f) -> (TopologicalSpace.IsSeparable.{u1} β _inst_1 (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align topological_space.is_separable.image TopologicalSpace.IsSeparable.imageₓ'. -/
theorem IsSeparable.image {β : Type _} [TopologicalSpace β] {s : Set α} (hs : IsSeparable s)
    {f : α → β} (hf : Continuous f) : IsSeparable (f '' s) :=
  by
  rcases hs with ⟨c, c_count, hc⟩
  refine' ⟨f '' c, c_count.image _, _⟩
  rw [image_subset_iff]
  exact hc.trans (closure_subset_preimage_closure_image hf)
#align topological_space.is_separable.image TopologicalSpace.IsSeparable.image

#print TopologicalSpace.isSeparable_of_separableSpace_subtype /-
theorem isSeparable_of_separableSpace_subtype (s : Set α) [SeparableSpace s] : IsSeparable s :=
  by
  have : IsSeparable ((coe : s → α) '' (univ : Set s)) :=
    (is_separable_of_separable_space _).image continuous_subtype_val
  simpa only [image_univ, Subtype.range_coe_subtype]
#align topological_space.is_separable_of_separable_space_subtype TopologicalSpace.isSeparable_of_separableSpace_subtype
-/

end TopologicalSpace

open TopologicalSpace

/- warning: is_topological_basis_pi -> isTopologicalBasis_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (X i)] {T : forall (i : ι), Set.{u2} (Set.{u2} (X i))}, (forall (i : ι), TopologicalSpace.IsTopologicalBasis.{u2} (X i) (_inst_1 i) (T i)) -> (TopologicalSpace.IsTopologicalBasis.{max u1 u2} (forall (i : ι), X i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => X i) (fun (a : ι) => _inst_1 a)) (setOf.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), X i)) (fun (S : Set.{max u1 u2} (forall (i : ι), X i)) => Exists.{max (succ u1) (succ u2)} (forall (i : ι), Set.{u2} (X i)) (fun (U : forall (i : ι), Set.{u2} (X i)) => Exists.{succ u1} (Finset.{u1} ι) (fun (F : Finset.{u1} ι) => And (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i F) -> (Membership.Mem.{u2, u2} (Set.{u2} (X i)) (Set.{u2} (Set.{u2} (X i))) (Set.hasMem.{u2} (Set.{u2} (X i))) (U i) (T i))) (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), X i)) S (Set.pi.{u1, u2} ι (fun (i : ι) => X i) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) F) U)))))))
but is expected to have type
  forall {ι : Type.{u2}} {X : ι -> Type.{u1}} [_inst_1 : forall (i : ι), TopologicalSpace.{u1} (X i)] {T : forall (i : ι), Set.{u1} (Set.{u1} (X i))}, (forall (i : ι), TopologicalSpace.IsTopologicalBasis.{u1} (X i) (_inst_1 i) (T i)) -> (TopologicalSpace.IsTopologicalBasis.{max u2 u1} (forall (i : ι), X i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => X i) (fun (a : ι) => _inst_1 a)) (setOf.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), X i)) (fun (S : Set.{max u2 u1} (forall (i : ι), X i)) => Exists.{max (succ u2) (succ u1)} (forall (i : ι), Set.{u1} (X i)) (fun (U : forall (i : ι), Set.{u1} (X i)) => Exists.{succ u2} (Finset.{u2} ι) (fun (F : Finset.{u2} ι) => And (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i F) -> (Membership.mem.{u1, u1} (Set.{u1} (X i)) (Set.{u1} (Set.{u1} (X i))) (Set.instMembershipSet.{u1} (Set.{u1} (X i))) (U i) (T i))) (Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), X i)) S (Set.pi.{u2, u1} ι (fun (i : ι) => X i) (Finset.toSet.{u2} ι F) U)))))))
Case conversion may be inaccurate. Consider using '#align is_topological_basis_pi isTopologicalBasis_piₓ'. -/
theorem isTopologicalBasis_pi {ι : Type _} {X : ι → Type _} [∀ i, TopologicalSpace (X i)]
    {T : ∀ i, Set (Set (X i))} (cond : ∀ i, IsTopologicalBasis (T i)) :
    IsTopologicalBasis
      { S : Set (∀ i, X i) |
        ∃ (U : ∀ i, Set (X i))(F : Finset ι), (∀ i, i ∈ F → U i ∈ T i) ∧ S = (F : Set ι).pi U } :=
  by
  refine' is_topological_basis_of_open_of_nhds _ _
  · rintro _ ⟨U, F, h1, rfl⟩
    apply isOpen_set_pi F.finite_to_set
    intro i hi
    exact (cond i).IsOpen (h1 i hi)
  · intro a U ha hU
    obtain ⟨I, t, hta, htU⟩ :
      ∃ (I : Finset ι)(t : ∀ i : ι, Set (X i)), (∀ i, t i ∈ 𝓝 (a i)) ∧ Set.pi (↑I) t ⊆ U :=
      by
      rw [← Filter.mem_pi', ← nhds_pi]
      exact hU.mem_nhds ha
    have : ∀ i, ∃ V ∈ T i, a i ∈ V ∧ V ⊆ t i := fun i => (cond i).mem_nhds_iffₓ.1 (hta i)
    choose V hVT haV hVt
    exact
      ⟨_, ⟨V, I, fun i hi => hVT i, rfl⟩, fun i hi => haV i, (pi_mono fun i hi => hVt i).trans htU⟩
#align is_topological_basis_pi isTopologicalBasis_pi

/- warning: is_topological_basis_infi -> isTopologicalBasis_iInf is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Type.{u2}} {X : ι -> Type.{u3}} [t : forall (i : ι), TopologicalSpace.{u3} (X i)] {T : forall (i : ι), Set.{u3} (Set.{u3} (X i))}, (forall (i : ι), TopologicalSpace.IsTopologicalBasis.{u3} (X i) (t i) (T i)) -> (forall (f : forall (i : ι), β -> (X i)), TopologicalSpace.IsTopologicalBasis.{u1} β (iInf.{u1, succ u2} (TopologicalSpace.{u1} β) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} β) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} β) (TopologicalSpace.completeLattice.{u1} β))) ι (fun (i : ι) => TopologicalSpace.induced.{u1, u3} β (X i) (f i) (t i))) (setOf.{u1} (Set.{u1} β) (fun (S : Set.{u1} β) => Exists.{max (succ u2) (succ u3)} (forall (i : ι), Set.{u3} (X i)) (fun (U : forall (i : ι), Set.{u3} (X i)) => Exists.{succ u2} (Finset.{u2} ι) (fun (F : Finset.{u2} ι) => And (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i F) -> (Membership.Mem.{u3, u3} (Set.{u3} (X i)) (Set.{u3} (Set.{u3} (X i))) (Set.hasMem.{u3} (Set.{u3} (X i))) (U i) (T i))) (Eq.{succ u1} (Set.{u1} β) S (Set.iInter.{u1, succ u2} β ι (fun (i : ι) => Set.iInter.{u1, 0} β (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i F) (fun (hi : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i F) => Set.preimage.{u1, u3} β (X i) (f i) (U i))))))))))
but is expected to have type
  forall {β : Type.{u3}} {ι : Type.{u2}} {X : ι -> Type.{u1}} [t : forall (i : ι), TopologicalSpace.{u1} (X i)] {T : forall (i : ι), Set.{u1} (Set.{u1} (X i))}, (forall (i : ι), TopologicalSpace.IsTopologicalBasis.{u1} (X i) (t i) (T i)) -> (forall (f : forall (i : ι), β -> (X i)), TopologicalSpace.IsTopologicalBasis.{u3} β (iInf.{u3, succ u2} (TopologicalSpace.{u3} β) (ConditionallyCompleteLattice.toInfSet.{u3} (TopologicalSpace.{u3} β) (CompleteLattice.toConditionallyCompleteLattice.{u3} (TopologicalSpace.{u3} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u3} β))) ι (fun (i : ι) => TopologicalSpace.induced.{u3, u1} β (X i) (f i) (t i))) (setOf.{u3} (Set.{u3} β) (fun (S : Set.{u3} β) => Exists.{max (succ u2) (succ u1)} (forall (i : ι), Set.{u1} (X i)) (fun (U : forall (i : ι), Set.{u1} (X i)) => Exists.{succ u2} (Finset.{u2} ι) (fun (F : Finset.{u2} ι) => And (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i F) -> (Membership.mem.{u1, u1} (Set.{u1} (X i)) (Set.{u1} (Set.{u1} (X i))) (Set.instMembershipSet.{u1} (Set.{u1} (X i))) (U i) (T i))) (Eq.{succ u3} (Set.{u3} β) S (Set.iInter.{u3, succ u2} β ι (fun (i : ι) => Set.iInter.{u3, 0} β (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i F) (fun (hi : Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i F) => Set.preimage.{u3, u1} β (X i) (f i) (U i))))))))))
Case conversion may be inaccurate. Consider using '#align is_topological_basis_infi isTopologicalBasis_iInfₓ'. -/
theorem isTopologicalBasis_iInf {β : Type _} {ι : Type _} {X : ι → Type _}
    [t : ∀ i, TopologicalSpace (X i)] {T : ∀ i, Set (Set (X i))}
    (cond : ∀ i, IsTopologicalBasis (T i)) (f : ∀ i, β → X i) :
    @IsTopologicalBasis β (⨅ i, induced (f i) (t i))
      { S |
        ∃ (U : ∀ i, Set (X i))(F : Finset ι),
          (∀ i, i ∈ F → U i ∈ T i) ∧ S = ⋂ (i) (hi : i ∈ F), f i ⁻¹' U i } :=
  by
  convert(isTopologicalBasis_pi cond).Inducing (inducing_iInf_to_pi _)
  ext V
  constructor
  · rintro ⟨U, F, h1, h2⟩
    have : (F : Set ι).pi U = ⋂ (i : ι) (hi : i ∈ F), (fun z : ∀ j, X j => z i) ⁻¹' U i :=
      by
      ext
      simp
    refine' ⟨(F : Set ι).pi U, ⟨U, F, h1, rfl⟩, _⟩
    rw [this, h2, Set.preimage_iInter]
    congr 1
    ext1
    rw [Set.preimage_iInter]
    rfl
  · rintro ⟨U, ⟨U, F, h1, rfl⟩, h⟩
    refine' ⟨U, F, h1, _⟩
    have : (F : Set ι).pi U = ⋂ (i : ι) (hi : i ∈ F), (fun z : ∀ j, X j => z i) ⁻¹' U i :=
      by
      ext
      simp
    rw [← h, this, Set.preimage_iInter]
    congr 1
    ext1
    rw [Set.preimage_iInter]
    rfl
#align is_topological_basis_infi isTopologicalBasis_iInf

#print isTopologicalBasis_singletons /-
theorem isTopologicalBasis_singletons (α : Type _) [TopologicalSpace α] [DiscreteTopology α] :
    IsTopologicalBasis { s | ∃ x : α, (s : Set α) = {x} } :=
  isTopologicalBasis_of_open_of_nhds (fun u hu => isOpen_discrete _) fun x u hx u_open =>
    ⟨{x}, ⟨x, rfl⟩, mem_singleton x, singleton_subset_iff.2 hx⟩
#align is_topological_basis_singletons isTopologicalBasis_singletons
-/

/- warning: dense_range.separable_space -> DenseRange.separableSpace is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.SeparableSpace.{u1} α _inst_1] [_inst_3 : TopologicalSpace.{u2} β] {f : α -> β}, (DenseRange.{u2, u1} β _inst_3 α f) -> (Continuous.{u1, u2} α β _inst_1 _inst_3 f) -> (TopologicalSpace.SeparableSpace.{u2} β _inst_3)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.SeparableSpace.{u2} α _inst_1] [_inst_3 : TopologicalSpace.{u1} β] {f : α -> β}, (DenseRange.{u1, u2} β _inst_3 α f) -> (Continuous.{u2, u1} α β _inst_1 _inst_3 f) -> (TopologicalSpace.SeparableSpace.{u1} β _inst_3)
Case conversion may be inaccurate. Consider using '#align dense_range.separable_space DenseRange.separableSpaceₓ'. -/
/-- If `α` is a separable space and `f : α → β` is a continuous map with dense range, then `β` is
a separable space as well. E.g., the completion of a separable uniform space is separable. -/
protected theorem DenseRange.separableSpace {α β : Type _} [TopologicalSpace α] [SeparableSpace α]
    [TopologicalSpace β] {f : α → β} (h : DenseRange f) (h' : Continuous f) : SeparableSpace β :=
  let ⟨s, s_cnt, s_dense⟩ := exists_countable_dense α
  ⟨⟨f '' s, Countable.image s_cnt f, h.dense_image h' s_dense⟩⟩
#align dense_range.separable_space DenseRange.separableSpace

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem Dense.exists_countable_dense_subset {α : Type _} [TopologicalSpace α] {s : Set α}
    [SeparableSpace s] (hs : Dense s) : ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ Dense t :=
  let ⟨t, htc, htd⟩ := exists_countable_dense s
  ⟨coe '' t, image_subset_iff.2 fun x _ => mem_preimage.2 <| Subtype.coe_prop _, htc.image coe,
    hs.denseRange_val.dense_image continuous_subtype_val htd⟩
#align dense.exists_countable_dense_subset Dense.exists_countable_dense_subsetₓ

/- warning: dense.exists_countable_dense_subset_bot_top -> Dense.exists_countable_dense_subset_bot_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : PartialOrder.{u1} α] {s : Set.{u1} α} [_inst_3 : TopologicalSpace.SeparableSpace.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1)], (Dense.{u1} α _inst_1 s) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) => And (Set.Countable.{u1} α t) (And (Dense.{u1} α _inst_1 t) (And (forall (x : α), (IsBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)) (forall (x : α), (IsTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : PartialOrder.{u1} α] {s : Set.{u1} α} [_inst_3 : TopologicalSpace.SeparableSpace.{u1} (Set.Elem.{u1} α s) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) _inst_1)], (Dense.{u1} α _inst_1 s) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) (And (Set.Countable.{u1} α t) (And (Dense.{u1} α _inst_1 t) (And (forall (x : α), (IsBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t)) (forall (x : α), (IsTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t)))))))
Case conversion may be inaccurate. Consider using '#align dense.exists_countable_dense_subset_bot_top Dense.exists_countable_dense_subset_bot_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/-- Let `s` be a dense set in a topological space `α` with partial order structure. If `s` is a
separable space (e.g., if `α` has a second countable topology), then there exists a countable
dense subset `t ⊆ s` such that `t` contains bottom/top element of `α` when they exist and belong
to `s`. For a dense subset containing neither bot nor top elements, see
`dense.exists_countable_dense_subset_no_bot_top`. -/
theorem Dense.exists_countable_dense_subset_bot_top {α : Type _} [TopologicalSpace α]
    [PartialOrder α] {s : Set α} [SeparableSpace s] (hs : Dense s) :
    ∃ (t : _)(_ : t ⊆ s),
      t.Countable ∧ Dense t ∧ (∀ x, IsBot x → x ∈ s → x ∈ t) ∧ ∀ x, IsTop x → x ∈ s → x ∈ t :=
  by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, htd⟩
  refine' ⟨(t ∪ ({ x | IsBot x } ∪ { x | IsTop x })) ∩ s, _, _, _, _, _⟩
  exacts[inter_subset_right _ _,
    (htc.union ((countable_is_bot α).union (countable_is_top α))).mono (inter_subset_left _ _),
    htd.mono (subset_inter (subset_union_left _ _) hts), fun x hx hxs => ⟨Or.inr <| Or.inl hx, hxs⟩,
    fun x hx hxs => ⟨Or.inr <| Or.inr hx, hxs⟩]
#align dense.exists_countable_dense_subset_bot_top Dense.exists_countable_dense_subset_bot_top

#print separableSpace_univ /-
instance separableSpace_univ {α : Type _} [TopologicalSpace α] [SeparableSpace α] :
    SeparableSpace (univ : Set α) :=
  (Equiv.Set.univ α).symm.Surjective.DenseRange.SeparableSpace (continuous_id.subtype_mk _)
#align separable_space_univ separableSpace_univ
-/

/- warning: exists_countable_dense_bot_top -> exists_countable_dense_bot_top is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.SeparableSpace.{u1} α _inst_1] [_inst_3 : PartialOrder.{u1} α], Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Set.Countable.{u1} α s) (And (Dense.{u1} α _inst_1 s) (And (forall (x : α), (IsBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) x) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) (forall (x : α), (IsTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) x) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.SeparableSpace.{u1} α _inst_1] [_inst_3 : PartialOrder.{u1} α], Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Set.Countable.{u1} α s) (And (Dense.{u1} α _inst_1 s) (And (forall (x : α), (IsBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) x) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) (forall (x : α), (IsTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) x) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)))))
Case conversion may be inaccurate. Consider using '#align exists_countable_dense_bot_top exists_countable_dense_bot_topₓ'. -/
/-- If `α` is a separable topological space with a partial order, then there exists a countable
dense set `s : set α` that contains those of both bottom and top elements of `α` that actually
exist. For a dense set containing neither bot nor top elements, see
`exists_countable_dense_no_bot_top`. -/
theorem exists_countable_dense_bot_top (α : Type _) [TopologicalSpace α] [SeparableSpace α]
    [PartialOrder α] :
    ∃ s : Set α, s.Countable ∧ Dense s ∧ (∀ x, IsBot x → x ∈ s) ∧ ∀ x, IsTop x → x ∈ s := by
  simpa using dense_univ.exists_countable_dense_subset_bot_top
#align exists_countable_dense_bot_top exists_countable_dense_bot_top

namespace TopologicalSpace

universe u

variable (α : Type u) [t : TopologicalSpace α]

include t

#print TopologicalSpace.FirstCountableTopology /-
/-- A first-countable space is one in which every point has a
  countable neighborhood basis. -/
class FirstCountableTopology : Prop where
  nhds_generated_countable : ∀ a : α, (𝓝 a).IsCountablyGenerated
#align topological_space.first_countable_topology TopologicalSpace.FirstCountableTopology
-/

attribute [instance] first_countable_topology.nhds_generated_countable

namespace FirstCountableTopology

variable {α}

#print TopologicalSpace.FirstCountableTopology.tendsto_subseq /-
/-- In a first-countable space, a cluster point `x` of a sequence
is the limit of some subsequence. -/
theorem tendsto_subseq [FirstCountableTopology α] {u : ℕ → α} {x : α}
    (hx : MapClusterPt x atTop u) : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (u ∘ ψ) atTop (𝓝 x) :=
  subseq_tendsto_of_neBot hx
#align topological_space.first_countable_topology.tendsto_subseq TopologicalSpace.FirstCountableTopology.tendsto_subseq
-/

end FirstCountableTopology

variable {α}

instance {β} [TopologicalSpace β] [FirstCountableTopology α] [FirstCountableTopology β] :
    FirstCountableTopology (α × β) :=
  ⟨fun ⟨x, y⟩ => by
    rw [nhds_prod_eq]
    infer_instance⟩

section Pi

omit t

instance {ι : Type _} {π : ι → Type _} [Countable ι] [∀ i, TopologicalSpace (π i)]
    [∀ i, FirstCountableTopology (π i)] : FirstCountableTopology (∀ i, π i) :=
  ⟨fun f => by
    rw [nhds_pi]
    infer_instance⟩

end Pi

#print TopologicalSpace.isCountablyGenerated_nhdsWithin /-
instance isCountablyGenerated_nhdsWithin (x : α) [IsCountablyGenerated (𝓝 x)] (s : Set α) :
    IsCountablyGenerated (𝓝[s] x) :=
  Inf.isCountablyGenerated _ _
#align topological_space.is_countably_generated_nhds_within TopologicalSpace.isCountablyGenerated_nhdsWithin
-/

variable (α)

#print TopologicalSpace.SecondCountableTopology /-
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`is_open_generated_countable] [] -/
/-- A second-countable space is one with a countable basis. -/
class SecondCountableTopology : Prop where
  is_open_generated_countable : ∃ b : Set (Set α), b.Countable ∧ t = TopologicalSpace.generateFrom b
#align topological_space.second_countable_topology TopologicalSpace.SecondCountableTopology
-/

variable {α}

#print TopologicalSpace.IsTopologicalBasis.secondCountableTopology /-
protected theorem IsTopologicalBasis.secondCountableTopology {b : Set (Set α)}
    (hb : IsTopologicalBasis b) (hc : b.Countable) : SecondCountableTopology α :=
  ⟨⟨b, hc, hb.eq_generateFrom⟩⟩
#align topological_space.is_topological_basis.second_countable_topology TopologicalSpace.IsTopologicalBasis.secondCountableTopology
-/

variable (α)

#print TopologicalSpace.exists_countable_basis /-
theorem exists_countable_basis [SecondCountableTopology α] :
    ∃ b : Set (Set α), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b :=
  by
  obtain ⟨b, hb₁, hb₂⟩ := second_countable_topology.is_open_generated_countable α
  refine' ⟨_, _, not_mem_diff_of_mem _, (is_topological_basis_of_subbasis hb₂).diff_empty⟩
  exacts[((countable_set_of_finite_subset hb₁).image _).mono (diff_subset _ _), rfl]
#align topological_space.exists_countable_basis TopologicalSpace.exists_countable_basis
-/

#print TopologicalSpace.countableBasis /-
/-- A countable topological basis of `α`. -/
def countableBasis [SecondCountableTopology α] : Set (Set α) :=
  (exists_countable_basis α).some
#align topological_space.countable_basis TopologicalSpace.countableBasis
-/

#print TopologicalSpace.countable_countableBasis /-
theorem countable_countableBasis [SecondCountableTopology α] : (countableBasis α).Countable :=
  (exists_countable_basis α).choose_spec.1
#align topological_space.countable_countable_basis TopologicalSpace.countable_countableBasis
-/

#print TopologicalSpace.encodableCountableBasis /-
instance encodableCountableBasis [SecondCountableTopology α] : Encodable (countableBasis α) :=
  (countable_countableBasis α).toEncodable
#align topological_space.encodable_countable_basis TopologicalSpace.encodableCountableBasis
-/

#print TopologicalSpace.empty_nmem_countableBasis /-
theorem empty_nmem_countableBasis [SecondCountableTopology α] : ∅ ∉ countableBasis α :=
  (exists_countable_basis α).choose_spec.2.1
#align topological_space.empty_nmem_countable_basis TopologicalSpace.empty_nmem_countableBasis
-/

#print TopologicalSpace.isBasis_countableBasis /-
theorem isBasis_countableBasis [SecondCountableTopology α] :
    IsTopologicalBasis (countableBasis α) :=
  (exists_countable_basis α).choose_spec.2.2
#align topological_space.is_basis_countable_basis TopologicalSpace.isBasis_countableBasis
-/

#print TopologicalSpace.eq_generateFrom_countableBasis /-
theorem eq_generateFrom_countableBasis [SecondCountableTopology α] :
    ‹TopologicalSpace α› = generateFrom (countableBasis α) :=
  (isBasis_countableBasis α).eq_generateFrom
#align topological_space.eq_generate_from_countable_basis TopologicalSpace.eq_generateFrom_countableBasis
-/

variable {α}

#print TopologicalSpace.isOpen_of_mem_countableBasis /-
theorem isOpen_of_mem_countableBasis [SecondCountableTopology α] {s : Set α}
    (hs : s ∈ countableBasis α) : IsOpen s :=
  (isBasis_countableBasis α).IsOpen hs
#align topological_space.is_open_of_mem_countable_basis TopologicalSpace.isOpen_of_mem_countableBasis
-/

#print TopologicalSpace.nonempty_of_mem_countableBasis /-
theorem nonempty_of_mem_countableBasis [SecondCountableTopology α] {s : Set α}
    (hs : s ∈ countableBasis α) : s.Nonempty :=
  nonempty_iff_ne_empty.2 <| ne_of_mem_of_not_mem hs <| empty_nmem_countableBasis α
#align topological_space.nonempty_of_mem_countable_basis TopologicalSpace.nonempty_of_mem_countableBasis
-/

variable (α)

#print TopologicalSpace.SecondCountableTopology.to_firstCountableTopology /-
-- see Note [lower instance priority]
instance (priority := 100) SecondCountableTopology.to_firstCountableTopology
    [SecondCountableTopology α] : FirstCountableTopology α :=
  ⟨fun x =>
    HasCountableBasis.isCountablyGenerated <|
      ⟨(isBasis_countableBasis α).nhds_hasBasis,
        (countable_countableBasis α).mono <| inter_subset_left _ _⟩⟩
#align topological_space.second_countable_topology.to_first_countable_topology TopologicalSpace.SecondCountableTopology.to_firstCountableTopology
-/

/- warning: topological_space.second_countable_topology_induced -> TopologicalSpace.secondCountableTopology_induced is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [t : TopologicalSpace.{u2} β] [_inst_1 : TopologicalSpace.SecondCountableTopology.{u2} β t] (f : α -> β), TopologicalSpace.SecondCountableTopology.{u1} α (TopologicalSpace.induced.{u1, u2} α β f t)
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}) [t : TopologicalSpace.{u1} β] [_inst_1 : TopologicalSpace.SecondCountableTopology.{u1} β t] (f : α -> β), TopologicalSpace.SecondCountableTopology.{u2} α (TopologicalSpace.induced.{u2, u1} α β f t)
Case conversion may be inaccurate. Consider using '#align topological_space.second_countable_topology_induced TopologicalSpace.secondCountableTopology_inducedₓ'. -/
/-- If `β` is a second-countable space, then its induced topology
via `f` on `α` is also second-countable. -/
theorem secondCountableTopology_induced (β) [t : TopologicalSpace β] [SecondCountableTopology β]
    (f : α → β) : @SecondCountableTopology α (t.induced f) :=
  by
  rcases second_countable_topology.is_open_generated_countable β with ⟨b, hb, eq⟩
  refine' { is_open_generated_countable := ⟨preimage f '' b, hb.image _, _⟩ }
  rw [Eq, induced_generateFrom_eq]
#align topological_space.second_countable_topology_induced TopologicalSpace.secondCountableTopology_induced

#print TopologicalSpace.Subtype.secondCountableTopology /-
instance Subtype.secondCountableTopology (s : Set α) [SecondCountableTopology α] :
    SecondCountableTopology s :=
  secondCountableTopology_induced s α coe
#align topological_space.subtype.second_countable_topology TopologicalSpace.Subtype.secondCountableTopology
-/

-- TODO: more fine grained instances for first_countable_topology, separable_space, t2_space, ...
instance {β : Type _} [TopologicalSpace β] [SecondCountableTopology α] [SecondCountableTopology β] :
    SecondCountableTopology (α × β) :=
  ((isBasis_countableBasis α).Prod (isBasis_countableBasis β)).SecondCountableTopology <|
    (countable_countableBasis α).image2 (countable_countableBasis β) _

instance {ι : Type _} {π : ι → Type _} [Countable ι] [t : ∀ a, TopologicalSpace (π a)]
    [∀ a, SecondCountableTopology (π a)] : SecondCountableTopology (∀ a, π a) :=
  by
  have : t = fun a => generate_from (countable_basis (π a)) :=
    funext fun a => (is_basis_countable_basis (π a)).eq_generateFrom
  rw [this, pi_generateFrom_eq]
  constructor
  refine' ⟨_, _, rfl⟩
  have :
    Set.Countable
      { T : Set (∀ i, π i) |
        ∃ (I : Finset ι)(s : ∀ i : I, Set (π i)),
          (∀ i, s i ∈ countable_basis (π i)) ∧ T = { f | ∀ i : I, f i ∈ s i } } :=
    by
    simp only [set_of_exists, ← exists_prop]
    refine' countable_Union fun I => countable.bUnion _ fun _ _ => countable_singleton _
    change Set.Countable { s : ∀ i : I, Set (π i) | ∀ i, s i ∈ countable_basis (π i) }
    exact countable_pi fun i => countable_countable_basis _
  convert this using 1
  ext1 T
  constructor
  · rintro ⟨s, I, hs, rfl⟩
    refine' ⟨I, fun i => s i, fun i => hs i i.2, _⟩
    simp only [Set.pi, SetCoe.forall']
    rfl
  · rintro ⟨I, s, hs, rfl⟩
    rcases@Subtype.surjective_restrict ι (fun i => Set (π i)) _ (fun i => i ∈ I) s with ⟨s, rfl⟩
    exact ⟨s, I, fun i hi => hs ⟨i, hi⟩, Set.ext fun f => Subtype.forall⟩

#print TopologicalSpace.SecondCountableTopology.to_separableSpace /-
-- see Note [lower instance priority]
instance (priority := 100) SecondCountableTopology.to_separableSpace [SecondCountableTopology α] :
    SeparableSpace α :=
  by
  choose p hp using fun s : countable_basis α => nonempty_of_mem_countable_basis s.2
  exact
    ⟨⟨range p, countable_range _,
        (is_basis_countable_basis α).dense_iff.2 fun o ho _ => ⟨p ⟨o, ho⟩, hp _, mem_range_self _⟩⟩⟩
#align topological_space.second_countable_topology.to_separable_space TopologicalSpace.SecondCountableTopology.to_separableSpace
-/

variable {α}

/- warning: topological_space.second_countable_topology_of_countable_cover -> TopologicalSpace.secondCountableTopology_of_countable_cover is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] {ι : Type.{u2}} [_inst_1 : Encodable.{u2} ι] {U : ι -> (Set.{u1} α)} [_inst_2 : forall (i : ι), TopologicalSpace.SecondCountableTopology.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (U i)) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (U i)) t)], (forall (i : ι), IsOpen.{u1} α t (U i)) -> (Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => U i)) (Set.univ.{u1} α)) -> (TopologicalSpace.SecondCountableTopology.{u1} α t)
but is expected to have type
  forall {α : Type.{u2}} [t : TopologicalSpace.{u2} α] {ι : Type.{u1}} [_inst_1 : Encodable.{u1} ι] {U : ι -> (Set.{u2} α)} [_inst_2 : forall (i : ι), TopologicalSpace.SecondCountableTopology.{u2} (Set.Elem.{u2} α (U i)) (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (U i)) t)], (forall (i : ι), IsOpen.{u2} α t (U i)) -> (Eq.{succ u2} (Set.{u2} α) (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => U i)) (Set.univ.{u2} α)) -> (TopologicalSpace.SecondCountableTopology.{u2} α t)
Case conversion may be inaccurate. Consider using '#align topological_space.second_countable_topology_of_countable_cover TopologicalSpace.secondCountableTopology_of_countable_coverₓ'. -/
/-- A countable open cover induces a second-countable topology if all open covers
are themselves second countable. -/
theorem secondCountableTopology_of_countable_cover {ι} [Encodable ι] {U : ι → Set α}
    [∀ i, SecondCountableTopology (U i)] (Uo : ∀ i, IsOpen (U i)) (hc : (⋃ i, U i) = univ) :
    SecondCountableTopology α :=
  haveI : is_topological_basis (⋃ i, image (coe : U i → α) '' countable_basis (U i)) :=
    is_topological_basis_of_cover Uo hc fun i => is_basis_countable_basis (U i)
  this.second_countable_topology (countable_Union fun i => (countable_countable_basis _).image _)
#align topological_space.second_countable_topology_of_countable_cover TopologicalSpace.secondCountableTopology_of_countable_cover

/- warning: topological_space.is_open_Union_countable -> TopologicalSpace.isOpen_iUnion_countable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] [_inst_1 : TopologicalSpace.SecondCountableTopology.{u1} α t] {ι : Type.{u2}} (s : ι -> (Set.{u1} α)), (forall (i : ι), IsOpen.{u1} α t (s i)) -> (Exists.{succ u2} (Set.{u2} ι) (fun (T : Set.{u2} ι) => And (Set.Countable.{u2} ι T) (Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i T) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i T) => s i))) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => s i)))))
but is expected to have type
  forall {α : Type.{u2}} [t : TopologicalSpace.{u2} α] [_inst_1 : TopologicalSpace.SecondCountableTopology.{u2} α t] {ι : Type.{u1}} (s : ι -> (Set.{u2} α)), (forall (i : ι), IsOpen.{u2} α t (s i)) -> (Exists.{succ u1} (Set.{u1} ι) (fun (T : Set.{u1} ι) => And (Set.Countable.{u1} ι T) (Eq.{succ u2} (Set.{u2} α) (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => Set.iUnion.{u2, 0} α (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i T) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i T) => s i))) (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => s i)))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_open_Union_countable TopologicalSpace.isOpen_iUnion_countableₓ'. -/
/-- In a second-countable space, an open set, given as a union of open sets,
is equal to the union of countably many of those sets. -/
theorem isOpen_iUnion_countable [SecondCountableTopology α] {ι} (s : ι → Set α)
    (H : ∀ i, IsOpen (s i)) : ∃ T : Set ι, T.Countable ∧ (⋃ i ∈ T, s i) = ⋃ i, s i :=
  by
  let B := { b ∈ countable_basis α | ∃ i, b ⊆ s i }
  choose f hf using fun b : B => b.2.2
  haveI : Encodable B := ((countable_countable_basis α).mono (sep_subset _ _)).toEncodable
  refine' ⟨_, countable_range f, (Union₂_subset_Union _ _).antisymm (sUnion_subset _)⟩
  rintro _ ⟨i, rfl⟩ x xs
  rcases(is_basis_countable_basis α).exists_subset_of_mem_open xs (H _) with ⟨b, hb, xb, bs⟩
  exact ⟨_, ⟨_, rfl⟩, _, ⟨⟨⟨_, hb, _, bs⟩, rfl⟩, rfl⟩, hf _ xb⟩
#align topological_space.is_open_Union_countable TopologicalSpace.isOpen_iUnion_countable

#print TopologicalSpace.isOpen_sUnion_countable /-
theorem isOpen_sUnion_countable [SecondCountableTopology α] (S : Set (Set α))
    (H : ∀ s ∈ S, IsOpen s) : ∃ T : Set (Set α), T.Countable ∧ T ⊆ S ∧ ⋃₀ T = ⋃₀ S :=
  let ⟨T, cT, hT⟩ := isOpen_iUnion_countable (fun s : S => s.1) fun s => H s.1 s.2
  ⟨Subtype.val '' T, cT.image _, image_subset_iff.2 fun ⟨x, xs⟩ xt => xs, by
    rwa [sUnion_image, sUnion_eq_Union]⟩
#align topological_space.is_open_sUnion_countable TopologicalSpace.isOpen_sUnion_countable
-/

#print TopologicalSpace.countable_cover_nhds /-
/-- In a topological space with second countable topology, if `f` is a function that sends each
point `x` to a neighborhood of `x`, then for some countable set `s`, the neighborhoods `f x`,
`x ∈ s`, cover the whole space. -/
theorem countable_cover_nhds [SecondCountableTopology α] {f : α → Set α} (hf : ∀ x, f x ∈ 𝓝 x) :
    ∃ s : Set α, s.Countable ∧ (⋃ x ∈ s, f x) = univ :=
  by
  rcases is_open_Union_countable (fun x => interior (f x)) fun x => isOpen_interior with
    ⟨s, hsc, hsU⟩
  suffices : (⋃ x ∈ s, interior (f x)) = univ
  exact ⟨s, hsc, flip eq_univ_of_subset this <| Union₂_mono fun _ _ => interior_subset⟩
  simp only [hsU, eq_univ_iff_forall, mem_Union]
  exact fun x => ⟨x, mem_interior_iff_mem_nhds.2 (hf x)⟩
#align topological_space.countable_cover_nhds TopologicalSpace.countable_cover_nhds
-/

/- warning: topological_space.countable_cover_nhds_within -> TopologicalSpace.countable_cover_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] [_inst_1 : TopologicalSpace.SecondCountableTopology.{u1} α t] {f : α -> (Set.{u1} α)} {s : Set.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (f x) (nhdsWithin.{u1} α t x s))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) => And (Set.Countable.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) => f x)))))))
but is expected to have type
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α] [_inst_1 : TopologicalSpace.SecondCountableTopology.{u1} α t] {f : α -> (Set.{u1} α)} {s : Set.{u1} α}, (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (f x) (nhdsWithin.{u1} α t x s))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) (And (Set.Countable.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) (fun (h._@.Mathlib.Topology.Bases._hyg.7220 : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) => f x)))))))
Case conversion may be inaccurate. Consider using '#align topological_space.countable_cover_nhds_within TopologicalSpace.countable_cover_nhdsWithinₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem countable_cover_nhdsWithin [SecondCountableTopology α] {f : α → Set α} {s : Set α}
    (hf : ∀ x ∈ s, f x ∈ 𝓝[s] x) : ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ s ⊆ ⋃ x ∈ t, f x :=
  by
  have : ∀ x : s, coe ⁻¹' f x ∈ 𝓝 x := fun x => preimage_coe_mem_nhds_subtype.2 (hf x x.2)
  rcases countable_cover_nhds this with ⟨t, htc, htU⟩
  refine' ⟨coe '' t, Subtype.coe_image_subset _ _, htc.image _, fun x hx => _⟩
  simp only [bUnion_image, eq_univ_iff_forall, ← preimage_Union, mem_preimage] at htU⊢
  exact htU ⟨x, hx⟩
#align topological_space.countable_cover_nhds_within TopologicalSpace.countable_cover_nhdsWithin

section Sigma

variable {ι : Type _} {E : ι → Type _} [∀ i, TopologicalSpace (E i)]

omit t

/- warning: topological_space.is_topological_basis.sigma -> TopologicalSpace.IsTopologicalBasis.sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (E i)] {s : forall (i : ι), Set.{u2} (Set.{u2} (E i))}, (forall (i : ι), TopologicalSpace.IsTopologicalBasis.{u2} (E i) (_inst_1 i) (s i)) -> (TopologicalSpace.IsTopologicalBasis.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => E i)) (Sigma.topologicalSpace.{u1, u2} ι (fun (i : ι) => E i) (fun (a : ι) => _inst_1 a)) (Set.iUnion.{max u1 u2, succ u1} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => E i))) ι (fun (i : ι) => Set.image.{u2, max u1 u2} (Set.{u2} (E i)) (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => E i))) (fun (u : Set.{u2} (E i)) => Set.image.{u2, max u1 u2} (E i) (Sigma.{u1, u2} ι (fun (i : ι) => E i)) (Sigma.mk.{u1, u2} ι (fun (i : ι) => E i) i) u) (s i))))
but is expected to have type
  forall {ι : Type.{u1}} {E : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (E i)] {s : forall (i : ι), Set.{u2} (Set.{u2} (E i))}, (forall (i : ι), TopologicalSpace.IsTopologicalBasis.{u2} (E i) (_inst_1 i) (s i)) -> (TopologicalSpace.IsTopologicalBasis.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => E i)) (instTopologicalSpaceSigma.{u1, u2} ι (fun (i : ι) => E i) (fun (a : ι) => _inst_1 a)) (Set.iUnion.{max u1 u2, succ u1} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => E i))) ι (fun (i : ι) => Set.image.{u2, max u1 u2} (Set.{u2} (E i)) (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => E i))) (fun (u : Set.{u2} (E i)) => Set.image.{u2, max u1 u2} (E i) (Sigma.{u1, u2} ι (fun (i : ι) => E i)) (Sigma.mk.{u1, u2} ι (fun (i : ι) => E i) i) u) (s i))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.sigma TopologicalSpace.IsTopologicalBasis.sigmaₓ'. -/
/-- In a disjoint union space `Σ i, E i`, one can form a topological basis by taking the union of
topological bases on each of the parts of the space. -/
theorem IsTopologicalBasis.sigma {s : ∀ i : ι, Set (Set (E i))}
    (hs : ∀ i, IsTopologicalBasis (s i)) :
    IsTopologicalBasis (⋃ i : ι, (fun u => (Sigma.mk i '' u : Set (Σi, E i))) '' s i) :=
  by
  apply is_topological_basis_of_open_of_nhds
  · intro u hu
    obtain ⟨i, t, ts, rfl⟩ : ∃ (i : ι)(t : Set (E i)), t ∈ s i ∧ Sigma.mk i '' t = u := by
      simpa only [mem_Union, mem_image] using hu
    exact isOpenMap_sigmaMk _ ((hs i).IsOpen ts)
  · rintro ⟨i, x⟩ u hxu u_open
    have hx : x ∈ Sigma.mk i ⁻¹' u := hxu
    obtain ⟨v, vs, xv, hv⟩ : ∃ (v : Set (E i))(H : v ∈ s i), x ∈ v ∧ v ⊆ Sigma.mk i ⁻¹' u :=
      (hs i).exists_subset_of_mem_open hx (isOpen_sigma_iff.1 u_open i)
    exact
      ⟨Sigma.mk i '' v, mem_Union.2 ⟨i, mem_image_of_mem _ vs⟩, mem_image_of_mem _ xv,
        image_subset_iff.2 hv⟩
#align topological_space.is_topological_basis.sigma TopologicalSpace.IsTopologicalBasis.sigma

/-- A countable disjoint union of second countable spaces is second countable. -/
instance [Countable ι] [∀ i, SecondCountableTopology (E i)] : SecondCountableTopology (Σi, E i) :=
  by
  let b := ⋃ i : ι, (fun u => (Sigma.mk i '' u : Set (Σi, E i))) '' countable_basis (E i)
  have A : is_topological_basis b := is_topological_basis.sigma fun i => is_basis_countable_basis _
  have B : b.countable := countable_Union fun i => countable.image (countable_countable_basis _) _
  exact A.second_countable_topology B

end Sigma

section Sum

omit t

variable {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

/- warning: topological_space.is_topological_basis.sum -> TopologicalSpace.IsTopologicalBasis.sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} (Set.{u1} α)}, (TopologicalSpace.IsTopologicalBasis.{u1} α _inst_1 s) -> (forall {t : Set.{u2} (Set.{u2} β)}, (TopologicalSpace.IsTopologicalBasis.{u2} β _inst_2 t) -> (TopologicalSpace.IsTopologicalBasis.{max u1 u2} (Sum.{u1, u2} α β) (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Union.union.{max u1 u2} (Set.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β))) (Set.hasUnion.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β))) (Set.image.{u1, max u1 u2} (Set.{u1} α) (Set.{max u1 u2} (Sum.{u1, u2} α β)) (fun (u : Set.{u1} α) => Set.image.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) u) s) (Set.image.{u2, max u1 u2} (Set.{u2} β) (Set.{max u1 u2} (Sum.{u1, u2} α β)) (fun (u : Set.{u2} β) => Set.image.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β) u) t))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} (Set.{u2} α)}, (TopologicalSpace.IsTopologicalBasis.{u2} α _inst_1 s) -> (forall {t : Set.{u1} (Set.{u1} β)}, (TopologicalSpace.IsTopologicalBasis.{u1} β _inst_2 t) -> (TopologicalSpace.IsTopologicalBasis.{max u1 u2} (Sum.{u2, u1} α β) (instTopologicalSpaceSum.{u2, u1} α β _inst_1 _inst_2) (Union.union.{max u1 u2} (Set.{max u1 u2} (Set.{max u1 u2} (Sum.{u2, u1} α β))) (Set.instUnionSet.{max u2 u1} (Set.{max u1 u2} (Sum.{u2, u1} α β))) (Set.image.{u2, max u1 u2} (Set.{u2} α) (Set.{max u1 u2} (Sum.{u2, u1} α β)) (fun (u : Set.{u2} α) => Set.image.{u2, max u1 u2} α (Sum.{u2, u1} α β) (Sum.inl.{u2, u1} α β) u) s) (Set.image.{u1, max u2 u1} (Set.{u1} β) (Set.{max u1 u2} (Sum.{u2, u1} α β)) (fun (u : Set.{u1} β) => Set.image.{u1, max u2 u1} β (Sum.{u2, u1} α β) (Sum.inr.{u2, u1} α β) u) t))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.sum TopologicalSpace.IsTopologicalBasis.sumₓ'. -/
/-- In a sum space `α ⊕ β`, one can form a topological basis by taking the union of
topological bases on each of the two components. -/
theorem IsTopologicalBasis.sum {s : Set (Set α)} (hs : IsTopologicalBasis s) {t : Set (Set β)}
    (ht : IsTopologicalBasis t) :
    IsTopologicalBasis ((fun u => Sum.inl '' u) '' s ∪ (fun u => Sum.inr '' u) '' t) :=
  by
  apply is_topological_basis_of_open_of_nhds
  · intro u hu
    cases hu
    · rcases hu with ⟨w, hw, rfl⟩
      exact open_embedding_inl.is_open_map w (hs.is_open hw)
    · rcases hu with ⟨w, hw, rfl⟩
      exact open_embedding_inr.is_open_map w (ht.is_open hw)
  · rintro x u hxu u_open
    cases x
    · have h'x : x ∈ Sum.inl ⁻¹' u := hxu
      obtain ⟨v, vs, xv, vu⟩ : ∃ (v : Set α)(H : v ∈ s), x ∈ v ∧ v ⊆ Sum.inl ⁻¹' u :=
        hs.exists_subset_of_mem_open h'x (isOpen_sum_iff.1 u_open).1
      exact
        ⟨Sum.inl '' v, mem_union_left _ (mem_image_of_mem _ vs), mem_image_of_mem _ xv,
          image_subset_iff.2 vu⟩
    · have h'x : x ∈ Sum.inr ⁻¹' u := hxu
      obtain ⟨v, vs, xv, vu⟩ : ∃ (v : Set β)(H : v ∈ t), x ∈ v ∧ v ⊆ Sum.inr ⁻¹' u :=
        ht.exists_subset_of_mem_open h'x (isOpen_sum_iff.1 u_open).2
      exact
        ⟨Sum.inr '' v, mem_union_right _ (mem_image_of_mem _ vs), mem_image_of_mem _ xv,
          image_subset_iff.2 vu⟩
#align topological_space.is_topological_basis.sum TopologicalSpace.IsTopologicalBasis.sum

/-- A sum type of two second countable spaces is second countable. -/
instance [SecondCountableTopology α] [SecondCountableTopology β] :
    SecondCountableTopology (Sum α β) :=
  by
  let b :=
    (fun u => Sum.inl '' u) '' countable_basis α ∪ (fun u => Sum.inr '' u) '' countable_basis β
  have A : is_topological_basis b := (is_basis_countable_basis α).Sum (is_basis_countable_basis β)
  have B : b.countable :=
    (countable.image (countable_countable_basis _) _).union
      (countable.image (countable_countable_basis _) _)
  exact A.second_countable_topology B

end Sum

section Quotient

variable {X : Type _} [TopologicalSpace X] {Y : Type _} [TopologicalSpace Y] {π : X → Y}

omit t

/- warning: topological_space.is_topological_basis.quotient_map -> TopologicalSpace.IsTopologicalBasis.quotientMap is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {Y : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} Y] {π : X -> Y} {V : Set.{u1} (Set.{u1} X)}, (TopologicalSpace.IsTopologicalBasis.{u1} X _inst_1 V) -> (QuotientMap.{u1, u2} X Y _inst_1 _inst_2 π) -> (IsOpenMap.{u1, u2} X Y _inst_1 _inst_2 π) -> (TopologicalSpace.IsTopologicalBasis.{u2} Y _inst_2 (Set.image.{u1, u2} (Set.{u1} X) (Set.{u2} Y) (Set.image.{u1, u2} X Y π) V))
but is expected to have type
  forall {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {Y : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} Y] {π : X -> Y} {V : Set.{u2} (Set.{u2} X)}, (TopologicalSpace.IsTopologicalBasis.{u2} X _inst_1 V) -> (QuotientMap.{u2, u1} X Y _inst_1 _inst_2 π) -> (IsOpenMap.{u2, u1} X Y _inst_1 _inst_2 π) -> (TopologicalSpace.IsTopologicalBasis.{u1} Y _inst_2 (Set.image.{u2, u1} (Set.{u2} X) (Set.{u1} Y) (Set.image.{u2, u1} X Y π) V))
Case conversion may be inaccurate. Consider using '#align topological_space.is_topological_basis.quotient_map TopologicalSpace.IsTopologicalBasis.quotientMapₓ'. -/
/-- The image of a topological basis under an open quotient map is a topological basis. -/
theorem IsTopologicalBasis.quotientMap {V : Set (Set X)} (hV : IsTopologicalBasis V)
    (h' : QuotientMap π) (h : IsOpenMap π) : IsTopologicalBasis (Set.image π '' V) :=
  by
  apply is_topological_basis_of_open_of_nhds
  · rintro - ⟨U, U_in_V, rfl⟩
    apply h U (hV.is_open U_in_V)
  · intro y U y_in_U U_open
    obtain ⟨x, rfl⟩ := h'.surjective y
    let W := π ⁻¹' U
    have x_in_W : x ∈ W := y_in_U
    have W_open : IsOpen W := U_open.preimage h'.continuous
    obtain ⟨Z, Z_in_V, x_in_Z, Z_in_W⟩ := hV.exists_subset_of_mem_open x_in_W W_open
    have πZ_in_U : π '' Z ⊆ U := (Set.image_subset _ Z_in_W).trans (image_preimage_subset π U)
    exact ⟨π '' Z, ⟨Z, Z_in_V, rfl⟩, ⟨x, x_in_Z, rfl⟩, πZ_in_U⟩
#align topological_space.is_topological_basis.quotient_map TopologicalSpace.IsTopologicalBasis.quotientMap

/- warning: topological_space.quotient_map.second_countable_topology -> QuotientMap.secondCountableTopology is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {Y : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} Y] {π : X -> Y} [_inst_3 : TopologicalSpace.SecondCountableTopology.{u1} X _inst_1], (QuotientMap.{u1, u2} X Y _inst_1 _inst_2 π) -> (IsOpenMap.{u1, u2} X Y _inst_1 _inst_2 π) -> (TopologicalSpace.SecondCountableTopology.{u2} Y _inst_2)
but is expected to have type
  forall {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {Y : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} Y] {π : X -> Y} [_inst_3 : TopologicalSpace.SecondCountableTopology.{u2} X _inst_1], (QuotientMap.{u2, u1} X Y _inst_1 _inst_2 π) -> (IsOpenMap.{u2, u1} X Y _inst_1 _inst_2 π) -> (TopologicalSpace.SecondCountableTopology.{u1} Y _inst_2)
Case conversion may be inaccurate. Consider using '#align topological_space.quotient_map.second_countable_topology QuotientMap.secondCountableTopologyₓ'. -/
/-- A second countable space is mapped by an open quotient map to a second countable space. -/
theorem QuotientMap.secondCountableTopology [SecondCountableTopology X] (h' : QuotientMap π)
    (h : IsOpenMap π) : SecondCountableTopology Y :=
  {
    is_open_generated_countable :=
      by
      obtain ⟨V, V_countable, V_no_empty, V_generates⟩ := exists_countable_basis X
      exact
        ⟨Set.image π '' V, V_countable.image (Set.image π),
          (V_generates.quotient_map h' h).eq_generateFrom⟩ }
#align topological_space.quotient_map.second_countable_topology QuotientMap.secondCountableTopology

variable {S : Setoid X}

#print TopologicalSpace.IsTopologicalBasis.quotient /-
/-- The image of a topological basis "downstairs" in an open quotient is a topological basis. -/
theorem IsTopologicalBasis.quotient {V : Set (Set X)} (hV : IsTopologicalBasis V)
    (h : IsOpenMap (Quotient.mk' : X → Quotient S)) :
    IsTopologicalBasis (Set.image (Quotient.mk' : X → Quotient S) '' V) :=
  hV.QuotientMap quotientMap_quotient_mk' h
#align topological_space.is_topological_basis.quotient TopologicalSpace.IsTopologicalBasis.quotient
-/

#print TopologicalSpace.Quotient.secondCountableTopology /-
/-- An open quotient of a second countable space is second countable. -/
theorem Quotient.secondCountableTopology [SecondCountableTopology X]
    (h : IsOpenMap (Quotient.mk' : X → Quotient S)) : SecondCountableTopology (Quotient S) :=
  quotientMap_quotient_mk'.SecondCountableTopology h
#align topological_space.quotient.second_countable_topology TopologicalSpace.Quotient.secondCountableTopology
-/

end Quotient

end TopologicalSpace

open TopologicalSpace

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}

#print Inducing.secondCountableTopology /-
protected theorem Inducing.secondCountableTopology [SecondCountableTopology β] (hf : Inducing f) :
    SecondCountableTopology α := by
  rw [hf.1]
  exact second_countable_topology_induced α β f
#align inducing.second_countable_topology Inducing.secondCountableTopology
-/

#print Embedding.secondCountableTopology /-
protected theorem Embedding.secondCountableTopology [SecondCountableTopology β] (hf : Embedding f) :
    SecondCountableTopology α :=
  hf.1.SecondCountableTopology
#align embedding.second_countable_topology Embedding.secondCountableTopology
-/

