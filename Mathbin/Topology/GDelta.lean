/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module topology.G_delta
! leanprover-community/mathlib commit b9e46fe101fc897fb2e7edaf0bf1f09ea49eb81a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.Basic
import Mathbin.Topology.Separation
import Mathbin.Order.Filter.CountableInter

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

open Classical Topology Filter uniformity

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

#print isGδ_empty /-
@[simp]
theorem isGδ_empty : IsGδ (∅ : Set α) :=
  isOpen_empty.IsGδ
#align is_Gδ_empty isGδ_empty
-/

#print isGδ_univ /-
@[simp]
theorem isGδ_univ : IsGδ (univ : Set α) :=
  isOpen_univ.IsGδ
#align is_Gδ_univ isGδ_univ
-/

#print isGδ_biInter_of_open /-
theorem isGδ_biInter_of_open {I : Set ι} (hI : I.Countable) {f : ι → Set α}
    (hf : ∀ i ∈ I, IsOpen (f i)) : IsGδ (⋂ i ∈ I, f i) :=
  ⟨f '' I, by rwa [ball_image_iff], hI.image _, by rw [sInter_image]⟩
#align is_Gδ_bInter_of_open isGδ_biInter_of_open
-/

#print isGδ_iInter_of_open /-
theorem isGδ_iInter_of_open [Encodable ι] {f : ι → Set α} (hf : ∀ i, IsOpen (f i)) :
    IsGδ (⋂ i, f i) :=
  ⟨range f, by rwa [forall_range_iff], countable_range _, by rw [sInter_range]⟩
#align is_Gδ_Inter_of_open isGδ_iInter_of_open
-/

#print isGδ_iInter /-
/-- The intersection of an encodable family of Gδ sets is a Gδ set. -/
theorem isGδ_iInter [Encodable ι] {s : ι → Set α} (hs : ∀ i, IsGδ (s i)) : IsGδ (⋂ i, s i) :=
  by
  choose T hTo hTc hTs using hs
  obtain rfl : s = fun i => ⋂₀ T i := funext hTs
  refine' ⟨⋃ i, T i, _, countable_Union hTc, (sInter_Union _).symm⟩
  simpa [@forall_swap ι] using hTo
#align is_Gδ_Inter isGδ_iInter
-/

#print isGδ_biInter /-
theorem isGδ_biInter {s : Set ι} (hs : s.Countable) {t : ∀ i ∈ s, Set α}
    (ht : ∀ i ∈ s, IsGδ (t i ‹_›)) : IsGδ (⋂ i ∈ s, t i ‹_›) :=
  by
  rw [bInter_eq_Inter]
  haveI := hs.to_encodable
  exact isGδ_iInter fun x => ht x x.2
#align is_Gδ_bInter isGδ_biInter
-/

#print isGδ_sInter /-
/-- A countable intersection of Gδ sets is a Gδ set. -/
theorem isGδ_sInter {S : Set (Set α)} (h : ∀ s ∈ S, IsGδ s) (hS : S.Countable) : IsGδ (⋂₀ S) := by
  simpa only [sInter_eq_bInter] using isGδ_biInter hS h
#align is_Gδ_sInter isGδ_sInter
-/

/- warning: is_Gδ.inter -> IsGδ.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsGδ.{u1} α _inst_1 s) -> (IsGδ.{u1} α _inst_1 t) -> (IsGδ.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsGδ.{u1} α _inst_1 s) -> (IsGδ.{u1} α _inst_1 t) -> (IsGδ.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align is_Gδ.inter IsGδ.interₓ'. -/
theorem IsGδ.inter {s t : Set α} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∩ t) :=
  by
  rw [inter_eq_Inter]
  exact isGδ_iInter (Bool.forall_bool.2 ⟨ht, hs⟩)
#align is_Gδ.inter IsGδ.inter

/- warning: is_Gδ.union -> IsGδ.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsGδ.{u1} α _inst_1 s) -> (IsGδ.{u1} α _inst_1 t) -> (IsGδ.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsGδ.{u1} α _inst_1 s) -> (IsGδ.{u1} α _inst_1 t) -> (IsGδ.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align is_Gδ.union IsGδ.unionₓ'. -/
/-- The union of two Gδ sets is a Gδ set. -/
theorem IsGδ.union {s t : Set α} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∪ t) :=
  by
  rcases hs with ⟨S, Sopen, Scount, rfl⟩
  rcases ht with ⟨T, Topen, Tcount, rfl⟩
  rw [sInter_union_sInter]
  apply isGδ_biInter_of_open (Scount.prod Tcount)
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  exact (Sopen a ha).union (Topen b hb)
#align is_Gδ.union IsGδ.union

#print isGδ_biUnion /-
/-- The union of finitely many Gδ sets is a Gδ set. -/
theorem isGδ_biUnion {s : Set ι} (hs : s.Finite) {f : ι → Set α} (h : ∀ i ∈ s, IsGδ (f i)) :
    IsGδ (⋃ i ∈ s, f i) := by
  refine' finite.induction_on hs (by simp) _ h
  simp only [ball_insert_iff, bUnion_insert]
  exact fun a s _ _ ihs H => H.1.union (ihs H.2)
#align is_Gδ_bUnion isGδ_biUnion
-/

#print IsClosed.isGδ /-
theorem IsClosed.isGδ {α} [UniformSpace α] [IsCountablyGenerated (𝓤 α)] {s : Set α}
    (hs : IsClosed s) : IsGδ s :=
  by
  rcases(@uniformity_hasBasis_open α _).exists_antitone_subbasis with ⟨U, hUo, hU, -⟩
  rw [← hs.closure_eq, ← hU.bInter_bUnion_ball]
  refine' isGδ_biInter (to_countable _) fun n hn => IsOpen.isGδ _
  exact isOpen_biUnion fun x hx => UniformSpace.isOpen_ball _ (hUo _).2
#align is_closed.is_Gδ IsClosed.isGδ
-/

section T1Space

variable [T1Space α]

/- warning: is_Gδ_compl_singleton -> isGδ_compl_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : T1Space.{u1} α _inst_1] (a : α), IsGδ.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : T1Space.{u1} α _inst_1] (a : α), IsGδ.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))
Case conversion may be inaccurate. Consider using '#align is_Gδ_compl_singleton isGδ_compl_singletonₓ'. -/
theorem isGδ_compl_singleton (a : α) : IsGδ ({a}ᶜ : Set α) :=
  isOpen_compl_singleton.IsGδ
#align is_Gδ_compl_singleton isGδ_compl_singleton

/- warning: set.countable.is_Gδ_compl -> Set.Countable.isGδ_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : T1Space.{u1} α _inst_1] {s : Set.{u1} α}, (Set.Countable.{u1} α s) -> (IsGδ.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : T1Space.{u1} α _inst_1] {s : Set.{u1} α}, (Set.Countable.{u1} α s) -> (IsGδ.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align set.countable.is_Gδ_compl Set.Countable.isGδ_complₓ'. -/
theorem Set.Countable.isGδ_compl {s : Set α} (hs : s.Countable) : IsGδ (sᶜ) :=
  by
  rw [← bUnion_of_singleton s, compl_Union₂]
  exact isGδ_biInter hs fun x _ => isGδ_compl_singleton x
#align set.countable.is_Gδ_compl Set.Countable.isGδ_compl

/- warning: set.finite.is_Gδ_compl -> Set.Finite.isGδ_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : T1Space.{u1} α _inst_1] {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (IsGδ.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : T1Space.{u1} α _inst_1] {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (IsGδ.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align set.finite.is_Gδ_compl Set.Finite.isGδ_complₓ'. -/
theorem Set.Finite.isGδ_compl {s : Set α} (hs : s.Finite) : IsGδ (sᶜ) :=
  hs.Countable.isGδ_compl
#align set.finite.is_Gδ_compl Set.Finite.isGδ_compl

/- warning: set.subsingleton.is_Gδ_compl -> Set.Subsingleton.isGδ_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : T1Space.{u1} α _inst_1] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (IsGδ.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : T1Space.{u1} α _inst_1] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (IsGδ.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align set.subsingleton.is_Gδ_compl Set.Subsingleton.isGδ_complₓ'. -/
theorem Set.Subsingleton.isGδ_compl {s : Set α} (hs : s.Subsingleton) : IsGδ (sᶜ) :=
  hs.Finite.isGδ_compl
#align set.subsingleton.is_Gδ_compl Set.Subsingleton.isGδ_compl

/- warning: finset.is_Gδ_compl -> Finset.isGδ_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : T1Space.{u1} α _inst_1] (s : Finset.{u1} α), IsGδ.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : T1Space.{u1} α _inst_1] (s : Finset.{u1} α), IsGδ.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Finset.toSet.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.is_Gδ_compl Finset.isGδ_complₓ'. -/
theorem Finset.isGδ_compl (s : Finset α) : IsGδ (sᶜ : Set α) :=
  s.finite_toSet.isGδ_compl
#align finset.is_Gδ_compl Finset.isGδ_compl

open TopologicalSpace

variable [FirstCountableTopology α]

#print isGδ_singleton /-
theorem isGδ_singleton (a : α) : IsGδ ({a} : Set α) :=
  by
  rcases(nhds_basis_opens a).exists_antitone_subbasis with ⟨U, hU, h_basis⟩
  rw [← biInter_basis_nhds h_basis.to_has_basis]
  exact isGδ_biInter (to_countable _) fun n hn => (hU n).2.IsGδ
#align is_Gδ_singleton isGδ_singleton
-/

#print Set.Finite.isGδ /-
theorem Set.Finite.isGδ {s : Set α} (hs : s.Finite) : IsGδ s :=
  Finite.induction_on hs isGδ_empty fun a s _ _ hs => (isGδ_singleton a).union hs
#align set.finite.is_Gδ Set.Finite.isGδ
-/

end T1Space

end IsGδ

section ContinuousAt

open TopologicalSpace

open uniformity

variable [TopologicalSpace α]

#print isGδ_setOf_continuousAt /-
/-- The set of points where a function is continuous is a Gδ set. -/
theorem isGδ_setOf_continuousAt [UniformSpace β] [IsCountablyGenerated (𝓤 β)] (f : α → β) :
    IsGδ { x | ContinuousAt f x } :=
  by
  obtain ⟨U, hUo, hU⟩ := (@uniformity_hasBasis_open_symmetric β _).exists_antitone_subbasis
  simp only [Uniform.continuousAt_iff_prod, nhds_prod_eq]
  simp only [(nhds_basis_opens _).prod_self.tendsto_iffₓ hU.to_has_basis, forall_prop_of_true,
    set_of_forall, id]
  refine' isGδ_iInter fun k => IsOpen.isGδ <| isOpen_iff_mem_nhds.2 fun x => _
  rintro ⟨s, ⟨hsx, hso⟩, hsU⟩
  filter_upwards [IsOpen.mem_nhds hso hsx]with _ hy using⟨s, ⟨hy, hso⟩, hsU⟩
#align is_Gδ_set_of_continuous_at isGδ_setOf_continuousAt
-/

end ContinuousAt

section residual

variable [TopologicalSpace α]

#print residual /-
/-- A set `s` is called *residual* if it includes a countable intersection of dense open sets. -/
def residual (α : Type _) [TopologicalSpace α] : Filter α :=
  Filter.countableGenerate { t | IsOpen t ∧ Dense t }deriving CountableInterFilter
#align residual residual
-/

instance countableInterFilter_residual : CountableInterFilter (residual α) := by
  rw [residual] <;> infer_instance
#align countable_Inter_filter_residual countableInterFilter_residual

/-- Dense open sets are residual. -/
theorem residual_of_dense_open {s : Set α} (ho : IsOpen s) (hd : Dense s) : s ∈ residual α :=
  CountableGenerateSets.basic ⟨ho, hd⟩
#align residual_of_dense_open residual_of_dense_open

/-- Dense Gδ sets are residual. -/
theorem residual_of_dense_Gδ {s : Set α} (ho : IsGδ s) (hd : Dense s) : s ∈ residual α :=
  by
  rcases ho with ⟨T, To, Tct, rfl⟩
  exact
    (countable_sInter_mem Tct).mpr fun t tT =>
      residual_of_dense_open (To t tT) (hd.mono (sInter_subset_of_mem tT))
#align residual_of_dense_Gδ residual_of_dense_Gδ

/-- A set is residual iff it includes a countable intersection of dense open sets. -/
theorem mem_residual_iff {s : Set α} :
    s ∈ residual α ↔
      ∃ S : Set (Set α), (∀ t ∈ S, IsOpen t) ∧ (∀ t ∈ S, Dense t) ∧ S.Countable ∧ ⋂₀ S ⊆ s :=
  mem_countableGenerate_iff.trans <| by simp_rw [subset_def, mem_set_of, forall_and, and_assoc']
#align mem_residual_iff mem_residual_iff

end residual

