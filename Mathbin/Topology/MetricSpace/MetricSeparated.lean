/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.metric_space.metric_separated
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.EmetricSpace

/-!
# Metric separated pairs of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the predicate `is_metric_separated`. We say that two sets in an (extended)
metric space are *metric separated* if the (extended) distance between `x ∈ s` and `y ∈ t` is
bounded from below by a positive constant.

This notion is useful, e.g., to define metric outer measures.
-/


open Emetric Set

noncomputable section

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (r «expr ≠ » 0) -/
#print IsMetricSeparated /-
/-- Two sets in an (extended) metric space are called *metric separated* if the (extended) distance
between `x ∈ s` and `y ∈ t` is bounded from below by a positive constant. -/
def IsMetricSeparated {X : Type _} [EMetricSpace X] (s t : Set X) :=
  ∃ (r : _)(_ : r ≠ 0), ∀ x ∈ s, ∀ y ∈ t, r ≤ edist x y
#align is_metric_separated IsMetricSeparated
-/

namespace IsMetricSeparated

variable {X : Type _} [EMetricSpace X] {s t : Set X} {x y : X}

#print IsMetricSeparated.symm /-
@[symm]
theorem symm (h : IsMetricSeparated s t) : IsMetricSeparated t s :=
  let ⟨r, r0, hr⟩ := h
  ⟨r, r0, fun y hy x hx => edist_comm x y ▸ hr x hx y hy⟩
#align is_metric_separated.symm IsMetricSeparated.symm
-/

#print IsMetricSeparated.comm /-
theorem comm : IsMetricSeparated s t ↔ IsMetricSeparated t s :=
  ⟨symm, symm⟩
#align is_metric_separated.comm IsMetricSeparated.comm
-/

#print IsMetricSeparated.empty_left /-
@[simp]
theorem empty_left (s : Set X) : IsMetricSeparated ∅ s :=
  ⟨1, one_ne_zero, fun x => False.elim⟩
#align is_metric_separated.empty_left IsMetricSeparated.empty_left
-/

#print IsMetricSeparated.empty_right /-
@[simp]
theorem empty_right (s : Set X) : IsMetricSeparated s ∅ :=
  (empty_left s).symm
#align is_metric_separated.empty_right IsMetricSeparated.empty_right
-/

/- warning: is_metric_separated.disjoint -> IsMetricSeparated.disjoint is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : EMetricSpace.{u1} X] {s : Set.{u1} X} {t : Set.{u1} X}, (IsMetricSeparated.{u1} X _inst_1 s t) -> (Disjoint.{u1} (Set.{u1} X) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} X) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} X) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} X) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} X) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} X) (Set.completeBooleanAlgebra.{u1} X)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} X) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X))) s t)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : EMetricSpace.{u1} X] {s : Set.{u1} X} {t : Set.{u1} X}, (IsMetricSeparated.{u1} X _inst_1 s t) -> (Disjoint.{u1} (Set.{u1} X) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} X) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} X) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} X) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} X) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} X) (Set.instCompleteBooleanAlgebraSet.{u1} X)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} X) (Preorder.toLE.{u1} (Set.{u1} X) (PartialOrder.toPreorder.{u1} (Set.{u1} X) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} X) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} X) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} X) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} X) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} X) (Set.instCompleteBooleanAlgebraSet.{u1} X)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} X) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} X) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} X) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} X) (Set.instCompleteBooleanAlgebraSet.{u1} X)))))) s t)
Case conversion may be inaccurate. Consider using '#align is_metric_separated.disjoint IsMetricSeparated.disjointₓ'. -/
protected theorem disjoint (h : IsMetricSeparated s t) : Disjoint s t :=
  let ⟨r, r0, hr⟩ := h
  Set.disjoint_left.mpr fun x hx1 hx2 => r0 <| by simpa using hr x hx1 x hx2
#align is_metric_separated.disjoint IsMetricSeparated.disjoint

/- warning: is_metric_separated.subset_compl_right -> IsMetricSeparated.subset_compl_right is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : EMetricSpace.{u1} X] {s : Set.{u1} X} {t : Set.{u1} X}, (IsMetricSeparated.{u1} X _inst_1 s t) -> (HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) s (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X)) t))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : EMetricSpace.{u1} X] {s : Set.{u1} X} {t : Set.{u1} X}, (IsMetricSeparated.{u1} X _inst_1 s t) -> (HasSubset.Subset.{u1} (Set.{u1} X) (Set.instHasSubsetSet.{u1} X) s (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) t))
Case conversion may be inaccurate. Consider using '#align is_metric_separated.subset_compl_right IsMetricSeparated.subset_compl_rightₓ'. -/
theorem subset_compl_right (h : IsMetricSeparated s t) : s ⊆ tᶜ := fun x hs ht =>
  h.Disjoint.le_bot ⟨hs, ht⟩
#align is_metric_separated.subset_compl_right IsMetricSeparated.subset_compl_right

#print IsMetricSeparated.mono /-
@[mono]
theorem mono {s' t'} (hs : s ⊆ s') (ht : t ⊆ t') :
    IsMetricSeparated s' t' → IsMetricSeparated s t := fun ⟨r, r0, hr⟩ =>
  ⟨r, r0, fun x hx y hy => hr x (hs hx) y (ht hy)⟩
#align is_metric_separated.mono IsMetricSeparated.mono
-/

#print IsMetricSeparated.mono_left /-
theorem mono_left {s'} (h' : IsMetricSeparated s' t) (hs : s ⊆ s') : IsMetricSeparated s t :=
  h'.mono hs Subset.rfl
#align is_metric_separated.mono_left IsMetricSeparated.mono_left
-/

#print IsMetricSeparated.mono_right /-
theorem mono_right {t'} (h' : IsMetricSeparated s t') (ht : t ⊆ t') : IsMetricSeparated s t :=
  h'.mono Subset.rfl ht
#align is_metric_separated.mono_right IsMetricSeparated.mono_right
-/

/- warning: is_metric_separated.union_left -> IsMetricSeparated.union_left is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : EMetricSpace.{u1} X] {s : Set.{u1} X} {t : Set.{u1} X} {s' : Set.{u1} X}, (IsMetricSeparated.{u1} X _inst_1 s t) -> (IsMetricSeparated.{u1} X _inst_1 s' t) -> (IsMetricSeparated.{u1} X _inst_1 (Union.union.{u1} (Set.{u1} X) (Set.hasUnion.{u1} X) s s') t)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : EMetricSpace.{u1} X] {s : Set.{u1} X} {t : Set.{u1} X} {s' : Set.{u1} X}, (IsMetricSeparated.{u1} X _inst_1 s t) -> (IsMetricSeparated.{u1} X _inst_1 s' t) -> (IsMetricSeparated.{u1} X _inst_1 (Union.union.{u1} (Set.{u1} X) (Set.instUnionSet.{u1} X) s s') t)
Case conversion may be inaccurate. Consider using '#align is_metric_separated.union_left IsMetricSeparated.union_leftₓ'. -/
theorem union_left {s'} (h : IsMetricSeparated s t) (h' : IsMetricSeparated s' t) :
    IsMetricSeparated (s ∪ s') t :=
  by
  rcases h, h' with ⟨⟨r, r0, hr⟩, ⟨r', r0', hr'⟩⟩
  refine' ⟨min r r', _, fun x hx y hy => hx.elim _ _⟩
  · rw [← pos_iff_ne_zero] at r0 r0'⊢
    exact lt_min r0 r0'
  · exact fun hx => (min_le_left _ _).trans (hr _ hx _ hy)
  · exact fun hx => (min_le_right _ _).trans (hr' _ hx _ hy)
#align is_metric_separated.union_left IsMetricSeparated.union_left

/- warning: is_metric_separated.union_left_iff -> IsMetricSeparated.union_left_iff is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : EMetricSpace.{u1} X] {s : Set.{u1} X} {t : Set.{u1} X} {s' : Set.{u1} X}, Iff (IsMetricSeparated.{u1} X _inst_1 (Union.union.{u1} (Set.{u1} X) (Set.hasUnion.{u1} X) s s') t) (And (IsMetricSeparated.{u1} X _inst_1 s t) (IsMetricSeparated.{u1} X _inst_1 s' t))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : EMetricSpace.{u1} X] {s : Set.{u1} X} {t : Set.{u1} X} {s' : Set.{u1} X}, Iff (IsMetricSeparated.{u1} X _inst_1 (Union.union.{u1} (Set.{u1} X) (Set.instUnionSet.{u1} X) s s') t) (And (IsMetricSeparated.{u1} X _inst_1 s t) (IsMetricSeparated.{u1} X _inst_1 s' t))
Case conversion may be inaccurate. Consider using '#align is_metric_separated.union_left_iff IsMetricSeparated.union_left_iffₓ'. -/
@[simp]
theorem union_left_iff {s'} :
    IsMetricSeparated (s ∪ s') t ↔ IsMetricSeparated s t ∧ IsMetricSeparated s' t :=
  ⟨fun h => ⟨h.mono_left (subset_union_left _ _), h.mono_left (subset_union_right _ _)⟩, fun h =>
    h.1.union_left h.2⟩
#align is_metric_separated.union_left_iff IsMetricSeparated.union_left_iff

/- warning: is_metric_separated.union_right -> IsMetricSeparated.union_right is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : EMetricSpace.{u1} X] {s : Set.{u1} X} {t : Set.{u1} X} {t' : Set.{u1} X}, (IsMetricSeparated.{u1} X _inst_1 s t) -> (IsMetricSeparated.{u1} X _inst_1 s t') -> (IsMetricSeparated.{u1} X _inst_1 s (Union.union.{u1} (Set.{u1} X) (Set.hasUnion.{u1} X) t t'))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : EMetricSpace.{u1} X] {s : Set.{u1} X} {t : Set.{u1} X} {t' : Set.{u1} X}, (IsMetricSeparated.{u1} X _inst_1 s t) -> (IsMetricSeparated.{u1} X _inst_1 s t') -> (IsMetricSeparated.{u1} X _inst_1 s (Union.union.{u1} (Set.{u1} X) (Set.instUnionSet.{u1} X) t t'))
Case conversion may be inaccurate. Consider using '#align is_metric_separated.union_right IsMetricSeparated.union_rightₓ'. -/
theorem union_right {t'} (h : IsMetricSeparated s t) (h' : IsMetricSeparated s t') :
    IsMetricSeparated s (t ∪ t') :=
  (h.symm.union_left h'.symm).symm
#align is_metric_separated.union_right IsMetricSeparated.union_right

/- warning: is_metric_separated.union_right_iff -> IsMetricSeparated.union_right_iff is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : EMetricSpace.{u1} X] {s : Set.{u1} X} {t : Set.{u1} X} {t' : Set.{u1} X}, Iff (IsMetricSeparated.{u1} X _inst_1 s (Union.union.{u1} (Set.{u1} X) (Set.hasUnion.{u1} X) t t')) (And (IsMetricSeparated.{u1} X _inst_1 s t) (IsMetricSeparated.{u1} X _inst_1 s t'))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : EMetricSpace.{u1} X] {s : Set.{u1} X} {t : Set.{u1} X} {t' : Set.{u1} X}, Iff (IsMetricSeparated.{u1} X _inst_1 s (Union.union.{u1} (Set.{u1} X) (Set.instUnionSet.{u1} X) t t')) (And (IsMetricSeparated.{u1} X _inst_1 s t) (IsMetricSeparated.{u1} X _inst_1 s t'))
Case conversion may be inaccurate. Consider using '#align is_metric_separated.union_right_iff IsMetricSeparated.union_right_iffₓ'. -/
@[simp]
theorem union_right_iff {t'} :
    IsMetricSeparated s (t ∪ t') ↔ IsMetricSeparated s t ∧ IsMetricSeparated s t' :=
  comm.trans <| union_left_iff.trans <| and_congr comm comm
#align is_metric_separated.union_right_iff IsMetricSeparated.union_right_iff

#print IsMetricSeparated.finite_unionᵢ_left_iff /-
theorem finite_unionᵢ_left_iff {ι : Type _} {I : Set ι} (hI : I.Finite) {s : ι → Set X}
    {t : Set X} : IsMetricSeparated (⋃ i ∈ I, s i) t ↔ ∀ i ∈ I, IsMetricSeparated (s i) t :=
  by
  refine' finite.induction_on hI (by simp) fun i I hi _ hI => _
  rw [bUnion_insert, ball_insert_iff, union_left_iff, hI]
#align is_metric_separated.finite_Union_left_iff IsMetricSeparated.finite_unionᵢ_left_iff
-/

alias finite_Union_left_iff ↔ _ finite_Union_left
#align is_metric_separated.finite_Union_left IsMetricSeparated.finite_unionᵢ_left

#print IsMetricSeparated.finite_unionᵢ_right_iff /-
theorem finite_unionᵢ_right_iff {ι : Type _} {I : Set ι} (hI : I.Finite) {s : Set X}
    {t : ι → Set X} : IsMetricSeparated s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, IsMetricSeparated s (t i) := by
  simpa only [@comm _ _ s] using finite_Union_left_iff hI
#align is_metric_separated.finite_Union_right_iff IsMetricSeparated.finite_unionᵢ_right_iff
-/

#print IsMetricSeparated.finset_unionᵢ_left_iff /-
@[simp]
theorem finset_unionᵢ_left_iff {ι : Type _} {I : Finset ι} {s : ι → Set X} {t : Set X} :
    IsMetricSeparated (⋃ i ∈ I, s i) t ↔ ∀ i ∈ I, IsMetricSeparated (s i) t :=
  finite_unionᵢ_left_iff I.finite_toSet
#align is_metric_separated.finset_Union_left_iff IsMetricSeparated.finset_unionᵢ_left_iff
-/

alias finset_Union_left_iff ↔ _ finset_Union_left
#align is_metric_separated.finset_Union_left IsMetricSeparated.finset_unionᵢ_left

#print IsMetricSeparated.finset_unionᵢ_right_iff /-
@[simp]
theorem finset_unionᵢ_right_iff {ι : Type _} {I : Finset ι} {s : Set X} {t : ι → Set X} :
    IsMetricSeparated s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, IsMetricSeparated s (t i) :=
  finite_unionᵢ_right_iff I.finite_toSet
#align is_metric_separated.finset_Union_right_iff IsMetricSeparated.finset_unionᵢ_right_iff
-/

alias finset_Union_right_iff ↔ _ finset_Union_right
#align is_metric_separated.finset_Union_right IsMetricSeparated.finset_unionᵢ_right

end IsMetricSeparated

