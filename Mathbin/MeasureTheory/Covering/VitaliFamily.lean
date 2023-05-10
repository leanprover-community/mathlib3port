/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.covering.vitali_family
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.MeasureSpace

/-!
# Vitali families

On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets with
nonempty interiors, called `sets_at x`. This family is a Vitali family if it satisfies the following
property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `sets_at x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.

This file gives the basic definition of Vitali families. More interesting developments of this
notion are deferred to other files:
* constructions of specific Vitali families are provided by the Besicovitch covering theorem, in
`besicovitch.vitali_family`, and by the Vitali covering theorem, in `vitali.vitali_family`.
* The main theorem on differentiation of measures along a Vitali family is proved in
`vitali_family.ae_tendsto_rn_deriv`.

## Main definitions

* `vitali_family μ` is a structure made, for each `x : X`, of a family of sets around `x`, such that
one can extract an almost everywhere disjoint covering from any subfamily containing sets of
arbitrarily small diameters.

Let `v` be such a Vitali family.
* `v.fine_subfamily_on` describes the subfamilies of `v` from which one can extract almost
everywhere disjoint coverings. This property, called
`v.fine_subfamily_on.exists_disjoint_covering_ae`, is essentially a restatement of the definition
of a Vitali family. We also provide an API to use efficiently such a disjoint covering.
* `v.filter_at x` is a filter on sets of `X`, such that convergence with respect to this filter
means convergence when sets in the Vitali family shrink towards `x`.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.8][Federer1996] (Vitali families are called
Vitali relations there)
-/


open MeasureTheory Metric Set Filter TopologicalSpace MeasureTheory.Measure

open Filter MeasureTheory Topology

variable {α : Type _} [MetricSpace α]

#print VitaliFamily /-
/-- On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets
with nonempty interiors, called `sets_at x`. This family is a Vitali family if it satisfies the
following property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `sets_at x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.
-/
@[nolint has_nonempty_instance]
structure VitaliFamily {m : MeasurableSpace α} (μ : Measure α) where
  setsAt : ∀ x : α, Set (Set α)
  MeasurableSet' : ∀ x : α, ∀ a : Set α, a ∈ sets_at x → MeasurableSet a
  nonempty_interior : ∀ x : α, ∀ y : Set α, y ∈ sets_at x → (interior y).Nonempty
  Nontrivial : ∀ (x : α), ∀ ε > (0 : ℝ), ∃ y ∈ sets_at x, y ⊆ closedBall x ε
  covering :
    ∀ (s : Set α) (f : ∀ x : α, Set (Set α)),
      (∀ x ∈ s, f x ⊆ sets_at x) →
        (∀ x ∈ s, ∀ ε > (0 : ℝ), ∃ a ∈ f x, a ⊆ closedBall x ε) →
          ∃ t : Set (α × Set α),
            (∀ p : α × Set α, p ∈ t → p.1 ∈ s) ∧
              (t.PairwiseDisjoint fun p => p.2) ∧
                (∀ p : α × Set α, p ∈ t → p.2 ∈ f p.1) ∧
                  μ (s \ ⋃ (p : α × Set α) (hp : p ∈ t), p.2) = 0
#align vitali_family VitaliFamily
-/

namespace VitaliFamily

variable {m0 : MeasurableSpace α} {μ : Measure α}

include μ

#print VitaliFamily.mono /-
/-- A Vitali family for a measure `μ` is also a Vitali family for any measure absolutely continuous
with respect to `μ`. -/
def mono (v : VitaliFamily μ) (ν : Measure α) (hν : ν ≪ μ) : VitaliFamily ν
    where
  setsAt := v.setsAt
  MeasurableSet' := v.MeasurableSet'
  nonempty_interior := v.nonempty_interior
  Nontrivial := v.Nontrivial
  covering s f h h' :=
    by
    rcases v.covering s f h h' with ⟨t, ts, disj, mem_f, hμ⟩
    exact ⟨t, ts, disj, mem_f, hν hμ⟩
#align vitali_family.mono VitaliFamily.mono
-/

#print VitaliFamily.FineSubfamilyOn /-
/-- Given a Vitali family `v` for a measure `μ`, a family `f` is a fine subfamily on a set `s` if
every point `x` in `s` belongs to arbitrarily small sets in `v.sets_at x ∩ f x`. This is precisely
the subfamilies for which the Vitali family definition ensures that one can extract a disjoint
covering of almost all `s`. -/
def FineSubfamilyOn (v : VitaliFamily μ) (f : α → Set (Set α)) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ ε > 0, ∃ a ∈ v.setsAt x ∩ f x, a ⊆ closedBall x ε
#align vitali_family.fine_subfamily_on VitaliFamily.FineSubfamilyOn
-/

namespace FineSubfamilyOn

variable {v : VitaliFamily μ} {f : α → Set (Set α)} {s : Set α} (h : v.FineSubfamilyOn f s)

include h

/- warning: vitali_family.fine_subfamily_on.exists_disjoint_covering_ae -> VitaliFamily.FineSubfamilyOn.exists_disjoint_covering_ae is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {v : VitaliFamily.{u1} α _inst_1 m0 μ} {f : α -> (Set.{u1} (Set.{u1} α))} {s : Set.{u1} α}, (VitaliFamily.FineSubfamilyOn.{u1} α _inst_1 m0 μ v f s) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (fun (t : Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) => And (forall (p : Prod.{u1, u1} α (Set.{u1} α)), (Membership.Mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.hasMem.{u1} (Prod.{u1, u1} α (Set.{u1} α))) p t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Prod.fst.{u1, u1} α (Set.{u1} α) p) s)) (And (Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) (Prod.{u1, u1} α (Set.{u1} α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) t (fun (p : Prod.{u1, u1} α (Set.{u1} α)) => Prod.snd.{u1, u1} α (Set.{u1} α) p)) (And (forall (p : Prod.{u1, u1} α (Set.{u1} α)), (Membership.Mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.hasMem.{u1} (Prod.{u1, u1} α (Set.{u1} α))) p t) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Prod.snd.{u1, u1} α (Set.{u1} α) p) (Inter.inter.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasInter.{u1} (Set.{u1} α)) (VitaliFamily.setsAt.{u1} α _inst_1 m0 μ v (Prod.fst.{u1, u1} α (Set.{u1} α) p)) (f (Prod.fst.{u1, u1} α (Set.{u1} α) p))))) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Set.unionᵢ.{u1, succ u1} α (Prod.{u1, u1} α (Set.{u1} α)) (fun (p : Prod.{u1, u1} α (Set.{u1} α)) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.hasMem.{u1} (Prod.{u1, u1} α (Set.{u1} α))) p t) (fun (hp : Membership.Mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.hasMem.{u1} (Prod.{u1, u1} α (Set.{u1} α))) p t) => Prod.snd.{u1, u1} α (Set.{u1} α) p))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {v : VitaliFamily.{u1} α _inst_1 m0 μ} {f : α -> (Set.{u1} (Set.{u1} α))} {s : Set.{u1} α}, (VitaliFamily.FineSubfamilyOn.{u1} α _inst_1 m0 μ v f s) -> (Exists.{succ u1} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (fun (t : Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) => And (forall (p : Prod.{u1, u1} α (Set.{u1} α)), (Membership.mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α (Set.{u1} α))) p t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Prod.fst.{u1, u1} α (Set.{u1} α) p) s)) (And (Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) (Prod.{u1, u1} α (Set.{u1} α)) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) t (fun (p : Prod.{u1, u1} α (Set.{u1} α)) => Prod.snd.{u1, u1} α (Set.{u1} α) p)) (And (forall (p : Prod.{u1, u1} α (Set.{u1} α)), (Membership.mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α (Set.{u1} α))) p t) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (Prod.snd.{u1, u1} α (Set.{u1} α) p) (Inter.inter.{u1} (Set.{u1} (Set.{u1} α)) (Set.instInterSet.{u1} (Set.{u1} α)) (VitaliFamily.setsAt.{u1} α _inst_1 m0 μ v (Prod.fst.{u1, u1} α (Set.{u1} α) p)) (f (Prod.fst.{u1, u1} α (Set.{u1} α) p))))) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Set.unionᵢ.{u1, succ u1} α (Prod.{u1, u1} α (Set.{u1} α)) (fun (p : Prod.{u1, u1} α (Set.{u1} α)) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α (Set.{u1} α))) p t) (fun (hp : Membership.mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α (Set.{u1} α))) p t) => Prod.snd.{u1, u1} α (Set.{u1} α) p))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))))))
Case conversion may be inaccurate. Consider using '#align vitali_family.fine_subfamily_on.exists_disjoint_covering_ae VitaliFamily.FineSubfamilyOn.exists_disjoint_covering_aeₓ'. -/
theorem exists_disjoint_covering_ae :
    ∃ t : Set (α × Set α),
      (∀ p : α × Set α, p ∈ t → p.1 ∈ s) ∧
        (t.PairwiseDisjoint fun p => p.2) ∧
          (∀ p : α × Set α, p ∈ t → p.2 ∈ v.setsAt p.1 ∩ f p.1) ∧
            μ (s \ ⋃ (p : α × Set α) (hp : p ∈ t), p.2) = 0 :=
  v.covering s (fun x => v.setsAt x ∩ f x) (fun x hx => inter_subset_left _ _) h
#align vitali_family.fine_subfamily_on.exists_disjoint_covering_ae VitaliFamily.FineSubfamilyOn.exists_disjoint_covering_ae

#print VitaliFamily.FineSubfamilyOn.index /-
/-- Given `h : v.fine_subfamily_on f s`, then `h.index` is a set parametrizing a disjoint
covering of almost every `s`. -/
protected def index : Set (α × Set α) :=
  h.exists_disjoint_covering_ae.some
#align vitali_family.fine_subfamily_on.index VitaliFamily.FineSubfamilyOn.index
-/

#print VitaliFamily.FineSubfamilyOn.covering /-
/-- Given `h : v.fine_subfamily_on f s`, then `h.covering p` is a set in the family,
for `p ∈ h.index`, such that these sets form a disjoint covering of almost every `s`. -/
@[nolint unused_arguments]
protected def covering : α × Set α → Set α := fun p => p.2
#align vitali_family.fine_subfamily_on.covering VitaliFamily.FineSubfamilyOn.covering
-/

#print VitaliFamily.FineSubfamilyOn.index_subset /-
theorem index_subset : ∀ p : α × Set α, p ∈ h.index → p.1 ∈ s :=
  h.exists_disjoint_covering_ae.choose_spec.1
#align vitali_family.fine_subfamily_on.index_subset VitaliFamily.FineSubfamilyOn.index_subset
-/

/- warning: vitali_family.fine_subfamily_on.covering_disjoint -> VitaliFamily.FineSubfamilyOn.covering_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {v : VitaliFamily.{u1} α _inst_1 m0 μ} {f : α -> (Set.{u1} (Set.{u1} α))} {s : Set.{u1} α} (h : VitaliFamily.FineSubfamilyOn.{u1} α _inst_1 m0 μ v f s), Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) (Prod.{u1, u1} α (Set.{u1} α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h) (VitaliFamily.FineSubfamilyOn.covering.{u1} α _inst_1 m0 μ v f s h)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {v : VitaliFamily.{u1} α _inst_1 m0 μ} {f : α -> (Set.{u1} (Set.{u1} α))} {s : Set.{u1} α} (h : VitaliFamily.FineSubfamilyOn.{u1} α _inst_1 m0 μ v f s), Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) (Prod.{u1, u1} α (Set.{u1} α)) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h) (VitaliFamily.FineSubfamilyOn.covering.{u1} α _inst_1 m0 μ v f s h)
Case conversion may be inaccurate. Consider using '#align vitali_family.fine_subfamily_on.covering_disjoint VitaliFamily.FineSubfamilyOn.covering_disjointₓ'. -/
theorem covering_disjoint : h.index.PairwiseDisjoint h.covering :=
  h.exists_disjoint_covering_ae.choose_spec.2.1
#align vitali_family.fine_subfamily_on.covering_disjoint VitaliFamily.FineSubfamilyOn.covering_disjoint

/- warning: vitali_family.fine_subfamily_on.covering_disjoint_subtype -> VitaliFamily.FineSubfamilyOn.covering_disjoint_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {v : VitaliFamily.{u1} α _inst_1 m0 μ} {f : α -> (Set.{u1} (Set.{u1} α))} {s : Set.{u1} α} (h : VitaliFamily.FineSubfamilyOn.{u1} α _inst_1 m0 μ v f s), Pairwise.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Function.onFun.{succ u1, succ u1, 1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) => VitaliFamily.FineSubfamilyOn.covering.{u1} α _inst_1 m0 μ v f s h ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Prod.{u1, u1} α (Set.{u1} α)) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Prod.{u1, u1} α (Set.{u1} α)) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Prod.{u1, u1} α (Set.{u1} α)) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Prod.{u1, u1} α (Set.{u1} α)) (coeSubtype.{succ u1} (Prod.{u1, u1} α (Set.{u1} α)) (fun (x : Prod.{u1, u1} α (Set.{u1} α)) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.hasMem.{u1} (Prod.{u1, u1} α (Set.{u1} α))) x (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)))))) x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {v : VitaliFamily.{u1} α _inst_1 m0 μ} {f : α -> (Set.{u1} (Set.{u1} α))} {s : Set.{u1} α} (h : VitaliFamily.FineSubfamilyOn.{u1} α _inst_1 m0 μ v f s), Pairwise.{u1} (Set.Elem.{u1} (Prod.{u1, u1} α (Set.{u1} α)) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Function.onFun.{succ u1, succ u1, 1} (Set.Elem.{u1} (Prod.{u1, u1} α (Set.{u1} α)) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (fun (x : Set.Elem.{u1} (Prod.{u1, u1} α (Set.{u1} α)) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) => VitaliFamily.FineSubfamilyOn.covering.{u1} α _inst_1 m0 μ v f s h (Subtype.val.{succ u1} (Prod.{u1, u1} α (Set.{u1} α)) (fun (x : Prod.{u1, u1} α (Set.{u1} α)) => Membership.mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α (Set.{u1} α))) x (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) x)))
Case conversion may be inaccurate. Consider using '#align vitali_family.fine_subfamily_on.covering_disjoint_subtype VitaliFamily.FineSubfamilyOn.covering_disjoint_subtypeₓ'. -/
theorem covering_disjoint_subtype : Pairwise (Disjoint on fun x : h.index => h.covering x) :=
  (pairwise_subtype_iff_pairwise_set _ _).2 h.covering_disjoint
#align vitali_family.fine_subfamily_on.covering_disjoint_subtype VitaliFamily.FineSubfamilyOn.covering_disjoint_subtype

#print VitaliFamily.FineSubfamilyOn.covering_mem /-
theorem covering_mem {p : α × Set α} (hp : p ∈ h.index) : h.covering p ∈ f p.1 :=
  (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).2
#align vitali_family.fine_subfamily_on.covering_mem VitaliFamily.FineSubfamilyOn.covering_mem
-/

#print VitaliFamily.FineSubfamilyOn.covering_mem_family /-
theorem covering_mem_family {p : α × Set α} (hp : p ∈ h.index) : h.covering p ∈ v.setsAt p.1 :=
  (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).1
#align vitali_family.fine_subfamily_on.covering_mem_family VitaliFamily.FineSubfamilyOn.covering_mem_family
-/

/- warning: vitali_family.fine_subfamily_on.measure_diff_bUnion -> VitaliFamily.FineSubfamilyOn.measure_diff_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {v : VitaliFamily.{u1} α _inst_1 m0 μ} {f : α -> (Set.{u1} (Set.{u1} α))} {s : Set.{u1} α} (h : VitaliFamily.FineSubfamilyOn.{u1} α _inst_1 m0 μ v f s), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Set.unionᵢ.{u1, succ u1} α (Prod.{u1, u1} α (Set.{u1} α)) (fun (p : Prod.{u1, u1} α (Set.{u1} α)) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.hasMem.{u1} (Prod.{u1, u1} α (Set.{u1} α))) p (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (fun (H : Membership.Mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.hasMem.{u1} (Prod.{u1, u1} α (Set.{u1} α))) p (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) => VitaliFamily.FineSubfamilyOn.covering.{u1} α _inst_1 m0 μ v f s h p))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {v : VitaliFamily.{u1} α _inst_1 m0 μ} {f : α -> (Set.{u1} (Set.{u1} α))} {s : Set.{u1} α} (h : VitaliFamily.FineSubfamilyOn.{u1} α _inst_1 m0 μ v f s), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Set.unionᵢ.{u1, succ u1} α (Prod.{u1, u1} α (Set.{u1} α)) (fun (p : Prod.{u1, u1} α (Set.{u1} α)) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α (Set.{u1} α))) p (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (fun (H : Membership.mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α (Set.{u1} α))) p (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) => VitaliFamily.FineSubfamilyOn.covering.{u1} α _inst_1 m0 μ v f s h p))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align vitali_family.fine_subfamily_on.measure_diff_bUnion VitaliFamily.FineSubfamilyOn.measure_diff_bunionᵢₓ'. -/
theorem measure_diff_bunionᵢ : μ (s \ ⋃ p ∈ h.index, h.covering p) = 0 :=
  h.exists_disjoint_covering_ae.choose_spec.2.2.2
#align vitali_family.fine_subfamily_on.measure_diff_bUnion VitaliFamily.FineSubfamilyOn.measure_diff_bunionᵢ

#print VitaliFamily.FineSubfamilyOn.index_countable /-
theorem index_countable [SecondCountableTopology α] : h.index.Countable :=
  h.covering_disjoint.countable_of_nonempty_interior fun x hx =>
    v.nonempty_interior _ _ (h.covering_mem_family hx)
#align vitali_family.fine_subfamily_on.index_countable VitaliFamily.FineSubfamilyOn.index_countable
-/

#print VitaliFamily.FineSubfamilyOn.measurableSet_u /-
protected theorem measurableSet_u {p : α × Set α} (hp : p ∈ h.index) :
    MeasurableSet (h.covering p) :=
  v.MeasurableSet' p.1 _ (h.covering_mem_family hp)
#align vitali_family.fine_subfamily_on.measurable_set_u VitaliFamily.FineSubfamilyOn.measurableSet_u
-/

/- warning: vitali_family.fine_subfamily_on.measure_le_tsum_of_absolutely_continuous -> VitaliFamily.FineSubfamilyOn.measure_le_tsum_of_absolutelyContinuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {v : VitaliFamily.{u1} α _inst_1 m0 μ} {f : α -> (Set.{u1} (Set.{u1} α))} {s : Set.{u1} α} (h : VitaliFamily.FineSubfamilyOn.{u1} α _inst_1 m0 μ v f s) [_inst_2 : TopologicalSpace.SecondCountableTopology.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)))] {ρ : MeasureTheory.Measure.{u1} α m0}, (MeasureTheory.Measure.AbsolutelyContinuous.{u1} α m0 ρ μ) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) ρ s) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (fun (p : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) ρ (VitaliFamily.FineSubfamilyOn.covering.{u1} α _inst_1 m0 μ v f s h ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Prod.{u1, u1} α (Set.{u1} α)) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Prod.{u1, u1} α (Set.{u1} α)) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Prod.{u1, u1} α (Set.{u1} α)) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Prod.{u1, u1} α (Set.{u1} α)) (coeSubtype.{succ u1} (Prod.{u1, u1} α (Set.{u1} α)) (fun (x : Prod.{u1, u1} α (Set.{u1} α)) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.hasMem.{u1} (Prod.{u1, u1} α (Set.{u1} α))) x (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)))))) p)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {v : VitaliFamily.{u1} α _inst_1 m0 μ} {f : α -> (Set.{u1} (Set.{u1} α))} {s : Set.{u1} α} (h : VitaliFamily.FineSubfamilyOn.{u1} α _inst_1 m0 μ v f s) [_inst_2 : TopologicalSpace.SecondCountableTopology.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)))] {ρ : MeasureTheory.Measure.{u1} α m0}, (MeasureTheory.Measure.AbsolutelyContinuous.{u1} α m0 ρ μ) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 ρ) s) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u1} (Prod.{u1, u1} α (Set.{u1} α)) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (fun (p : Set.Elem.{u1} (Prod.{u1, u1} α (Set.{u1} α)) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 ρ) (VitaliFamily.FineSubfamilyOn.covering.{u1} α _inst_1 m0 μ v f s h (Subtype.val.{succ u1} (Prod.{u1, u1} α (Set.{u1} α)) (fun (x : Prod.{u1, u1} α (Set.{u1} α)) => Membership.mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α (Set.{u1} α))) x (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) p)))))
Case conversion may be inaccurate. Consider using '#align vitali_family.fine_subfamily_on.measure_le_tsum_of_absolutely_continuous VitaliFamily.FineSubfamilyOn.measure_le_tsum_of_absolutelyContinuousₓ'. -/
theorem measure_le_tsum_of_absolutelyContinuous [SecondCountableTopology α] {ρ : Measure α}
    (hρ : ρ ≪ μ) : ρ s ≤ ∑' p : h.index, ρ (h.covering p) :=
  calc
    ρ s ≤ ρ ((s \ ⋃ p ∈ h.index, h.covering p) ∪ ⋃ p ∈ h.index, h.covering p) :=
      measure_mono (by simp only [subset_union_left, diff_union_self])
    _ ≤ ρ (s \ ⋃ p ∈ h.index, h.covering p) + ρ (⋃ p ∈ h.index, h.covering p) :=
      (measure_union_le _ _)
    _ = ∑' p : h.index, ρ (h.covering p) := by
      rw [hρ h.measure_diff_bUnion,
        measure_bUnion h.index_countable h.covering_disjoint fun x hx => h.measurable_set_u hx,
        zero_add]
    
#align vitali_family.fine_subfamily_on.measure_le_tsum_of_absolutely_continuous VitaliFamily.FineSubfamilyOn.measure_le_tsum_of_absolutelyContinuous

/- warning: vitali_family.fine_subfamily_on.measure_le_tsum -> VitaliFamily.FineSubfamilyOn.measure_le_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {v : VitaliFamily.{u1} α _inst_1 m0 μ} {f : α -> (Set.{u1} (Set.{u1} α))} {s : Set.{u1} α} (h : VitaliFamily.FineSubfamilyOn.{u1} α _inst_1 m0 μ v f s) [_inst_2 : TopologicalSpace.SecondCountableTopology.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)))], LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (VitaliFamily.FineSubfamilyOn.covering.{u1} α _inst_1 m0 μ v f s h ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Prod.{u1, u1} α (Set.{u1} α)) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Prod.{u1, u1} α (Set.{u1} α)) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Prod.{u1, u1} α (Set.{u1} α)) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) Type.{u1} (Set.hasCoeToSort.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (Prod.{u1, u1} α (Set.{u1} α)) (coeSubtype.{succ u1} (Prod.{u1, u1} α (Set.{u1} α)) (fun (x : Prod.{u1, u1} α (Set.{u1} α)) => Membership.Mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.hasMem.{u1} (Prod.{u1, u1} α (Set.{u1} α))) x (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)))))) x))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {v : VitaliFamily.{u1} α _inst_1 m0 μ} {f : α -> (Set.{u1} (Set.{u1} α))} {s : Set.{u1} α} (h : VitaliFamily.FineSubfamilyOn.{u1} α _inst_1 m0 μ v f s) [_inst_2 : TopologicalSpace.SecondCountableTopology.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)))], LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u1} (Prod.{u1, u1} α (Set.{u1} α)) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) (fun (x : Set.Elem.{u1} (Prod.{u1, u1} α (Set.{u1} α)) (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (VitaliFamily.FineSubfamilyOn.covering.{u1} α _inst_1 m0 μ v f s h (Subtype.val.{succ u1} (Prod.{u1, u1} α (Set.{u1} α)) (fun (x : Prod.{u1, u1} α (Set.{u1} α)) => Membership.mem.{u1, u1} (Prod.{u1, u1} α (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} α (Set.{u1} α))) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α (Set.{u1} α))) x (VitaliFamily.FineSubfamilyOn.index.{u1} α _inst_1 m0 μ v f s h)) x))))
Case conversion may be inaccurate. Consider using '#align vitali_family.fine_subfamily_on.measure_le_tsum VitaliFamily.FineSubfamilyOn.measure_le_tsumₓ'. -/
theorem measure_le_tsum [SecondCountableTopology α] : μ s ≤ ∑' x : h.index, μ (h.covering x) :=
  h.measure_le_tsum_of_absolutelyContinuous Measure.AbsolutelyContinuous.rfl
#align vitali_family.fine_subfamily_on.measure_le_tsum VitaliFamily.FineSubfamilyOn.measure_le_tsum

end FineSubfamilyOn

/- warning: vitali_family.enlarge -> VitaliFamily.enlarge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0}, (VitaliFamily.{u1} α _inst_1 m0 μ) -> (forall (δ : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (VitaliFamily.{u1} α _inst_1 m0 μ))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0}, (VitaliFamily.{u1} α _inst_1 m0 μ) -> (forall (δ : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (VitaliFamily.{u1} α _inst_1 m0 μ))
Case conversion may be inaccurate. Consider using '#align vitali_family.enlarge VitaliFamily.enlargeₓ'. -/
/-- One can enlarge a Vitali family by adding to the sets `f x` at `x` all sets which are not
contained in a `δ`-neighborhood on `x`. This does not change the local filter at a point, but it
can be convenient to get a nicer global behavior. -/
def enlarge (v : VitaliFamily μ) (δ : ℝ) (δpos : 0 < δ) : VitaliFamily μ
    where
  setsAt x := v.setsAt x ∪ { a | MeasurableSet a ∧ (interior a).Nonempty ∧ ¬a ⊆ closedBall x δ }
  MeasurableSet' x a ha := by
    cases ha
    exacts[v.measurable_set' _ _ ha, ha.1]
  nonempty_interior x a ha := by
    cases ha
    exacts[v.nonempty_interior _ _ ha, ha.2.1]
  Nontrivial := by
    intro x ε εpos
    rcases v.nontrivial x ε εpos with ⟨a, ha, h'a⟩
    exact ⟨a, mem_union_left _ ha, h'a⟩
  covering := by
    intro s f fset ffine
    let g : α → Set (Set α) := fun x => f x ∩ v.sets_at x
    have : ∀ x ∈ s, ∀ ε : ℝ, ε > 0 → ∃ (a : Set α)(H : a ∈ g x), a ⊆ closed_ball x ε :=
      by
      intro x hx ε εpos
      obtain ⟨a, af, ha⟩ : ∃ a ∈ f x, a ⊆ closed_ball x (min ε δ)
      exact ffine x hx (min ε δ) (lt_min εpos δpos)
      rcases fset x hx af with (h'a | h'a)
      · exact ⟨a, ⟨af, h'a⟩, ha.trans (closed_ball_subset_closed_ball (min_le_left _ _))⟩
      · refine' False.elim (h'a.2.2 _)
        exact ha.trans (closed_ball_subset_closed_ball (min_le_right _ _))
    rcases v.covering s g (fun x hx => inter_subset_right _ _) this with ⟨t, ts, tdisj, tg, μt⟩
    exact ⟨t, ts, tdisj, fun p hp => (tg p hp).1, μt⟩
#align vitali_family.enlarge VitaliFamily.enlarge

variable (v : VitaliFamily μ)

include v

#print VitaliFamily.filterAt /-
/-- Given a vitali family `v`, then `v.filter_at x` is the filter on `set α` made of those families
that contain all sets of `v.sets_at x` of a sufficiently small diameter. This filter makes it
possible to express limiting behavior when sets in `v.sets_at x` shrink to `x`. -/
def filterAt (x : α) : Filter (Set α) :=
  ⨅ ε ∈ Ioi (0 : ℝ), 𝓟 ({ a ∈ v.setsAt x | a ⊆ closedBall x ε })
#align vitali_family.filter_at VitaliFamily.filterAt
-/

/- warning: vitali_family.mem_filter_at_iff -> VitaliFamily.mem_filterAt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (v : VitaliFamily.{u1} α _inst_1 m0 μ) {x : α} {s : Set.{u1} (Set.{u1} α)}, Iff (Membership.Mem.{u1, u1} (Set.{u1} (Set.{u1} α)) (Filter.{u1} (Set.{u1} α)) (Filter.hasMem.{u1} (Set.{u1} α)) s (VitaliFamily.filterAt.{u1} α _inst_1 m0 μ v x)) (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (a : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) a (VitaliFamily.setsAt.{u1} α _inst_1 m0 μ v x)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) a (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε)) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) a s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (v : VitaliFamily.{u1} α _inst_1 m0 μ) {x : α} {s : Set.{u1} (Set.{u1} α)}, Iff (Membership.mem.{u1, u1} (Set.{u1} (Set.{u1} α)) (Filter.{u1} (Set.{u1} α)) (instMembershipSetFilter.{u1} (Set.{u1} α)) s (VitaliFamily.filterAt.{u1} α _inst_1 m0 μ v x)) (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (a : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) a (VitaliFamily.setsAt.{u1} α _inst_1 m0 μ v x)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) a (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε)) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) a s))))
Case conversion may be inaccurate. Consider using '#align vitali_family.mem_filter_at_iff VitaliFamily.mem_filterAt_iffₓ'. -/
theorem mem_filterAt_iff {x : α} {s : Set (Set α)} :
    s ∈ v.filterAt x ↔ ∃ ε > (0 : ℝ), ∀ a ∈ v.setsAt x, a ⊆ closedBall x ε → a ∈ s :=
  by
  simp only [filter_at, exists_prop, gt_iff_lt]
  rw [mem_binfi_of_directed]
  · simp only [subset_def, and_imp, exists_prop, mem_sep_iff, mem_Ioi, mem_principal]
  · simp only [DirectedOn, exists_prop, ge_iff_le, le_principal_iff, mem_Ioi, Order.Preimage,
      mem_principal]
    intro x hx y hy
    refine'
      ⟨min x y, lt_min hx hy, fun a ha =>
        ⟨ha.1, ha.2.trans (closed_ball_subset_closed_ball (min_le_left _ _))⟩, fun a ha =>
        ⟨ha.1, ha.2.trans (closed_ball_subset_closed_ball (min_le_right _ _))⟩⟩
  · exact ⟨(1 : ℝ), mem_Ioi.2 zero_lt_one⟩
#align vitali_family.mem_filter_at_iff VitaliFamily.mem_filterAt_iff

#print VitaliFamily.filterAt_neBot /-
instance filterAt_neBot (x : α) : (v.filterAt x).ne_bot :=
  by
  simp only [ne_bot_iff, ← empty_mem_iff_bot, mem_filter_at_iff, not_exists, exists_prop,
    mem_empty_iff_false, and_true_iff, gt_iff_lt, not_and, Ne.def, not_false_iff, not_forall]
  intro ε εpos
  obtain ⟨w, w_sets, hw⟩ : ∃ w ∈ v.sets_at x, w ⊆ closed_ball x ε := v.nontrivial x ε εpos
  exact ⟨w, w_sets, hw⟩
#align vitali_family.filter_at_ne_bot VitaliFamily.filterAt_neBot
-/

/- warning: vitali_family.eventually_filter_at_iff -> VitaliFamily.eventually_filterAt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (v : VitaliFamily.{u1} α _inst_1 m0 μ) {x : α} {P : (Set.{u1} α) -> Prop}, Iff (Filter.Eventually.{u1} (Set.{u1} α) (fun (a : Set.{u1} α) => P a) (VitaliFamily.filterAt.{u1} α _inst_1 m0 μ v x)) (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (a : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) a (VitaliFamily.setsAt.{u1} α _inst_1 m0 μ v x)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) a (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε)) -> (P a))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (v : VitaliFamily.{u1} α _inst_1 m0 μ) {x : α} {P : (Set.{u1} α) -> Prop}, Iff (Filter.Eventually.{u1} (Set.{u1} α) (fun (a : Set.{u1} α) => P a) (VitaliFamily.filterAt.{u1} α _inst_1 m0 μ v x)) (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (a : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) a (VitaliFamily.setsAt.{u1} α _inst_1 m0 μ v x)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) a (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε)) -> (P a))))
Case conversion may be inaccurate. Consider using '#align vitali_family.eventually_filter_at_iff VitaliFamily.eventually_filterAt_iffₓ'. -/
theorem eventually_filterAt_iff {x : α} {P : Set α → Prop} :
    (∀ᶠ a in v.filterAt x, P a) ↔ ∃ ε > (0 : ℝ), ∀ a ∈ v.setsAt x, a ⊆ closedBall x ε → P a :=
  v.mem_filterAt_iff
#align vitali_family.eventually_filter_at_iff VitaliFamily.eventually_filterAt_iff

#print VitaliFamily.eventually_filterAt_mem_sets /-
theorem eventually_filterAt_mem_sets (x : α) : ∀ᶠ a in v.filterAt x, a ∈ v.setsAt x :=
  by
  simp (config := { contextual := true }) only [eventually_filter_at_iff, exists_prop, and_true_iff,
    gt_iff_lt, imp_true_iff]
  exact ⟨1, zero_lt_one⟩
#align vitali_family.eventually_filter_at_mem_sets VitaliFamily.eventually_filterAt_mem_sets
-/

/- warning: vitali_family.eventually_filter_at_subset_closed_ball -> VitaliFamily.eventually_filterAt_subset_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (v : VitaliFamily.{u1} α _inst_1 m0 μ) (x : α) {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Filter.Eventually.{u1} (Set.{u1} α) (fun (a : Set.{u1} α) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) a (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε)) (VitaliFamily.filterAt.{u1} α _inst_1 m0 μ v x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (v : VitaliFamily.{u1} α _inst_1 m0 μ) (x : α) {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Filter.Eventually.{u1} (Set.{u1} α) (fun (a : Set.{u1} α) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) a (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε)) (VitaliFamily.filterAt.{u1} α _inst_1 m0 μ v x))
Case conversion may be inaccurate. Consider using '#align vitali_family.eventually_filter_at_subset_closed_ball VitaliFamily.eventually_filterAt_subset_closedBallₓ'. -/
theorem eventually_filterAt_subset_closedBall (x : α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : Set α in v.filterAt x, a ⊆ closedBall x ε :=
  by
  simp only [v.eventually_filter_at_iff]
  exact ⟨ε, hε, fun a ha ha' => ha'⟩
#align vitali_family.eventually_filter_at_subset_closed_ball VitaliFamily.eventually_filterAt_subset_closedBall

/- warning: vitali_family.tendsto_filter_at_iff -> VitaliFamily.tendsto_filterAt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (v : VitaliFamily.{u1} α _inst_1 m0 μ) {ι : Type.{u2}} {l : Filter.{u2} ι} {f : ι -> (Set.{u1} α)} {x : α}, Iff (Filter.Tendsto.{u2, u1} ι (Set.{u1} α) f l (VitaliFamily.filterAt.{u1} α _inst_1 m0 μ v x)) (And (Filter.Eventually.{u2} ι (fun (i : ι) => Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (f i) (VitaliFamily.setsAt.{u1} α _inst_1 m0 μ v x)) l) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Eventually.{u2} ι (fun (i : ι) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (f i) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε)) l)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (v : VitaliFamily.{u1} α _inst_1 m0 μ) {ι : Type.{u2}} {l : Filter.{u2} ι} {f : ι -> (Set.{u1} α)} {x : α}, Iff (Filter.Tendsto.{u2, u1} ι (Set.{u1} α) f l (VitaliFamily.filterAt.{u1} α _inst_1 m0 μ v x)) (And (Filter.Eventually.{u2} ι (fun (i : ι) => Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (f i) (VitaliFamily.setsAt.{u1} α _inst_1 m0 μ v x)) l) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Eventually.{u2} ι (fun (i : ι) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (f i) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε)) l)))
Case conversion may be inaccurate. Consider using '#align vitali_family.tendsto_filter_at_iff VitaliFamily.tendsto_filterAt_iffₓ'. -/
theorem tendsto_filterAt_iff {ι : Type _} {l : Filter ι} {f : ι → Set α} {x : α} :
    Tendsto f l (v.filterAt x) ↔
      (∀ᶠ i in l, f i ∈ v.setsAt x) ∧ ∀ ε > (0 : ℝ), ∀ᶠ i in l, f i ⊆ closedBall x ε :=
  by
  refine'
    ⟨fun H =>
      ⟨H.Eventually <| v.eventually_filter_at_mem_sets x, fun ε hε =>
        H.Eventually <| v.eventually_filter_at_subset_closed_ball x hε⟩,
      fun H s hs => (_ : ∀ᶠ i in l, f i ∈ s)⟩
  obtain ⟨ε, εpos, hε⟩ := v.mem_filter_at_iff.mp hs
  filter_upwards [H.1, H.2 ε εpos]with i hi hiε using hε _ hi hiε
#align vitali_family.tendsto_filter_at_iff VitaliFamily.tendsto_filterAt_iff

#print VitaliFamily.eventually_filterAt_measurableSet /-
theorem eventually_filterAt_measurableSet (x : α) : ∀ᶠ a in v.filterAt x, MeasurableSet a := by
  filter_upwards [v.eventually_filter_at_mem_sets x]with _ ha using v.measurable_set' _ _ ha
#align vitali_family.eventually_filter_at_measurable_set VitaliFamily.eventually_filterAt_measurableSet
-/

/- warning: vitali_family.frequently_filter_at_iff -> VitaliFamily.frequently_filterAt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (v : VitaliFamily.{u1} α _inst_1 m0 μ) {x : α} {P : (Set.{u1} α) -> Prop}, Iff (Filter.Frequently.{u1} (Set.{u1} α) (fun (a : Set.{u1} α) => P a) (VitaliFamily.filterAt.{u1} α _inst_1 m0 μ v x)) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (a : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) a (VitaliFamily.setsAt.{u1} α _inst_1 m0 μ v x)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) a (VitaliFamily.setsAt.{u1} α _inst_1 m0 μ v x)) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) a (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε)) (P a)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (v : VitaliFamily.{u1} α _inst_1 m0 μ) {x : α} {P : (Set.{u1} α) -> Prop}, Iff (Filter.Frequently.{u1} (Set.{u1} α) (fun (a : Set.{u1} α) => P a) (VitaliFamily.filterAt.{u1} α _inst_1 m0 μ v x)) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u1} (Set.{u1} α) (fun (a : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) a (VitaliFamily.setsAt.{u1} α _inst_1 m0 μ v x)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) a (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x ε)) (P a)))))
Case conversion may be inaccurate. Consider using '#align vitali_family.frequently_filter_at_iff VitaliFamily.frequently_filterAt_iffₓ'. -/
theorem frequently_filterAt_iff {x : α} {P : Set α → Prop} :
    (∃ᶠ a in v.filterAt x, P a) ↔ ∀ ε > (0 : ℝ), ∃ a ∈ v.setsAt x, a ⊆ closedBall x ε ∧ P a := by
  simp only [Filter.Frequently, eventually_filter_at_iff, not_exists, exists_prop, not_and,
    Classical.not_not, not_forall]
#align vitali_family.frequently_filter_at_iff VitaliFamily.frequently_filterAt_iff

#print VitaliFamily.eventually_filterAt_subset_of_nhds /-
theorem eventually_filterAt_subset_of_nhds {x : α} {o : Set α} (hx : o ∈ 𝓝 x) :
    ∀ᶠ a in v.filterAt x, a ⊆ o := by
  rw [eventually_filter_at_iff]
  rcases Metric.mem_nhds_iff.1 hx with ⟨ε, εpos, hε⟩
  exact
    ⟨ε / 2, half_pos εpos, fun a av ha =>
      ha.trans ((closed_ball_subset_ball (half_lt_self εpos)).trans hε)⟩
#align vitali_family.eventually_filter_at_subset_of_nhds VitaliFamily.eventually_filterAt_subset_of_nhds
-/

#print VitaliFamily.fineSubfamilyOn_of_frequently /-
theorem fineSubfamilyOn_of_frequently (v : VitaliFamily μ) (f : α → Set (Set α)) (s : Set α)
    (h : ∀ x ∈ s, ∃ᶠ a in v.filterAt x, a ∈ f x) : v.FineSubfamilyOn f s :=
  by
  intro x hx ε εpos
  obtain ⟨a, av, ha, af⟩ : ∃ (a : Set α)(H : a ∈ v.sets_at x), a ⊆ closed_ball x ε ∧ a ∈ f x :=
    v.frequently_filter_at_iff.1 (h x hx) ε εpos
  exact ⟨a, ⟨av, af⟩, ha⟩
#align vitali_family.fine_subfamily_on_of_frequently VitaliFamily.fineSubfamilyOn_of_frequently
-/

end VitaliFamily

