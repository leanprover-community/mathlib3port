/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.metric_space.hausdorff_distance
! leanprover-community/mathlib commit bc91ed7093bf098d253401e69df601fc33dde156
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecificLimits.Basic
import Mathbin.Topology.MetricSpace.IsometricSmul
import Mathbin.Topology.MetricSpace.Isometry
import Mathbin.Topology.Instances.Ennreal

/-!
# Hausdorff distance

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Hausdorff distance on subsets of a metric (or emetric) space.

Given two subsets `s` and `t` of a metric space, their Hausdorff distance is the smallest `d`
such that any point `s` is within `d` of a point in `t`, and conversely. This quantity
is often infinite (think of `s` bounded and `t` unbounded), and therefore better
expressed in the setting of emetric spaces.

## Main definitions

This files introduces:
* `inf_edist x s`, the infimum edistance of a point `x` to a set `s` in an emetric space
* `Hausdorff_edist s t`, the Hausdorff edistance of two sets in an emetric space
* Versions of these notions on metric spaces, called respectively `inf_dist` and `Hausdorff_dist`
* `thickening δ s`, the open thickening by radius `δ` of a set `s` in a pseudo emetric space.
* `cthickening δ s`, the closed thickening by radius `δ` of a set `s` in a pseudo emetric space.
-/


noncomputable section

open Classical NNReal ENNReal Topology Pointwise

universe u v w

open Classical Set Function TopologicalSpace Filter

variable {ι : Sort _} {α : Type u} {β : Type v}

namespace Emetric

section InfEdist

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x y : α} {s t : Set α} {Φ : α → β}

/-! ### Distance of a point to a set as a function into `ℝ≥0∞`. -/


#print EMetric.infEdist /-
/-- The minimal edistance of a point to a set -/
def infEdist (x : α) (s : Set α) : ℝ≥0∞ :=
  ⨅ y ∈ s, edist x y
#align emetric.inf_edist EMetric.infEdist
-/

/- warning: emetric.inf_edist_empty -> EMetric.infEdist_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, Eq.{1} ENNReal (EMetric.infEdist.{u1} α _inst_1 x (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, Eq.{1} ENNReal (EMetric.infEdist.{u1} α _inst_1 x (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align emetric.inf_edist_empty EMetric.infEdist_emptyₓ'. -/
@[simp]
theorem infEdist_empty : infEdist x ∅ = ∞ :=
  iInf_emptyset
#align emetric.inf_edist_empty EMetric.infEdist_empty

/- warning: emetric.le_inf_edist -> EMetric.le_infEdist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {d : ENNReal}, Iff (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) d (EMetric.infEdist.{u1} α _inst_1 x s)) (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) d (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {d : ENNReal}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) d (EMetric.infEdist.{u1} α _inst_1 x s)) (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) d (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y)))
Case conversion may be inaccurate. Consider using '#align emetric.le_inf_edist EMetric.le_infEdistₓ'. -/
theorem le_infEdist {d} : d ≤ infEdist x s ↔ ∀ y ∈ s, d ≤ edist x y := by
  simp only [inf_edist, le_iInf_iff]
#align emetric.le_inf_edist EMetric.le_infEdist

#print EMetric.infEdist_union /-
/-- The edist to a union is the minimum of the edists -/
@[simp]
theorem infEdist_union : infEdist x (s ∪ t) = infEdist x s ⊓ infEdist x t :=
  iInf_union
#align emetric.inf_edist_union EMetric.infEdist_union
-/

/- warning: emetric.inf_edist_Union -> EMetric.infEdist_iUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u2}} {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (f : ι -> (Set.{u1} α)) (x : α), Eq.{1} ENNReal (EMetric.infEdist.{u1} α _inst_1 x (Set.iUnion.{u1, u2} α ι (fun (i : ι) => f i))) (iInf.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => EMetric.infEdist.{u1} α _inst_1 x (f i)))
but is expected to have type
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} α] (f : ι -> (Set.{u2} α)) (x : α), Eq.{1} ENNReal (EMetric.infEdist.{u2} α _inst_1 x (Set.iUnion.{u2, u1} α ι (fun (i : ι) => f i))) (iInf.{0, u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => EMetric.infEdist.{u2} α _inst_1 x (f i)))
Case conversion may be inaccurate. Consider using '#align emetric.inf_edist_Union EMetric.infEdist_iUnionₓ'. -/
@[simp]
theorem infEdist_iUnion (f : ι → Set α) (x : α) : infEdist x (⋃ i, f i) = ⨅ i, infEdist x (f i) :=
  iInf_iUnion f _
#align emetric.inf_edist_Union EMetric.infEdist_iUnion

#print EMetric.infEdist_singleton /-
/-- The edist to a singleton is the edistance to the single point of this singleton -/
@[simp]
theorem infEdist_singleton : infEdist x {y} = edist x y :=
  iInf_singleton
#align emetric.inf_edist_singleton EMetric.infEdist_singleton
-/

/- warning: emetric.inf_edist_le_edist_of_mem -> EMetric.infEdist_le_edist_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.infEdist.{u1} α _inst_1 x s) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.infEdist.{u1} α _inst_1 x s) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y))
Case conversion may be inaccurate. Consider using '#align emetric.inf_edist_le_edist_of_mem EMetric.infEdist_le_edist_of_memₓ'. -/
/-- The edist to a set is bounded above by the edist to any of its points -/
theorem infEdist_le_edist_of_mem (h : y ∈ s) : infEdist x s ≤ edist x y :=
  iInf₂_le _ h
#align emetric.inf_edist_le_edist_of_mem EMetric.infEdist_le_edist_of_mem

/- warning: emetric.inf_edist_zero_of_mem -> EMetric.infEdist_zero_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{1} ENNReal (EMetric.infEdist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Eq.{1} ENNReal (EMetric.infEdist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align emetric.inf_edist_zero_of_mem EMetric.infEdist_zero_of_memₓ'. -/
/-- If a point `x` belongs to `s`, then its edist to `s` vanishes -/
theorem infEdist_zero_of_mem (h : x ∈ s) : infEdist x s = 0 :=
  nonpos_iff_eq_zero.1 <| @edist_self _ _ x ▸ infEdist_le_edist_of_mem h
#align emetric.inf_edist_zero_of_mem EMetric.infEdist_zero_of_mem

/- warning: emetric.inf_edist_anti -> EMetric.infEdist_anti is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.infEdist.{u1} α _inst_1 x t) (EMetric.infEdist.{u1} α _inst_1 x s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.infEdist.{u1} α _inst_1 x t) (EMetric.infEdist.{u1} α _inst_1 x s))
Case conversion may be inaccurate. Consider using '#align emetric.inf_edist_anti EMetric.infEdist_antiₓ'. -/
/-- The edist is antitone with respect to inclusion. -/
theorem infEdist_anti (h : s ⊆ t) : infEdist x t ≤ infEdist x s :=
  iInf_le_iInf_of_subset h
#align emetric.inf_edist_anti EMetric.infEdist_anti

/- warning: emetric.inf_edist_lt_iff -> EMetric.infEdist_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {r : ENNReal}, Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.infEdist.{u1} α _inst_1 x s) r) (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) r)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {r : ENNReal}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.infEdist.{u1} α _inst_1 x s) r) (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) r)))
Case conversion may be inaccurate. Consider using '#align emetric.inf_edist_lt_iff EMetric.infEdist_lt_iffₓ'. -/
/-- The edist to a set is `< r` iff there exists a point in the set at edistance `< r` -/
theorem infEdist_lt_iff {r : ℝ≥0∞} : infEdist x s < r ↔ ∃ y ∈ s, edist x y < r := by
  simp_rw [inf_edist, iInf_lt_iff]
#align emetric.inf_edist_lt_iff EMetric.infEdist_lt_iff

/- warning: emetric.inf_edist_le_inf_edist_add_edist -> EMetric.infEdist_le_infEdist_add_edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α}, LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.infEdist.{u1} α _inst_1 x s) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EMetric.infEdist.{u1} α _inst_1 y s) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α}, LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.infEdist.{u1} α _inst_1 x s) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EMetric.infEdist.{u1} α _inst_1 y s) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y))
Case conversion may be inaccurate. Consider using '#align emetric.inf_edist_le_inf_edist_add_edist EMetric.infEdist_le_infEdist_add_edistₓ'. -/
/-- The edist of `x` to `s` is bounded by the sum of the edist of `y` to `s` and
the edist from `x` to `y` -/
theorem infEdist_le_infEdist_add_edist : infEdist x s ≤ infEdist y s + edist x y :=
  calc
    (⨅ z ∈ s, edist x z) ≤ ⨅ z ∈ s, edist y z + edist x y :=
      iInf₂_mono fun z hz => (edist_triangle _ _ _).trans_eq (add_comm _ _)
    _ = (⨅ z ∈ s, edist y z) + edist x y := by simp only [ENNReal.iInf_add]
    
#align emetric.inf_edist_le_inf_edist_add_edist EMetric.infEdist_le_infEdist_add_edist

/- warning: emetric.inf_edist_le_edist_add_inf_edist -> EMetric.infEdist_le_edist_add_infEdist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α}, LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.infEdist.{u1} α _inst_1 x s) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (EMetric.infEdist.{u1} α _inst_1 y s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α}, LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.infEdist.{u1} α _inst_1 x s) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) (EMetric.infEdist.{u1} α _inst_1 y s))
Case conversion may be inaccurate. Consider using '#align emetric.inf_edist_le_edist_add_inf_edist EMetric.infEdist_le_edist_add_infEdistₓ'. -/
theorem infEdist_le_edist_add_infEdist : infEdist x s ≤ edist x y + infEdist y s :=
  by
  rw [add_comm]
  exact inf_edist_le_inf_edist_add_edist
#align emetric.inf_edist_le_edist_add_inf_edist EMetric.infEdist_le_edist_add_infEdist

/- warning: emetric.edist_le_inf_edist_add_ediam -> EMetric.edist_le_infEdist_add_ediam is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EMetric.infEdist.{u1} α _inst_1 x s) (EMetric.diam.{u1} α _inst_1 s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EMetric.infEdist.{u1} α _inst_1 x s) (EMetric.diam.{u1} α _inst_1 s)))
Case conversion may be inaccurate. Consider using '#align emetric.edist_le_inf_edist_add_ediam EMetric.edist_le_infEdist_add_ediamₓ'. -/
theorem edist_le_infEdist_add_ediam (hy : y ∈ s) : edist x y ≤ infEdist x s + diam s :=
  by
  simp_rw [inf_edist, ENNReal.iInf_add]
  refine' le_iInf fun i => le_iInf fun hi => _
  calc
    edist x y ≤ edist x i + edist i y := edist_triangle _ _ _
    _ ≤ edist x i + diam s := add_le_add le_rfl (edist_le_diam_of_mem hi hy)
    
#align emetric.edist_le_inf_edist_add_ediam EMetric.edist_le_infEdist_add_ediam

/- warning: emetric.continuous_inf_edist -> EMetric.continuous_infEdist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, Continuous.{u1, 0} α ENNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) ENNReal.topologicalSpace (fun (x : α) => EMetric.infEdist.{u1} α _inst_1 x s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, Continuous.{u1, 0} α ENNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) ENNReal.instTopologicalSpaceENNReal (fun (x : α) => EMetric.infEdist.{u1} α _inst_1 x s)
Case conversion may be inaccurate. Consider using '#align emetric.continuous_inf_edist EMetric.continuous_infEdistₓ'. -/
/-- The edist to a set depends continuously on the point -/
@[continuity]
theorem continuous_infEdist : Continuous fun x => infEdist x s :=
  continuous_of_le_add_edist 1 (by simp) <| by
    simp only [one_mul, inf_edist_le_inf_edist_add_edist, forall₂_true_iff]
#align emetric.continuous_inf_edist EMetric.continuous_infEdist

#print EMetric.infEdist_closure /-
/-- The edist to a set and to its closure coincide -/
theorem infEdist_closure : infEdist x (closure s) = infEdist x s :=
  by
  refine' le_antisymm (inf_edist_anti subset_closure) _
  refine' ENNReal.le_of_forall_pos_le_add fun ε εpos h => _
  have ε0 : 0 < (ε / 2 : ℝ≥0∞) := by simpa [pos_iff_ne_zero] using εpos
  have : inf_edist x (closure s) < inf_edist x (closure s) + ε / 2 :=
    ENNReal.lt_add_right h.ne ε0.ne'
  rcases inf_edist_lt_iff.mp this with ⟨y, ycs, hy⟩
  -- y : α,  ycs : y ∈ closure s,  hy : edist x y < inf_edist x (closure s) + ↑ε / 2
  rcases EMetric.mem_closure_iff.1 ycs (ε / 2) ε0 with ⟨z, zs, dyz⟩
  -- z : α,  zs : z ∈ s,  dyz : edist y z < ↑ε / 2
  calc
    inf_edist x s ≤ edist x z := inf_edist_le_edist_of_mem zs
    _ ≤ edist x y + edist y z := (edist_triangle _ _ _)
    _ ≤ inf_edist x (closure s) + ε / 2 + ε / 2 := (add_le_add (le_of_lt hy) (le_of_lt dyz))
    _ = inf_edist x (closure s) + ↑ε := by rw [add_assoc, ENNReal.add_halves]
    
#align emetric.inf_edist_closure EMetric.infEdist_closure
-/

/- warning: emetric.mem_closure_iff_inf_edist_zero -> EMetric.mem_closure_iff_infEdist_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (Eq.{1} ENNReal (EMetric.infEdist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (Eq.{1} ENNReal (EMetric.infEdist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align emetric.mem_closure_iff_inf_edist_zero EMetric.mem_closure_iff_infEdist_zeroₓ'. -/
/-- A point belongs to the closure of `s` iff its infimum edistance to this set vanishes -/
theorem mem_closure_iff_infEdist_zero : x ∈ closure s ↔ infEdist x s = 0 :=
  ⟨fun h => by
    rw [← inf_edist_closure]
    exact inf_edist_zero_of_mem h, fun h =>
    EMetric.mem_closure_iff.2 fun ε εpos => infEdist_lt_iff.mp <| by rwa [h]⟩
#align emetric.mem_closure_iff_inf_edist_zero EMetric.mem_closure_iff_infEdist_zero

/- warning: emetric.mem_iff_inf_edist_zero_of_closed -> EMetric.mem_iff_infEdist_zero_of_closed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (Eq.{1} ENNReal (EMetric.infEdist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Eq.{1} ENNReal (EMetric.infEdist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align emetric.mem_iff_inf_edist_zero_of_closed EMetric.mem_iff_infEdist_zero_of_closedₓ'. -/
/-- Given a closed set `s`, a point belongs to `s` iff its infimum edistance to this set vanishes -/
theorem mem_iff_infEdist_zero_of_closed (h : IsClosed s) : x ∈ s ↔ infEdist x s = 0 :=
  by
  convert← mem_closure_iff_inf_edist_zero
  exact h.closure_eq
#align emetric.mem_iff_inf_edist_zero_of_closed EMetric.mem_iff_infEdist_zero_of_closed

/- warning: emetric.inf_edist_pos_iff_not_mem_closure -> EMetric.infEdist_pos_iff_not_mem_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {E : Set.{u1} α}, Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (EMetric.infEdist.{u1} α _inst_1 x E)) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {E : Set.{u1} α}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (EMetric.infEdist.{u1} α _inst_1 x E)) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E)))
Case conversion may be inaccurate. Consider using '#align emetric.inf_edist_pos_iff_not_mem_closure EMetric.infEdist_pos_iff_not_mem_closureₓ'. -/
/-- The infimum edistance of a point to a set is positive if and only if the point is not in the
closure of the set. -/
theorem infEdist_pos_iff_not_mem_closure {x : α} {E : Set α} : 0 < infEdist x E ↔ x ∉ closure E :=
  by rw [mem_closure_iff_inf_edist_zero, pos_iff_ne_zero]
#align emetric.inf_edist_pos_iff_not_mem_closure EMetric.infEdist_pos_iff_not_mem_closure

/- warning: emetric.inf_edist_closure_pos_iff_not_mem_closure -> EMetric.infEdist_closure_pos_iff_not_mem_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {E : Set.{u1} α}, Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (EMetric.infEdist.{u1} α _inst_1 x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E))) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {E : Set.{u1} α}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (EMetric.infEdist.{u1} α _inst_1 x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E))) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E)))
Case conversion may be inaccurate. Consider using '#align emetric.inf_edist_closure_pos_iff_not_mem_closure EMetric.infEdist_closure_pos_iff_not_mem_closureₓ'. -/
theorem infEdist_closure_pos_iff_not_mem_closure {x : α} {E : Set α} :
    0 < infEdist x (closure E) ↔ x ∉ closure E := by
  rw [inf_edist_closure, inf_edist_pos_iff_not_mem_closure]
#align emetric.inf_edist_closure_pos_iff_not_mem_closure EMetric.infEdist_closure_pos_iff_not_mem_closure

/- warning: emetric.exists_real_pos_lt_inf_edist_of_not_mem_closure -> EMetric.exists_real_pos_lt_infEdist_of_not_mem_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {E : Set.{u1} α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E))) -> (Exists.{1} Real (fun (ε : Real) => And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (ENNReal.ofReal ε) (EMetric.infEdist.{u1} α _inst_1 x E))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {E : Set.{u1} α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E))) -> (Exists.{1} Real (fun (ε : Real) => And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (ENNReal.ofReal ε) (EMetric.infEdist.{u1} α _inst_1 x E))))
Case conversion may be inaccurate. Consider using '#align emetric.exists_real_pos_lt_inf_edist_of_not_mem_closure EMetric.exists_real_pos_lt_infEdist_of_not_mem_closureₓ'. -/
theorem exists_real_pos_lt_infEdist_of_not_mem_closure {x : α} {E : Set α} (h : x ∉ closure E) :
    ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε < infEdist x E :=
  by
  rw [← inf_edist_pos_iff_not_mem_closure, ENNReal.lt_iff_exists_real_btwn] at h
  rcases h with ⟨ε, ⟨_, ⟨ε_pos, ε_lt⟩⟩⟩
  exact ⟨ε, ⟨ennreal.of_real_pos.mp ε_pos, ε_lt⟩⟩
#align emetric.exists_real_pos_lt_inf_edist_of_not_mem_closure EMetric.exists_real_pos_lt_infEdist_of_not_mem_closure

/- warning: emetric.disjoint_closed_ball_of_lt_inf_edist -> EMetric.disjoint_closedBall_of_lt_infEdist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {r : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) r (EMetric.infEdist.{u1} α _inst_1 x s)) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (EMetric.closedBall.{u1} α _inst_1 x r) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {r : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) r (EMetric.infEdist.{u1} α _inst_1 x s)) -> (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (EMetric.closedBall.{u1} α _inst_1 x r) s)
Case conversion may be inaccurate. Consider using '#align emetric.disjoint_closed_ball_of_lt_inf_edist EMetric.disjoint_closedBall_of_lt_infEdistₓ'. -/
theorem disjoint_closedBall_of_lt_infEdist {r : ℝ≥0∞} (h : r < infEdist x s) :
    Disjoint (closedBall x r) s := by
  rw [disjoint_left]
  intro y hy h'y
  apply lt_irrefl (inf_edist x s)
  calc
    inf_edist x s ≤ edist x y := inf_edist_le_edist_of_mem h'y
    _ ≤ r := by rwa [mem_closed_ball, edist_comm] at hy
    _ < inf_edist x s := h
    
#align emetric.disjoint_closed_ball_of_lt_inf_edist EMetric.disjoint_closedBall_of_lt_infEdist

#print EMetric.infEdist_image /-
/-- The infimum edistance is invariant under isometries -/
theorem infEdist_image (hΦ : Isometry Φ) : infEdist (Φ x) (Φ '' t) = infEdist x t := by
  simp only [inf_edist, iInf_image, hΦ.edist_eq]
#align emetric.inf_edist_image EMetric.infEdist_image
-/

/- warning: emetric.inf_edist_smul -> EMetric.infEdist_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {M : Type.{u2}} [_inst_3 : SMul.{u2, u1} M α] [_inst_4 : IsometricSMul.{u2, u1} M α _inst_1 _inst_3] (c : M) (x : α) (s : Set.{u1} α), Eq.{1} ENNReal (EMetric.infEdist.{u1} α _inst_1 (SMul.smul.{u2, u1} M α _inst_3 c x) (SMul.smul.{u2, u1} M (Set.{u1} α) (Set.smulSet.{u2, u1} M α _inst_3) c s)) (EMetric.infEdist.{u1} α _inst_1 x s)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} α] {M : Type.{u1}} [_inst_3 : SMul.{u1, u2} M α] [_inst_4 : IsometricSMul.{u1, u2} M α _inst_1 _inst_3] (c : M) (x : α) (s : Set.{u2} α), Eq.{1} ENNReal (EMetric.infEdist.{u2} α _inst_1 (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α _inst_3) c x) (HSMul.hSMul.{u1, u2, u2} M (Set.{u2} α) (Set.{u2} α) (instHSMul.{u1, u2} M (Set.{u2} α) (Set.smulSet.{u1, u2} M α _inst_3)) c s)) (EMetric.infEdist.{u2} α _inst_1 x s)
Case conversion may be inaccurate. Consider using '#align emetric.inf_edist_smul EMetric.infEdist_smulₓ'. -/
@[simp, to_additive]
theorem infEdist_smul {M} [SMul M α] [IsometricSMul M α] (c : M) (x : α) (s : Set α) :
    infEdist (c • x) (c • s) = infEdist x s :=
  infEdist_image (isometry_smul _ _)
#align emetric.inf_edist_smul EMetric.infEdist_smul
#align emetric.inf_edist_vadd EMetric.infEdist_vadd

/- warning: is_open.exists_Union_is_closed -> IsOpen.exists_iUnion_isClosed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {U : Set.{u1} α}, (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) U) -> (Exists.{succ u1} (Nat -> (Set.{u1} α)) (fun (F : Nat -> (Set.{u1} α)) => And (forall (n : Nat), IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (F n)) (And (forall (n : Nat), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (F n) U) (And (Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => F n)) U) (Monotone.{0, u1} Nat (Set.{u1} α) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) F)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {U : Set.{u1} α}, (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) U) -> (Exists.{succ u1} (Nat -> (Set.{u1} α)) (fun (F : Nat -> (Set.{u1} α)) => And (forall (n : Nat), IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (F n)) (And (forall (n : Nat), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (F n) U) (And (Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => F n)) U) (Monotone.{0, u1} Nat (Set.{u1} α) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) F)))))
Case conversion may be inaccurate. Consider using '#align is_open.exists_Union_is_closed IsOpen.exists_iUnion_isClosedₓ'. -/
theorem IsOpen.exists_iUnion_isClosed {U : Set α} (hU : IsOpen U) :
    ∃ F : ℕ → Set α, (∀ n, IsClosed (F n)) ∧ (∀ n, F n ⊆ U) ∧ (⋃ n, F n) = U ∧ Monotone F :=
  by
  obtain ⟨a, a_pos, a_lt_one⟩ : ∃ a : ℝ≥0∞, 0 < a ∧ a < 1 := exists_between zero_lt_one
  let F := fun n : ℕ => (fun x => inf_edist x (Uᶜ)) ⁻¹' Ici (a ^ n)
  have F_subset : ∀ n, F n ⊆ U := by
    intro n x hx
    have : inf_edist x (Uᶜ) ≠ 0 := ((ENNReal.pow_pos a_pos _).trans_le hx).ne'
    contrapose! this
    exact inf_edist_zero_of_mem this
  refine' ⟨F, fun n => IsClosed.preimage continuous_inf_edist isClosed_Ici, F_subset, _, _⟩
  show Monotone F
  · intro m n hmn x hx
    simp only [mem_Ici, mem_preimage] at hx⊢
    apply le_trans (pow_le_pow_of_le_one' a_lt_one.le hmn) hx
  show (⋃ n, F n) = U
  · refine' subset.antisymm (by simp only [Union_subset_iff, F_subset, forall_const]) fun x hx => _
    have : ¬x ∈ Uᶜ := by simpa using hx
    rw [mem_iff_inf_edist_zero_of_closed hU.is_closed_compl] at this
    have B : 0 < inf_edist x (Uᶜ) := by simpa [pos_iff_ne_zero] using this
    have : Filter.Tendsto (fun n => a ^ n) at_top (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_0_of_lt_1 a_lt_one
    rcases((tendsto_order.1 this).2 _ B).exists with ⟨n, hn⟩
    simp only [mem_Union, mem_Ici, mem_preimage]
    exact ⟨n, hn.le⟩
#align is_open.exists_Union_is_closed IsOpen.exists_iUnion_isClosed

/- warning: is_compact.exists_inf_edist_eq_edist -> IsCompact.exists_infEdist_eq_edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Set.Nonempty.{u1} α s) -> (forall (x : α), Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => Eq.{1} ENNReal (EMetric.infEdist.{u1} α _inst_1 x s) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Set.Nonempty.{u1} α s) -> (forall (x : α), Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (Eq.{1} ENNReal (EMetric.infEdist.{u1} α _inst_1 x s) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y))))
Case conversion may be inaccurate. Consider using '#align is_compact.exists_inf_edist_eq_edist IsCompact.exists_infEdist_eq_edistₓ'. -/
theorem IsCompact.exists_infEdist_eq_edist (hs : IsCompact s) (hne : s.Nonempty) (x : α) :
    ∃ y ∈ s, infEdist x s = edist x y :=
  by
  have A : Continuous fun y => edist x y := continuous_const.edist continuous_id
  obtain ⟨y, ys, hy⟩ : ∃ y ∈ s, ∀ z, z ∈ s → edist x y ≤ edist x z :=
    hs.exists_forall_le hne A.continuous_on
  exact ⟨y, ys, le_antisymm (inf_edist_le_edist_of_mem ys) (by rwa [le_inf_edist])⟩
#align is_compact.exists_inf_edist_eq_edist IsCompact.exists_infEdist_eq_edist

/- warning: emetric.exists_pos_forall_lt_edist -> EMetric.exists_pos_forall_lt_edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Exists.{1} NNReal (fun (r : NNReal) => And (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) r) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) r) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t) -> (Exists.{1} NNReal (fun (r : NNReal) => And (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) r) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (ENNReal.some r) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y))))))
Case conversion may be inaccurate. Consider using '#align emetric.exists_pos_forall_lt_edist EMetric.exists_pos_forall_lt_edistₓ'. -/
theorem exists_pos_forall_lt_edist (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ x ∈ s, ∀ y ∈ t, (r : ℝ≥0∞) < edist x y :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · use 1
    simp
  obtain ⟨x, hx, h⟩ : ∃ x ∈ s, ∀ y ∈ s, inf_edist x t ≤ inf_edist y t :=
    hs.exists_forall_le hne continuous_inf_edist.continuous_on
  have : 0 < inf_edist x t :=
    pos_iff_ne_zero.2 fun H => hst.le_bot ⟨hx, (mem_iff_inf_edist_zero_of_closed ht).mpr H⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 this with ⟨r, h₀, hr⟩
  exact ⟨r, ennreal.coe_pos.mp h₀, fun y hy z hz => hr.trans_le <| le_inf_edist.1 (h y hy) z hz⟩
#align emetric.exists_pos_forall_lt_edist EMetric.exists_pos_forall_lt_edist

end InfEdist

/-! ### The Hausdorff distance as a function into `ℝ≥0∞`. -/


#print EMetric.hausdorffEdist /-
--section
/-- The Hausdorff edistance between two sets is the smallest `r` such that each set
is contained in the `r`-neighborhood of the other one -/
irreducible_def hausdorffEdist {α : Type u} [PseudoEMetricSpace α] (s t : Set α) : ℝ≥0∞ :=
  (⨆ x ∈ s, infEdist x t) ⊔ ⨆ y ∈ t, infEdist y s
#align emetric.Hausdorff_edist EMetric.hausdorffEdist
-/

/- warning: emetric.Hausdorff_edist_def -> EMetric.hausdorffEdist_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (Sup.sup.{0} ENNReal (SemilatticeSup.toHasSup.{0} ENNReal ENNReal.semilatticeSup) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) α (fun (x : α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => EMetric.infEdist.{u1} α _inst_1 x t))) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) α (fun (y : α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => EMetric.infEdist.{u1} α _inst_1 y s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (Sup.sup.{0} ENNReal (SemilatticeSup.toSup.{0} ENNReal instENNRealSemilatticeSup) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) α (fun (x : α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) => EMetric.infEdist.{u1} α _inst_1 x t))) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) α (fun (y : α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) => EMetric.infEdist.{u1} α _inst_1 y s))))
Case conversion may be inaccurate. Consider using '#align emetric.Hausdorff_edist_def EMetric.hausdorffEdist_defₓ'. -/
theorem hausdorffEdist_def {α : Type u} [PseudoEMetricSpace α] (s t : Set α) :
    hausdorffEdist s t = (⨆ x ∈ s, infEdist x t) ⊔ ⨆ y ∈ t, infEdist y s := by rw [Hausdorff_edist]
#align emetric.Hausdorff_edist_def EMetric.hausdorffEdist_def

section HausdorffEdist

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x y : α} {s t u : Set α} {Φ : α → β}

/- warning: emetric.Hausdorff_edist_self -> EMetric.hausdorffEdist_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, Eq.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, Eq.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align emetric.Hausdorff_edist_self EMetric.hausdorffEdist_selfₓ'. -/
/-- The Hausdorff edistance of a set to itself vanishes -/
@[simp]
theorem hausdorffEdist_self : hausdorffEdist s s = 0 :=
  by
  simp only [Hausdorff_edist_def, sup_idem, ENNReal.iSup_eq_zero]
  exact fun x hx => inf_edist_zero_of_mem hx
#align emetric.Hausdorff_edist_self EMetric.hausdorffEdist_self

#print EMetric.hausdorffEdist_comm /-
/-- The Haudorff edistances of `s` to `t` and of `t` to `s` coincide -/
theorem hausdorffEdist_comm : hausdorffEdist s t = hausdorffEdist t s := by
  unfold Hausdorff_edist <;> apply sup_comm
#align emetric.Hausdorff_edist_comm EMetric.hausdorffEdist_comm
-/

/- warning: emetric.Hausdorff_edist_le_of_inf_edist -> EMetric.hausdorffEdist_le_of_infEdist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {r : ENNReal}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.infEdist.{u1} α _inst_1 x t) r)) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.infEdist.{u1} α _inst_1 x s) r)) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.hausdorffEdist.{u1} α _inst_1 s t) r)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {r : ENNReal}, (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.infEdist.{u1} α _inst_1 x t) r)) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.infEdist.{u1} α _inst_1 x s) r)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.hausdorffEdist.{u1} α _inst_1 s t) r)
Case conversion may be inaccurate. Consider using '#align emetric.Hausdorff_edist_le_of_inf_edist EMetric.hausdorffEdist_le_of_infEdistₓ'. -/
/-- Bounding the Hausdorff edistance by bounding the edistance of any point
in each set to the other set -/
theorem hausdorffEdist_le_of_infEdist {r : ℝ≥0∞} (H1 : ∀ x ∈ s, infEdist x t ≤ r)
    (H2 : ∀ x ∈ t, infEdist x s ≤ r) : hausdorffEdist s t ≤ r :=
  by
  simp only [Hausdorff_edist, sup_le_iff, iSup_le_iff]
  exact ⟨H1, H2⟩
#align emetric.Hausdorff_edist_le_of_inf_edist EMetric.hausdorffEdist_le_of_infEdist

/- warning: emetric.Hausdorff_edist_le_of_mem_edist -> EMetric.hausdorffEdist_le_of_mem_edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {r : ENNReal}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) r)))) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) r)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.hausdorffEdist.{u1} α _inst_1 s t) r)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {r : ENNReal}, (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) r)))) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) r)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.hausdorffEdist.{u1} α _inst_1 s t) r)
Case conversion may be inaccurate. Consider using '#align emetric.Hausdorff_edist_le_of_mem_edist EMetric.hausdorffEdist_le_of_mem_edistₓ'. -/
/-- Bounding the Hausdorff edistance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
theorem hausdorffEdist_le_of_mem_edist {r : ℝ≥0∞} (H1 : ∀ x ∈ s, ∃ y ∈ t, edist x y ≤ r)
    (H2 : ∀ x ∈ t, ∃ y ∈ s, edist x y ≤ r) : hausdorffEdist s t ≤ r :=
  by
  refine' Hausdorff_edist_le_of_inf_edist _ _
  · intro x xs
    rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_trans (inf_edist_le_edist_of_mem yt) hy
  · intro x xt
    rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_trans (inf_edist_le_edist_of_mem ys) hy
#align emetric.Hausdorff_edist_le_of_mem_edist EMetric.hausdorffEdist_le_of_mem_edist

/- warning: emetric.inf_edist_le_Hausdorff_edist_of_mem -> EMetric.infEdist_le_hausdorffEdist_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.infEdist.{u1} α _inst_1 x t) (EMetric.hausdorffEdist.{u1} α _inst_1 s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.infEdist.{u1} α _inst_1 x t) (EMetric.hausdorffEdist.{u1} α _inst_1 s t))
Case conversion may be inaccurate. Consider using '#align emetric.inf_edist_le_Hausdorff_edist_of_mem EMetric.infEdist_le_hausdorffEdist_of_memₓ'. -/
/-- The distance to a set is controlled by the Hausdorff distance -/
theorem infEdist_le_hausdorffEdist_of_mem (h : x ∈ s) : infEdist x t ≤ hausdorffEdist s t :=
  by
  rw [Hausdorff_edist_def]
  refine' le_trans _ le_sup_left
  exact le_iSup₂ x h
#align emetric.inf_edist_le_Hausdorff_edist_of_mem EMetric.infEdist_le_hausdorffEdist_of_mem

/- warning: emetric.exists_edist_lt_of_Hausdorff_edist_lt -> EMetric.exists_edist_lt_of_hausdorffEdist_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α} {r : ENNReal}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.hausdorffEdist.{u1} α _inst_1 s t) r) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) r)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α} {r : ENNReal}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.hausdorffEdist.{u1} α _inst_1 s t) r) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) r)))
Case conversion may be inaccurate. Consider using '#align emetric.exists_edist_lt_of_Hausdorff_edist_lt EMetric.exists_edist_lt_of_hausdorffEdist_ltₓ'. -/
/-- If the Hausdorff distance is `<r`, then any point in one of the sets has
a corresponding point at distance `<r` in the other set -/
theorem exists_edist_lt_of_hausdorffEdist_lt {r : ℝ≥0∞} (h : x ∈ s) (H : hausdorffEdist s t < r) :
    ∃ y ∈ t, edist x y < r :=
  infEdist_lt_iff.mp <|
    calc
      infEdist x t ≤ hausdorffEdist s t := infEdist_le_hausdorffEdist_of_mem h
      _ < r := H
      
#align emetric.exists_edist_lt_of_Hausdorff_edist_lt EMetric.exists_edist_lt_of_hausdorffEdist_lt

/- warning: emetric.inf_edist_le_inf_edist_add_Hausdorff_edist -> EMetric.infEdist_le_infEdist_add_hausdorffEdist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.infEdist.{u1} α _inst_1 x t) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EMetric.infEdist.{u1} α _inst_1 x s) (EMetric.hausdorffEdist.{u1} α _inst_1 s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.infEdist.{u1} α _inst_1 x t) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EMetric.infEdist.{u1} α _inst_1 x s) (EMetric.hausdorffEdist.{u1} α _inst_1 s t))
Case conversion may be inaccurate. Consider using '#align emetric.inf_edist_le_inf_edist_add_Hausdorff_edist EMetric.infEdist_le_infEdist_add_hausdorffEdistₓ'. -/
/-- The distance from `x` to `s` or `t` is controlled in terms of the Hausdorff distance
between `s` and `t` -/
theorem infEdist_le_infEdist_add_hausdorffEdist :
    infEdist x t ≤ infEdist x s + hausdorffEdist s t :=
  ENNReal.le_of_forall_pos_le_add fun ε εpos h =>
    by
    have ε0 : (ε / 2 : ℝ≥0∞) ≠ 0 := by simpa [pos_iff_ne_zero] using εpos
    have : inf_edist x s < inf_edist x s + ε / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 h).1.Ne ε0
    rcases inf_edist_lt_iff.mp this with ⟨y, ys, dxy⟩
    -- y : α,  ys : y ∈ s,  dxy : edist x y < inf_edist x s + ↑ε / 2
    have : Hausdorff_edist s t < Hausdorff_edist s t + ε / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 h).2.Ne ε0
    rcases exists_edist_lt_of_Hausdorff_edist_lt ys this with ⟨z, zt, dyz⟩
    -- z : α,  zt : z ∈ t,  dyz : edist y z < Hausdorff_edist s t + ↑ε / 2
    calc
      inf_edist x t ≤ edist x z := inf_edist_le_edist_of_mem zt
      _ ≤ edist x y + edist y z := (edist_triangle _ _ _)
      _ ≤ inf_edist x s + ε / 2 + (Hausdorff_edist s t + ε / 2) := (add_le_add dxy.le dyz.le)
      _ = inf_edist x s + Hausdorff_edist s t + ε := by
        simp [ENNReal.add_halves, add_comm, add_left_comm]
      
#align emetric.inf_edist_le_inf_edist_add_Hausdorff_edist EMetric.infEdist_le_infEdist_add_hausdorffEdist

#print EMetric.hausdorffEdist_image /-
/-- The Hausdorff edistance is invariant under eisometries -/
theorem hausdorffEdist_image (h : Isometry Φ) :
    hausdorffEdist (Φ '' s) (Φ '' t) = hausdorffEdist s t := by
  simp only [Hausdorff_edist_def, iSup_image, inf_edist_image h]
#align emetric.Hausdorff_edist_image EMetric.hausdorffEdist_image
-/

/- warning: emetric.Hausdorff_edist_le_ediam -> EMetric.hausdorffEdist_le_ediam is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u1} α t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (EMetric.diam.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u1} α t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (EMetric.diam.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align emetric.Hausdorff_edist_le_ediam EMetric.hausdorffEdist_le_ediamₓ'. -/
/-- The Hausdorff distance is controlled by the diameter of the union -/
theorem hausdorffEdist_le_ediam (hs : s.Nonempty) (ht : t.Nonempty) :
    hausdorffEdist s t ≤ diam (s ∪ t) :=
  by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine' Hausdorff_edist_le_of_mem_edist _ _
  · intro z hz
    exact ⟨y, yt, edist_le_diam_of_mem (subset_union_left _ _ hz) (subset_union_right _ _ yt)⟩
  · intro z hz
    exact ⟨x, xs, edist_le_diam_of_mem (subset_union_right _ _ hz) (subset_union_left _ _ xs)⟩
#align emetric.Hausdorff_edist_le_ediam EMetric.hausdorffEdist_le_ediam

/- warning: emetric.Hausdorff_edist_triangle -> EMetric.hausdorffEdist_triangle is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.hausdorffEdist.{u1} α _inst_1 s u) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (EMetric.hausdorffEdist.{u1} α _inst_1 t u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.hausdorffEdist.{u1} α _inst_1 s u) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (EMetric.hausdorffEdist.{u1} α _inst_1 t u))
Case conversion may be inaccurate. Consider using '#align emetric.Hausdorff_edist_triangle EMetric.hausdorffEdist_triangleₓ'. -/
/-- The Hausdorff distance satisfies the triangular inequality -/
theorem hausdorffEdist_triangle : hausdorffEdist s u ≤ hausdorffEdist s t + hausdorffEdist t u :=
  by
  rw [Hausdorff_edist_def]
  simp only [sup_le_iff, iSup_le_iff]
  constructor
  show ∀ x ∈ s, inf_edist x u ≤ Hausdorff_edist s t + Hausdorff_edist t u;
  exact fun x xs =>
    calc
      inf_edist x u ≤ inf_edist x t + Hausdorff_edist t u :=
        inf_edist_le_inf_edist_add_Hausdorff_edist
      _ ≤ Hausdorff_edist s t + Hausdorff_edist t u :=
        add_le_add_right (inf_edist_le_Hausdorff_edist_of_mem xs) _
      
  show ∀ x ∈ u, inf_edist x s ≤ Hausdorff_edist s t + Hausdorff_edist t u;
  exact fun x xu =>
    calc
      inf_edist x s ≤ inf_edist x t + Hausdorff_edist t s :=
        inf_edist_le_inf_edist_add_Hausdorff_edist
      _ ≤ Hausdorff_edist u t + Hausdorff_edist t s :=
        (add_le_add_right (inf_edist_le_Hausdorff_edist_of_mem xu) _)
      _ = Hausdorff_edist s t + Hausdorff_edist t u := by simp [Hausdorff_edist_comm, add_comm]
      
#align emetric.Hausdorff_edist_triangle EMetric.hausdorffEdist_triangle

/- warning: emetric.Hausdorff_edist_zero_iff_closure_eq_closure -> EMetric.hausdorffEdist_zero_iff_closure_eq_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{succ u1} (Set.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{succ u1} (Set.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t))
Case conversion may be inaccurate. Consider using '#align emetric.Hausdorff_edist_zero_iff_closure_eq_closure EMetric.hausdorffEdist_zero_iff_closure_eq_closureₓ'. -/
/-- Two sets are at zero Hausdorff edistance if and only if they have the same closure -/
theorem hausdorffEdist_zero_iff_closure_eq_closure :
    hausdorffEdist s t = 0 ↔ closure s = closure t :=
  calc
    hausdorffEdist s t = 0 ↔ s ⊆ closure t ∧ t ⊆ closure s := by
      simp only [Hausdorff_edist_def, ENNReal.sup_eq_zero, ENNReal.iSup_eq_zero, ←
        mem_closure_iff_inf_edist_zero, subset_def]
    _ ↔ closure s = closure t :=
      ⟨fun h =>
        Subset.antisymm (closure_minimal h.1 isClosed_closure)
          (closure_minimal h.2 isClosed_closure),
        fun h => ⟨h ▸ subset_closure, h.symm ▸ subset_closure⟩⟩
    
#align emetric.Hausdorff_edist_zero_iff_closure_eq_closure EMetric.hausdorffEdist_zero_iff_closure_eq_closure

/- warning: emetric.Hausdorff_edist_self_closure -> EMetric.hausdorffEdist_self_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, Eq.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, Eq.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align emetric.Hausdorff_edist_self_closure EMetric.hausdorffEdist_self_closureₓ'. -/
/-- The Hausdorff edistance between a set and its closure vanishes -/
@[simp]
theorem hausdorffEdist_self_closure : hausdorffEdist s (closure s) = 0 := by
  rw [Hausdorff_edist_zero_iff_closure_eq_closure, closure_closure]
#align emetric.Hausdorff_edist_self_closure EMetric.hausdorffEdist_self_closure

#print EMetric.hausdorffEdist_closure₁ /-
/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
theorem hausdorffEdist_closure₁ : hausdorffEdist (closure s) t = hausdorffEdist s t :=
  by
  refine' le_antisymm _ _
  ·
    calc
      _ ≤ Hausdorff_edist (closure s) s + Hausdorff_edist s t := Hausdorff_edist_triangle
      _ = Hausdorff_edist s t := by simp [Hausdorff_edist_comm]
      
  ·
    calc
      _ ≤ Hausdorff_edist s (closure s) + Hausdorff_edist (closure s) t := Hausdorff_edist_triangle
      _ = Hausdorff_edist (closure s) t := by simp
      
#align emetric.Hausdorff_edist_closure₁ EMetric.hausdorffEdist_closure₁
-/

#print EMetric.hausdorffEdist_closure₂ /-
/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
theorem hausdorffEdist_closure₂ : hausdorffEdist s (closure t) = hausdorffEdist s t := by
  simp [@Hausdorff_edist_comm _ _ s _]
#align emetric.Hausdorff_edist_closure₂ EMetric.hausdorffEdist_closure₂
-/

#print EMetric.hausdorffEdist_closure /-
/-- The Hausdorff edistance between sets or their closures is the same -/
@[simp]
theorem hausdorffEdist_closure : hausdorffEdist (closure s) (closure t) = hausdorffEdist s t := by
  simp
#align emetric.Hausdorff_edist_closure EMetric.hausdorffEdist_closure
-/

/- warning: emetric.Hausdorff_edist_zero_iff_eq_of_closed -> EMetric.hausdorffEdist_zero_iff_eq_of_closed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (Iff (Eq.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{succ u1} (Set.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (Iff (Eq.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{succ u1} (Set.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align emetric.Hausdorff_edist_zero_iff_eq_of_closed EMetric.hausdorffEdist_zero_iff_eq_of_closedₓ'. -/
/-- Two closed sets are at zero Hausdorff edistance if and only if they coincide -/
theorem hausdorffEdist_zero_iff_eq_of_closed (hs : IsClosed s) (ht : IsClosed t) :
    hausdorffEdist s t = 0 ↔ s = t := by
  rw [Hausdorff_edist_zero_iff_closure_eq_closure, hs.closure_eq, ht.closure_eq]
#align emetric.Hausdorff_edist_zero_iff_eq_of_closed EMetric.hausdorffEdist_zero_iff_eq_of_closed

/- warning: emetric.Hausdorff_edist_empty -> EMetric.hausdorffEdist_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align emetric.Hausdorff_edist_empty EMetric.hausdorffEdist_emptyₓ'. -/
/-- The Haudorff edistance to the empty set is infinite -/
theorem hausdorffEdist_empty (ne : s.Nonempty) : hausdorffEdist s ∅ = ∞ :=
  by
  rcases Ne with ⟨x, xs⟩
  have : inf_edist x ∅ ≤ Hausdorff_edist s ∅ := inf_edist_le_Hausdorff_edist_of_mem xs
  simpa using this
#align emetric.Hausdorff_edist_empty EMetric.hausdorffEdist_empty

/- warning: emetric.nonempty_of_Hausdorff_edist_ne_top -> EMetric.nonempty_of_hausdorffEdist_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Set.Nonempty.{u1} α t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Set.Nonempty.{u1} α t)
Case conversion may be inaccurate. Consider using '#align emetric.nonempty_of_Hausdorff_edist_ne_top EMetric.nonempty_of_hausdorffEdist_ne_topₓ'. -/
/-- If a set is at finite Hausdorff edistance of a nonempty set, it is nonempty -/
theorem nonempty_of_hausdorffEdist_ne_top (hs : s.Nonempty) (fin : hausdorffEdist s t ≠ ⊤) :
    t.Nonempty :=
  t.eq_empty_or_nonempty.elim (fun ht => (Fin <| ht.symm ▸ hausdorffEdist_empty hs).elim) id
#align emetric.nonempty_of_Hausdorff_edist_ne_top EMetric.nonempty_of_hausdorffEdist_ne_top

/- warning: emetric.empty_or_nonempty_of_Hausdorff_edist_ne_top -> EMetric.empty_or_nonempty_of_hausdorffEdist_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Or (And (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{succ u1} (Set.{u1} α) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))) (And (Set.Nonempty.{u1} α s) (Set.Nonempty.{u1} α t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α _inst_1 s t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Or (And (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Eq.{succ u1} (Set.{u1} α) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))) (And (Set.Nonempty.{u1} α s) (Set.Nonempty.{u1} α t)))
Case conversion may be inaccurate. Consider using '#align emetric.empty_or_nonempty_of_Hausdorff_edist_ne_top EMetric.empty_or_nonempty_of_hausdorffEdist_ne_topₓ'. -/
theorem empty_or_nonempty_of_hausdorffEdist_ne_top (fin : hausdorffEdist s t ≠ ⊤) :
    s = ∅ ∧ t = ∅ ∨ s.Nonempty ∧ t.Nonempty :=
  by
  cases' s.eq_empty_or_nonempty with hs hs
  · cases' t.eq_empty_or_nonempty with ht ht
    · exact Or.inl ⟨hs, ht⟩
    · rw [Hausdorff_edist_comm] at fin
      exact Or.inr ⟨nonempty_of_Hausdorff_edist_ne_top ht Fin, ht⟩
  · exact Or.inr ⟨hs, nonempty_of_Hausdorff_edist_ne_top hs Fin⟩
#align emetric.empty_or_nonempty_of_Hausdorff_edist_ne_top EMetric.empty_or_nonempty_of_hausdorffEdist_ne_top

end HausdorffEdist

-- section
end Emetric

/-! Now, we turn to the same notions in metric spaces. To avoid the difficulties related to
`Inf` and `Sup` on `ℝ` (which is only conditionally complete), we use the notions in `ℝ≥0∞`
formulated in terms of the edistance, and coerce them to `ℝ`.
Then their properties follow readily from the corresponding properties in `ℝ≥0∞`,
modulo some tedious rewriting of inequalities from one to the other. -/


--namespace
namespace Metric

section

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {s t u : Set α} {x y : α} {Φ : α → β}

open Emetric

/-! ### Distance of a point to a set as a function into `ℝ`. -/


#print Metric.infDist /-
/-- The minimal distance of a point to a set -/
def infDist (x : α) (s : Set α) : ℝ :=
  ENNReal.toReal (infEdist x s)
#align metric.inf_dist Metric.infDist
-/

/- warning: metric.inf_dist_eq_infi -> Metric.infDist_eq_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (iInf.{0, succ u1} Real Real.hasInf (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (y : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (iInf.{0, succ u1} Real Real.instInfSetReal (Set.Elem.{u1} α s) (fun (y : Set.Elem.{u1} α s) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) y)))
Case conversion may be inaccurate. Consider using '#align metric.inf_dist_eq_infi Metric.infDist_eq_iInfₓ'. -/
theorem infDist_eq_iInf : infDist x s = ⨅ y : s, dist x y :=
  by
  rw [inf_dist, inf_edist, iInf_subtype', ENNReal.toReal_iInf]
  · simp only [dist_edist]
    rfl
  · exact fun _ => edist_ne_top _ _
#align metric.inf_dist_eq_infi Metric.infDist_eq_iInf

/- warning: metric.inf_dist_nonneg -> Metric.infDist_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Metric.infDist.{u1} α _inst_1 x s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Metric.infDist.{u1} α _inst_1 x s)
Case conversion may be inaccurate. Consider using '#align metric.inf_dist_nonneg Metric.infDist_nonnegₓ'. -/
/-- the minimal distance is always nonnegative -/
theorem infDist_nonneg : 0 ≤ infDist x s := by simp [inf_dist]
#align metric.inf_dist_nonneg Metric.infDist_nonneg

/- warning: metric.inf_dist_empty -> Metric.infDist_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align metric.inf_dist_empty Metric.infDist_emptyₓ'. -/
/-- the minimal distance to the empty set is 0 (if you want to have the more reasonable
value ∞ instead, use `inf_edist`, which takes values in ℝ≥0∞) -/
@[simp]
theorem infDist_empty : infDist x ∅ = 0 := by simp [inf_dist]
#align metric.inf_dist_empty Metric.infDist_empty

/- warning: metric.inf_edist_ne_top -> Metric.infEdist_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, (Set.Nonempty.{u1} α s) -> (Ne.{1} ENNReal (EMetric.infEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) x s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, (Set.Nonempty.{u1} α s) -> (Ne.{1} ENNReal (EMetric.infEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) x s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align metric.inf_edist_ne_top Metric.infEdist_ne_topₓ'. -/
/-- In a metric space, the minimal edistance to a nonempty set is finite -/
theorem infEdist_ne_top (h : s.Nonempty) : infEdist x s ≠ ⊤ :=
  by
  rcases h with ⟨y, hy⟩
  apply lt_top_iff_ne_top.1
  calc
    inf_edist x s ≤ edist x y := inf_edist_le_edist_of_mem hy
    _ < ⊤ := lt_top_iff_ne_top.2 (edist_ne_top _ _)
    
#align metric.inf_edist_ne_top Metric.infEdist_ne_top

/- warning: metric.inf_dist_zero_of_mem -> Metric.infDist_zero_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align metric.inf_dist_zero_of_mem Metric.infDist_zero_of_memₓ'. -/
/-- The minimal distance of a point to a set containing it vanishes -/
theorem infDist_zero_of_mem (h : x ∈ s) : infDist x s = 0 := by
  simp [inf_edist_zero_of_mem h, inf_dist]
#align metric.inf_dist_zero_of_mem Metric.infDist_zero_of_mem

#print Metric.infDist_singleton /-
/-- The minimal distance to a singleton is the distance to the unique point in this singleton -/
@[simp]
theorem infDist_singleton : infDist x {y} = dist x y := by simp [inf_dist, inf_edist, dist_edist]
#align metric.inf_dist_singleton Metric.infDist_singleton
-/

/- warning: metric.inf_dist_le_dist_of_mem -> Metric.infDist_le_dist_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} Real Real.hasLe (Metric.infDist.{u1} α _inst_1 x s) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} Real Real.instLEReal (Metric.infDist.{u1} α _inst_1 x s) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y))
Case conversion may be inaccurate. Consider using '#align metric.inf_dist_le_dist_of_mem Metric.infDist_le_dist_of_memₓ'. -/
/-- The minimal distance to a set is bounded by the distance to any point in this set -/
theorem infDist_le_dist_of_mem (h : y ∈ s) : infDist x s ≤ dist x y :=
  by
  rw [dist_edist, inf_dist, ENNReal.toReal_le_toReal (inf_edist_ne_top ⟨_, h⟩) (edist_ne_top _ _)]
  exact inf_edist_le_edist_of_mem h
#align metric.inf_dist_le_dist_of_mem Metric.infDist_le_dist_of_mem

/- warning: metric.inf_dist_le_inf_dist_of_subset -> Metric.infDist_le_infDist_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Set.Nonempty.{u1} α s) -> (LE.le.{0} Real Real.hasLe (Metric.infDist.{u1} α _inst_1 x t) (Metric.infDist.{u1} α _inst_1 x s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (Set.Nonempty.{u1} α s) -> (LE.le.{0} Real Real.instLEReal (Metric.infDist.{u1} α _inst_1 x t) (Metric.infDist.{u1} α _inst_1 x s))
Case conversion may be inaccurate. Consider using '#align metric.inf_dist_le_inf_dist_of_subset Metric.infDist_le_infDist_of_subsetₓ'. -/
/-- The minimal distance is monotonous with respect to inclusion -/
theorem infDist_le_infDist_of_subset (h : s ⊆ t) (hs : s.Nonempty) : infDist x t ≤ infDist x s :=
  by
  have ht : t.nonempty := hs.mono h
  rw [inf_dist, inf_dist, ENNReal.toReal_le_toReal (inf_edist_ne_top ht) (inf_edist_ne_top hs)]
  exact inf_edist_anti h
#align metric.inf_dist_le_inf_dist_of_subset Metric.infDist_le_infDist_of_subset

/- warning: metric.inf_dist_lt_iff -> Metric.infDist_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {r : Real}, (Set.Nonempty.{u1} α s) -> (Iff (LT.lt.{0} Real Real.hasLt (Metric.infDist.{u1} α _inst_1 x s) r) (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) r))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {r : Real}, (Set.Nonempty.{u1} α s) -> (Iff (LT.lt.{0} Real Real.instLTReal (Metric.infDist.{u1} α _inst_1 x s) r) (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) r))))
Case conversion may be inaccurate. Consider using '#align metric.inf_dist_lt_iff Metric.infDist_lt_iffₓ'. -/
/-- The minimal distance to a set is `< r` iff there exists a point in this set at distance `< r` -/
theorem infDist_lt_iff {r : ℝ} (hs : s.Nonempty) : infDist x s < r ↔ ∃ y ∈ s, dist x y < r := by
  simp_rw [inf_dist, ← ENNReal.lt_ofReal_iff_toReal_lt (inf_edist_ne_top hs), inf_edist_lt_iff,
    ENNReal.lt_ofReal_iff_toReal_lt (edist_ne_top _ _), ← dist_edist]
#align metric.inf_dist_lt_iff Metric.infDist_lt_iff

/- warning: metric.inf_dist_le_inf_dist_add_dist -> Metric.infDist_le_infDist_add_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, LE.le.{0} Real Real.hasLe (Metric.infDist.{u1} α _inst_1 x s) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Metric.infDist.{u1} α _inst_1 y s) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, LE.le.{0} Real Real.instLEReal (Metric.infDist.{u1} α _inst_1 x s) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Metric.infDist.{u1} α _inst_1 y s) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y))
Case conversion may be inaccurate. Consider using '#align metric.inf_dist_le_inf_dist_add_dist Metric.infDist_le_infDist_add_distₓ'. -/
/-- The minimal distance from `x` to `s` is bounded by the distance from `y` to `s`, modulo
the distance between `x` and `y` -/
theorem infDist_le_infDist_add_dist : infDist x s ≤ infDist y s + dist x y :=
  by
  cases' s.eq_empty_or_nonempty with hs hs
  · simp [hs, dist_nonneg]
  · rw [inf_dist, inf_dist, dist_edist, ←
      ENNReal.toReal_add (inf_edist_ne_top hs) (edist_ne_top _ _),
      ENNReal.toReal_le_toReal (inf_edist_ne_top hs)]
    · exact inf_edist_le_inf_edist_add_edist
    · simp [ENNReal.add_eq_top, inf_edist_ne_top hs, edist_ne_top]
#align metric.inf_dist_le_inf_dist_add_dist Metric.infDist_le_infDist_add_dist

/- warning: metric.not_mem_of_dist_lt_inf_dist -> Metric.not_mem_of_dist_lt_infDist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (Metric.infDist.{u1} α _inst_1 x s)) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (Metric.infDist.{u1} α _inst_1 x s)) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s))
Case conversion may be inaccurate. Consider using '#align metric.not_mem_of_dist_lt_inf_dist Metric.not_mem_of_dist_lt_infDistₓ'. -/
theorem not_mem_of_dist_lt_infDist (h : dist x y < infDist x s) : y ∉ s := fun hy =>
  h.not_le <| infDist_le_dist_of_mem hy
#align metric.not_mem_of_dist_lt_inf_dist Metric.not_mem_of_dist_lt_infDist

/- warning: metric.disjoint_ball_inf_dist -> Metric.disjoint_ball_infDist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Metric.ball.{u1} α _inst_1 x (Metric.infDist.{u1} α _inst_1 x s)) s
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Metric.ball.{u1} α _inst_1 x (Metric.infDist.{u1} α _inst_1 x s)) s
Case conversion may be inaccurate. Consider using '#align metric.disjoint_ball_inf_dist Metric.disjoint_ball_infDistₓ'. -/
theorem disjoint_ball_infDist : Disjoint (ball x (infDist x s)) s :=
  disjoint_left.2 fun y hy =>
    not_mem_of_dist_lt_infDist <|
      calc
        dist x y = dist y x := dist_comm _ _
        _ < infDist x s := hy
        
#align metric.disjoint_ball_inf_dist Metric.disjoint_ball_infDist

/- warning: metric.ball_inf_dist_subset_compl -> Metric.ball_infDist_subset_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.ball.{u1} α _inst_1 x (Metric.infDist.{u1} α _inst_1 x s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.ball.{u1} α _inst_1 x (Metric.infDist.{u1} α _inst_1 x s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)
Case conversion may be inaccurate. Consider using '#align metric.ball_inf_dist_subset_compl Metric.ball_infDist_subset_complₓ'. -/
theorem ball_infDist_subset_compl : ball x (infDist x s) ⊆ sᶜ :=
  disjoint_ball_infDist.subset_compl_right
#align metric.ball_inf_dist_subset_compl Metric.ball_infDist_subset_compl

#print Metric.ball_infDist_compl_subset /-
theorem ball_infDist_compl_subset : ball x (infDist x (sᶜ)) ⊆ s :=
  ball_infDist_subset_compl.trans (compl_compl s).Subset
#align metric.ball_inf_dist_compl_subset Metric.ball_infDist_compl_subset
-/

/- warning: metric.disjoint_closed_ball_of_lt_inf_dist -> Metric.disjoint_closedBall_of_lt_infDist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {r : Real}, (LT.lt.{0} Real Real.hasLt r (Metric.infDist.{u1} α _inst_1 x s)) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Metric.closedBall.{u1} α _inst_1 x r) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {r : Real}, (LT.lt.{0} Real Real.instLTReal r (Metric.infDist.{u1} α _inst_1 x s)) -> (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Metric.closedBall.{u1} α _inst_1 x r) s)
Case conversion may be inaccurate. Consider using '#align metric.disjoint_closed_ball_of_lt_inf_dist Metric.disjoint_closedBall_of_lt_infDistₓ'. -/
theorem disjoint_closedBall_of_lt_infDist {r : ℝ} (h : r < infDist x s) :
    Disjoint (closedBall x r) s :=
  disjoint_ball_infDist.mono_left <| closedBall_subset_ball h
#align metric.disjoint_closed_ball_of_lt_inf_dist Metric.disjoint_closedBall_of_lt_infDist

/- warning: metric.dist_le_inf_dist_add_diam -> Metric.dist_le_infDist_add_diam is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, (Metric.Bounded.{u1} α _inst_1 s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Metric.infDist.{u1} α _inst_1 x s) (Metric.diam.{u1} α _inst_1 s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, (Metric.Bounded.{u1} α _inst_1 s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Metric.infDist.{u1} α _inst_1 x s) (Metric.diam.{u1} α _inst_1 s)))
Case conversion may be inaccurate. Consider using '#align metric.dist_le_inf_dist_add_diam Metric.dist_le_infDist_add_diamₓ'. -/
theorem dist_le_infDist_add_diam (hs : Bounded s) (hy : y ∈ s) : dist x y ≤ infDist x s + diam s :=
  by
  have A : inf_edist x s ≠ ∞ := inf_edist_ne_top ⟨y, hy⟩
  have B : EMetric.diam s ≠ ∞ := hs.ediam_ne_top
  rw [inf_dist, diam, ← ENNReal.toReal_add A B, dist_edist]
  apply (ENNReal.toReal_le_toReal _ _).2
  · exact edist_le_inf_edist_add_ediam hy
  · rw [edist_dist]
    exact ENNReal.ofReal_ne_top
  · exact ENNReal.add_ne_top.2 ⟨A, B⟩
#align metric.dist_le_inf_dist_add_diam Metric.dist_le_infDist_add_diam

variable (s)

#print Metric.lipschitz_infDist_pt /-
/-- The minimal distance to a set is Lipschitz in point with constant 1 -/
theorem lipschitz_infDist_pt : LipschitzWith 1 fun x => infDist x s :=
  LipschitzWith.of_le_add fun x y => infDist_le_infDist_add_dist
#align metric.lipschitz_inf_dist_pt Metric.lipschitz_infDist_pt
-/

#print Metric.uniformContinuous_infDist_pt /-
/-- The minimal distance to a set is uniformly continuous in point -/
theorem uniformContinuous_infDist_pt : UniformContinuous fun x => infDist x s :=
  (lipschitz_infDist_pt s).UniformContinuous
#align metric.uniform_continuous_inf_dist_pt Metric.uniformContinuous_infDist_pt
-/

#print Metric.continuous_infDist_pt /-
/-- The minimal distance to a set is continuous in point -/
@[continuity]
theorem continuous_infDist_pt : Continuous fun x => infDist x s :=
  (uniformContinuous_infDist_pt s).Continuous
#align metric.continuous_inf_dist_pt Metric.continuous_infDist_pt
-/

variable {s}

#print Metric.infDist_closure /-
/-- The minimal distance to a set and its closure coincide -/
theorem infDist_closure : infDist x (closure s) = infDist x s := by
  simp [inf_dist, inf_edist_closure]
#align metric.inf_dist_eq_closure Metric.infDist_closure
-/

/- warning: metric.inf_dist_zero_of_mem_closure -> Metric.infDist_zero_of_mem_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) -> (Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) -> (Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align metric.inf_dist_zero_of_mem_closure Metric.infDist_zero_of_mem_closureₓ'. -/
/-- If a point belongs to the closure of `s`, then its infimum distance to `s` equals zero.
The converse is true provided that `s` is nonempty, see `mem_closure_iff_inf_dist_zero`. -/
theorem infDist_zero_of_mem_closure (hx : x ∈ closure s) : infDist x s = 0 :=
  by
  rw [← inf_dist_eq_closure]
  exact inf_dist_zero_of_mem hx
#align metric.inf_dist_zero_of_mem_closure Metric.infDist_zero_of_mem_closure

/- warning: metric.mem_closure_iff_inf_dist_zero -> Metric.mem_closure_iff_infDist_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, (Set.Nonempty.{u1} α s) -> (Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, (Set.Nonempty.{u1} α s) -> (Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align metric.mem_closure_iff_inf_dist_zero Metric.mem_closure_iff_infDist_zeroₓ'. -/
/-- A point belongs to the closure of `s` iff its infimum distance to this set vanishes -/
theorem mem_closure_iff_infDist_zero (h : s.Nonempty) : x ∈ closure s ↔ infDist x s = 0 := by
  simp [mem_closure_iff_inf_edist_zero, inf_dist, ENNReal.toReal_eq_zero_iff, inf_edist_ne_top h]
#align metric.mem_closure_iff_inf_dist_zero Metric.mem_closure_iff_infDist_zero

/- warning: is_closed.mem_iff_inf_dist_zero -> IsClosed.mem_iff_infDist_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Set.Nonempty.{u1} α s) -> (Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Set.Nonempty.{u1} α s) -> (Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align is_closed.mem_iff_inf_dist_zero IsClosed.mem_iff_infDist_zeroₓ'. -/
/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes -/
theorem IsClosed.mem_iff_infDist_zero (h : IsClosed s) (hs : s.Nonempty) :
    x ∈ s ↔ infDist x s = 0 := by rw [← mem_closure_iff_inf_dist_zero hs, h.closure_eq]
#align is_closed.mem_iff_inf_dist_zero IsClosed.mem_iff_infDist_zero

/- warning: is_closed.not_mem_iff_inf_dist_pos -> IsClosed.not_mem_iff_infDist_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Set.Nonempty.{u1} α s) -> (Iff (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Metric.infDist.{u1} α _inst_1 x s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Set.Nonempty.{u1} α s) -> (Iff (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Metric.infDist.{u1} α _inst_1 x s)))
Case conversion may be inaccurate. Consider using '#align is_closed.not_mem_iff_inf_dist_pos IsClosed.not_mem_iff_infDist_posₓ'. -/
/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes -/
theorem IsClosed.not_mem_iff_infDist_pos (h : IsClosed s) (hs : s.Nonempty) :
    x ∉ s ↔ 0 < infDist x s := by
  rw [← not_iff_not]
  push_neg
  simp [h.mem_iff_inf_dist_zero hs, le_antisymm_iff, inf_dist_nonneg]
#align is_closed.not_mem_iff_inf_dist_pos IsClosed.not_mem_iff_infDist_pos

#print Metric.infDist_image /-
/-- The infimum distance is invariant under isometries -/
theorem infDist_image (hΦ : Isometry Φ) : infDist (Φ x) (Φ '' t) = infDist x t := by
  simp [inf_dist, inf_edist_image hΦ]
#align metric.inf_dist_image Metric.infDist_image
-/

#print Metric.infDist_inter_closedBall_of_mem /-
theorem infDist_inter_closedBall_of_mem (h : y ∈ s) :
    infDist x (s ∩ closedBall x (dist y x)) = infDist x s :=
  by
  replace h : y ∈ s ∩ closed_ball x (dist y x) := ⟨h, mem_closed_ball.2 le_rfl⟩
  refine' le_antisymm _ (inf_dist_le_inf_dist_of_subset (inter_subset_left _ _) ⟨y, h⟩)
  refine' not_lt.1 fun hlt => _
  rcases(inf_dist_lt_iff ⟨y, h.1⟩).mp hlt with ⟨z, hzs, hz⟩
  cases' le_or_lt (dist z x) (dist y x) with hle hlt
  · exact hz.not_le (inf_dist_le_dist_of_mem ⟨hzs, hle⟩)
  · rw [dist_comm z, dist_comm y] at hlt
    exact (hlt.trans hz).not_le (inf_dist_le_dist_of_mem h)
#align metric.inf_dist_inter_closed_ball_of_mem Metric.infDist_inter_closedBall_of_mem
-/

/- warning: is_compact.exists_inf_dist_eq_dist -> IsCompact.exists_infDist_eq_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Set.Nonempty.{u1} α s) -> (forall (x : α), Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Set.Nonempty.{u1} α s) -> (forall (x : α), Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y))))
Case conversion may be inaccurate. Consider using '#align is_compact.exists_inf_dist_eq_dist IsCompact.exists_infDist_eq_distₓ'. -/
theorem IsCompact.exists_infDist_eq_dist (h : IsCompact s) (hne : s.Nonempty) (x : α) :
    ∃ y ∈ s, infDist x s = dist x y :=
  let ⟨y, hys, hy⟩ := h.exists_infEdist_eq_edist hne x
  ⟨y, hys, by rw [inf_dist, dist_edist, hy]⟩
#align is_compact.exists_inf_dist_eq_dist IsCompact.exists_infDist_eq_dist

/- warning: is_closed.exists_inf_dist_eq_dist -> IsClosed.exists_infDist_eq_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_3 : ProperSpace.{u1} α _inst_1], (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Set.Nonempty.{u1} α s) -> (forall (x : α), Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_3 : ProperSpace.{u1} α _inst_1], (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Set.Nonempty.{u1} α s) -> (forall (x : α), Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y))))
Case conversion may be inaccurate. Consider using '#align is_closed.exists_inf_dist_eq_dist IsClosed.exists_infDist_eq_distₓ'. -/
theorem IsClosed.exists_infDist_eq_dist [ProperSpace α] (h : IsClosed s) (hne : s.Nonempty)
    (x : α) : ∃ y ∈ s, infDist x s = dist x y :=
  by
  rcases hne with ⟨z, hz⟩
  rw [← inf_dist_inter_closed_ball_of_mem hz]
  set t := s ∩ closed_ball x (dist z x)
  have htc : IsCompact t := (is_compact_closed_ball x (dist z x)).inter_left h
  have htne : t.nonempty := ⟨z, hz, mem_closed_ball.2 le_rfl⟩
  obtain ⟨y, ⟨hys, hyx⟩, hyd⟩ : ∃ y ∈ t, inf_dist x t = dist x y :=
    htc.exists_inf_dist_eq_dist htne x
  exact ⟨y, hys, hyd⟩
#align is_closed.exists_inf_dist_eq_dist IsClosed.exists_infDist_eq_dist

/- warning: metric.exists_mem_closure_inf_dist_eq_dist -> Metric.exists_mem_closure_infDist_eq_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_3 : ProperSpace.{u1} α _inst_1], (Set.Nonempty.{u1} α s) -> (forall (x : α), Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) => Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_3 : ProperSpace.{u1} α _inst_1], (Set.Nonempty.{u1} α s) -> (forall (x : α), Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (Eq.{1} Real (Metric.infDist.{u1} α _inst_1 x s) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y))))
Case conversion may be inaccurate. Consider using '#align metric.exists_mem_closure_inf_dist_eq_dist Metric.exists_mem_closure_infDist_eq_distₓ'. -/
theorem exists_mem_closure_infDist_eq_dist [ProperSpace α] (hne : s.Nonempty) (x : α) :
    ∃ y ∈ closure s, infDist x s = dist x y := by
  simpa only [inf_dist_eq_closure] using is_closed_closure.exists_inf_dist_eq_dist hne.closure x
#align metric.exists_mem_closure_inf_dist_eq_dist Metric.exists_mem_closure_infDist_eq_dist

/-! ### Distance of a point to a set as a function into `ℝ≥0`. -/


#print Metric.infNndist /-
/-- The minimal distance of a point to a set as a `ℝ≥0` -/
def infNndist (x : α) (s : Set α) : ℝ≥0 :=
  ENNReal.toNNReal (infEdist x s)
#align metric.inf_nndist Metric.infNndist
-/

/- warning: metric.coe_inf_nndist -> Metric.coe_infNndist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (Metric.infNndist.{u1} α _inst_1 x s)) (Metric.infDist.{u1} α _inst_1 x s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α}, Eq.{1} Real (NNReal.toReal (Metric.infNndist.{u1} α _inst_1 x s)) (Metric.infDist.{u1} α _inst_1 x s)
Case conversion may be inaccurate. Consider using '#align metric.coe_inf_nndist Metric.coe_infNndistₓ'. -/
@[simp]
theorem coe_infNndist : (infNndist x s : ℝ) = infDist x s :=
  rfl
#align metric.coe_inf_nndist Metric.coe_infNndist

/- warning: metric.lipschitz_inf_nndist_pt -> Metric.lipschitz_infNndist_pt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (s : Set.{u1} α), LipschitzWith.{u1, 0} α NNReal (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{0} NNReal NNReal.pseudoMetricSpace) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (fun (x : α) => Metric.infNndist.{u1} α _inst_1 x s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (s : Set.{u1} α), LipschitzWith.{u1, 0} α NNReal (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (EMetricSpace.toPseudoEMetricSpace.{0} NNReal (MetricSpace.toEMetricSpace.{0} NNReal instMetricSpaceNNReal)) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (fun (x : α) => Metric.infNndist.{u1} α _inst_1 x s)
Case conversion may be inaccurate. Consider using '#align metric.lipschitz_inf_nndist_pt Metric.lipschitz_infNndist_ptₓ'. -/
/-- The minimal distance to a set (as `ℝ≥0`) is Lipschitz in point with constant 1 -/
theorem lipschitz_infNndist_pt (s : Set α) : LipschitzWith 1 fun x => infNndist x s :=
  LipschitzWith.of_le_add fun x y => infDist_le_infDist_add_dist
#align metric.lipschitz_inf_nndist_pt Metric.lipschitz_infNndist_pt

/- warning: metric.uniform_continuous_inf_nndist_pt -> Metric.uniformContinuous_infNndist_pt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (s : Set.{u1} α), UniformContinuous.{u1, 0} α NNReal (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{0} NNReal NNReal.pseudoMetricSpace) (fun (x : α) => Metric.infNndist.{u1} α _inst_1 x s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (s : Set.{u1} α), UniformContinuous.{u1, 0} α NNReal (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal) (fun (x : α) => Metric.infNndist.{u1} α _inst_1 x s)
Case conversion may be inaccurate. Consider using '#align metric.uniform_continuous_inf_nndist_pt Metric.uniformContinuous_infNndist_ptₓ'. -/
/-- The minimal distance to a set (as `ℝ≥0`) is uniformly continuous in point -/
theorem uniformContinuous_infNndist_pt (s : Set α) : UniformContinuous fun x => infNndist x s :=
  (lipschitz_infNndist_pt s).UniformContinuous
#align metric.uniform_continuous_inf_nndist_pt Metric.uniformContinuous_infNndist_pt

/- warning: metric.continuous_inf_nndist_pt -> Metric.continuous_infNndist_pt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (s : Set.{u1} α), Continuous.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.topologicalSpace (fun (x : α) => Metric.infNndist.{u1} α _inst_1 x s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (s : Set.{u1} α), Continuous.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.instTopologicalSpaceNNReal (fun (x : α) => Metric.infNndist.{u1} α _inst_1 x s)
Case conversion may be inaccurate. Consider using '#align metric.continuous_inf_nndist_pt Metric.continuous_infNndist_ptₓ'. -/
/-- The minimal distance to a set (as `ℝ≥0`) is continuous in point -/
theorem continuous_infNndist_pt (s : Set α) : Continuous fun x => infNndist x s :=
  (uniformContinuous_infNndist_pt s).Continuous
#align metric.continuous_inf_nndist_pt Metric.continuous_infNndist_pt

/-! ### The Hausdorff distance as a function into `ℝ`. -/


#print Metric.hausdorffDist /-
/-- The Hausdorff distance between two sets is the smallest nonnegative `r` such that each set is
included in the `r`-neighborhood of the other. If there is no such `r`, it is defined to
be `0`, arbitrarily -/
def hausdorffDist (s t : Set α) : ℝ :=
  ENNReal.toReal (hausdorffEdist s t)
#align metric.Hausdorff_dist Metric.hausdorffDist
-/

/- warning: metric.Hausdorff_dist_nonneg -> Metric.hausdorffDist_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Metric.hausdorffDist.{u1} α _inst_1 s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Metric.hausdorffDist.{u1} α _inst_1 s t)
Case conversion may be inaccurate. Consider using '#align metric.Hausdorff_dist_nonneg Metric.hausdorffDist_nonnegₓ'. -/
/-- The Hausdorff distance is nonnegative -/
theorem hausdorffDist_nonneg : 0 ≤ hausdorffDist s t := by simp [Hausdorff_dist]
#align metric.Hausdorff_dist_nonneg Metric.hausdorffDist_nonneg

/- warning: metric.Hausdorff_edist_ne_top_of_nonempty_of_bounded -> Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u1} α t) -> (Metric.Bounded.{u1} α _inst_1 s) -> (Metric.Bounded.{u1} α _inst_1 t) -> (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u1} α t) -> (Metric.Bounded.{u1} α _inst_1 s) -> (Metric.Bounded.{u1} α _inst_1 t) -> (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align metric.Hausdorff_edist_ne_top_of_nonempty_of_bounded Metric.hausdorffEdist_ne_top_of_nonempty_of_boundedₓ'. -/
/-- If two sets are nonempty and bounded in a metric space, they are at finite Hausdorff
edistance. -/
theorem hausdorffEdist_ne_top_of_nonempty_of_bounded (hs : s.Nonempty) (ht : t.Nonempty)
    (bs : Bounded s) (bt : Bounded t) : hausdorffEdist s t ≠ ⊤ :=
  by
  rcases hs with ⟨cs, hcs⟩
  rcases ht with ⟨ct, hct⟩
  rcases(bounded_iff_subset_ball ct).1 bs with ⟨rs, hrs⟩
  rcases(bounded_iff_subset_ball cs).1 bt with ⟨rt, hrt⟩
  have : Hausdorff_edist s t ≤ ENNReal.ofReal (max rs rt) :=
    by
    apply Hausdorff_edist_le_of_mem_edist
    · intro x xs
      exists ct, hct
      have : dist x ct ≤ max rs rt := le_trans (hrs xs) (le_max_left _ _)
      rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff]
      exact le_trans dist_nonneg this
    · intro x xt
      exists cs, hcs
      have : dist x cs ≤ max rs rt := le_trans (hrt xt) (le_max_right _ _)
      rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff]
      exact le_trans dist_nonneg this
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
#align metric.Hausdorff_edist_ne_top_of_nonempty_of_bounded Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded

/- warning: metric.Hausdorff_dist_self_zero -> Metric.hausdorffDist_self_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Eq.{1} Real (Metric.hausdorffDist.{u1} α _inst_1 s s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Eq.{1} Real (Metric.hausdorffDist.{u1} α _inst_1 s s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align metric.Hausdorff_dist_self_zero Metric.hausdorffDist_self_zeroₓ'. -/
/-- The Hausdorff distance between a set and itself is zero -/
@[simp]
theorem hausdorffDist_self_zero : hausdorffDist s s = 0 := by simp [Hausdorff_dist]
#align metric.Hausdorff_dist_self_zero Metric.hausdorffDist_self_zero

#print Metric.hausdorffDist_comm /-
/-- The Hausdorff distance from `s` to `t` and from `t` to `s` coincide -/
theorem hausdorffDist_comm : hausdorffDist s t = hausdorffDist t s := by
  simp [Hausdorff_dist, Hausdorff_edist_comm]
#align metric.Hausdorff_dist_comm Metric.hausdorffDist_comm
-/

/- warning: metric.Hausdorff_dist_empty -> Metric.hausdorffDist_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Eq.{1} Real (Metric.hausdorffDist.{u1} α _inst_1 s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Eq.{1} Real (Metric.hausdorffDist.{u1} α _inst_1 s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align metric.Hausdorff_dist_empty Metric.hausdorffDist_emptyₓ'. -/
/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value ∞ instead, use `Hausdorff_edist`, which takes values in ℝ≥0∞) -/
@[simp]
theorem hausdorffDist_empty : hausdorffDist s ∅ = 0 :=
  by
  cases' s.eq_empty_or_nonempty with h h
  · simp [h]
  · simp [Hausdorff_dist, Hausdorff_edist_empty h]
#align metric.Hausdorff_dist_empty Metric.hausdorffDist_empty

/- warning: metric.Hausdorff_dist_empty' -> Metric.hausdorffDist_empty' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Eq.{1} Real (Metric.hausdorffDist.{u1} α _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Eq.{1} Real (Metric.hausdorffDist.{u1} α _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align metric.Hausdorff_dist_empty' Metric.hausdorffDist_empty'ₓ'. -/
/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value ∞ instead, use `Hausdorff_edist`, which takes values in ℝ≥0∞) -/
@[simp]
theorem hausdorffDist_empty' : hausdorffDist ∅ s = 0 := by simp [Hausdorff_dist_comm]
#align metric.Hausdorff_dist_empty' Metric.hausdorffDist_empty'

/- warning: metric.Hausdorff_dist_le_of_inf_dist -> Metric.hausdorffDist_le_of_infDist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LE.le.{0} Real Real.hasLe (Metric.infDist.{u1} α _inst_1 x t) r)) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (LE.le.{0} Real Real.hasLe (Metric.infDist.{u1} α _inst_1 x s) r)) -> (LE.le.{0} Real Real.hasLe (Metric.hausdorffDist.{u1} α _inst_1 s t) r)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {r : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LE.le.{0} Real Real.instLEReal (Metric.infDist.{u1} α _inst_1 x t) r)) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) -> (LE.le.{0} Real Real.instLEReal (Metric.infDist.{u1} α _inst_1 x s) r)) -> (LE.le.{0} Real Real.instLEReal (Metric.hausdorffDist.{u1} α _inst_1 s t) r)
Case conversion may be inaccurate. Consider using '#align metric.Hausdorff_dist_le_of_inf_dist Metric.hausdorffDist_le_of_infDistₓ'. -/
/-- Bounding the Hausdorff distance by bounding the distance of any point
in each set to the other set -/
theorem hausdorffDist_le_of_infDist {r : ℝ} (hr : 0 ≤ r) (H1 : ∀ x ∈ s, infDist x t ≤ r)
    (H2 : ∀ x ∈ t, infDist x s ≤ r) : hausdorffDist s t ≤ r :=
  by
  by_cases h1 : Hausdorff_edist s t = ⊤
  · rwa [Hausdorff_dist, h1, ENNReal.top_toReal]
  cases' s.eq_empty_or_nonempty with hs hs
  · rwa [hs, Hausdorff_dist_empty']
  cases' t.eq_empty_or_nonempty with ht ht
  · rwa [ht, Hausdorff_dist_empty]
  have : Hausdorff_edist s t ≤ ENNReal.ofReal r :=
    by
    apply Hausdorff_edist_le_of_inf_edist _ _
    · intro x hx
      have I := H1 x hx
      rwa [inf_dist, ← ENNReal.toReal_ofReal hr,
        ENNReal.toReal_le_toReal (inf_edist_ne_top ht) ENNReal.ofReal_ne_top] at I
    · intro x hx
      have I := H2 x hx
      rwa [inf_dist, ← ENNReal.toReal_ofReal hr,
        ENNReal.toReal_le_toReal (inf_edist_ne_top hs) ENNReal.ofReal_ne_top] at I
  rwa [Hausdorff_dist, ← ENNReal.toReal_ofReal hr,
    ENNReal.toReal_le_toReal h1 ENNReal.ofReal_ne_top]
#align metric.Hausdorff_dist_le_of_inf_dist Metric.hausdorffDist_le_of_infDist

/- warning: metric.Hausdorff_dist_le_of_mem_dist -> Metric.hausdorffDist_le_of_mem_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) r)))) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) r)))) -> (LE.le.{0} Real Real.hasLe (Metric.hausdorffDist.{u1} α _inst_1 s t) r)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {r : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) r)))) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) r)))) -> (LE.le.{0} Real Real.instLEReal (Metric.hausdorffDist.{u1} α _inst_1 s t) r)
Case conversion may be inaccurate. Consider using '#align metric.Hausdorff_dist_le_of_mem_dist Metric.hausdorffDist_le_of_mem_distₓ'. -/
/-- Bounding the Hausdorff distance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
theorem hausdorffDist_le_of_mem_dist {r : ℝ} (hr : 0 ≤ r) (H1 : ∀ x ∈ s, ∃ y ∈ t, dist x y ≤ r)
    (H2 : ∀ x ∈ t, ∃ y ∈ s, dist x y ≤ r) : hausdorffDist s t ≤ r :=
  by
  apply Hausdorff_dist_le_of_inf_dist hr
  · intro x xs
    rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_trans (inf_dist_le_dist_of_mem yt) hy
  · intro x xt
    rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_trans (inf_dist_le_dist_of_mem ys) hy
#align metric.Hausdorff_dist_le_of_mem_dist Metric.hausdorffDist_le_of_mem_dist

/- warning: metric.Hausdorff_dist_le_diam -> Metric.hausdorffDist_le_diam is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Metric.Bounded.{u1} α _inst_1 s) -> (Set.Nonempty.{u1} α t) -> (Metric.Bounded.{u1} α _inst_1 t) -> (LE.le.{0} Real Real.hasLe (Metric.hausdorffDist.{u1} α _inst_1 s t) (Metric.diam.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Metric.Bounded.{u1} α _inst_1 s) -> (Set.Nonempty.{u1} α t) -> (Metric.Bounded.{u1} α _inst_1 t) -> (LE.le.{0} Real Real.instLEReal (Metric.hausdorffDist.{u1} α _inst_1 s t) (Metric.diam.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align metric.Hausdorff_dist_le_diam Metric.hausdorffDist_le_diamₓ'. -/
/-- The Hausdorff distance is controlled by the diameter of the union -/
theorem hausdorffDist_le_diam (hs : s.Nonempty) (bs : Bounded s) (ht : t.Nonempty)
    (bt : Bounded t) : hausdorffDist s t ≤ diam (s ∪ t) :=
  by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine' Hausdorff_dist_le_of_mem_dist diam_nonneg _ _
  ·
    exact fun z hz =>
      ⟨y, yt,
        dist_le_diam_of_mem (bounded_union.2 ⟨bs, bt⟩) (subset_union_left _ _ hz)
          (subset_union_right _ _ yt)⟩
  ·
    exact fun z hz =>
      ⟨x, xs,
        dist_le_diam_of_mem (bounded_union.2 ⟨bs, bt⟩) (subset_union_right _ _ hz)
          (subset_union_left _ _ xs)⟩
#align metric.Hausdorff_dist_le_diam Metric.hausdorffDist_le_diam

/- warning: metric.inf_dist_le_Hausdorff_dist_of_mem -> Metric.infDist_le_hausdorffDist_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} Real Real.hasLe (Metric.infDist.{u1} α _inst_1 x t) (Metric.hausdorffDist.{u1} α _inst_1 s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} Real Real.instLEReal (Metric.infDist.{u1} α _inst_1 x t) (Metric.hausdorffDist.{u1} α _inst_1 s t))
Case conversion may be inaccurate. Consider using '#align metric.inf_dist_le_Hausdorff_dist_of_mem Metric.infDist_le_hausdorffDist_of_memₓ'. -/
/-- The distance to a set is controlled by the Hausdorff distance -/
theorem infDist_le_hausdorffDist_of_mem (hx : x ∈ s) (fin : hausdorffEdist s t ≠ ⊤) :
    infDist x t ≤ hausdorffDist s t :=
  by
  have ht : t.nonempty := nonempty_of_Hausdorff_edist_ne_top ⟨x, hx⟩ Fin
  rw [Hausdorff_dist, inf_dist, ENNReal.toReal_le_toReal (inf_edist_ne_top ht) Fin]
  exact inf_edist_le_Hausdorff_edist_of_mem hx
#align metric.inf_dist_le_Hausdorff_dist_of_mem Metric.infDist_le_hausdorffDist_of_mem

/- warning: metric.exists_dist_lt_of_Hausdorff_dist_lt -> Metric.exists_dist_lt_of_hausdorffDist_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α} {r : Real}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LT.lt.{0} Real Real.hasLt (Metric.hausdorffDist.{u1} α _inst_1 s t) r) -> (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) r)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α} {r : Real}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LT.lt.{0} Real Real.instLTReal (Metric.hausdorffDist.{u1} α _inst_1 s t) r) -> (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) r)))
Case conversion may be inaccurate. Consider using '#align metric.exists_dist_lt_of_Hausdorff_dist_lt Metric.exists_dist_lt_of_hausdorffDist_ltₓ'. -/
/-- If the Hausdorff distance is `<r`, then any point in one of the sets is at distance
`<r` of a point in the other set -/
theorem exists_dist_lt_of_hausdorffDist_lt {r : ℝ} (h : x ∈ s) (H : hausdorffDist s t < r)
    (fin : hausdorffEdist s t ≠ ⊤) : ∃ y ∈ t, dist x y < r :=
  by
  have r0 : 0 < r := lt_of_le_of_lt Hausdorff_dist_nonneg H
  have : Hausdorff_edist s t < ENNReal.ofReal r := by
    rwa [Hausdorff_dist, ← ENNReal.toReal_ofReal (le_of_lt r0),
      ENNReal.toReal_lt_toReal Fin ENNReal.ofReal_ne_top] at H
  rcases exists_edist_lt_of_Hausdorff_edist_lt h this with ⟨y, hy, yr⟩
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff r0] at yr
  exact ⟨y, hy, yr⟩
#align metric.exists_dist_lt_of_Hausdorff_dist_lt Metric.exists_dist_lt_of_hausdorffDist_lt

/- warning: metric.exists_dist_lt_of_Hausdorff_dist_lt' -> Metric.exists_dist_lt_of_hausdorffDist_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {y : α} {r : Real}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) -> (LT.lt.{0} Real Real.hasLt (Metric.hausdorffDist.{u1} α _inst_1 s t) r) -> (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) r)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {y : α} {r : Real}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) -> (LT.lt.{0} Real Real.instLTReal (Metric.hausdorffDist.{u1} α _inst_1 s t) r) -> (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) r)))
Case conversion may be inaccurate. Consider using '#align metric.exists_dist_lt_of_Hausdorff_dist_lt' Metric.exists_dist_lt_of_hausdorffDist_lt'ₓ'. -/
/-- If the Hausdorff distance is `<r`, then any point in one of the sets is at distance
`<r` of a point in the other set -/
theorem exists_dist_lt_of_hausdorffDist_lt' {r : ℝ} (h : y ∈ t) (H : hausdorffDist s t < r)
    (fin : hausdorffEdist s t ≠ ⊤) : ∃ x ∈ s, dist x y < r :=
  by
  rw [Hausdorff_dist_comm] at H
  rw [Hausdorff_edist_comm] at fin
  simpa [dist_comm] using exists_dist_lt_of_Hausdorff_dist_lt h H Fin
#align metric.exists_dist_lt_of_Hausdorff_dist_lt' Metric.exists_dist_lt_of_hausdorffDist_lt'

/- warning: metric.inf_dist_le_inf_dist_add_Hausdorff_dist -> Metric.infDist_le_infDist_add_hausdorffDist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} Real Real.hasLe (Metric.infDist.{u1} α _inst_1 x t) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Metric.infDist.{u1} α _inst_1 x s) (Metric.hausdorffDist.{u1} α _inst_1 s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} Real Real.instLEReal (Metric.infDist.{u1} α _inst_1 x t) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Metric.infDist.{u1} α _inst_1 x s) (Metric.hausdorffDist.{u1} α _inst_1 s t)))
Case conversion may be inaccurate. Consider using '#align metric.inf_dist_le_inf_dist_add_Hausdorff_dist Metric.infDist_le_infDist_add_hausdorffDistₓ'. -/
/-- The infimum distance to `s` and `t` are the same, up to the Hausdorff distance
between `s` and `t` -/
theorem infDist_le_infDist_add_hausdorffDist (fin : hausdorffEdist s t ≠ ⊤) :
    infDist x t ≤ infDist x s + hausdorffDist s t :=
  by
  rcases empty_or_nonempty_of_Hausdorff_edist_ne_top Fin with (⟨hs, ht⟩ | ⟨hs, ht⟩)
  · simp only [hs, ht, Hausdorff_dist_empty, inf_dist_empty, zero_add]
  rw [inf_dist, inf_dist, Hausdorff_dist, ← ENNReal.toReal_add (inf_edist_ne_top hs) Fin,
    ENNReal.toReal_le_toReal (inf_edist_ne_top ht)]
  · exact inf_edist_le_inf_edist_add_Hausdorff_edist
  · exact ENNReal.add_ne_top.2 ⟨inf_edist_ne_top hs, Fin⟩
#align metric.inf_dist_le_inf_dist_add_Hausdorff_dist Metric.infDist_le_infDist_add_hausdorffDist

#print Metric.hausdorffDist_image /-
/-- The Hausdorff distance is invariant under isometries -/
theorem hausdorffDist_image (h : Isometry Φ) :
    hausdorffDist (Φ '' s) (Φ '' t) = hausdorffDist s t := by
  simp [Hausdorff_dist, Hausdorff_edist_image h]
#align metric.Hausdorff_dist_image Metric.hausdorffDist_image
-/

/- warning: metric.Hausdorff_dist_triangle -> Metric.hausdorffDist_triangle is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} Real Real.hasLe (Metric.hausdorffDist.{u1} α _inst_1 s u) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Metric.hausdorffDist.{u1} α _inst_1 s t) (Metric.hausdorffDist.{u1} α _inst_1 t u)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} Real Real.instLEReal (Metric.hausdorffDist.{u1} α _inst_1 s u) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Metric.hausdorffDist.{u1} α _inst_1 s t) (Metric.hausdorffDist.{u1} α _inst_1 t u)))
Case conversion may be inaccurate. Consider using '#align metric.Hausdorff_dist_triangle Metric.hausdorffDist_triangleₓ'. -/
/-- The Hausdorff distance satisfies the triangular inequality -/
theorem hausdorffDist_triangle (fin : hausdorffEdist s t ≠ ⊤) :
    hausdorffDist s u ≤ hausdorffDist s t + hausdorffDist t u :=
  by
  by_cases Hausdorff_edist s u = ⊤
  ·
    calc
      Hausdorff_dist s u = 0 + 0 := by simp [Hausdorff_dist, h]
      _ ≤ Hausdorff_dist s t + Hausdorff_dist t u :=
        add_le_add Hausdorff_dist_nonneg Hausdorff_dist_nonneg
      
  · have Dtu : Hausdorff_edist t u < ⊤ :=
      calc
        Hausdorff_edist t u ≤ Hausdorff_edist t s + Hausdorff_edist s u := Hausdorff_edist_triangle
        _ = Hausdorff_edist s t + Hausdorff_edist s u := by simp [Hausdorff_edist_comm]
        _ < ⊤ := lt_top_iff_ne_top.mpr <| ennreal.add_ne_top.mpr ⟨Fin, h⟩
        
    rw [Hausdorff_dist, Hausdorff_dist, Hausdorff_dist, ← ENNReal.toReal_add Fin Dtu.ne,
      ENNReal.toReal_le_toReal h]
    · exact Hausdorff_edist_triangle
    · simp [ENNReal.add_eq_top, lt_top_iff_ne_top.1 Dtu, Fin]
#align metric.Hausdorff_dist_triangle Metric.hausdorffDist_triangle

/- warning: metric.Hausdorff_dist_triangle' -> Metric.hausdorffDist_triangle' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) t u) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} Real Real.hasLe (Metric.hausdorffDist.{u1} α _inst_1 s u) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Metric.hausdorffDist.{u1} α _inst_1 s t) (Metric.hausdorffDist.{u1} α _inst_1 t u)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) t u) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} Real Real.instLEReal (Metric.hausdorffDist.{u1} α _inst_1 s u) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Metric.hausdorffDist.{u1} α _inst_1 s t) (Metric.hausdorffDist.{u1} α _inst_1 t u)))
Case conversion may be inaccurate. Consider using '#align metric.Hausdorff_dist_triangle' Metric.hausdorffDist_triangle'ₓ'. -/
/-- The Hausdorff distance satisfies the triangular inequality -/
theorem hausdorffDist_triangle' (fin : hausdorffEdist t u ≠ ⊤) :
    hausdorffDist s u ≤ hausdorffDist s t + hausdorffDist t u :=
  by
  rw [Hausdorff_edist_comm] at fin
  have I : Hausdorff_dist u s ≤ Hausdorff_dist u t + Hausdorff_dist t s :=
    Hausdorff_dist_triangle Fin
  simpa [add_comm, Hausdorff_dist_comm] using I
#align metric.Hausdorff_dist_triangle' Metric.hausdorffDist_triangle'

/- warning: metric.Hausdorff_dist_self_closure -> Metric.hausdorffDist_self_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Eq.{1} Real (Metric.hausdorffDist.{u1} α _inst_1 s (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Eq.{1} Real (Metric.hausdorffDist.{u1} α _inst_1 s (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align metric.Hausdorff_dist_self_closure Metric.hausdorffDist_self_closureₓ'. -/
/-- The Hausdorff distance between a set and its closure vanish -/
@[simp]
theorem hausdorffDist_self_closure : hausdorffDist s (closure s) = 0 := by simp [Hausdorff_dist]
#align metric.Hausdorff_dist_self_closure Metric.hausdorffDist_self_closure

#print Metric.hausdorffDist_closure₁ /-
/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
theorem hausdorffDist_closure₁ : hausdorffDist (closure s) t = hausdorffDist s t := by
  simp [Hausdorff_dist]
#align metric.Hausdorff_dist_closure₁ Metric.hausdorffDist_closure₁
-/

#print Metric.hausdorffDist_closure₂ /-
/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
theorem hausdorffDist_closure₂ : hausdorffDist s (closure t) = hausdorffDist s t := by
  simp [Hausdorff_dist]
#align metric.Hausdorff_dist_closure₂ Metric.hausdorffDist_closure₂
-/

#print Metric.hausdorffDist_closure /-
/-- The Hausdorff distance between two sets and their closures coincide -/
@[simp]
theorem hausdorffDist_closure : hausdorffDist (closure s) (closure t) = hausdorffDist s t := by
  simp [Hausdorff_dist]
#align metric.Hausdorff_dist_closure Metric.hausdorffDist_closure
-/

/- warning: metric.Hausdorff_dist_zero_iff_closure_eq_closure -> Metric.hausdorffDist_zero_iff_closure_eq_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Iff (Eq.{1} Real (Metric.hausdorffDist.{u1} α _inst_1 s t) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{succ u1} (Set.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Iff (Eq.{1} Real (Metric.hausdorffDist.{u1} α _inst_1 s t) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{succ u1} (Set.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) t)))
Case conversion may be inaccurate. Consider using '#align metric.Hausdorff_dist_zero_iff_closure_eq_closure Metric.hausdorffDist_zero_iff_closure_eq_closureₓ'. -/
/-- Two sets are at zero Hausdorff distance if and only if they have the same closures -/
theorem hausdorffDist_zero_iff_closure_eq_closure (fin : hausdorffEdist s t ≠ ⊤) :
    hausdorffDist s t = 0 ↔ closure s = closure t := by
  simp [Hausdorff_edist_zero_iff_closure_eq_closure.symm, Hausdorff_dist,
    ENNReal.toReal_eq_zero_iff, Fin]
#align metric.Hausdorff_dist_zero_iff_closure_eq_closure Metric.hausdorffDist_zero_iff_closure_eq_closure

/- warning: is_closed.Hausdorff_dist_zero_iff_eq -> IsClosed.hausdorffDist_zero_iff_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Iff (Eq.{1} Real (Metric.hausdorffDist.{u1} α _inst_1 s t) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{succ u1} (Set.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (Ne.{1} ENNReal (EMetric.hausdorffEdist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Iff (Eq.{1} Real (Metric.hausdorffDist.{u1} α _inst_1 s t) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{succ u1} (Set.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align is_closed.Hausdorff_dist_zero_iff_eq IsClosed.hausdorffDist_zero_iff_eqₓ'. -/
/-- Two closed sets are at zero Hausdorff distance if and only if they coincide -/
theorem IsClosed.hausdorffDist_zero_iff_eq (hs : IsClosed s) (ht : IsClosed t)
    (fin : hausdorffEdist s t ≠ ⊤) : hausdorffDist s t = 0 ↔ s = t := by
  simp [← Hausdorff_edist_zero_iff_eq_of_closed hs ht, Hausdorff_dist, ENNReal.toReal_eq_zero_iff,
    Fin]
#align is_closed.Hausdorff_dist_zero_iff_eq IsClosed.hausdorffDist_zero_iff_eq

end

--section
section Thickening

variable [PseudoEMetricSpace α] {δ : ℝ} {s : Set α} {x : α}

open Emetric

#print Metric.thickening /-
/-- The (open) `δ`-thickening `thickening δ E` of a subset `E` in a pseudo emetric space consists
of those points that are at distance less than `δ` from some point of `E`. -/
def thickening (δ : ℝ) (E : Set α) : Set α :=
  { x : α | infEdist x E < ENNReal.ofReal δ }
#align metric.thickening Metric.thickening
-/

/- warning: metric.mem_thickening_iff_inf_edist_lt -> Metric.mem_thickening_iff_infEdist_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} {s : Set.{u1} α} {x : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Metric.thickening.{u1} α _inst_1 δ s)) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.infEdist.{u1} α _inst_1 x s) (ENNReal.ofReal δ))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} {s : Set.{u1} α} {x : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Metric.thickening.{u1} α _inst_1 δ s)) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.infEdist.{u1} α _inst_1 x s) (ENNReal.ofReal δ))
Case conversion may be inaccurate. Consider using '#align metric.mem_thickening_iff_inf_edist_lt Metric.mem_thickening_iff_infEdist_ltₓ'. -/
theorem mem_thickening_iff_infEdist_lt : x ∈ thickening δ s ↔ infEdist x s < ENNReal.ofReal δ :=
  Iff.rfl
#align metric.mem_thickening_iff_inf_edist_lt Metric.mem_thickening_iff_infEdist_lt

/- warning: metric.thickening_eq_preimage_inf_edist -> Metric.thickening_eq_preimage_infEdist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.thickening.{u1} α _inst_1 δ E) (Set.preimage.{u1, 0} α ENNReal (fun (x : α) => EMetric.infEdist.{u1} α _inst_1 x E) (Set.Iio.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (ENNReal.ofReal δ)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.thickening.{u1} α _inst_1 δ E) (Set.preimage.{u1, 0} α ENNReal (fun (x : α) => EMetric.infEdist.{u1} α _inst_1 x E) (Set.Iio.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (ENNReal.ofReal δ)))
Case conversion may be inaccurate. Consider using '#align metric.thickening_eq_preimage_inf_edist Metric.thickening_eq_preimage_infEdistₓ'. -/
/-- The (open) thickening equals the preimage of an open interval under `inf_edist`. -/
theorem thickening_eq_preimage_infEdist (δ : ℝ) (E : Set α) :
    thickening δ E = (fun x => infEdist x E) ⁻¹' Iio (ENNReal.ofReal δ) :=
  rfl
#align metric.thickening_eq_preimage_inf_edist Metric.thickening_eq_preimage_infEdist

#print Metric.isOpen_thickening /-
/-- The (open) thickening is an open set. -/
theorem isOpen_thickening {δ : ℝ} {E : Set α} : IsOpen (thickening δ E) :=
  Continuous.isOpen_preimage continuous_infEdist _ isOpen_Iio
#align metric.is_open_thickening Metric.isOpen_thickening
-/

#print Metric.thickening_empty /-
/-- The (open) thickening of the empty set is empty. -/
@[simp]
theorem thickening_empty (δ : ℝ) : thickening δ (∅ : Set α) = ∅ := by
  simp only [thickening, set_of_false, inf_edist_empty, not_top_lt]
#align metric.thickening_empty Metric.thickening_empty
-/

/- warning: metric.thickening_of_nonpos -> Metric.thickening_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LE.le.{0} Real Real.hasLe δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.thickening.{u1} α _inst_1 δ s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LE.le.{0} Real Real.instLEReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.thickening.{u1} α _inst_1 δ s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align metric.thickening_of_nonpos Metric.thickening_of_nonposₓ'. -/
theorem thickening_of_nonpos (hδ : δ ≤ 0) (s : Set α) : thickening δ s = ∅ :=
  eq_empty_of_forall_not_mem fun x => ((ENNReal.ofReal_of_nonpos hδ).trans_le bot_le).not_lt
#align metric.thickening_of_nonpos Metric.thickening_of_nonpos

/- warning: metric.thickening_mono -> Metric.thickening_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : Real} {δ₂ : Real}, (LE.le.{0} Real Real.hasLe δ₁ δ₂) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.thickening.{u1} α _inst_1 δ₁ E) (Metric.thickening.{u1} α _inst_1 δ₂ E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : Real} {δ₂ : Real}, (LE.le.{0} Real Real.instLEReal δ₁ δ₂) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.thickening.{u1} α _inst_1 δ₁ E) (Metric.thickening.{u1} α _inst_1 δ₂ E))
Case conversion may be inaccurate. Consider using '#align metric.thickening_mono Metric.thickening_monoₓ'. -/
/-- The (open) thickening `thickening δ E` of a fixed subset `E` is an increasing function of the
thickening radius `δ`. -/
theorem thickening_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    thickening δ₁ E ⊆ thickening δ₂ E :=
  preimage_mono (Iio_subset_Iio (ENNReal.ofReal_le_ofReal hle))
#align metric.thickening_mono Metric.thickening_mono

#print Metric.thickening_subset_of_subset /-
/-- The (open) thickening `thickening δ E` with a fixed thickening radius `δ` is
an increasing function of the subset `E`. -/
theorem thickening_subset_of_subset (δ : ℝ) {E₁ E₂ : Set α} (h : E₁ ⊆ E₂) :
    thickening δ E₁ ⊆ thickening δ E₂ := fun _ hx => lt_of_le_of_lt (infEdist_anti h) hx
#align metric.thickening_subset_of_subset Metric.thickening_subset_of_subset
-/

/- warning: metric.mem_thickening_iff_exists_edist_lt -> Metric.mem_thickening_iff_exists_edist_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (E : Set.{u1} α) (x : α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Metric.thickening.{u1} α _inst_1 δ E)) (Exists.{succ u1} α (fun (z : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z E) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z E) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x z) (ENNReal.ofReal δ))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (E : Set.{u1} α) (x : α), Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Metric.thickening.{u1} α _inst_1 δ E)) (Exists.{succ u1} α (fun (z : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z E) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x z) (ENNReal.ofReal δ))))
Case conversion may be inaccurate. Consider using '#align metric.mem_thickening_iff_exists_edist_lt Metric.mem_thickening_iff_exists_edist_ltₓ'. -/
theorem mem_thickening_iff_exists_edist_lt {δ : ℝ} (E : Set α) (x : α) :
    x ∈ thickening δ E ↔ ∃ z ∈ E, edist x z < ENNReal.ofReal δ :=
  infEdist_lt_iff
#align metric.mem_thickening_iff_exists_edist_lt Metric.mem_thickening_iff_exists_edist_lt

#print Metric.frontier_thickening_subset /-
/-- The frontier of the (open) thickening of a set is contained in an `inf_edist` level set. -/
theorem frontier_thickening_subset (E : Set α) {δ : ℝ} :
    frontier (thickening δ E) ⊆ { x : α | infEdist x E = ENNReal.ofReal δ } :=
  frontier_lt_subset_eq continuous_infEdist continuous_const
#align metric.frontier_thickening_subset Metric.frontier_thickening_subset
-/

/- warning: metric.frontier_thickening_disjoint -> Metric.frontier_thickening_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (A : Set.{u1} α), Pairwise.{0} Real (Function.onFun.{1, succ u1, 1} Real (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) (fun (r : Real) => frontier.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (Metric.thickening.{u1} α _inst_1 r A)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (A : Set.{u1} α), Pairwise.{0} Real (Function.onFun.{1, succ u1, 1} Real (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (fun (r : Real) => frontier.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (Metric.thickening.{u1} α _inst_1 r A)))
Case conversion may be inaccurate. Consider using '#align metric.frontier_thickening_disjoint Metric.frontier_thickening_disjointₓ'. -/
theorem frontier_thickening_disjoint (A : Set α) :
    Pairwise (Disjoint on fun r : ℝ => frontier (thickening r A)) :=
  by
  refine' (pairwise_disjoint_on _).2 fun r₁ r₂ hr => _
  cases' le_total r₁ 0 with h₁ h₁
  · simp [thickening_of_nonpos h₁]
  refine'
    ((disjoint_singleton.2 fun h => hr.ne _).Preimage _).mono (frontier_thickening_subset _)
      (frontier_thickening_subset _)
  apply_fun ENNReal.toReal  at h
  rwa [ENNReal.toReal_ofReal h₁, ENNReal.toReal_ofReal (h₁.trans hr.le)] at h
#align metric.frontier_thickening_disjoint Metric.frontier_thickening_disjoint

variable {X : Type u} [PseudoMetricSpace X]

/- warning: metric.mem_thickening_iff -> Metric.mem_thickening_iff is a dubious translation:
lean 3 declaration is
  forall {δ : Real} {X : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} X] {E : Set.{u1} X} {x : X}, Iff (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x (Metric.thickening.{u1} X (PseudoMetricSpace.toPseudoEMetricSpace.{u1} X _inst_2) δ E)) (Exists.{succ u1} X (fun (z : X) => Exists.{0} (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) z E) (fun (H : Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) z E) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} X (PseudoMetricSpace.toHasDist.{u1} X _inst_2) x z) δ)))
but is expected to have type
  forall {δ : Real} {X : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} X] {E : Set.{u1} X} {x : X}, Iff (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) x (Metric.thickening.{u1} X (PseudoMetricSpace.toPseudoEMetricSpace.{u1} X _inst_2) δ E)) (Exists.{succ u1} X (fun (z : X) => And (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) z E) (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} X (PseudoMetricSpace.toDist.{u1} X _inst_2) x z) δ)))
Case conversion may be inaccurate. Consider using '#align metric.mem_thickening_iff Metric.mem_thickening_iffₓ'. -/
/-- A point in a metric space belongs to the (open) `δ`-thickening of a subset `E` if and only if
it is at distance less than `δ` from some point of `E`. -/
theorem mem_thickening_iff {E : Set X} {x : X} : x ∈ thickening δ E ↔ ∃ z ∈ E, dist x z < δ :=
  by
  have key_iff : ∀ z : X, edist x z < ENNReal.ofReal δ ↔ dist x z < δ :=
    by
    intro z
    rw [dist_edist]
    have d_lt_top : edist x z < ∞ := by simp only [edist_dist, ENNReal.ofReal_lt_top]
    have key := @ENNReal.ofReal_lt_ofReal_iff_of_nonneg (edist x z).toReal δ ENNReal.toReal_nonneg
    rwa [ENNReal.ofReal_toReal d_lt_top.ne] at key
  simp_rw [mem_thickening_iff_exists_edist_lt, key_iff]
#align metric.mem_thickening_iff Metric.mem_thickening_iff

#print Metric.thickening_singleton /-
@[simp]
theorem thickening_singleton (δ : ℝ) (x : X) : thickening δ ({x} : Set X) = ball x δ :=
  by
  ext
  simp [mem_thickening_iff]
#align metric.thickening_singleton Metric.thickening_singleton
-/

#print Metric.ball_subset_thickening /-
theorem ball_subset_thickening {x : X} {E : Set X} (hx : x ∈ E) (δ : ℝ) :
    ball x δ ⊆ thickening δ E :=
  Subset.trans (by simp) (thickening_subset_of_subset δ <| singleton_subset_iff.mpr hx)
#align metric.ball_subset_thickening Metric.ball_subset_thickening
-/

#print Metric.thickening_eq_biUnion_ball /-
/-- The (open) `δ`-thickening `thickening δ E` of a subset `E` in a metric space equals the
union of balls of radius `δ` centered at points of `E`. -/
theorem thickening_eq_biUnion_ball {δ : ℝ} {E : Set X} : thickening δ E = ⋃ x ∈ E, ball x δ :=
  by
  ext x
  rw [mem_Union₂]
  exact mem_thickening_iff
#align metric.thickening_eq_bUnion_ball Metric.thickening_eq_biUnion_ball
-/

#print Metric.Bounded.thickening /-
theorem Bounded.thickening {δ : ℝ} {E : Set X} (h : Bounded E) : Bounded (thickening δ E) :=
  by
  refine' bounded_iff_mem_bounded.2 fun x hx => _
  rcases h.subset_ball x with ⟨R, hR⟩
  refine' (bounded_iff_subset_ball x).2 ⟨R + δ, _⟩
  intro y hy
  rcases mem_thickening_iff.1 hy with ⟨z, zE, hz⟩
  calc
    dist y x ≤ dist z x + dist y z := by
      rw [add_comm]
      exact dist_triangle _ _ _
    _ ≤ R + δ := add_le_add (hR zE) hz.le
    
#align metric.bounded.thickening Metric.Bounded.thickening
-/

end Thickening

--section
section Cthickening

variable [PseudoEMetricSpace α] {δ ε : ℝ} {s t : Set α} {x : α}

open Emetric

#print Metric.cthickening /-
/-- The closed `δ`-thickening `cthickening δ E` of a subset `E` in a pseudo emetric space consists
of those points that are at infimum distance at most `δ` from `E`. -/
def cthickening (δ : ℝ) (E : Set α) : Set α :=
  { x : α | infEdist x E ≤ ENNReal.ofReal δ }
#align metric.cthickening Metric.cthickening
-/

/- warning: metric.mem_cthickening_iff -> Metric.mem_cthickening_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} {s : Set.{u1} α} {x : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Metric.cthickening.{u1} α _inst_1 δ s)) (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.infEdist.{u1} α _inst_1 x s) (ENNReal.ofReal δ))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} {s : Set.{u1} α} {x : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Metric.cthickening.{u1} α _inst_1 δ s)) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.infEdist.{u1} α _inst_1 x s) (ENNReal.ofReal δ))
Case conversion may be inaccurate. Consider using '#align metric.mem_cthickening_iff Metric.mem_cthickening_iffₓ'. -/
@[simp]
theorem mem_cthickening_iff : x ∈ cthickening δ s ↔ infEdist x s ≤ ENNReal.ofReal δ :=
  Iff.rfl
#align metric.mem_cthickening_iff Metric.mem_cthickening_iff

/- warning: metric.mem_cthickening_of_edist_le -> Metric.mem_cthickening_of_edist_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) (y : α) (δ : Real) (E : Set.{u1} α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y E) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (ENNReal.ofReal δ)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Metric.cthickening.{u1} α _inst_1 δ E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) (y : α) (δ : Real) (E : Set.{u1} α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y E) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) (ENNReal.ofReal δ)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Metric.cthickening.{u1} α _inst_1 δ E))
Case conversion may be inaccurate. Consider using '#align metric.mem_cthickening_of_edist_le Metric.mem_cthickening_of_edist_leₓ'. -/
theorem mem_cthickening_of_edist_le (x y : α) (δ : ℝ) (E : Set α) (h : y ∈ E)
    (h' : edist x y ≤ ENNReal.ofReal δ) : x ∈ cthickening δ E :=
  (infEdist_le_edist_of_mem h).trans h'
#align metric.mem_cthickening_of_edist_le Metric.mem_cthickening_of_edist_le

/- warning: metric.mem_cthickening_of_dist_le -> Metric.mem_cthickening_of_dist_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (δ : Real) (E : Set.{u1} α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y E) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_2) x y) δ) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) δ E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (δ : Real) (E : Set.{u1} α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y E) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_2) x y) δ) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) δ E))
Case conversion may be inaccurate. Consider using '#align metric.mem_cthickening_of_dist_le Metric.mem_cthickening_of_dist_leₓ'. -/
theorem mem_cthickening_of_dist_le {α : Type _} [PseudoMetricSpace α] (x y : α) (δ : ℝ) (E : Set α)
    (h : y ∈ E) (h' : dist x y ≤ δ) : x ∈ cthickening δ E :=
  by
  apply mem_cthickening_of_edist_le x y δ E h
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal h'
#align metric.mem_cthickening_of_dist_le Metric.mem_cthickening_of_dist_le

/- warning: metric.cthickening_eq_preimage_inf_edist -> Metric.cthickening_eq_preimage_infEdist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (Set.preimage.{u1, 0} α ENNReal (fun (x : α) => EMetric.infEdist.{u1} α _inst_1 x E) (Set.Iic.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (ENNReal.ofReal δ)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (Set.preimage.{u1, 0} α ENNReal (fun (x : α) => EMetric.infEdist.{u1} α _inst_1 x E) (Set.Iic.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (ENNReal.ofReal δ)))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_eq_preimage_inf_edist Metric.cthickening_eq_preimage_infEdistₓ'. -/
theorem cthickening_eq_preimage_infEdist (δ : ℝ) (E : Set α) :
    cthickening δ E = (fun x => infEdist x E) ⁻¹' Iic (ENNReal.ofReal δ) :=
  rfl
#align metric.cthickening_eq_preimage_inf_edist Metric.cthickening_eq_preimage_infEdist

#print Metric.isClosed_cthickening /-
/-- The closed thickening is a closed set. -/
theorem isClosed_cthickening {δ : ℝ} {E : Set α} : IsClosed (cthickening δ E) :=
  IsClosed.preimage continuous_infEdist isClosed_Iic
#align metric.is_closed_cthickening Metric.isClosed_cthickening
-/

#print Metric.cthickening_empty /-
/-- The closed thickening of the empty set is empty. -/
@[simp]
theorem cthickening_empty (δ : ℝ) : cthickening δ (∅ : Set α) = ∅ := by
  simp only [cthickening, ENNReal.ofReal_ne_top, set_of_false, inf_edist_empty, top_le_iff]
#align metric.cthickening_empty Metric.cthickening_empty
-/

/- warning: metric.cthickening_of_nonpos -> Metric.cthickening_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LE.le.{0} Real Real.hasLe δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LE.le.{0} Real Real.instLEReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_of_nonpos Metric.cthickening_of_nonposₓ'. -/
theorem cthickening_of_nonpos {δ : ℝ} (hδ : δ ≤ 0) (E : Set α) : cthickening δ E = closure E :=
  by
  ext x
  simp [mem_closure_iff_inf_edist_zero, cthickening, ENNReal.ofReal_eq_zero.2 hδ]
#align metric.cthickening_of_nonpos Metric.cthickening_of_nonpos

/- warning: metric.cthickening_zero -> Metric.cthickening_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) E) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) E) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E)
Case conversion may be inaccurate. Consider using '#align metric.cthickening_zero Metric.cthickening_zeroₓ'. -/
/-- The closed thickening with radius zero is the closure of the set. -/
@[simp]
theorem cthickening_zero (E : Set α) : cthickening 0 E = closure E :=
  cthickening_of_nonpos le_rfl E
#align metric.cthickening_zero Metric.cthickening_zero

/- warning: metric.cthickening_max_zero -> Metric.cthickening_max_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 (LinearOrder.max.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) E) (Metric.cthickening.{u1} α _inst_1 δ E)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) E) (Metric.cthickening.{u1} α _inst_1 δ E)
Case conversion may be inaccurate. Consider using '#align metric.cthickening_max_zero Metric.cthickening_max_zeroₓ'. -/
theorem cthickening_max_zero (δ : ℝ) (E : Set α) : cthickening (max 0 δ) E = cthickening δ E := by
  cases le_total δ 0 <;> simp [cthickening_of_nonpos, *]
#align metric.cthickening_max_zero Metric.cthickening_max_zero

/- warning: metric.cthickening_mono -> Metric.cthickening_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : Real} {δ₂ : Real}, (LE.le.{0} Real Real.hasLe δ₁ δ₂) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ₁ E) (Metric.cthickening.{u1} α _inst_1 δ₂ E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : Real} {δ₂ : Real}, (LE.le.{0} Real Real.instLEReal δ₁ δ₂) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ₁ E) (Metric.cthickening.{u1} α _inst_1 δ₂ E))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_mono Metric.cthickening_monoₓ'. -/
/-- The closed thickening `cthickening δ E` of a fixed subset `E` is an increasing function of
the thickening radius `δ`. -/
theorem cthickening_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    cthickening δ₁ E ⊆ cthickening δ₂ E :=
  preimage_mono (Iic_subset_Iic.mpr (ENNReal.ofReal_le_ofReal hle))
#align metric.cthickening_mono Metric.cthickening_mono

/- warning: metric.cthickening_singleton -> Metric.cthickening_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] (x : α) {δ : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) δ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (Metric.closedBall.{u1} α _inst_2 x δ))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] (x : α) {δ : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) δ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (Metric.closedBall.{u1} α _inst_2 x δ))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_singleton Metric.cthickening_singletonₓ'. -/
@[simp]
theorem cthickening_singleton {α : Type _} [PseudoMetricSpace α] (x : α) {δ : ℝ} (hδ : 0 ≤ δ) :
    cthickening δ ({x} : Set α) = closedBall x δ :=
  by
  ext y
  simp [cthickening, edist_dist, ENNReal.ofReal_le_ofReal_iff hδ]
#align metric.cthickening_singleton Metric.cthickening_singleton

#print Metric.closedBall_subset_cthickening_singleton /-
theorem closedBall_subset_cthickening_singleton {α : Type _} [PseudoMetricSpace α] (x : α) (δ : ℝ) :
    closedBall x δ ⊆ cthickening δ ({x} : Set α) :=
  by
  rcases lt_or_le δ 0 with (hδ | hδ)
  · simp only [closed_ball_eq_empty.mpr hδ, empty_subset]
  · simp only [cthickening_singleton x hδ]
#align metric.closed_ball_subset_cthickening_singleton Metric.closedBall_subset_cthickening_singleton
-/

#print Metric.cthickening_subset_of_subset /-
/-- The closed thickening `cthickening δ E` with a fixed thickening radius `δ` is
an increasing function of the subset `E`. -/
theorem cthickening_subset_of_subset (δ : ℝ) {E₁ E₂ : Set α} (h : E₁ ⊆ E₂) :
    cthickening δ E₁ ⊆ cthickening δ E₂ := fun _ hx => le_trans (infEdist_anti h) hx
#align metric.cthickening_subset_of_subset Metric.cthickening_subset_of_subset
-/

/- warning: metric.cthickening_subset_thickening -> Metric.cthickening_subset_thickening is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : NNReal} {δ₂ : Real}, (LT.lt.{0} Real Real.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) δ₁) δ₂) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.cthickening.{u1} α _inst_1 ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) δ₁) E) (Metric.thickening.{u1} α _inst_1 δ₂ E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : NNReal} {δ₂ : Real}, (LT.lt.{0} Real Real.instLTReal (NNReal.toReal δ₁) δ₂) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.cthickening.{u1} α _inst_1 (NNReal.toReal δ₁) E) (Metric.thickening.{u1} α _inst_1 δ₂ E))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_subset_thickening Metric.cthickening_subset_thickeningₓ'. -/
theorem cthickening_subset_thickening {δ₁ : ℝ≥0} {δ₂ : ℝ} (hlt : (δ₁ : ℝ) < δ₂) (E : Set α) :
    cthickening δ₁ E ⊆ thickening δ₂ E := fun _ hx =>
  lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt δ₁.Prop hlt)).mpr hlt)
#align metric.cthickening_subset_thickening Metric.cthickening_subset_thickening

/- warning: metric.cthickening_subset_thickening' -> Metric.cthickening_subset_thickening' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : Real} {δ₂ : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ₂) -> (LT.lt.{0} Real Real.hasLt δ₁ δ₂) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ₁ E) (Metric.thickening.{u1} α _inst_1 δ₂ E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : Real} {δ₂ : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ₂) -> (LT.lt.{0} Real Real.instLTReal δ₁ δ₂) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ₁ E) (Metric.thickening.{u1} α _inst_1 δ₂ E))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_subset_thickening' Metric.cthickening_subset_thickening'ₓ'. -/
/-- The closed thickening `cthickening δ₁ E` is contained in the open thickening `thickening δ₂ E`
if the radius of the latter is positive and larger. -/
theorem cthickening_subset_thickening' {δ₁ δ₂ : ℝ} (δ₂_pos : 0 < δ₂) (hlt : δ₁ < δ₂) (E : Set α) :
    cthickening δ₁ E ⊆ thickening δ₂ E := fun _ hx =>
  lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff δ₂_pos).mpr hlt)
#align metric.cthickening_subset_thickening' Metric.cthickening_subset_thickening'

#print Metric.thickening_subset_cthickening /-
/-- The open thickening `thickening δ E` is contained in the closed thickening `cthickening δ E`
with the same radius. -/
theorem thickening_subset_cthickening (δ : ℝ) (E : Set α) : thickening δ E ⊆ cthickening δ E :=
  by
  intro x hx
  rw [thickening, mem_set_of_eq] at hx
  exact hx.le
#align metric.thickening_subset_cthickening Metric.thickening_subset_cthickening
-/

/- warning: metric.thickening_subset_cthickening_of_le -> Metric.thickening_subset_cthickening_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : Real} {δ₂ : Real}, (LE.le.{0} Real Real.hasLe δ₁ δ₂) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.thickening.{u1} α _inst_1 δ₁ E) (Metric.cthickening.{u1} α _inst_1 δ₂ E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : Real} {δ₂ : Real}, (LE.le.{0} Real Real.instLEReal δ₁ δ₂) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.thickening.{u1} α _inst_1 δ₁ E) (Metric.cthickening.{u1} α _inst_1 δ₂ E))
Case conversion may be inaccurate. Consider using '#align metric.thickening_subset_cthickening_of_le Metric.thickening_subset_cthickening_of_leₓ'. -/
theorem thickening_subset_cthickening_of_le {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    thickening δ₁ E ⊆ cthickening δ₂ E :=
  (thickening_subset_cthickening δ₁ E).trans (cthickening_mono hle E)
#align metric.thickening_subset_cthickening_of_le Metric.thickening_subset_cthickening_of_le

#print Metric.Bounded.cthickening /-
theorem Bounded.cthickening {α : Type _} [PseudoMetricSpace α] {δ : ℝ} {E : Set α} (h : Bounded E) :
    Bounded (cthickening δ E) :=
  by
  have : bounded (thickening (max (δ + 1) 1) E) := h.thickening
  apply bounded.mono _ this
  exact
    cthickening_subset_thickening' (zero_lt_one.trans_le (le_max_right _ _))
      ((lt_add_one _).trans_le (le_max_left _ _)) _
#align metric.bounded.cthickening Metric.Bounded.cthickening
-/

#print Metric.thickening_subset_interior_cthickening /-
theorem thickening_subset_interior_cthickening (δ : ℝ) (E : Set α) :
    thickening δ E ⊆ interior (cthickening δ E) :=
  (subset_interior_iff_isOpen.mpr isOpen_thickening).trans
    (interior_mono (thickening_subset_cthickening δ E))
#align metric.thickening_subset_interior_cthickening Metric.thickening_subset_interior_cthickening
-/

#print Metric.closure_thickening_subset_cthickening /-
theorem closure_thickening_subset_cthickening (δ : ℝ) (E : Set α) :
    closure (thickening δ E) ⊆ cthickening δ E :=
  (closure_mono (thickening_subset_cthickening δ E)).trans isClosed_cthickening.closure_subset
#align metric.closure_thickening_subset_cthickening Metric.closure_thickening_subset_cthickening
-/

#print Metric.closure_subset_cthickening /-
/-- The closed thickening of a set contains the closure of the set. -/
theorem closure_subset_cthickening (δ : ℝ) (E : Set α) : closure E ⊆ cthickening δ E :=
  by
  rw [← cthickening_of_nonpos (min_le_right δ 0)]
  exact cthickening_mono (min_le_left δ 0) E
#align metric.closure_subset_cthickening Metric.closure_subset_cthickening
-/

/- warning: metric.closure_subset_thickening -> Metric.closure_subset_thickening is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (Metric.thickening.{u1} α _inst_1 δ E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (Metric.thickening.{u1} α _inst_1 δ E))
Case conversion may be inaccurate. Consider using '#align metric.closure_subset_thickening Metric.closure_subset_thickeningₓ'. -/
/-- The (open) thickening of a set contains the closure of the set. -/
theorem closure_subset_thickening {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    closure E ⊆ thickening δ E := by
  rw [← cthickening_zero]
  exact cthickening_subset_thickening' δ_pos δ_pos E
#align metric.closure_subset_thickening Metric.closure_subset_thickening

/- warning: metric.self_subset_thickening -> Metric.self_subset_thickening is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) E (Metric.thickening.{u1} α _inst_1 δ E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (forall (E : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) E (Metric.thickening.{u1} α _inst_1 δ E))
Case conversion may be inaccurate. Consider using '#align metric.self_subset_thickening Metric.self_subset_thickeningₓ'. -/
/-- A set is contained in its own (open) thickening. -/
theorem self_subset_thickening {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) : E ⊆ thickening δ E :=
  (@subset_closure _ _ E).trans (closure_subset_thickening δ_pos E)
#align metric.self_subset_thickening Metric.self_subset_thickening

#print Metric.self_subset_cthickening /-
/-- A set is contained in its own closed thickening. -/
theorem self_subset_cthickening {δ : ℝ} (E : Set α) : E ⊆ cthickening δ E :=
  subset_closure.trans (closure_subset_cthickening δ E)
#align metric.self_subset_cthickening Metric.self_subset_cthickening
-/

/- warning: metric.thickening_mem_nhds_set -> Metric.thickening_mem_nhdsSet is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α) {δ : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Metric.thickening.{u1} α _inst_1 δ E) (nhdsSet.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α) {δ : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (Metric.thickening.{u1} α _inst_1 δ E) (nhdsSet.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E))
Case conversion may be inaccurate. Consider using '#align metric.thickening_mem_nhds_set Metric.thickening_mem_nhdsSetₓ'. -/
theorem thickening_mem_nhdsSet (E : Set α) {δ : ℝ} (hδ : 0 < δ) : thickening δ E ∈ 𝓝ˢ E :=
  isOpen_thickening.mem_nhdsSet.2 <| self_subset_thickening hδ E
#align metric.thickening_mem_nhds_set Metric.thickening_mem_nhdsSet

/- warning: metric.cthickening_mem_nhds_set -> Metric.cthickening_mem_nhdsSet is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α) {δ : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (nhdsSet.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α) {δ : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (nhdsSet.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_mem_nhds_set Metric.cthickening_mem_nhdsSetₓ'. -/
theorem cthickening_mem_nhdsSet (E : Set α) {δ : ℝ} (hδ : 0 < δ) : cthickening δ E ∈ 𝓝ˢ E :=
  mem_of_superset (thickening_mem_nhdsSet E hδ) (thickening_subset_cthickening _ _)
#align metric.cthickening_mem_nhds_set Metric.cthickening_mem_nhdsSet

#print Metric.thickening_union /-
@[simp]
theorem thickening_union (δ : ℝ) (s t : Set α) :
    thickening δ (s ∪ t) = thickening δ s ∪ thickening δ t := by
  simp_rw [thickening, inf_edist_union, inf_eq_min, min_lt_iff, set_of_or]
#align metric.thickening_union Metric.thickening_union
-/

#print Metric.cthickening_union /-
@[simp]
theorem cthickening_union (δ : ℝ) (s t : Set α) :
    cthickening δ (s ∪ t) = cthickening δ s ∪ cthickening δ t := by
  simp_rw [cthickening, inf_edist_union, inf_eq_min, min_le_iff, set_of_or]
#align metric.cthickening_union Metric.cthickening_union
-/

/- warning: metric.thickening_Union -> Metric.thickening_iUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u2}} {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) (f : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Metric.thickening.{u1} α _inst_1 δ (Set.iUnion.{u1, u2} α ι (fun (i : ι) => f i))) (Set.iUnion.{u1, u2} α ι (fun (i : ι) => Metric.thickening.{u1} α _inst_1 δ (f i)))
but is expected to have type
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} α] (δ : Real) (f : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Metric.thickening.{u2} α _inst_1 δ (Set.iUnion.{u2, u1} α ι (fun (i : ι) => f i))) (Set.iUnion.{u2, u1} α ι (fun (i : ι) => Metric.thickening.{u2} α _inst_1 δ (f i)))
Case conversion may be inaccurate. Consider using '#align metric.thickening_Union Metric.thickening_iUnionₓ'. -/
@[simp]
theorem thickening_iUnion (δ : ℝ) (f : ι → Set α) :
    thickening δ (⋃ i, f i) = ⋃ i, thickening δ (f i) := by
  simp_rw [thickening, inf_edist_Union, iInf_lt_iff, set_of_exists]
#align metric.thickening_Union Metric.thickening_iUnion

/- warning: metric.ediam_cthickening_le -> Metric.ediam_cthickening_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} (ε : NNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α _inst_1 (Metric.cthickening.{u1} α _inst_1 ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) ε) s)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EMetric.diam.{u1} α _inst_1 s) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (OfNat.ofNat.{0} ENNReal 2 (OfNat.mk.{0} ENNReal 2 (bit0.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) ε)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} (ε : NNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α _inst_1 (Metric.cthickening.{u1} α _inst_1 (NNReal.toReal ε) s)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EMetric.diam.{u1} α _inst_1 s) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (OfNat.ofNat.{0} ENNReal 2 (instOfNat.{0} ENNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (ENNReal.some ε)))
Case conversion may be inaccurate. Consider using '#align metric.ediam_cthickening_le Metric.ediam_cthickening_leₓ'. -/
theorem ediam_cthickening_le (ε : ℝ≥0) : EMetric.diam (cthickening ε s) ≤ EMetric.diam s + 2 * ε :=
  by
  refine' diam_le fun x hx y hy => ENNReal.le_of_forall_pos_le_add fun δ hδ _ => _
  rw [mem_cthickening_iff, ENNReal.ofReal_coe_nnreal] at hx hy
  have hε : (ε : ℝ≥0∞) < ε + ↑(δ / 2) := ENNReal.coe_lt_coe.2 (lt_add_of_pos_right _ <| half_pos hδ)
  rw [ENNReal.coe_div two_ne_zero, ENNReal.coe_two] at hε
  replace hx := hx.trans_lt hε
  replace hy := hy.trans_lt hε
  rw [inf_edist_lt_iff] at hx hy
  obtain ⟨x', hx', hxx'⟩ := hx
  obtain ⟨y', hy', hyy'⟩ := hy
  refine'
    (edist_triangle_right _ _ _).trans
      ((add_le_add hxx'.le <|
            (edist_triangle _ _ _).trans <|
              add_le_add hyy'.le <| edist_le_diam_of_mem hy' hx').trans_eq
        _)
  -- Now we're done, but `ring` won't do it because we're on `ennreal` :(
  rw [← add_assoc, ← two_mul, mul_add, ENNReal.mul_div_cancel' two_ne_zero ENNReal.two_ne_top]
  abel
#align metric.ediam_cthickening_le Metric.ediam_cthickening_le

/- warning: metric.ediam_thickening_le -> Metric.ediam_thickening_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} (ε : NNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α _inst_1 (Metric.thickening.{u1} α _inst_1 ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) ε) s)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EMetric.diam.{u1} α _inst_1 s) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (OfNat.ofNat.{0} ENNReal 2 (OfNat.mk.{0} ENNReal 2 (bit0.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) ε)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} (ε : NNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α _inst_1 (Metric.thickening.{u1} α _inst_1 (NNReal.toReal ε) s)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EMetric.diam.{u1} α _inst_1 s) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (OfNat.ofNat.{0} ENNReal 2 (instOfNat.{0} ENNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (ENNReal.some ε)))
Case conversion may be inaccurate. Consider using '#align metric.ediam_thickening_le Metric.ediam_thickening_leₓ'. -/
theorem ediam_thickening_le (ε : ℝ≥0) : EMetric.diam (thickening ε s) ≤ EMetric.diam s + 2 * ε :=
  (EMetric.diam_mono <| thickening_subset_cthickening _ _).trans <| ediam_cthickening_le _
#align metric.ediam_thickening_le Metric.ediam_thickening_le

/- warning: metric.diam_cthickening_le -> Metric.diam_cthickening_le is a dubious translation:
lean 3 declaration is
  forall {ε : Real} {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] (s : Set.{u1} α), (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (LE.le.{0} Real Real.hasLe (Metric.diam.{u1} α _inst_2 (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) ε s)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Metric.diam.{u1} α _inst_2 s) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) ε)))
but is expected to have type
  forall {ε : Real} {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] (s : Set.{u1} α), (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (LE.le.{0} Real Real.instLEReal (Metric.diam.{u1} α _inst_2 (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) ε s)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Metric.diam.{u1} α _inst_2 s) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) ε)))
Case conversion may be inaccurate. Consider using '#align metric.diam_cthickening_le Metric.diam_cthickening_leₓ'. -/
theorem diam_cthickening_le {α : Type _} [PseudoMetricSpace α] (s : Set α) (hε : 0 ≤ ε) :
    diam (cthickening ε s) ≤ diam s + 2 * ε :=
  by
  by_cases hs : bounded (cthickening ε s)
  · replace hs := hs.mono (self_subset_cthickening _)
    lift ε to ℝ≥0 using hε
    have : (2 : ℝ≥0∞) * ε ≠ ⊤ := by simp [ENNReal.mul_eq_top]
    refine'
      (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hs.ediam_ne_top, this⟩) <|
            ediam_cthickening_le ε).trans_eq
        _
    simp [ENNReal.toReal_add hs.ediam_ne_top this, diam]
  · rw [diam_eq_zero_of_unbounded hs]
    positivity
#align metric.diam_cthickening_le Metric.diam_cthickening_le

/- warning: metric.diam_thickening_le -> Metric.diam_thickening_le is a dubious translation:
lean 3 declaration is
  forall {ε : Real} {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] (s : Set.{u1} α), (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (LE.le.{0} Real Real.hasLe (Metric.diam.{u1} α _inst_2 (Metric.thickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) ε s)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Metric.diam.{u1} α _inst_2 s) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) ε)))
but is expected to have type
  forall {ε : Real} {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] (s : Set.{u1} α), (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (LE.le.{0} Real Real.instLEReal (Metric.diam.{u1} α _inst_2 (Metric.thickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) ε s)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Metric.diam.{u1} α _inst_2 s) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) ε)))
Case conversion may be inaccurate. Consider using '#align metric.diam_thickening_le Metric.diam_thickening_leₓ'. -/
theorem diam_thickening_le {α : Type _} [PseudoMetricSpace α] (s : Set α) (hε : 0 ≤ ε) :
    diam (thickening ε s) ≤ diam s + 2 * ε :=
  by
  by_cases hs : bounded s
  ·
    exact
      (diam_mono (thickening_subset_cthickening _ _) hs.cthickening).trans
        (diam_cthickening_le _ hε)
  obtain rfl | hε := hε.eq_or_lt
  · simp [thickening_of_nonpos, diam_nonneg]
  · rw [diam_eq_zero_of_unbounded (mt (bounded.mono <| self_subset_thickening hε _) hs)]
    positivity
#align metric.diam_thickening_le Metric.diam_thickening_le

#print Metric.thickening_closure /-
@[simp]
theorem thickening_closure : thickening δ (closure s) = thickening δ s := by
  simp_rw [thickening, inf_edist_closure]
#align metric.thickening_closure Metric.thickening_closure
-/

#print Metric.cthickening_closure /-
@[simp]
theorem cthickening_closure : cthickening δ (closure s) = cthickening δ s := by
  simp_rw [cthickening, inf_edist_closure]
#align metric.cthickening_closure Metric.cthickening_closure
-/

open ENNReal

/- warning: disjoint.exists_thickenings -> Disjoint.exists_thickenings is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (Exists.{1} Real (fun (δ : Real) => And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Metric.thickening.{u1} α _inst_1 δ s) (Metric.thickening.{u1} α _inst_1 δ t))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t) -> (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (Exists.{1} Real (fun (δ : Real) => And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Metric.thickening.{u1} α _inst_1 δ s) (Metric.thickening.{u1} α _inst_1 δ t))))
Case conversion may be inaccurate. Consider using '#align disjoint.exists_thickenings Disjoint.exists_thickeningsₓ'. -/
theorem Disjoint.exists_thickenings (hst : Disjoint s t) (hs : IsCompact s) (ht : IsClosed t) :
    ∃ δ, 0 < δ ∧ Disjoint (thickening δ s) (thickening δ t) :=
  by
  obtain ⟨r, hr, h⟩ := exists_pos_forall_lt_edist hs ht hst
  refine' ⟨r / 2, half_pos (NNReal.coe_pos.2 hr), _⟩
  rw [disjoint_iff_inf_le]
  rintro z ⟨hzs, hzt⟩
  rw [mem_thickening_iff_exists_edist_lt] at hzs hzt
  rw [← NNReal.coe_two, ← NNReal.coe_div, ENNReal.ofReal_coe_nnreal] at hzs hzt
  obtain ⟨x, hx, hzx⟩ := hzs
  obtain ⟨y, hy, hzy⟩ := hzt
  refine' (h x hx y hy).not_le _
  calc
    edist x y ≤ edist z x + edist z y := edist_triangle_left _ _ _
    _ ≤ ↑(r / 2) + ↑(r / 2) := (add_le_add hzx.le hzy.le)
    _ = r := by rw [← ENNReal.coe_add, add_halves]
    
#align disjoint.exists_thickenings Disjoint.exists_thickenings

/- warning: disjoint.exists_cthickenings -> Disjoint.exists_cthickenings is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (Exists.{1} Real (fun (δ : Real) => And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Metric.cthickening.{u1} α _inst_1 δ s) (Metric.cthickening.{u1} α _inst_1 δ t))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t) -> (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (Exists.{1} Real (fun (δ : Real) => And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Metric.cthickening.{u1} α _inst_1 δ s) (Metric.cthickening.{u1} α _inst_1 δ t))))
Case conversion may be inaccurate. Consider using '#align disjoint.exists_cthickenings Disjoint.exists_cthickeningsₓ'. -/
theorem Disjoint.exists_cthickenings (hst : Disjoint s t) (hs : IsCompact s) (ht : IsClosed t) :
    ∃ δ, 0 < δ ∧ Disjoint (cthickening δ s) (cthickening δ t) :=
  by
  obtain ⟨δ, hδ, h⟩ := hst.exists_thickenings hs ht
  refine' ⟨δ / 2, half_pos hδ, h.mono _ _⟩ <;>
    exact cthickening_subset_thickening' hδ (half_lt_self hδ) _
#align disjoint.exists_cthickenings Disjoint.exists_cthickenings

/- warning: is_compact.exists_cthickening_subset_open -> IsCompact.exists_cthickening_subset_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Exists.{1} Real (fun (δ : Real) => And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ s) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (Exists.{1} Real (fun (δ : Real) => And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ s) t)))
Case conversion may be inaccurate. Consider using '#align is_compact.exists_cthickening_subset_open IsCompact.exists_cthickening_subset_openₓ'. -/
theorem IsCompact.exists_cthickening_subset_open (hs : IsCompact s) (ht : IsOpen t) (hst : s ⊆ t) :
    ∃ δ, 0 < δ ∧ cthickening δ s ⊆ t :=
  (hst.disjoint_compl_right.exists_cthickenings hs ht.isClosed_compl).imp fun δ h =>
    ⟨h.1, disjoint_compl_right_iff_subset.1 <| h.2.mono_right <| self_subset_cthickening _⟩
#align is_compact.exists_cthickening_subset_open IsCompact.exists_cthickening_subset_open

/- warning: is_compact.exists_thickening_subset_open -> IsCompact.exists_thickening_subset_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Exists.{1} Real (fun (δ : Real) => And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.thickening.{u1} α _inst_1 δ s) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (Exists.{1} Real (fun (δ : Real) => And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.thickening.{u1} α _inst_1 δ s) t)))
Case conversion may be inaccurate. Consider using '#align is_compact.exists_thickening_subset_open IsCompact.exists_thickening_subset_openₓ'. -/
theorem IsCompact.exists_thickening_subset_open (hs : IsCompact s) (ht : IsOpen t) (hst : s ⊆ t) :
    ∃ δ, 0 < δ ∧ thickening δ s ⊆ t :=
  let ⟨δ, h₀, hδ⟩ := hs.exists_cthickening_subset_open ht hst
  ⟨δ, h₀, (thickening_subset_cthickening _ _).trans hδ⟩
#align is_compact.exists_thickening_subset_open IsCompact.exists_thickening_subset_open

/- warning: metric.has_basis_nhds_set_thickening -> Metric.hasBasis_nhdsSet_thickening is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {K : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) K) -> (Filter.HasBasis.{u1, 1} α Real (nhdsSet.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) K) (fun (δ : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (fun (δ : Real) => Metric.thickening.{u1} α _inst_1 δ K))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {K : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) K) -> (Filter.HasBasis.{u1, 1} α Real (nhdsSet.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) K) (fun (δ : Real) => LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (fun (δ : Real) => Metric.thickening.{u1} α _inst_1 δ K))
Case conversion may be inaccurate. Consider using '#align metric.has_basis_nhds_set_thickening Metric.hasBasis_nhdsSet_thickeningₓ'. -/
theorem hasBasis_nhdsSet_thickening {K : Set α} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis (fun δ : ℝ => 0 < δ) fun δ => thickening δ K :=
  (hasBasis_nhdsSet K).to_has_basis' (fun U hU => hK.exists_thickening_subset_open hU.1 hU.2)
    fun _ => thickening_mem_nhdsSet K
#align metric.has_basis_nhds_set_thickening Metric.hasBasis_nhdsSet_thickening

/- warning: metric.has_basis_nhds_set_cthickening -> Metric.hasBasis_nhdsSet_cthickening is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {K : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) K) -> (Filter.HasBasis.{u1, 1} α Real (nhdsSet.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) K) (fun (δ : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (fun (δ : Real) => Metric.cthickening.{u1} α _inst_1 δ K))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {K : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) K) -> (Filter.HasBasis.{u1, 1} α Real (nhdsSet.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) K) (fun (δ : Real) => LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (fun (δ : Real) => Metric.cthickening.{u1} α _inst_1 δ K))
Case conversion may be inaccurate. Consider using '#align metric.has_basis_nhds_set_cthickening Metric.hasBasis_nhdsSet_cthickeningₓ'. -/
theorem hasBasis_nhdsSet_cthickening {K : Set α} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis (fun δ : ℝ => 0 < δ) fun δ => cthickening δ K :=
  (hasBasis_nhdsSet K).to_has_basis' (fun U hU => hK.exists_cthickening_subset_open hU.1 hU.2)
    fun _ => cthickening_mem_nhdsSet K
#align metric.has_basis_nhds_set_cthickening Metric.hasBasis_nhdsSet_cthickening

/- warning: metric.cthickening_eq_Inter_cthickening' -> Metric.cthickening_eq_iInter_cthickening' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (s : Set.{0} Real), (HasSubset.Subset.{0} (Set.{0} Real) (Set.hasSubset.{0} Real) s (Set.Ioi.{0} Real Real.preorder δ)) -> (forall (ε : Real), (LT.lt.{0} Real Real.hasLt δ ε) -> (Set.Nonempty.{0} Real (Inter.inter.{0} (Set.{0} Real) (Set.hasInter.{0} Real) s (Set.Ioc.{0} Real Real.preorder δ ε)))) -> (forall (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (Set.iInter.{u1, 1} α Real (fun (ε : Real) => Set.iInter.{u1, 0} α (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) ε s) (fun (H : Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) ε s) => Metric.cthickening.{u1} α _inst_1 ε E))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (s : Set.{0} Real), (HasSubset.Subset.{0} (Set.{0} Real) (Set.instHasSubsetSet.{0} Real) s (Set.Ioi.{0} Real Real.instPreorderReal δ)) -> (forall (ε : Real), (LT.lt.{0} Real Real.instLTReal δ ε) -> (Set.Nonempty.{0} Real (Inter.inter.{0} (Set.{0} Real) (Set.instInterSet.{0} Real) s (Set.Ioc.{0} Real Real.instPreorderReal δ ε)))) -> (forall (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (Set.iInter.{u1, 1} α Real (fun (ε : Real) => Set.iInter.{u1, 0} α (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) ε s) (fun (H : Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) ε s) => Metric.cthickening.{u1} α _inst_1 ε E))))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_eq_Inter_cthickening' Metric.cthickening_eq_iInter_cthickening'ₓ'. -/
theorem cthickening_eq_iInter_cthickening' {δ : ℝ} (s : Set ℝ) (hsδ : s ⊆ Ioi δ)
    (hs : ∀ ε, δ < ε → (s ∩ Ioc δ ε).Nonempty) (E : Set α) :
    cthickening δ E = ⋂ ε ∈ s, cthickening ε E :=
  by
  apply subset.antisymm
  · exact subset_Inter₂ fun _ hε => cthickening_mono (le_of_lt (hsδ hε)) E
  · unfold thickening cthickening
    intro x hx
    simp only [mem_Inter, mem_set_of_eq] at *
    apply ENNReal.le_of_forall_pos_le_add
    intro η η_pos _
    rcases hs (δ + η) (lt_add_of_pos_right _ (nnreal.coe_pos.mpr η_pos)) with ⟨ε, ⟨hsε, hε⟩⟩
    apply ((hx ε hsε).trans (ENNReal.ofReal_le_ofReal hε.2)).trans
    rw [ENNReal.coe_nnreal_eq η]
    exact ENNReal.ofReal_add_le
#align metric.cthickening_eq_Inter_cthickening' Metric.cthickening_eq_iInter_cthickening'

/- warning: metric.cthickening_eq_Inter_cthickening -> Metric.cthickening_eq_iInter_cthickening is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (Set.iInter.{u1, 1} α Real (fun (ε : Real) => Set.iInter.{u1, 0} α (LT.lt.{0} Real Real.hasLt δ ε) (fun (h : LT.lt.{0} Real Real.hasLt δ ε) => Metric.cthickening.{u1} α _inst_1 ε E)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (Set.iInter.{u1, 1} α Real (fun (ε : Real) => Set.iInter.{u1, 0} α (LT.lt.{0} Real Real.instLTReal δ ε) (fun (h : LT.lt.{0} Real Real.instLTReal δ ε) => Metric.cthickening.{u1} α _inst_1 ε E)))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_eq_Inter_cthickening Metric.cthickening_eq_iInter_cthickeningₓ'. -/
theorem cthickening_eq_iInter_cthickening {δ : ℝ} (E : Set α) :
    cthickening δ E = ⋂ (ε : ℝ) (h : δ < ε), cthickening ε E :=
  by
  apply cthickening_eq_Inter_cthickening' (Ioi δ) rfl.subset
  simp_rw [inter_eq_right_iff_subset.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε
#align metric.cthickening_eq_Inter_cthickening Metric.cthickening_eq_iInter_cthickening

/- warning: metric.cthickening_eq_Inter_thickening' -> Metric.cthickening_eq_iInter_thickening' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (forall (s : Set.{0} Real), (HasSubset.Subset.{0} (Set.{0} Real) (Set.hasSubset.{0} Real) s (Set.Ioi.{0} Real Real.preorder δ)) -> (forall (ε : Real), (LT.lt.{0} Real Real.hasLt δ ε) -> (Set.Nonempty.{0} Real (Inter.inter.{0} (Set.{0} Real) (Set.hasInter.{0} Real) s (Set.Ioc.{0} Real Real.preorder δ ε)))) -> (forall (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (Set.iInter.{u1, 1} α Real (fun (ε : Real) => Set.iInter.{u1, 0} α (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) ε s) (fun (H : Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) ε s) => Metric.thickening.{u1} α _inst_1 ε E)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (forall (s : Set.{0} Real), (HasSubset.Subset.{0} (Set.{0} Real) (Set.instHasSubsetSet.{0} Real) s (Set.Ioi.{0} Real Real.instPreorderReal δ)) -> (forall (ε : Real), (LT.lt.{0} Real Real.instLTReal δ ε) -> (Set.Nonempty.{0} Real (Inter.inter.{0} (Set.{0} Real) (Set.instInterSet.{0} Real) s (Set.Ioc.{0} Real Real.instPreorderReal δ ε)))) -> (forall (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (Set.iInter.{u1, 1} α Real (fun (ε : Real) => Set.iInter.{u1, 0} α (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) ε s) (fun (H : Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) ε s) => Metric.thickening.{u1} α _inst_1 ε E)))))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_eq_Inter_thickening' Metric.cthickening_eq_iInter_thickening'ₓ'. -/
theorem cthickening_eq_iInter_thickening' {δ : ℝ} (δ_nn : 0 ≤ δ) (s : Set ℝ) (hsδ : s ⊆ Ioi δ)
    (hs : ∀ ε, δ < ε → (s ∩ Ioc δ ε).Nonempty) (E : Set α) :
    cthickening δ E = ⋂ ε ∈ s, thickening ε E :=
  by
  refine' (subset_Inter₂ fun ε hε => _).antisymm _
  · obtain ⟨ε', hsε', hε'⟩ := hs ε (hsδ hε)
    have ss := cthickening_subset_thickening' (lt_of_le_of_lt δ_nn hε'.1) hε'.1 E
    exact ss.trans (thickening_mono hε'.2 E)
  · rw [cthickening_eq_Inter_cthickening' s hsδ hs E]
    exact Inter₂_mono fun ε hε => thickening_subset_cthickening ε E
#align metric.cthickening_eq_Inter_thickening' Metric.cthickening_eq_iInter_thickening'

/- warning: metric.cthickening_eq_Inter_thickening -> Metric.cthickening_eq_iInter_thickening is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (forall (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (Set.iInter.{u1, 1} α Real (fun (ε : Real) => Set.iInter.{u1, 0} α (LT.lt.{0} Real Real.hasLt δ ε) (fun (h : LT.lt.{0} Real Real.hasLt δ ε) => Metric.thickening.{u1} α _inst_1 ε E))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (forall (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (Set.iInter.{u1, 1} α Real (fun (ε : Real) => Set.iInter.{u1, 0} α (LT.lt.{0} Real Real.instLTReal δ ε) (fun (h : LT.lt.{0} Real Real.instLTReal δ ε) => Metric.thickening.{u1} α _inst_1 ε E))))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_eq_Inter_thickening Metric.cthickening_eq_iInter_thickeningₓ'. -/
theorem cthickening_eq_iInter_thickening {δ : ℝ} (δ_nn : 0 ≤ δ) (E : Set α) :
    cthickening δ E = ⋂ (ε : ℝ) (h : δ < ε), thickening ε E :=
  by
  apply cthickening_eq_Inter_thickening' δ_nn (Ioi δ) rfl.subset
  simp_rw [inter_eq_right_iff_subset.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε
#align metric.cthickening_eq_Inter_thickening Metric.cthickening_eq_iInter_thickening

/- warning: metric.cthickening_eq_Inter_thickening'' -> Metric.cthickening_eq_iInter_thickening'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (Set.iInter.{u1, 1} α Real (fun (ε : Real) => Set.iInter.{u1, 0} α (LT.lt.{0} Real Real.hasLt (LinearOrder.max.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) ε) (fun (h : LT.lt.{0} Real Real.hasLt (LinearOrder.max.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) ε) => Metric.thickening.{u1} α _inst_1 ε E)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α _inst_1 δ E) (Set.iInter.{u1, 1} α Real (fun (ε : Real) => Set.iInter.{u1, 0} α (LT.lt.{0} Real Real.instLTReal (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) ε) (fun (h : LT.lt.{0} Real Real.instLTReal (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) ε) => Metric.thickening.{u1} α _inst_1 ε E)))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_eq_Inter_thickening'' Metric.cthickening_eq_iInter_thickening''ₓ'. -/
theorem cthickening_eq_iInter_thickening'' (δ : ℝ) (E : Set α) :
    cthickening δ E = ⋂ (ε : ℝ) (h : max 0 δ < ε), thickening ε E :=
  by
  rw [← cthickening_max_zero, cthickening_eq_Inter_thickening]
  exact le_max_left _ _
#align metric.cthickening_eq_Inter_thickening'' Metric.cthickening_eq_iInter_thickening''

/- warning: metric.closure_eq_Inter_cthickening' -> Metric.closure_eq_iInter_cthickening' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α) (s : Set.{0} Real), (forall (ε : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Set.Nonempty.{0} Real (Inter.inter.{0} (Set.{0} Real) (Set.hasInter.{0} Real) s (Set.Ioc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε)))) -> (Eq.{succ u1} (Set.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (Set.iInter.{u1, 1} α Real (fun (δ : Real) => Set.iInter.{u1, 0} α (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) δ s) (fun (H : Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) δ s) => Metric.cthickening.{u1} α _inst_1 δ E))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α) (s : Set.{0} Real), (forall (ε : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Set.Nonempty.{0} Real (Inter.inter.{0} (Set.{0} Real) (Set.instInterSet.{0} Real) s (Set.Ioc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε)))) -> (Eq.{succ u1} (Set.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (Set.iInter.{u1, 1} α Real (fun (δ : Real) => Set.iInter.{u1, 0} α (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) δ s) (fun (H : Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) δ s) => Metric.cthickening.{u1} α _inst_1 δ E))))
Case conversion may be inaccurate. Consider using '#align metric.closure_eq_Inter_cthickening' Metric.closure_eq_iInter_cthickening'ₓ'. -/
/-- The closure of a set equals the intersection of its closed thickenings of positive radii
accumulating at zero. -/
theorem closure_eq_iInter_cthickening' (E : Set α) (s : Set ℝ)
    (hs : ∀ ε, 0 < ε → (s ∩ Ioc 0 ε).Nonempty) : closure E = ⋂ δ ∈ s, cthickening δ E :=
  by
  by_cases hs₀ : s ⊆ Ioi 0
  · rw [← cthickening_zero]
    apply cthickening_eq_Inter_cthickening' _ hs₀ hs
  obtain ⟨δ, hδs, δ_nonpos⟩ := not_subset.mp hs₀
  rw [Set.mem_Ioi, not_lt] at δ_nonpos
  apply subset.antisymm
  · exact subset_Inter₂ fun ε _ => closure_subset_cthickening ε E
  · rw [← cthickening_of_nonpos δ_nonpos E]
    exact bInter_subset_of_mem hδs
#align metric.closure_eq_Inter_cthickening' Metric.closure_eq_iInter_cthickening'

/- warning: metric.closure_eq_Inter_cthickening -> Metric.closure_eq_iInter_cthickening is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (Set.iInter.{u1, 1} α Real (fun (δ : Real) => Set.iInter.{u1, 0} α (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (fun (h : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) => Metric.cthickening.{u1} α _inst_1 δ E)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (Set.iInter.{u1, 1} α Real (fun (δ : Real) => Set.iInter.{u1, 0} α (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (fun (h : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) => Metric.cthickening.{u1} α _inst_1 δ E)))
Case conversion may be inaccurate. Consider using '#align metric.closure_eq_Inter_cthickening Metric.closure_eq_iInter_cthickeningₓ'. -/
/-- The closure of a set equals the intersection of its closed thickenings of positive radii. -/
theorem closure_eq_iInter_cthickening (E : Set α) :
    closure E = ⋂ (δ : ℝ) (h : 0 < δ), cthickening δ E :=
  by
  rw [← cthickening_zero]
  exact cthickening_eq_Inter_cthickening E
#align metric.closure_eq_Inter_cthickening Metric.closure_eq_iInter_cthickening

/- warning: metric.closure_eq_Inter_thickening' -> Metric.closure_eq_iInter_thickening' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α) (s : Set.{0} Real), (HasSubset.Subset.{0} (Set.{0} Real) (Set.hasSubset.{0} Real) s (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (forall (ε : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Set.Nonempty.{0} Real (Inter.inter.{0} (Set.{0} Real) (Set.hasInter.{0} Real) s (Set.Ioc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε)))) -> (Eq.{succ u1} (Set.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (Set.iInter.{u1, 1} α Real (fun (δ : Real) => Set.iInter.{u1, 0} α (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) δ s) (fun (H : Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) δ s) => Metric.thickening.{u1} α _inst_1 δ E))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α) (s : Set.{0} Real), (HasSubset.Subset.{0} (Set.{0} Real) (Set.instHasSubsetSet.{0} Real) s (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (forall (ε : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Set.Nonempty.{0} Real (Inter.inter.{0} (Set.{0} Real) (Set.instInterSet.{0} Real) s (Set.Ioc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε)))) -> (Eq.{succ u1} (Set.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (Set.iInter.{u1, 1} α Real (fun (δ : Real) => Set.iInter.{u1, 0} α (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) δ s) (fun (H : Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) δ s) => Metric.thickening.{u1} α _inst_1 δ E))))
Case conversion may be inaccurate. Consider using '#align metric.closure_eq_Inter_thickening' Metric.closure_eq_iInter_thickening'ₓ'. -/
/-- The closure of a set equals the intersection of its open thickenings of positive radii
accumulating at zero. -/
theorem closure_eq_iInter_thickening' (E : Set α) (s : Set ℝ) (hs₀ : s ⊆ Ioi 0)
    (hs : ∀ ε, 0 < ε → (s ∩ Ioc 0 ε).Nonempty) : closure E = ⋂ δ ∈ s, thickening δ E :=
  by
  rw [← cthickening_zero]
  apply cthickening_eq_Inter_thickening' le_rfl _ hs₀ hs
#align metric.closure_eq_Inter_thickening' Metric.closure_eq_iInter_thickening'

/- warning: metric.closure_eq_Inter_thickening -> Metric.closure_eq_iInter_thickening is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (Set.iInter.{u1, 1} α Real (fun (δ : Real) => Set.iInter.{u1, 0} α (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (fun (h : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) => Metric.thickening.{u1} α _inst_1 δ E)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (E : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (Set.iInter.{u1, 1} α Real (fun (δ : Real) => Set.iInter.{u1, 0} α (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (fun (h : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) => Metric.thickening.{u1} α _inst_1 δ E)))
Case conversion may be inaccurate. Consider using '#align metric.closure_eq_Inter_thickening Metric.closure_eq_iInter_thickeningₓ'. -/
/-- The closure of a set equals the intersection of its (open) thickenings of positive radii. -/
theorem closure_eq_iInter_thickening (E : Set α) :
    closure E = ⋂ (δ : ℝ) (h : 0 < δ), thickening δ E :=
  by
  rw [← cthickening_zero]
  exact cthickening_eq_Inter_thickening rfl.ge E
#align metric.closure_eq_Inter_thickening Metric.closure_eq_iInter_thickening

#print Metric.frontier_cthickening_subset /-
/-- The frontier of the closed thickening of a set is contained in an `inf_edist` level set. -/
theorem frontier_cthickening_subset (E : Set α) {δ : ℝ} :
    frontier (cthickening δ E) ⊆ { x : α | infEdist x E = ENNReal.ofReal δ } :=
  frontier_le_subset_eq continuous_infEdist continuous_const
#align metric.frontier_cthickening_subset Metric.frontier_cthickening_subset
-/

#print Metric.closedBall_subset_cthickening /-
/-- The closed ball of radius `δ` centered at a point of `E` is included in the closed
thickening of `E`. -/
theorem closedBall_subset_cthickening {α : Type _} [PseudoMetricSpace α] {x : α} {E : Set α}
    (hx : x ∈ E) (δ : ℝ) : closedBall x δ ⊆ cthickening δ E :=
  by
  refine' (closed_ball_subset_cthickening_singleton _ _).trans (cthickening_subset_of_subset _ _)
  simpa using hx
#align metric.closed_ball_subset_cthickening Metric.closedBall_subset_cthickening
-/

/- warning: metric.cthickening_subset_Union_closed_ball_of_lt -> Metric.cthickening_subset_iUnion_closedBall_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] (E : Set.{u1} α) {δ : Real} {δ' : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ') -> (LT.lt.{0} Real Real.hasLt δ δ') -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) δ E) (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x E) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x E) => Metric.closedBall.{u1} α _inst_2 x δ'))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] (E : Set.{u1} α) {δ : Real} {δ' : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ') -> (LT.lt.{0} Real Real.instLTReal δ δ') -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) δ E) (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x E) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x E) => Metric.closedBall.{u1} α _inst_2 x δ'))))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_subset_Union_closed_ball_of_lt Metric.cthickening_subset_iUnion_closedBall_of_ltₓ'. -/
theorem cthickening_subset_iUnion_closedBall_of_lt {α : Type _} [PseudoMetricSpace α] (E : Set α)
    {δ δ' : ℝ} (hδ₀ : 0 < δ') (hδδ' : δ < δ') : cthickening δ E ⊆ ⋃ x ∈ E, closedBall x δ' :=
  by
  refine' (cthickening_subset_thickening' hδ₀ hδδ' E).trans fun x hx => _
  obtain ⟨y, hy₁, hy₂⟩ := mem_thickening_iff.mp hx
  exact mem_Union₂.mpr ⟨y, hy₁, hy₂.le⟩
#align metric.cthickening_subset_Union_closed_ball_of_lt Metric.cthickening_subset_iUnion_closedBall_of_lt

/- warning: is_compact.cthickening_eq_bUnion_closed_ball -> IsCompact.cthickening_eq_biUnion_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] {δ : Real} {E : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) E) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) δ E) (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x E) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x E) => Metric.closedBall.{u1} α _inst_2 x δ))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] {δ : Real} {E : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) E) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) δ E) (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x E) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x E) => Metric.closedBall.{u1} α _inst_2 x δ))))
Case conversion may be inaccurate. Consider using '#align is_compact.cthickening_eq_bUnion_closed_ball IsCompact.cthickening_eq_biUnion_closedBallₓ'. -/
/-- The closed thickening of a compact set `E` is the union of the balls `closed_ball x δ` over
`x ∈ E`.

See also `metric.cthickening_eq_bUnion_closed_ball`. -/
theorem IsCompact.cthickening_eq_biUnion_closedBall {α : Type _} [PseudoMetricSpace α] {δ : ℝ}
    {E : Set α} (hE : IsCompact E) (hδ : 0 ≤ δ) : cthickening δ E = ⋃ x ∈ E, closedBall x δ :=
  by
  rcases eq_empty_or_nonempty E with (rfl | hne)
  · simp only [cthickening_empty, Union_false, Union_empty]
  refine'
    subset.antisymm (fun x hx => _) (Union₂_subset fun x hx => closed_ball_subset_cthickening hx _)
  obtain ⟨y, yE, hy⟩ : ∃ y ∈ E, inf_edist x E = edist x y := hE.exists_inf_edist_eq_edist hne _
  have D1 : edist x y ≤ ENNReal.ofReal δ := (le_of_eq hy.symm).trans hx
  have D2 : dist x y ≤ δ := by
    rw [edist_dist] at D1
    exact (ENNReal.ofReal_le_ofReal_iff hδ).1 D1
  exact mem_bUnion yE D2
#align is_compact.cthickening_eq_bUnion_closed_ball IsCompact.cthickening_eq_biUnion_closedBall

/- warning: metric.cthickening_eq_bUnion_closed_ball -> Metric.cthickening_eq_biUnion_closedBall is a dubious translation:
lean 3 declaration is
  forall {δ : Real} {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] [_inst_3 : ProperSpace.{u1} α _inst_2] (E : Set.{u1} α), (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) δ E) (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) E)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) E)) => Metric.closedBall.{u1} α _inst_2 x δ))))
but is expected to have type
  forall {δ : Real} {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] [_inst_3 : ProperSpace.{u1} α _inst_2] (E : Set.{u1} α), (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) δ E) (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) E)) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) E)) => Metric.closedBall.{u1} α _inst_2 x δ))))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_eq_bUnion_closed_ball Metric.cthickening_eq_biUnion_closedBallₓ'. -/
theorem cthickening_eq_biUnion_closedBall {α : Type _} [PseudoMetricSpace α] [ProperSpace α]
    (E : Set α) (hδ : 0 ≤ δ) : cthickening δ E = ⋃ x ∈ closure E, closedBall x δ :=
  by
  rcases eq_empty_or_nonempty E with (rfl | hne)
  · simp only [cthickening_empty, Union_false, Union_empty, closure_empty]
  rw [← cthickening_closure]
  refine'
    subset.antisymm (fun x hx => _) (Union₂_subset fun x hx => closed_ball_subset_cthickening hx _)
  obtain ⟨y, yE, hy⟩ : ∃ y ∈ closure E, inf_dist x (closure E) = dist x y :=
    is_closed_closure.exists_inf_dist_eq_dist (closure_nonempty_iff.mpr hne) x
  replace hy : dist x y ≤ δ :=
    (ENNReal.ofReal_le_ofReal_iff hδ).mp
      (((congr_arg ENNReal.ofReal hy.symm).le.trans ENNReal.ofReal_toReal_le).trans hx)
  exact mem_bUnion yE hy
#align metric.cthickening_eq_bUnion_closed_ball Metric.cthickening_eq_biUnion_closedBall

/- warning: is_closed.cthickening_eq_bUnion_closed_ball -> IsClosed.cthickening_eq_biUnion_closedBall is a dubious translation:
lean 3 declaration is
  forall {δ : Real} {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] [_inst_3 : ProperSpace.{u1} α _inst_2] {E : Set.{u1} α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) E) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) δ E) (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x E) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x E) => Metric.closedBall.{u1} α _inst_2 x δ))))
but is expected to have type
  forall {δ : Real} {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] [_inst_3 : ProperSpace.{u1} α _inst_2] {E : Set.{u1} α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) E) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (Eq.{succ u1} (Set.{u1} α) (Metric.cthickening.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_2) δ E) (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x E) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x E) => Metric.closedBall.{u1} α _inst_2 x δ))))
Case conversion may be inaccurate. Consider using '#align is_closed.cthickening_eq_bUnion_closed_ball IsClosed.cthickening_eq_biUnion_closedBallₓ'. -/
theorem IsClosed.cthickening_eq_biUnion_closedBall {α : Type _} [PseudoMetricSpace α]
    [ProperSpace α] {E : Set α} (hE : IsClosed E) (hδ : 0 ≤ δ) :
    cthickening δ E = ⋃ x ∈ E, closedBall x δ := by
  rw [cthickening_eq_bUnion_closed_ball E hδ, hE.closure_eq]
#align is_closed.cthickening_eq_bUnion_closed_ball IsClosed.cthickening_eq_biUnion_closedBall

/- warning: metric.inf_edist_le_inf_edist_cthickening_add -> Metric.infEdist_le_infEdist_cthickening_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} {s : Set.{u1} α} {x : α}, LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.infEdist.{u1} α _inst_1 x s) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EMetric.infEdist.{u1} α _inst_1 x (Metric.cthickening.{u1} α _inst_1 δ s)) (ENNReal.ofReal δ))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} {s : Set.{u1} α} {x : α}, LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.infEdist.{u1} α _inst_1 x s) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EMetric.infEdist.{u1} α _inst_1 x (Metric.cthickening.{u1} α _inst_1 δ s)) (ENNReal.ofReal δ))
Case conversion may be inaccurate. Consider using '#align metric.inf_edist_le_inf_edist_cthickening_add Metric.infEdist_le_infEdist_cthickening_addₓ'. -/
/-- For the equality, see `inf_edist_cthickening`. -/
theorem infEdist_le_infEdist_cthickening_add :
    infEdist x s ≤ infEdist x (cthickening δ s) + ENNReal.ofReal δ :=
  by
  refine' le_of_forall_lt' fun r h => _
  simp_rw [← lt_tsub_iff_right, inf_edist_lt_iff, mem_cthickening_iff] at h
  obtain ⟨y, hy, hxy⟩ := h
  exact
    inf_edist_le_edist_add_inf_edist.trans_lt
      ((ENNReal.add_lt_add_of_lt_of_le (hy.trans_lt ENNReal.ofReal_lt_top).Ne hxy hy).trans_le
        (tsub_add_cancel_of_le <| le_self_add.trans (lt_tsub_iff_left.1 hxy).le).le)
#align metric.inf_edist_le_inf_edist_cthickening_add Metric.infEdist_le_infEdist_cthickening_add

/- warning: metric.inf_edist_le_inf_edist_thickening_add -> Metric.infEdist_le_infEdist_thickening_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} {s : Set.{u1} α} {x : α}, LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.infEdist.{u1} α _inst_1 x s) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EMetric.infEdist.{u1} α _inst_1 x (Metric.thickening.{u1} α _inst_1 δ s)) (ENNReal.ofReal δ))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} {s : Set.{u1} α} {x : α}, LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.infEdist.{u1} α _inst_1 x s) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EMetric.infEdist.{u1} α _inst_1 x (Metric.thickening.{u1} α _inst_1 δ s)) (ENNReal.ofReal δ))
Case conversion may be inaccurate. Consider using '#align metric.inf_edist_le_inf_edist_thickening_add Metric.infEdist_le_infEdist_thickening_addₓ'. -/
/-- For the equality, see `inf_edist_thickening`. -/
theorem infEdist_le_infEdist_thickening_add :
    infEdist x s ≤ infEdist x (thickening δ s) + ENNReal.ofReal δ :=
  infEdist_le_infEdist_cthickening_add.trans <|
    add_le_add_right (infEdist_anti <| thickening_subset_cthickening _ _) _
#align metric.inf_edist_le_inf_edist_thickening_add Metric.infEdist_le_infEdist_thickening_add

/- warning: metric.thickening_thickening_subset -> Metric.thickening_thickening_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (ε : Real) (δ : Real) (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.thickening.{u1} α _inst_1 ε (Metric.thickening.{u1} α _inst_1 δ s)) (Metric.thickening.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ε δ) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (ε : Real) (δ : Real) (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.thickening.{u1} α _inst_1 ε (Metric.thickening.{u1} α _inst_1 δ s)) (Metric.thickening.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) ε δ) s)
Case conversion may be inaccurate. Consider using '#align metric.thickening_thickening_subset Metric.thickening_thickening_subsetₓ'. -/
/-- For the equality, see `thickening_thickening`. -/
@[simp]
theorem thickening_thickening_subset (ε δ : ℝ) (s : Set α) :
    thickening ε (thickening δ s) ⊆ thickening (ε + δ) s :=
  by
  obtain hε | hε := le_total ε 0
  · simp only [thickening_of_nonpos hε, empty_subset]
  obtain hδ | hδ := le_total δ 0
  · simp only [thickening_of_nonpos hδ, thickening_empty, empty_subset]
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, ENNReal.ofReal_add hε hδ]
  exact fun ⟨y, ⟨z, hz, hy⟩, hx⟩ =>
    ⟨z, hz, (edist_triangle _ _ _).trans_lt <| ENNReal.add_lt_add hx hy⟩
#align metric.thickening_thickening_subset Metric.thickening_thickening_subset

/- warning: metric.thickening_cthickening_subset -> Metric.thickening_cthickening_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (ε : Real), (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (forall (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.thickening.{u1} α _inst_1 ε (Metric.cthickening.{u1} α _inst_1 δ s)) (Metric.thickening.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ε δ) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (ε : Real), (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (forall (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.thickening.{u1} α _inst_1 ε (Metric.cthickening.{u1} α _inst_1 δ s)) (Metric.thickening.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) ε δ) s))
Case conversion may be inaccurate. Consider using '#align metric.thickening_cthickening_subset Metric.thickening_cthickening_subsetₓ'. -/
/-- For the equality, see `thickening_cthickening`. -/
@[simp]
theorem thickening_cthickening_subset (ε : ℝ) (hδ : 0 ≤ δ) (s : Set α) :
    thickening ε (cthickening δ s) ⊆ thickening (ε + δ) s :=
  by
  obtain hε | hε := le_total ε 0
  · simp only [thickening_of_nonpos hε, empty_subset]
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, mem_cthickening_iff, ← inf_edist_lt_iff,
    ENNReal.ofReal_add hε hδ]
  rintro ⟨y, hy, hxy⟩
  exact
    inf_edist_le_edist_add_inf_edist.trans_lt
      (ENNReal.add_lt_add_of_lt_of_le (hy.trans_lt ENNReal.ofReal_lt_top).Ne hxy hy)
#align metric.thickening_cthickening_subset Metric.thickening_cthickening_subset

/- warning: metric.cthickening_thickening_subset -> Metric.cthickening_thickening_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {ε : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (forall (δ : Real) (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.cthickening.{u1} α _inst_1 ε (Metric.thickening.{u1} α _inst_1 δ s)) (Metric.cthickening.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ε δ) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {ε : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (forall (δ : Real) (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.cthickening.{u1} α _inst_1 ε (Metric.thickening.{u1} α _inst_1 δ s)) (Metric.cthickening.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) ε δ) s))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_thickening_subset Metric.cthickening_thickening_subsetₓ'. -/
/-- For the equality, see `cthickening_thickening`. -/
@[simp]
theorem cthickening_thickening_subset (hε : 0 ≤ ε) (δ : ℝ) (s : Set α) :
    cthickening ε (thickening δ s) ⊆ cthickening (ε + δ) s :=
  by
  obtain hδ | hδ := le_total δ 0
  · simp only [thickening_of_nonpos hδ, cthickening_empty, empty_subset]
  intro x
  simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ]
  exact fun hx => inf_edist_le_inf_edist_thickening_add.trans (add_le_add_right hx _)
#align metric.cthickening_thickening_subset Metric.cthickening_thickening_subset

/- warning: metric.cthickening_cthickening_subset -> Metric.cthickening_cthickening_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} {ε : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (forall (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.cthickening.{u1} α _inst_1 ε (Metric.cthickening.{u1} α _inst_1 δ s)) (Metric.cthickening.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ε δ) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} {ε : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (forall (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.cthickening.{u1} α _inst_1 ε (Metric.cthickening.{u1} α _inst_1 δ s)) (Metric.cthickening.{u1} α _inst_1 (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) ε δ) s))
Case conversion may be inaccurate. Consider using '#align metric.cthickening_cthickening_subset Metric.cthickening_cthickening_subsetₓ'. -/
/-- For the equality, see `cthickening_cthickening`. -/
@[simp]
theorem cthickening_cthickening_subset (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (s : Set α) :
    cthickening ε (cthickening δ s) ⊆ cthickening (ε + δ) s :=
  by
  intro x
  simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ]
  exact fun hx => inf_edist_le_inf_edist_cthickening_add.trans (add_le_add_right hx _)
#align metric.cthickening_cthickening_subset Metric.cthickening_cthickening_subset

/- warning: metric.frontier_cthickening_disjoint -> Metric.frontier_cthickening_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (A : Set.{u1} α), Pairwise.{0} NNReal (Function.onFun.{1, succ u1, 1} NNReal (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) (fun (r : NNReal) => frontier.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (Metric.cthickening.{u1} α _inst_1 ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r) A)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (A : Set.{u1} α), Pairwise.{0} NNReal (Function.onFun.{1, succ u1, 1} NNReal (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (fun (r : NNReal) => frontier.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (Metric.cthickening.{u1} α _inst_1 (NNReal.toReal r) A)))
Case conversion may be inaccurate. Consider using '#align metric.frontier_cthickening_disjoint Metric.frontier_cthickening_disjointₓ'. -/
theorem frontier_cthickening_disjoint (A : Set α) :
    Pairwise (Disjoint on fun r : ℝ≥0 => frontier (cthickening r A)) := fun r₁ r₂ hr =>
  ((disjoint_singleton.2 <| by simpa).Preimage _).mono (frontier_cthickening_subset _)
    (frontier_cthickening_subset _)
#align metric.frontier_cthickening_disjoint Metric.frontier_cthickening_disjoint

end Cthickening

--section
end Metric

--namespace
