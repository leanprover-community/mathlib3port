/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.metric_space.antilipschitz
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.Lipschitz
import Mathbin.Topology.UniformSpace.CompleteSeparated

/-!
# Antilipschitz functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that a map `f : α → β` between two (extended) metric spaces is
`antilipschitz_with K`, `K ≥ 0`, if for all `x, y` we have `edist x y ≤ K * edist (f x) (f y)`.
For a metric space, the latter inequality is equivalent to `dist x y ≤ K * dist (f x) (f y)`.

## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjuction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. We do not require `0 < K` in the definition, mostly because
we do not have a `posreal` type.
-/


variable {α : Type _} {β : Type _} {γ : Type _}

open NNReal ENNReal uniformity

open Set Filter Bornology

#print AntilipschitzWith /-
/-- We say that `f : α → β` is `antilipschitz_with K` if for any two points `x`, `y` we have
`edist x y ≤ K * edist (f x) (f y)`. -/
def AntilipschitzWith [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) (f : α → β) :=
  ∀ x y, edist x y ≤ K * edist (f x) (f y)
#align antilipschitz_with AntilipschitzWith
-/

/- warning: antilipschitz_with.edist_lt_top -> AntilipschitzWith.edist_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β _inst_1 (PseudoMetricSpace.toPseudoEMetricSpace.{u2} β _inst_2) K f) -> (forall (x : α) (y : α), LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β _inst_1 (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) K f) -> (forall (x : α) (y : α), LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} α (PseudoEMetricSpace.toEDist.{u2} α _inst_1) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.edist_lt_top AntilipschitzWith.edist_lt_topₓ'. -/
theorem AntilipschitzWith.edist_lt_top [PseudoEMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {f : α → β} (h : AntilipschitzWith K f) (x y : α) : edist x y < ⊤ :=
  (h x y).trans_lt <| ENNReal.mul_lt_top ENNReal.coe_ne_top (edist_ne_top _ _)
#align antilipschitz_with.edist_lt_top AntilipschitzWith.edist_lt_top

/- warning: antilipschitz_with.edist_ne_top -> AntilipschitzWith.edist_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β _inst_1 (PseudoMetricSpace.toPseudoEMetricSpace.{u2} β _inst_2) K f) -> (forall (x : α) (y : α), Ne.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β _inst_1 (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) K f) -> (forall (x : α) (y : α), Ne.{1} ENNReal (EDist.edist.{u2} α (PseudoEMetricSpace.toEDist.{u2} α _inst_1) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.edist_ne_top AntilipschitzWith.edist_ne_topₓ'. -/
theorem AntilipschitzWith.edist_ne_top [PseudoEMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {f : α → β} (h : AntilipschitzWith K f) (x y : α) : edist x y ≠ ⊤ :=
  (h.edist_lt_top x y).Ne
#align antilipschitz_with.edist_ne_top AntilipschitzWith.edist_ne_top

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0} {f : α → β}

/- warning: antilipschitz_with_iff_le_mul_nndist -> antilipschitzWith_iff_le_mul_nndist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, Iff (AntilipschitzWith.{u1, u2} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} β _inst_2) K f) (forall (x : α) (y : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) K (NNDist.nndist.{u2} β (PseudoMetricSpace.toNNDist.{u2} β _inst_2) (f x) (f y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} α] [_inst_2 : PseudoMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, Iff (AntilipschitzWith.{u2, u1} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u2} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) K f) (forall (x : α) (y : α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u2} α (PseudoMetricSpace.toNNDist.{u2} α _inst_1) x y) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) K (NNDist.nndist.{u1} β (PseudoMetricSpace.toNNDist.{u1} β _inst_2) (f x) (f y))))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with_iff_le_mul_nndist antilipschitzWith_iff_le_mul_nndistₓ'. -/
theorem antilipschitzWith_iff_le_mul_nndist :
    AntilipschitzWith K f ↔ ∀ x y, nndist x y ≤ K * nndist (f x) (f y) := by
  simp only [AntilipschitzWith, edist_nndist]; norm_cast
#align antilipschitz_with_iff_le_mul_nndist antilipschitzWith_iff_le_mul_nndist

/- warning: antilipschitz_with.le_mul_nndist -> AntilipschitzWith.le_mul_nndist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} β _inst_2) K f) -> (forall (x : α) (y : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) K (NNDist.nndist.{u2} β (PseudoMetricSpace.toNNDist.{u2} β _inst_2) (f x) (f y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} α] [_inst_2 : PseudoMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u2} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) K f) -> (forall (x : α) (y : α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u2} α (PseudoMetricSpace.toNNDist.{u2} α _inst_1) x y) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) K (NNDist.nndist.{u1} β (PseudoMetricSpace.toNNDist.{u1} β _inst_2) (f x) (f y))))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.le_mul_nndist AntilipschitzWith.le_mul_nndistₓ'. -/
/- warning: antilipschitz_with.of_le_mul_nndist -> AntilipschitzWith.of_le_mul_nndist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (forall (x : α) (y : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) K (NNDist.nndist.{u2} β (PseudoMetricSpace.toNNDist.{u2} β _inst_2) (f x) (f y)))) -> (AntilipschitzWith.{u1, u2} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} β _inst_2) K f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} α] [_inst_2 : PseudoMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (forall (x : α) (y : α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u2} α (PseudoMetricSpace.toNNDist.{u2} α _inst_1) x y) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) K (NNDist.nndist.{u1} β (PseudoMetricSpace.toNNDist.{u1} β _inst_2) (f x) (f y)))) -> (AntilipschitzWith.{u2, u1} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u2} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) K f)
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.of_le_mul_nndist AntilipschitzWith.of_le_mul_nndistₓ'. -/
alias antilipschitzWith_iff_le_mul_nndist ↔
  AntilipschitzWith.le_mul_nndist AntilipschitzWith.of_le_mul_nndist
#align antilipschitz_with.le_mul_nndist AntilipschitzWith.le_mul_nndist
#align antilipschitz_with.of_le_mul_nndist AntilipschitzWith.of_le_mul_nndist

/- warning: antilipschitz_with_iff_le_mul_dist -> antilipschitzWith_iff_le_mul_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, Iff (AntilipschitzWith.{u1, u2} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} β _inst_2) K f) (forall (x : α) (y : α), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) K) (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f x) (f y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} α] [_inst_2 : PseudoMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, Iff (AntilipschitzWith.{u2, u1} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u2} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) K f) (forall (x : α) (y : α), LE.le.{0} Real Real.instLEReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (NNReal.toReal K) (Dist.dist.{u1} β (PseudoMetricSpace.toDist.{u1} β _inst_2) (f x) (f y))))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with_iff_le_mul_dist antilipschitzWith_iff_le_mul_distₓ'. -/
theorem antilipschitzWith_iff_le_mul_dist :
    AntilipschitzWith K f ↔ ∀ x y, dist x y ≤ K * dist (f x) (f y) := by
  simp only [antilipschitzWith_iff_le_mul_nndist, dist_nndist]; norm_cast
#align antilipschitz_with_iff_le_mul_dist antilipschitzWith_iff_le_mul_dist

/- warning: antilipschitz_with.le_mul_dist -> AntilipschitzWith.le_mul_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} β _inst_2) K f) -> (forall (x : α) (y : α), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) K) (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f x) (f y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} α] [_inst_2 : PseudoMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u2} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) K f) -> (forall (x : α) (y : α), LE.le.{0} Real Real.instLEReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (NNReal.toReal K) (Dist.dist.{u1} β (PseudoMetricSpace.toDist.{u1} β _inst_2) (f x) (f y))))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.le_mul_dist AntilipschitzWith.le_mul_distₓ'. -/
/- warning: antilipschitz_with.of_le_mul_dist -> AntilipschitzWith.of_le_mul_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (forall (x : α) (y : α), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) K) (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f x) (f y)))) -> (AntilipschitzWith.{u1, u2} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} β _inst_2) K f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} α] [_inst_2 : PseudoMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (forall (x : α) (y : α), LE.le.{0} Real Real.instLEReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (NNReal.toReal K) (Dist.dist.{u1} β (PseudoMetricSpace.toDist.{u1} β _inst_2) (f x) (f y)))) -> (AntilipschitzWith.{u2, u1} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u2} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) K f)
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.of_le_mul_dist AntilipschitzWith.of_le_mul_distₓ'. -/
alias antilipschitzWith_iff_le_mul_dist ↔
  AntilipschitzWith.le_mul_dist AntilipschitzWith.of_le_mul_dist
#align antilipschitz_with.le_mul_dist AntilipschitzWith.le_mul_dist
#align antilipschitz_with.of_le_mul_dist AntilipschitzWith.of_le_mul_dist

namespace AntilipschitzWith

/- warning: antilipschitz_with.mul_le_nndist -> AntilipschitzWith.mul_le_nndist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} β _inst_2) K f) -> (forall (x : α) (y : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) K) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y)) (NNDist.nndist.{u2} β (PseudoMetricSpace.toNNDist.{u2} β _inst_2) (f x) (f y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} α] [_inst_2 : PseudoMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u2} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) K f) -> (forall (x : α) (y : α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) K) (NNDist.nndist.{u2} α (PseudoMetricSpace.toNNDist.{u2} α _inst_1) x y)) (NNDist.nndist.{u1} β (PseudoMetricSpace.toNNDist.{u1} β _inst_2) (f x) (f y)))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.mul_le_nndist AntilipschitzWith.mul_le_nndistₓ'. -/
theorem mul_le_nndist (hf : AntilipschitzWith K f) (x y : α) :
    K⁻¹ * nndist x y ≤ nndist (f x) (f y) := by
  simpa only [div_eq_inv_mul] using NNReal.div_le_of_le_mul' (hf.le_mul_nndist x y)
#align antilipschitz_with.mul_le_nndist AntilipschitzWith.mul_le_nndist

/- warning: antilipschitz_with.mul_le_dist -> AntilipschitzWith.mul_le_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} β _inst_2) K f) -> (forall (x : α) (y : α), LE.le.{0} Real Real.hasLe (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Inv.inv.{0} Real Real.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) K)) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)) (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f x) (f y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} α] [_inst_2 : PseudoMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u2} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) K f) -> (forall (x : α) (y : α), LE.le.{0} Real Real.instLEReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (NNReal.toReal (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) K)) (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) x y)) (Dist.dist.{u1} β (PseudoMetricSpace.toDist.{u1} β _inst_2) (f x) (f y)))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.mul_le_dist AntilipschitzWith.mul_le_distₓ'. -/
theorem mul_le_dist (hf : AntilipschitzWith K f) (x y : α) :
    (K⁻¹ * dist x y : ℝ) ≤ dist (f x) (f y) := by exact_mod_cast hf.mul_le_nndist x y
#align antilipschitz_with.mul_le_dist AntilipschitzWith.mul_le_dist

end AntilipschitzWith

end Metric

namespace AntilipschitzWith

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]

variable {K : ℝ≥0} {f : α → β}

open Emetric

#print AntilipschitzWith.k /-
-- uses neither `f` nor `hf`
/-- Extract the constant from `hf : antilipschitz_with K f`. This is useful, e.g.,
if `K` is given by a long formula, and we want to reuse this value. -/
@[nolint unused_arguments]
protected def k (hf : AntilipschitzWith K f) : ℝ≥0 :=
  K
#align antilipschitz_with.K AntilipschitzWith.k
-/

/- warning: antilipschitz_with.injective -> AntilipschitzWith.injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : EMetricSpace.{u1} α] [_inst_5 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_4) _inst_5 K f) -> (Function.Injective.{succ u1, succ u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : EMetricSpace.{u2} α] [_inst_5 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β (EMetricSpace.toPseudoEMetricSpace.{u2} α _inst_4) _inst_5 K f) -> (Function.Injective.{succ u2, succ u1} α β f)
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.injective AntilipschitzWith.injectiveₓ'. -/
protected theorem injective {α : Type _} {β : Type _} [EMetricSpace α] [PseudoEMetricSpace β]
    {K : ℝ≥0} {f : α → β} (hf : AntilipschitzWith K f) : Function.Injective f := fun x y h => by
  simpa only [h, edist_self, MulZeroClass.mul_zero, edist_le_zero] using hf x y
#align antilipschitz_with.injective AntilipschitzWith.injective

/- warning: antilipschitz_with.mul_le_edist -> AntilipschitzWith.mul_le_edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β _inst_1 _inst_2 K f) -> (forall (x : α) (y : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (Inv.inv.{0} ENNReal ENNReal.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) K)) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y)) (EDist.edist.{u2} β (PseudoEMetricSpace.toHasEdist.{u2} β _inst_2) (f x) (f y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β _inst_1 _inst_2 K f) -> (forall (x : α) (y : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Inv.inv.{0} ENNReal ENNReal.instInvENNReal (ENNReal.some K)) (EDist.edist.{u2} α (PseudoEMetricSpace.toEDist.{u2} α _inst_1) x y)) (EDist.edist.{u1} β (PseudoEMetricSpace.toEDist.{u1} β _inst_2) (f x) (f y)))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.mul_le_edist AntilipschitzWith.mul_le_edistₓ'. -/
theorem mul_le_edist (hf : AntilipschitzWith K f) (x y : α) :
    (K⁻¹ * edist x y : ℝ≥0∞) ≤ edist (f x) (f y) :=
  by
  rw [mul_comm, ← div_eq_mul_inv]
  exact ENNReal.div_le_of_le_mul' (hf x y)
#align antilipschitz_with.mul_le_edist AntilipschitzWith.mul_le_edist

/- warning: antilipschitz_with.ediam_preimage_le -> AntilipschitzWith.ediam_preimage_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β _inst_1 _inst_2 K f) -> (forall (s : Set.{u2} β), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f s)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) K) (EMetric.diam.{u2} β _inst_2 s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β _inst_1 _inst_2 K f) -> (forall (s : Set.{u1} β), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f s)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some K) (EMetric.diam.{u1} β _inst_2 s)))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.ediam_preimage_le AntilipschitzWith.ediam_preimage_leₓ'. -/
theorem ediam_preimage_le (hf : AntilipschitzWith K f) (s : Set β) : diam (f ⁻¹' s) ≤ K * diam s :=
  diam_le fun x hx y hy => (hf x y).trans <| mul_le_mul_left' (edist_le_diam_of_mem hx hy) K
#align antilipschitz_with.ediam_preimage_le AntilipschitzWith.ediam_preimage_le

/- warning: antilipschitz_with.le_mul_ediam_image -> AntilipschitzWith.le_mul_ediam_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β _inst_1 _inst_2 K f) -> (forall (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α _inst_1 s) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) K) (EMetric.diam.{u2} β _inst_2 (Set.image.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β _inst_1 _inst_2 K f) -> (forall (s : Set.{u2} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u2} α _inst_1 s) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some K) (EMetric.diam.{u1} β _inst_2 (Set.image.{u2, u1} α β f s))))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.le_mul_ediam_image AntilipschitzWith.le_mul_ediam_imageₓ'. -/
theorem le_mul_ediam_image (hf : AntilipschitzWith K f) (s : Set α) : diam s ≤ K * diam (f '' s) :=
  (diam_mono (subset_preimage_image _ _)).trans (hf.ediam_preimage_le (f '' s))
#align antilipschitz_with.le_mul_ediam_image AntilipschitzWith.le_mul_ediam_image

#print AntilipschitzWith.id /-
protected theorem id : AntilipschitzWith 1 (id : α → α) := fun x y => by
  simp only [ENNReal.coe_one, one_mul, id, le_refl]
#align antilipschitz_with.id AntilipschitzWith.id
-/

/- warning: antilipschitz_with.comp -> AntilipschitzWith.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] [_inst_3 : PseudoEMetricSpace.{u3} γ] {Kg : NNReal} {g : β -> γ}, (AntilipschitzWith.{u2, u3} β γ _inst_2 _inst_3 Kg g) -> (forall {Kf : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β _inst_1 _inst_2 Kf f) -> (AntilipschitzWith.{u1, u3} α γ _inst_1 _inst_3 (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) Kf Kg) (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u3} β] [_inst_3 : PseudoEMetricSpace.{u2} γ] {Kg : NNReal} {g : β -> γ}, (AntilipschitzWith.{u3, u2} β γ _inst_2 _inst_3 Kg g) -> (forall {Kf : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u3} α β _inst_1 _inst_2 Kf f) -> (AntilipschitzWith.{u1, u2} α γ _inst_1 _inst_3 (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) Kf Kg) (Function.comp.{succ u1, succ u3, succ u2} α β γ g f)))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.comp AntilipschitzWith.compₓ'. -/
theorem comp {Kg : ℝ≥0} {g : β → γ} (hg : AntilipschitzWith Kg g) {Kf : ℝ≥0} {f : α → β}
    (hf : AntilipschitzWith Kf f) : AntilipschitzWith (Kf * Kg) (g ∘ f) := fun x y =>
  calc
    edist x y ≤ Kf * edist (f x) (f y) := hf x y
    _ ≤ Kf * (Kg * edist (g (f x)) (g (f y))) := (ENNReal.mul_left_mono (hg _ _))
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]
    
#align antilipschitz_with.comp AntilipschitzWith.comp

/- warning: antilipschitz_with.restrict -> AntilipschitzWith.restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β _inst_1 _inst_2 K f) -> (forall (s : Set.{u1} α), AntilipschitzWith.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.pseudoEmetricSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2 K (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β _inst_1 _inst_2 K f) -> (forall (s : Set.{u2} α), AntilipschitzWith.{u2, u1} (Set.Elem.{u2} α s) β (instPseudoEMetricSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2 K (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.restrict AntilipschitzWith.restrictₓ'. -/
theorem restrict (hf : AntilipschitzWith K f) (s : Set α) : AntilipschitzWith K (s.restrict f) :=
  fun x y => hf x y
#align antilipschitz_with.restrict AntilipschitzWith.restrict

/- warning: antilipschitz_with.cod_restrict -> AntilipschitzWith.codRestrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β _inst_1 _inst_2 K f) -> (forall {s : Set.{u2} β} (hs : forall (x : α), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) s), AntilipschitzWith.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 (Subtype.pseudoEmetricSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) _inst_2) K (Set.codRestrict.{u2, succ u1} β α f s hs))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β _inst_1 _inst_2 K f) -> (forall {s : Set.{u1} β} (hs : forall (x : α), Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) s), AntilipschitzWith.{u2, u1} α (Set.Elem.{u1} β s) _inst_1 (instPseudoEMetricSpaceSubtype.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s) _inst_2) K (Set.codRestrict.{u1, succ u2} β α f s hs))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.cod_restrict AntilipschitzWith.codRestrictₓ'. -/
theorem codRestrict (hf : AntilipschitzWith K f) {s : Set β} (hs : ∀ x, f x ∈ s) :
    AntilipschitzWith K (s.codRestrict f hs) := fun x y => hf x y
#align antilipschitz_with.cod_restrict AntilipschitzWith.codRestrict

/- warning: antilipschitz_with.to_right_inv_on' -> AntilipschitzWith.to_rightInvOn' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β} {s : Set.{u1} α}, (AntilipschitzWith.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.pseudoEmetricSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2 K (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f)) -> (forall {g : β -> α} {t : Set.{u2} β}, (Set.MapsTo.{u2, u1} β α g t s) -> (Set.RightInvOn.{u1, u2} α β g f t) -> (LipschitzWith.{u2, u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) α (Subtype.pseudoEmetricSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) _inst_2) _inst_1 K (Set.restrict.{u2, u1} β (fun (ᾰ : β) => α) t g)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β} {s : Set.{u2} α}, (AntilipschitzWith.{u2, u1} (Set.Elem.{u2} α s) β (instPseudoEMetricSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2 K (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f)) -> (forall {g : β -> α} {t : Set.{u1} β}, (Set.MapsTo.{u1, u2} β α g t s) -> (Set.RightInvOn.{u2, u1} α β g f t) -> (LipschitzWith.{u1, u2} (Set.Elem.{u1} β t) α (instPseudoEMetricSpaceSubtype.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x t) _inst_2) _inst_1 K (Set.restrict.{u1, u2} β (fun (ᾰ : β) => α) t g)))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.to_right_inv_on' AntilipschitzWith.to_rightInvOn'ₓ'. -/
theorem to_rightInvOn' {s : Set α} (hf : AntilipschitzWith K (s.restrict f)) {g : β → α} {t : Set β}
    (g_maps : MapsTo g t s) (g_inv : RightInvOn g f t) : LipschitzWith K (t.restrict g) :=
  fun x y => by
  simpa only [restrict_apply, g_inv x.mem, g_inv y.mem, Subtype.edist_eq, Subtype.coe_mk] using
    hf ⟨g x, g_maps x.mem⟩ ⟨g y, g_maps y.mem⟩
#align antilipschitz_with.to_right_inv_on' AntilipschitzWith.to_rightInvOn'

/- warning: antilipschitz_with.to_right_inv_on -> AntilipschitzWith.to_rightInvOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β _inst_1 _inst_2 K f) -> (forall {g : β -> α} {t : Set.{u2} β}, (Set.RightInvOn.{u1, u2} α β g f t) -> (LipschitzWith.{u2, u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) α (Subtype.pseudoEmetricSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) _inst_2) _inst_1 K (Set.restrict.{u2, u1} β (fun (ᾰ : β) => α) t g)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β _inst_1 _inst_2 K f) -> (forall {g : β -> α} {t : Set.{u1} β}, (Set.RightInvOn.{u2, u1} α β g f t) -> (LipschitzWith.{u1, u2} (Set.Elem.{u1} β t) α (instPseudoEMetricSpaceSubtype.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x t) _inst_2) _inst_1 K (Set.restrict.{u1, u2} β (fun (ᾰ : β) => α) t g)))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.to_right_inv_on AntilipschitzWith.to_rightInvOnₓ'. -/
theorem to_rightInvOn (hf : AntilipschitzWith K f) {g : β → α} {t : Set β} (h : RightInvOn g f t) :
    LipschitzWith K (t.restrict g) :=
  (hf.restrict univ).to_rightInvOn' (mapsTo_univ g t) h
#align antilipschitz_with.to_right_inv_on AntilipschitzWith.to_rightInvOn

/- warning: antilipschitz_with.to_right_inverse -> AntilipschitzWith.to_rightInverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β _inst_1 _inst_2 K f) -> (forall {g : β -> α}, (Function.RightInverse.{succ u1, succ u2} α β g f) -> (LipschitzWith.{u2, u1} β α _inst_2 _inst_1 K g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β _inst_1 _inst_2 K f) -> (forall {g : β -> α}, (Function.RightInverse.{succ u2, succ u1} α β g f) -> (LipschitzWith.{u1, u2} β α _inst_2 _inst_1 K g))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.to_right_inverse AntilipschitzWith.to_rightInverseₓ'. -/
theorem to_rightInverse (hf : AntilipschitzWith K f) {g : β → α} (hg : Function.RightInverse g f) :
    LipschitzWith K g := by
  intro x y
  have := hf (g x) (g y)
  rwa [hg x, hg y] at this
#align antilipschitz_with.to_right_inverse AntilipschitzWith.to_rightInverse

/- warning: antilipschitz_with.comap_uniformity_le -> AntilipschitzWith.comap_uniformity_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β _inst_1 _inst_2 K f) -> (LE.le.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Preorder.toHasLe.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.partialOrder.{u1} (Prod.{u1, u1} α α)))) (Filter.comap.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (Prod.map.{u1, u2, u1, u2} α β α β f f) (uniformity.{u2} β (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2))) (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β _inst_1 _inst_2 K f) -> (LE.le.{u2} (Filter.{u2} (Prod.{u2, u2} α α)) (Preorder.toLE.{u2} (Filter.{u2} (Prod.{u2, u2} α α)) (PartialOrder.toPreorder.{u2} (Filter.{u2} (Prod.{u2, u2} α α)) (Filter.instPartialOrderFilter.{u2} (Prod.{u2, u2} α α)))) (Filter.comap.{u2, u1} (Prod.{u2, u2} α α) (Prod.{u1, u1} β β) (Prod.map.{u2, u1, u2, u1} α β α β f f) (uniformity.{u1} β (PseudoEMetricSpace.toUniformSpace.{u1} β _inst_2))) (uniformity.{u2} α (PseudoEMetricSpace.toUniformSpace.{u2} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.comap_uniformity_le AntilipschitzWith.comap_uniformity_leₓ'. -/
theorem comap_uniformity_le (hf : AntilipschitzWith K f) : (𝓤 β).comap (Prod.map f f) ≤ 𝓤 α :=
  by
  refine' ((uniformity_basis_edist.comap _).le_basis_iffₓ uniformity_basis_edist).2 fun ε h₀ => _
  refine' ⟨K⁻¹ * ε, ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top) h₀.ne', _⟩
  refine' fun x hx => (hf x.1 x.2).trans_lt _
  rw [mul_comm, ← div_eq_mul_inv] at hx
  rw [mul_comm]
  exact ENNReal.mul_lt_of_lt_div hx
#align antilipschitz_with.comap_uniformity_le AntilipschitzWith.comap_uniformity_le

/- warning: antilipschitz_with.uniform_inducing -> AntilipschitzWith.uniformInducing is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β _inst_1 _inst_2 K f) -> (UniformContinuous.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) f) -> (UniformInducing.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β _inst_1 _inst_2 K f) -> (UniformContinuous.{u2, u1} α β (PseudoEMetricSpace.toUniformSpace.{u2} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u1} β _inst_2) f) -> (UniformInducing.{u2, u1} α β (PseudoEMetricSpace.toUniformSpace.{u2} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u1} β _inst_2) f)
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.uniform_inducing AntilipschitzWith.uniformInducingₓ'. -/
protected theorem uniformInducing (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    UniformInducing f :=
  ⟨le_antisymm hf.comap_uniformity_le hfc.le_comap⟩
#align antilipschitz_with.uniform_inducing AntilipschitzWith.uniformInducing

/- warning: antilipschitz_with.uniform_embedding -> AntilipschitzWith.uniformEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : EMetricSpace.{u1} α] [_inst_5 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_4) _inst_5 K f) -> (UniformContinuous.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_4)) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_5) f) -> (UniformEmbedding.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_4)) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_5) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : EMetricSpace.{u2} α] [_inst_5 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β (EMetricSpace.toPseudoEMetricSpace.{u2} α _inst_4) _inst_5 K f) -> (UniformContinuous.{u2, u1} α β (PseudoEMetricSpace.toUniformSpace.{u2} α (EMetricSpace.toPseudoEMetricSpace.{u2} α _inst_4)) (PseudoEMetricSpace.toUniformSpace.{u1} β _inst_5) f) -> (UniformEmbedding.{u2, u1} α β (PseudoEMetricSpace.toUniformSpace.{u2} α (EMetricSpace.toPseudoEMetricSpace.{u2} α _inst_4)) (PseudoEMetricSpace.toUniformSpace.{u1} β _inst_5) f)
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.uniform_embedding AntilipschitzWith.uniformEmbeddingₓ'. -/
protected theorem uniformEmbedding {α : Type _} {β : Type _} [EMetricSpace α] [PseudoEMetricSpace β]
    {K : ℝ≥0} {f : α → β} (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    UniformEmbedding f :=
  ⟨hf.UniformInducing hfc, hf.Injective⟩
#align antilipschitz_with.uniform_embedding AntilipschitzWith.uniformEmbedding

/- warning: antilipschitz_with.is_complete_range -> AntilipschitzWith.isComplete_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β} [_inst_4 : CompleteSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)], (AntilipschitzWith.{u1, u2} α β _inst_1 _inst_2 K f) -> (UniformContinuous.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) f) -> (IsComplete.{u2} β (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β} [_inst_4 : CompleteSpace.{u2} α (PseudoEMetricSpace.toUniformSpace.{u2} α _inst_1)], (AntilipschitzWith.{u2, u1} α β _inst_1 _inst_2 K f) -> (UniformContinuous.{u2, u1} α β (PseudoEMetricSpace.toUniformSpace.{u2} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u1} β _inst_2) f) -> (IsComplete.{u1} β (PseudoEMetricSpace.toUniformSpace.{u1} β _inst_2) (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.is_complete_range AntilipschitzWith.isComplete_rangeₓ'. -/
theorem isComplete_range [CompleteSpace α] (hf : AntilipschitzWith K f)
    (hfc : UniformContinuous f) : IsComplete (range f) :=
  (hf.UniformInducing hfc).isComplete_range
#align antilipschitz_with.is_complete_range AntilipschitzWith.isComplete_range

/- warning: antilipschitz_with.is_closed_range -> AntilipschitzWith.isClosed_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : PseudoEMetricSpace.{u1} α] [_inst_5 : EMetricSpace.{u2} β] [_inst_6 : CompleteSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_4)] {f : α -> β} {K : NNReal}, (AntilipschitzWith.{u1, u2} α β _inst_4 (EMetricSpace.toPseudoEmetricSpace.{u2} β _inst_5) K f) -> (UniformContinuous.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_4) (PseudoEMetricSpace.toUniformSpace.{u2} β (EMetricSpace.toPseudoEmetricSpace.{u2} β _inst_5)) f) -> (IsClosed.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoEMetricSpace.toUniformSpace.{u2} β (EMetricSpace.toPseudoEmetricSpace.{u2} β _inst_5))) (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : PseudoEMetricSpace.{u2} α] [_inst_5 : EMetricSpace.{u1} β] [_inst_6 : CompleteSpace.{u2} α (PseudoEMetricSpace.toUniformSpace.{u2} α _inst_4)] {f : α -> β} {K : NNReal}, (AntilipschitzWith.{u2, u1} α β _inst_4 (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_5) K f) -> (UniformContinuous.{u2, u1} α β (PseudoEMetricSpace.toUniformSpace.{u2} α _inst_4) (PseudoEMetricSpace.toUniformSpace.{u1} β (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_5)) f) -> (IsClosed.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoEMetricSpace.toUniformSpace.{u1} β (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_5))) (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.is_closed_range AntilipschitzWith.isClosed_rangeₓ'. -/
theorem isClosed_range {α β : Type _} [PseudoEMetricSpace α] [EMetricSpace β] [CompleteSpace α]
    {f : α → β} {K : ℝ≥0} (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    IsClosed (range f) :=
  (hf.isComplete_range hfc).IsClosed
#align antilipschitz_with.is_closed_range AntilipschitzWith.isClosed_range

/- warning: antilipschitz_with.closed_embedding -> AntilipschitzWith.closedEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : EMetricSpace.{u1} α] [_inst_5 : EMetricSpace.{u2} β] {K : NNReal} {f : α -> β} [_inst_6 : CompleteSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_4))], (AntilipschitzWith.{u1, u2} α β (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_4) (EMetricSpace.toPseudoEmetricSpace.{u2} β _inst_5) K f) -> (UniformContinuous.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_4)) (PseudoEMetricSpace.toUniformSpace.{u2} β (EMetricSpace.toPseudoEmetricSpace.{u2} β _inst_5)) f) -> (ClosedEmbedding.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_4))) (UniformSpace.toTopologicalSpace.{u2} β (PseudoEMetricSpace.toUniformSpace.{u2} β (EMetricSpace.toPseudoEmetricSpace.{u2} β _inst_5))) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : EMetricSpace.{u2} α] [_inst_5 : EMetricSpace.{u1} β] {K : NNReal} {f : α -> β} [_inst_6 : CompleteSpace.{u2} α (PseudoEMetricSpace.toUniformSpace.{u2} α (EMetricSpace.toPseudoEMetricSpace.{u2} α _inst_4))], (AntilipschitzWith.{u2, u1} α β (EMetricSpace.toPseudoEMetricSpace.{u2} α _inst_4) (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_5) K f) -> (UniformContinuous.{u2, u1} α β (PseudoEMetricSpace.toUniformSpace.{u2} α (EMetricSpace.toPseudoEMetricSpace.{u2} α _inst_4)) (PseudoEMetricSpace.toUniformSpace.{u1} β (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_5)) f) -> (ClosedEmbedding.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u2} α (PseudoEMetricSpace.toUniformSpace.{u2} α (EMetricSpace.toPseudoEMetricSpace.{u2} α _inst_4))) (UniformSpace.toTopologicalSpace.{u1} β (PseudoEMetricSpace.toUniformSpace.{u1} β (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_5))) f)
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.closed_embedding AntilipschitzWith.closedEmbeddingₓ'. -/
theorem closedEmbedding {α : Type _} {β : Type _} [EMetricSpace α] [EMetricSpace β] {K : ℝ≥0}
    {f : α → β} [CompleteSpace α] (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    ClosedEmbedding f :=
  { (hf.UniformEmbedding hfc).Embedding with closed_range := hf.isClosed_range hfc }
#align antilipschitz_with.closed_embedding AntilipschitzWith.closedEmbedding

#print AntilipschitzWith.subtype_coe /-
theorem subtype_coe (s : Set α) : AntilipschitzWith 1 (coe : s → α) :=
  AntilipschitzWith.id.restrict s
#align antilipschitz_with.subtype_coe AntilipschitzWith.subtype_coe
-/

/- warning: antilipschitz_with.of_subsingleton -> AntilipschitzWith.of_subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β} [_inst_4 : Subsingleton.{succ u1} α] {K : NNReal}, AntilipschitzWith.{u1, u2} α β _inst_1 _inst_2 K f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoEMetricSpace.{u1} β] {f : α -> β} [_inst_4 : Subsingleton.{succ u2} α] {K : NNReal}, AntilipschitzWith.{u2, u1} α β _inst_1 _inst_2 K f
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.of_subsingleton AntilipschitzWith.of_subsingletonₓ'. -/
theorem of_subsingleton [Subsingleton α] {K : ℝ≥0} : AntilipschitzWith K f := fun x y => by
  simp only [Subsingleton.elim x y, edist_self, zero_le]
#align antilipschitz_with.of_subsingleton AntilipschitzWith.of_subsingleton

/- warning: antilipschitz_with.subsingleton -> AntilipschitzWith.subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : EMetricSpace.{u1} α] [_inst_5 : PseudoEMetricSpace.{u2} β] {f : α -> β}, (AntilipschitzWith.{u1, u2} α β (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_4) _inst_5 (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) f) -> (Subsingleton.{succ u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : EMetricSpace.{u2} α] [_inst_5 : PseudoEMetricSpace.{u1} β] {f : α -> β}, (AntilipschitzWith.{u2, u1} α β (EMetricSpace.toPseudoEMetricSpace.{u2} α _inst_4) _inst_5 (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) f) -> (Subsingleton.{succ u2} α)
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.subsingleton AntilipschitzWith.subsingletonₓ'. -/
/-- If `f : α → β` is `0`-antilipschitz, then `α` is a `subsingleton`. -/
protected theorem subsingleton {α β} [EMetricSpace α] [PseudoEMetricSpace β] {f : α → β}
    (h : AntilipschitzWith 0 f) : Subsingleton α :=
  ⟨fun x y => edist_le_zero.1 <| (h x y).trans_eq <| MulZeroClass.zero_mul _⟩
#align antilipschitz_with.subsingleton AntilipschitzWith.subsingleton

end AntilipschitzWith

namespace AntilipschitzWith

open Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0} {f : α → β}

/- warning: antilipschitz_with.bounded_preimage -> AntilipschitzWith.bounded_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} β _inst_2) K f) -> (forall {s : Set.{u2} β}, (Metric.Bounded.{u2} β _inst_2 s) -> (Metric.Bounded.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} α] [_inst_2 : PseudoMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u2} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) K f) -> (forall {s : Set.{u1} β}, (Metric.Bounded.{u1} β _inst_2 s) -> (Metric.Bounded.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.bounded_preimage AntilipschitzWith.bounded_preimageₓ'. -/
theorem bounded_preimage (hf : AntilipschitzWith K f) {s : Set β} (hs : Bounded s) :
    Bounded (f ⁻¹' s) :=
  Exists.intro (K * diam s) fun x hx y hy =>
    calc
      dist x y ≤ K * dist (f x) (f y) := hf.le_mul_dist x y
      _ ≤ K * diam s := mul_le_mul_of_nonneg_left (dist_le_diam_of_mem hs hx hy) K.2
      
#align antilipschitz_with.bounded_preimage AntilipschitzWith.bounded_preimage

/- warning: antilipschitz_with.tendsto_cobounded -> AntilipschitzWith.tendsto_cobounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u1, u2} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} β _inst_2) K f) -> (Filter.Tendsto.{u1, u2} α β f (Bornology.cobounded.{u1} α (PseudoMetricSpace.toBornology.{u1} α _inst_1)) (Bornology.cobounded.{u2} β (PseudoMetricSpace.toBornology.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} α] [_inst_2 : PseudoMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (AntilipschitzWith.{u2, u1} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u2} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) K f) -> (Filter.Tendsto.{u2, u1} α β f (Bornology.cobounded.{u2} α (PseudoMetricSpace.toBornology.{u2} α _inst_1)) (Bornology.cobounded.{u1} β (PseudoMetricSpace.toBornology.{u1} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align antilipschitz_with.tendsto_cobounded AntilipschitzWith.tendsto_coboundedₓ'. -/
theorem tendsto_cobounded (hf : AntilipschitzWith K f) : Tendsto f (cobounded α) (cobounded β) :=
  compl_surjective.forall.2 fun s (hs : IsBounded s) =>
    Metric.isBounded_iff.2 <| hf.bounded_preimage <| Metric.isBounded_iff.1 hs
#align antilipschitz_with.tendsto_cobounded AntilipschitzWith.tendsto_cobounded

#print AntilipschitzWith.properSpace /-
/-- The image of a proper space under an expanding onto map is proper. -/
protected theorem properSpace {α : Type _} [MetricSpace α] {K : ℝ≥0} {f : α → β} [ProperSpace α]
    (hK : AntilipschitzWith K f) (f_cont : Continuous f) (hf : Function.Surjective f) :
    ProperSpace β :=
  by
  apply properSpace_of_compact_closedBall_of_le 0 fun x₀ r hr => _
  let K := f ⁻¹' closed_ball x₀ r
  have A : IsClosed K := is_closed_ball.preimage f_cont
  have B : bounded K := hK.bounded_preimage bounded_closed_ball
  have : IsCompact K := is_compact_iff_is_closed_bounded.2 ⟨A, B⟩
  convert this.image f_cont
  exact (hf.image_preimage _).symm
#align antilipschitz_with.proper_space AntilipschitzWith.properSpace
-/

end AntilipschitzWith

/- warning: lipschitz_with.to_right_inverse -> LipschitzWith.to_rightInverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {K : NNReal} {f : α -> β}, (LipschitzWith.{u1, u2} α β _inst_1 _inst_2 K f) -> (forall {g : β -> α}, (Function.RightInverse.{succ u1, succ u2} α β g f) -> (AntilipschitzWith.{u2, u1} β α _inst_2 _inst_1 K g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} α] [_inst_2 : PseudoEMetricSpace.{u1} β] {K : NNReal} {f : α -> β}, (LipschitzWith.{u2, u1} α β _inst_1 _inst_2 K f) -> (forall {g : β -> α}, (Function.RightInverse.{succ u2, succ u1} α β g f) -> (AntilipschitzWith.{u1, u2} β α _inst_2 _inst_1 K g))
Case conversion may be inaccurate. Consider using '#align lipschitz_with.to_right_inverse LipschitzWith.to_rightInverseₓ'. -/
theorem LipschitzWith.to_rightInverse [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : ℝ≥0}
    {f : α → β} (hf : LipschitzWith K f) {g : β → α} (hg : Function.RightInverse g f) :
    AntilipschitzWith K g := fun x y => by simpa only [hg _] using hf (g x) (g y)
#align lipschitz_with.to_right_inverse LipschitzWith.to_rightInverse

/- warning: lipschitz_with.proper_space -> LipschitzWith.properSpace is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : MetricSpace.{u2} β] [_inst_3 : ProperSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_2)] {K : NNReal} {f : Homeomorph.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_2)))}, (LipschitzWith.{u1, u2} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_2)) K (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_2)))) (fun (_x : Homeomorph.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_2)))) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_2)))) f)) -> (ProperSpace.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} α] [_inst_2 : MetricSpace.{u1} β] [_inst_3 : ProperSpace.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_2)] {K : NNReal} {f : Homeomorph.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_2)))}, (LipschitzWith.{u2, u1} α β (PseudoMetricSpace.toPseudoEMetricSpace.{u2} α _inst_1) (EMetricSpace.toPseudoEMetricSpace.{u1} β (MetricSpace.toEMetricSpace.{u1} β _inst_2)) K (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_2)))) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_2)))) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_2)))) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_2)))))) f)) -> (ProperSpace.{u2} α _inst_1)
Case conversion may be inaccurate. Consider using '#align lipschitz_with.proper_space LipschitzWith.properSpaceₓ'. -/
/-- The preimage of a proper space under a Lipschitz homeomorphism is proper. -/
@[protected]
theorem LipschitzWith.properSpace [PseudoMetricSpace α] [MetricSpace β] [ProperSpace β] {K : ℝ≥0}
    {f : α ≃ₜ β} (hK : LipschitzWith K f) : ProperSpace α :=
  (hK.to_rightInverse f.right_inv).ProperSpace f.symm.Continuous f.symm.Surjective
#align lipschitz_with.proper_space LipschitzWith.properSpace

