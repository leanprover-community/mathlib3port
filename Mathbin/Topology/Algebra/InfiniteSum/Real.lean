/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module topology.algebra.infinite_sum.real
! leanprover-community/mathlib commit 9a59dcb7a2d06bf55da57b9030169219980660cd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Intervals
import Mathbin.Topology.Algebra.InfiniteSum.Order
import Mathbin.Topology.Instances.Real

/-!
# Infinite sum in the reals

This file provides lemmas about Cauchy sequences in terms of infinite sums.
-/


open Filter Finset

open BigOperators NNReal Topology

variable {α : Type _}

/- warning: cauchy_seq_of_edist_le_of_summable -> cauchySeq_of_edist_le_of_summable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Nat -> α} (d : Nat -> NNReal), (forall (n : Nat), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f n) (f (Nat.succ n))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (d n))) -> (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal NNReal.pseudoMetricSpace)) d) -> (CauchySeq.{u1, 0} α Nat (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Nat -> α} (d : Nat -> NNReal), (forall (n : Nat), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f n) (f (Nat.succ n))) (ENNReal.some (d n))) -> (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) d) -> (CauchySeq.{u1, 0} α Nat (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) f)
Case conversion may be inaccurate. Consider using '#align cauchy_seq_of_edist_le_of_summable cauchySeq_of_edist_le_of_summableₓ'. -/
/-- If the extended distance between consecutive points of a sequence is estimated
by a summable series of `nnreal`s, then the original sequence is a Cauchy sequence. -/
theorem cauchySeq_of_edist_le_of_summable [PseudoEMetricSpace α] {f : ℕ → α} (d : ℕ → ℝ≥0)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : Summable d) : CauchySeq f :=
  by
  refine' EMetric.cauchySeq_iff_NNReal.2 fun ε εpos => _
  -- Actually we need partial sums of `d` to be a Cauchy sequence
  replace hd : CauchySeq fun n : ℕ => ∑ x in range n, d x :=
    let ⟨_, H⟩ := hd
    H.tendsto_sum_nat.cauchy_seq
  -- Now we take the same `N` as in one of the definitions of a Cauchy sequence
  refine' (Metric.cauchySeq_iff'.1 hd ε (NNReal.coe_pos.2 εpos)).imp fun N hN n hn => _
  have hsum := hN n hn
  -- We simplify the known inequality
  rw [dist_nndist, NNReal.nndist_eq, ← sum_range_add_sum_Ico _ hn, add_tsub_cancel_left] at hsum
  norm_cast  at hsum
  replace hsum := lt_of_le_of_lt (le_max_left _ _) hsum
  rw [edist_comm]
  -- Then use `hf` to simplify the goal to the same form
  apply lt_of_le_of_lt (edist_le_Ico_sum_of_edist_le hn fun k _ _ => hf k)
  assumption_mod_cast
#align cauchy_seq_of_edist_le_of_summable cauchySeq_of_edist_le_of_summable

variable [PseudoMetricSpace α] {f : ℕ → α} {a : α}

/- warning: cauchy_seq_of_dist_le_of_summable -> cauchySeq_of_dist_le_of_summable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} (d : Nat -> Real), (forall (n : Nat), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f n) (f (Nat.succ n))) (d n)) -> (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) d) -> (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} (d : Nat -> Real), (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f n) (f (Nat.succ n))) (d n)) -> (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) d) -> (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) f)
Case conversion may be inaccurate. Consider using '#align cauchy_seq_of_dist_le_of_summable cauchySeq_of_dist_le_of_summableₓ'. -/
/-- If the distance between consecutive points of a sequence is estimated by a summable series,
then the original sequence is a Cauchy sequence. -/
theorem cauchySeq_of_dist_le_of_summable (d : ℕ → ℝ) (hf : ∀ n, dist (f n) (f n.succ) ≤ d n)
    (hd : Summable d) : CauchySeq f :=
  by
  refine' Metric.cauchySeq_iff'.2 fun ε εpos => _
  replace hd : CauchySeq fun n : ℕ => ∑ x in range n, d x :=
    let ⟨_, H⟩ := hd
    H.tendsto_sum_nat.cauchy_seq
  refine' (Metric.cauchySeq_iff'.1 hd ε εpos).imp fun N hN n hn => _
  have hsum := hN n hn
  rw [Real.dist_eq, ← sum_Ico_eq_sub _ hn] at hsum
  calc
    dist (f n) (f N) = dist (f N) (f n) := dist_comm _ _
    _ ≤ ∑ x in Ico N n, d x := (dist_le_Ico_sum_of_dist_le hn fun k _ _ => hf k)
    _ ≤ |∑ x in Ico N n, d x| := (le_abs_self _)
    _ < ε := hsum
    
#align cauchy_seq_of_dist_le_of_summable cauchySeq_of_dist_le_of_summable

#print cauchySeq_of_summable_dist /-
theorem cauchySeq_of_summable_dist (h : Summable fun n => dist (f n) (f n.succ)) : CauchySeq f :=
  cauchySeq_of_dist_le_of_summable _ (fun _ => le_rfl) h
#align cauchy_seq_of_summable_dist cauchySeq_of_summable_dist
-/

/- warning: dist_le_tsum_of_dist_le_of_tendsto -> dist_le_tsum_of_dist_le_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} (d : Nat -> Real), (forall (n : Nat), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f n) (f (Nat.succ n))) (d n)) -> (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) d) -> (forall {a : α}, (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f n) a) (tsum.{0, 0} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (m : Nat) => d (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n m)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} (d : Nat -> Real), (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f n) (f (Nat.succ n))) (d n)) -> (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) d) -> (forall {a : α}, (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f n) a) (tsum.{0, 0} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (m : Nat) => d (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n m)))))
Case conversion may be inaccurate. Consider using '#align dist_le_tsum_of_dist_le_of_tendsto dist_le_tsum_of_dist_le_of_tendstoₓ'. -/
theorem dist_le_tsum_of_dist_le_of_tendsto (d : ℕ → ℝ) (hf : ∀ n, dist (f n) (f n.succ) ≤ d n)
    (hd : Summable d) {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ ∑' m, d (n + m) :=
  by
  refine' le_of_tendsto (tendsto_const_nhds.dist ha) (eventually_at_top.2 ⟨n, fun m hnm => _⟩)
  refine' le_trans (dist_le_Ico_sum_of_dist_le hnm fun k _ _ => hf k) _
  rw [sum_Ico_eq_sum_range]
  refine' sum_le_tsum (range _) (fun _ _ => le_trans dist_nonneg (hf _)) _
  exact hd.comp_injective (add_right_injective n)
#align dist_le_tsum_of_dist_le_of_tendsto dist_le_tsum_of_dist_le_of_tendsto

/- warning: dist_le_tsum_of_dist_le_of_tendsto₀ -> dist_le_tsum_of_dist_le_of_tendsto₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} {a : α} (d : Nat -> Real), (forall (n : Nat), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f n) (f (Nat.succ n))) (d n)) -> (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) d) -> (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) a) (tsum.{0, 0} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} {a : α} (d : Nat -> Real), (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f n) (f (Nat.succ n))) (d n)) -> (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) d) -> (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) a) (tsum.{0, 0} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat d))
Case conversion may be inaccurate. Consider using '#align dist_le_tsum_of_dist_le_of_tendsto₀ dist_le_tsum_of_dist_le_of_tendsto₀ₓ'. -/
theorem dist_le_tsum_of_dist_le_of_tendsto₀ (d : ℕ → ℝ) (hf : ∀ n, dist (f n) (f n.succ) ≤ d n)
    (hd : Summable d) (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a ≤ tsum d := by
  simpa only [zero_add] using dist_le_tsum_of_dist_le_of_tendsto d hf hd ha 0
#align dist_le_tsum_of_dist_le_of_tendsto₀ dist_le_tsum_of_dist_le_of_tendsto₀

/- warning: dist_le_tsum_dist_of_tendsto -> dist_le_tsum_dist_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} {a : α}, (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f n) (f (Nat.succ n)))) -> (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f n) a) (tsum.{0, 0} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (m : Nat) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n m)) (f (Nat.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n m))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} {a : α}, (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f n) (f (Nat.succ n)))) -> (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f n) a) (tsum.{0, 0} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (m : Nat) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n m)) (f (Nat.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n m))))))
Case conversion may be inaccurate. Consider using '#align dist_le_tsum_dist_of_tendsto dist_le_tsum_dist_of_tendstoₓ'. -/
theorem dist_le_tsum_dist_of_tendsto (h : Summable fun n => dist (f n) (f n.succ))
    (ha : Tendsto f atTop (𝓝 a)) (n) : dist (f n) a ≤ ∑' m, dist (f (n + m)) (f (n + m).succ) :=
  show dist (f n) a ≤ ∑' m, (fun x => dist (f x) (f x.succ)) (n + m) from
    dist_le_tsum_of_dist_le_of_tendsto (fun n => dist (f n) (f n.succ)) (fun _ => le_rfl) h ha n
#align dist_le_tsum_dist_of_tendsto dist_le_tsum_dist_of_tendsto

/- warning: dist_le_tsum_dist_of_tendsto₀ -> dist_le_tsum_dist_of_tendsto₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} {a : α}, (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f n) (f (Nat.succ n)))) -> (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) a) (tsum.{0, 0} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (n : Nat) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f n) (f (Nat.succ n)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} {a : α}, (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f n) (f (Nat.succ n)))) -> (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) a) (tsum.{0, 0} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (n : Nat) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f n) (f (Nat.succ n)))))
Case conversion may be inaccurate. Consider using '#align dist_le_tsum_dist_of_tendsto₀ dist_le_tsum_dist_of_tendsto₀ₓ'. -/
theorem dist_le_tsum_dist_of_tendsto₀ (h : Summable fun n => dist (f n) (f n.succ))
    (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a ≤ ∑' n, dist (f n) (f n.succ) := by
  simpa only [zero_add] using dist_le_tsum_dist_of_tendsto h ha 0
#align dist_le_tsum_dist_of_tendsto₀ dist_le_tsum_dist_of_tendsto₀

