/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Heather Macbeth, Johannes Hölzl, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.normed.group.infinite_sum
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Intervals
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Topology.Instances.Nnreal

/-!
# Infinite sums in (semi)normed groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In a complete (semi)normed group,

- `summable_iff_vanishing_norm`: a series `∑' i, f i` is summable if and only if for any `ε > 0`,
  there exists a finite set `s` such that the sum `∑ i in t, f i` over any finite set `t` disjoint
  with `s` has norm less than `ε`;

- `summable_of_norm_bounded`, `summable_of_norm_bounded_eventually`: if `‖f i‖` is bounded above by
  a summable series `∑' i, g i`, then `∑' i, f i` is summable as well; the same is true if the
  inequality hold only off some finite set.

- `tsum_of_norm_bounded`, `has_sum.norm_le_of_bounded`: if `‖f i‖ ≤ g i`, where `∑' i, g i` is a
  summable series, then `‖∑' i, f i‖ ≤ ∑' i, g i`.

## Tags

infinite series, absolute convergence, normed group
-/


open Classical BigOperators Topology NNReal

open Finset Filter Metric

variable {ι α E F : Type _} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/- warning: cauchy_seq_finset_iff_vanishing_norm -> cauchySeq_finset_iff_vanishing_norm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {f : ι -> E}, Iff (CauchySeq.{u2, u1} E (Finset.{u1} ι) (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1)) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.lattice.{u1} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u1} ι a b)))) (fun (s : Finset.{u1} ι) => Finset.sum.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) s (fun (i : ι) => f i))) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u1} (Finset.{u1} ι) (fun (s : Finset.{u1} ι) => forall (t : Finset.{u1} ι), (Disjoint.{u1} (Finset.{u1} ι) (Finset.partialOrder.{u1} ι) (Finset.orderBot.{u1} ι) t s) -> (LT.lt.{0} Real Real.hasLt (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (Finset.sum.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) t (fun (i : ι) => f i))) ε))))
but is expected to have type
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {f : ι -> E}, Iff (CauchySeq.{u2, u1} E (Finset.{u1} ι) (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1)) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.instLatticeFinset.{u1} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u1} ι a b)))) (fun (s : Finset.{u1} ι) => Finset.sum.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) s (fun (i : ι) => f i))) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u1} (Finset.{u1} ι) (fun (s : Finset.{u1} ι) => forall (t : Finset.{u1} ι), (Disjoint.{u1} (Finset.{u1} ι) (Finset.partialOrder.{u1} ι) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} ι) t s) -> (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u2} E (SeminormedAddCommGroup.toNorm.{u2} E _inst_1) (Finset.sum.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) t (fun (i : ι) => f i))) ε))))
Case conversion may be inaccurate. Consider using '#align cauchy_seq_finset_iff_vanishing_norm cauchySeq_finset_iff_vanishing_normₓ'. -/
theorem cauchySeq_finset_iff_vanishing_norm {f : ι → E} :
    (CauchySeq fun s : Finset ι => ∑ i in s, f i) ↔
      ∀ ε > (0 : ℝ), ∃ s : Finset ι, ∀ t, Disjoint t s → ‖∑ i in t, f i‖ < ε :=
  by
  rw [cauchySeq_finset_iff_vanishing, nhds_basis_ball.forall_iff]
  · simp only [ball_zero_eq, Set.mem_setOf_eq]
  · rintro s t hst ⟨s', hs'⟩
    exact ⟨s', fun t' ht' => hst <| hs' _ ht'⟩
#align cauchy_seq_finset_iff_vanishing_norm cauchySeq_finset_iff_vanishing_norm

/- warning: summable_iff_vanishing_norm -> summable_iff_vanishing_norm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_3 : CompleteSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))] {f : ι -> E}, Iff (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) f) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u1} (Finset.{u1} ι) (fun (s : Finset.{u1} ι) => forall (t : Finset.{u1} ι), (Disjoint.{u1} (Finset.{u1} ι) (Finset.partialOrder.{u1} ι) (Finset.orderBot.{u1} ι) t s) -> (LT.lt.{0} Real Real.hasLt (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (Finset.sum.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) t (fun (i : ι) => f i))) ε))))
but is expected to have type
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_3 : CompleteSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))] {f : ι -> E}, Iff (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) f) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u1} (Finset.{u1} ι) (fun (s : Finset.{u1} ι) => forall (t : Finset.{u1} ι), (Disjoint.{u1} (Finset.{u1} ι) (Finset.partialOrder.{u1} ι) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} ι) t s) -> (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u2} E (SeminormedAddCommGroup.toNorm.{u2} E _inst_1) (Finset.sum.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) t (fun (i : ι) => f i))) ε))))
Case conversion may be inaccurate. Consider using '#align summable_iff_vanishing_norm summable_iff_vanishing_normₓ'. -/
theorem summable_iff_vanishing_norm [CompleteSpace E] {f : ι → E} :
    Summable f ↔ ∀ ε > (0 : ℝ), ∃ s : Finset ι, ∀ t, Disjoint t s → ‖∑ i in t, f i‖ < ε := by
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_vanishing_norm]
#align summable_iff_vanishing_norm summable_iff_vanishing_norm

/- warning: cauchy_seq_finset_of_norm_bounded_eventually -> cauchySeq_finset_of_norm_bounded_eventually is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {f : ι -> E} {g : ι -> Real}, (Summable.{0, u1} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (Filter.Eventually.{u1} ι (fun (i : ι) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f i)) (g i)) (Filter.cofinite.{u1} ι)) -> (CauchySeq.{u2, u1} E (Finset.{u1} ι) (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1)) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.lattice.{u1} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u1} ι a b)))) (fun (s : Finset.{u1} ι) => Finset.sum.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) s (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] {f : ι -> E} {g : ι -> Real}, (Summable.{0, u2} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (Filter.Eventually.{u2} ι (fun (i : ι) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (f i)) (g i)) (Filter.cofinite.{u2} ι)) -> (CauchySeq.{u1, u2} E (Finset.{u2} ι) (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) (Lattice.toSemilatticeSup.{u2} (Finset.{u2} ι) (Finset.instLatticeFinset.{u2} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u2} ι a b)))) (fun (s : Finset.{u2} ι) => Finset.sum.{u1, u2} E ι (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align cauchy_seq_finset_of_norm_bounded_eventually cauchySeq_finset_of_norm_bounded_eventuallyₓ'. -/
theorem cauchySeq_finset_of_norm_bounded_eventually {f : ι → E} {g : ι → ℝ} (hg : Summable g)
    (h : ∀ᶠ i in cofinite, ‖f i‖ ≤ g i) : CauchySeq fun s => ∑ i in s, f i :=
  by
  refine' cauchySeq_finset_iff_vanishing_norm.2 fun ε hε => _
  rcases summable_iff_vanishing_norm.1 hg ε hε with ⟨s, hs⟩
  refine' ⟨s ∪ h.to_finset, fun t ht => _⟩
  have : ∀ i ∈ t, ‖f i‖ ≤ g i := by
    intro i hi
    simp only [disjoint_left, mem_union, not_or, h.mem_to_finset, Set.mem_compl_iff,
      Classical.not_not] at ht
    exact (ht hi).2
  calc
    ‖∑ i in t, f i‖ ≤ ∑ i in t, g i := norm_sum_le_of_le _ this
    _ ≤ ‖∑ i in t, g i‖ := (le_abs_self _)
    _ < ε := hs _ (ht.mono_right le_sup_left)
    
#align cauchy_seq_finset_of_norm_bounded_eventually cauchySeq_finset_of_norm_bounded_eventually

/- warning: cauchy_seq_finset_of_norm_bounded -> cauchySeq_finset_of_norm_bounded is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {f : ι -> E} (g : ι -> Real), (Summable.{0, u1} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (forall (i : ι), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f i)) (g i)) -> (CauchySeq.{u2, u1} E (Finset.{u1} ι) (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1)) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.lattice.{u1} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u1} ι a b)))) (fun (s : Finset.{u1} ι) => Finset.sum.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) s (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] {f : ι -> E} (g : ι -> Real), (Summable.{0, u2} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (forall (i : ι), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (f i)) (g i)) -> (CauchySeq.{u1, u2} E (Finset.{u2} ι) (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) (Lattice.toSemilatticeSup.{u2} (Finset.{u2} ι) (Finset.instLatticeFinset.{u2} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u2} ι a b)))) (fun (s : Finset.{u2} ι) => Finset.sum.{u1, u2} E ι (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align cauchy_seq_finset_of_norm_bounded cauchySeq_finset_of_norm_boundedₓ'. -/
theorem cauchySeq_finset_of_norm_bounded {f : ι → E} (g : ι → ℝ) (hg : Summable g)
    (h : ∀ i, ‖f i‖ ≤ g i) : CauchySeq fun s : Finset ι => ∑ i in s, f i :=
  cauchySeq_finset_of_norm_bounded_eventually hg <| eventually_of_forall h
#align cauchy_seq_finset_of_norm_bounded cauchySeq_finset_of_norm_bounded

/- warning: cauchy_seq_range_of_norm_bounded -> cauchySeq_range_of_norm_bounded is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] {f : Nat -> E} (g : Nat -> Real), (CauchySeq.{0, 0} Real Nat (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => g i))) -> (forall (i : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} E (SeminormedAddCommGroup.toHasNorm.{u1} E _inst_1) (f i)) (g i)) -> (CauchySeq.{u1, 0} E Nat (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) (fun (n : Nat) => Finset.sum.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (Finset.range n) (fun (i : Nat) => f i)))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] {f : Nat -> E} (g : Nat -> Real), (CauchySeq.{0, 0} Real Nat (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => g i))) -> (forall (i : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (f i)) (g i)) -> (CauchySeq.{u1, 0} E Nat (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) (fun (n : Nat) => Finset.sum.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (Finset.range n) (fun (i : Nat) => f i)))
Case conversion may be inaccurate. Consider using '#align cauchy_seq_range_of_norm_bounded cauchySeq_range_of_norm_boundedₓ'. -/
/-- A version of the **direct comparison test** for conditionally convergent series.
See `cauchy_seq_finset_of_norm_bounded` for the same statement about absolutely convergent ones. -/
theorem cauchySeq_range_of_norm_bounded {f : ℕ → E} (g : ℕ → ℝ)
    (hg : CauchySeq fun n => ∑ i in range n, g i) (hf : ∀ i, ‖f i‖ ≤ g i) :
    CauchySeq fun n => ∑ i in range n, f i :=
  by
  refine' Metric.cauchySeq_iff'.2 fun ε hε => _
  refine' (Metric.cauchySeq_iff'.1 hg ε hε).imp fun N hg n hn => _
  specialize hg n hn
  rw [dist_eq_norm, ← sum_Ico_eq_sub _ hn] at hg⊢
  calc
    ‖∑ k in Ico N n, f k‖ ≤ ∑ k in _, ‖f k‖ := norm_sum_le _ _
    _ ≤ ∑ k in _, g k := (sum_le_sum fun x _ => hf x)
    _ ≤ ‖∑ k in _, g k‖ := (le_abs_self _)
    _ < ε := hg
    
#align cauchy_seq_range_of_norm_bounded cauchySeq_range_of_norm_bounded

/- warning: cauchy_seq_finset_of_summable_norm -> cauchySeq_finset_of_summable_norm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {f : ι -> E}, (Summable.{0, u1} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : ι) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f a))) -> (CauchySeq.{u2, u1} E (Finset.{u1} ι) (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1)) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.lattice.{u1} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u1} ι a b)))) (fun (s : Finset.{u1} ι) => Finset.sum.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) s (fun (a : ι) => f a)))
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] {f : ι -> E}, (Summable.{0, u2} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : ι) => Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (f a))) -> (CauchySeq.{u1, u2} E (Finset.{u2} ι) (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) (Lattice.toSemilatticeSup.{u2} (Finset.{u2} ι) (Finset.instLatticeFinset.{u2} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u2} ι a b)))) (fun (s : Finset.{u2} ι) => Finset.sum.{u1, u2} E ι (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) s (fun (a : ι) => f a)))
Case conversion may be inaccurate. Consider using '#align cauchy_seq_finset_of_summable_norm cauchySeq_finset_of_summable_normₓ'. -/
theorem cauchySeq_finset_of_summable_norm {f : ι → E} (hf : Summable fun a => ‖f a‖) :
    CauchySeq fun s : Finset ι => ∑ a in s, f a :=
  cauchySeq_finset_of_norm_bounded _ hf fun i => le_rfl
#align cauchy_seq_finset_of_summable_norm cauchySeq_finset_of_summable_norm

/- warning: has_sum_of_subseq_of_summable -> hasSum_of_subseq_of_summable is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {E : Type.{u3}} [_inst_1 : SeminormedAddCommGroup.{u3} E] {f : ι -> E}, (Summable.{0, u1} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : ι) => Norm.norm.{u3} E (SeminormedAddCommGroup.toHasNorm.{u3} E _inst_1) (f a))) -> (forall {s : α -> (Finset.{u1} ι)} {p : Filter.{u2} α} [_inst_3 : Filter.NeBot.{u2} α p], (Filter.Tendsto.{u2, u1} α (Finset.{u1} ι) s p (Filter.atTop.{u1} (Finset.{u1} ι) (PartialOrder.toPreorder.{u1} (Finset.{u1} ι) (Finset.partialOrder.{u1} ι)))) -> (forall {a : E}, (Filter.Tendsto.{u2, u3} α E (fun (b : α) => Finset.sum.{u3, u1} E ι (AddCommGroup.toAddCommMonoid.{u3} E (SeminormedAddCommGroup.toAddCommGroup.{u3} E _inst_1)) (s b) (fun (i : ι) => f i)) p (nhds.{u3} E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E _inst_1))) a)) -> (HasSum.{u3, u1} E ι (AddCommGroup.toAddCommMonoid.{u3} E (SeminormedAddCommGroup.toAddCommGroup.{u3} E _inst_1)) (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E _inst_1))) f a)))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {f : ι -> E}, (Summable.{0, u3} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : ι) => Norm.norm.{u2} E (SeminormedAddCommGroup.toNorm.{u2} E _inst_1) (f a))) -> (forall {s : α -> (Finset.{u3} ι)} {p : Filter.{u1} α} [_inst_3 : Filter.NeBot.{u1} α p], (Filter.Tendsto.{u1, u3} α (Finset.{u3} ι) s p (Filter.atTop.{u3} (Finset.{u3} ι) (PartialOrder.toPreorder.{u3} (Finset.{u3} ι) (Finset.partialOrder.{u3} ι)))) -> (forall {a : E}, (Filter.Tendsto.{u1, u2} α E (fun (b : α) => Finset.sum.{u2, u3} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (s b) (fun (i : ι) => f i)) p (nhds.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) a)) -> (HasSum.{u2, u3} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) f a)))
Case conversion may be inaccurate. Consider using '#align has_sum_of_subseq_of_summable hasSum_of_subseq_of_summableₓ'. -/
/-- If a function `f` is summable in norm, and along some sequence of finsets exhausting the space
its sum is converging to a limit `a`, then this holds along all finsets, i.e., `f` is summable
with sum `a`. -/
theorem hasSum_of_subseq_of_summable {f : ι → E} (hf : Summable fun a => ‖f a‖) {s : α → Finset ι}
    {p : Filter α} [NeBot p] (hs : Tendsto s p atTop) {a : E}
    (ha : Tendsto (fun b => ∑ i in s b, f i) p (𝓝 a)) : HasSum f a :=
  tendsto_nhds_of_cauchySeq_of_subseq (cauchySeq_finset_of_summable_norm hf) hs ha
#align has_sum_of_subseq_of_summable hasSum_of_subseq_of_summable

#print hasSum_iff_tendsto_nat_of_summable_norm /-
theorem hasSum_iff_tendsto_nat_of_summable_norm {f : ℕ → E} {a : E} (hf : Summable fun i => ‖f i‖) :
    HasSum f a ↔ Tendsto (fun n : ℕ => ∑ i in range n, f i) atTop (𝓝 a) :=
  ⟨fun h => h.tendsto_sum_nat, fun h => hasSum_of_subseq_of_summable hf tendsto_finset_range h⟩
#align has_sum_iff_tendsto_nat_of_summable_norm hasSum_iff_tendsto_nat_of_summable_norm
-/

/- warning: summable_of_norm_bounded -> summable_of_norm_bounded is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_3 : CompleteSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))] {f : ι -> E} (g : ι -> Real), (Summable.{0, u1} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (forall (i : ι), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f i)) (g i)) -> (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) f)
but is expected to have type
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_3 : CompleteSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))] {f : ι -> E} (g : ι -> Real), (Summable.{0, u1} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (forall (i : ι), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E (SeminormedAddCommGroup.toNorm.{u2} E _inst_1) (f i)) (g i)) -> (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) f)
Case conversion may be inaccurate. Consider using '#align summable_of_norm_bounded summable_of_norm_boundedₓ'. -/
/-- The direct comparison test for series:  if the norm of `f` is bounded by a real function `g`
which is summable, then `f` is summable. -/
theorem summable_of_norm_bounded [CompleteSpace E] {f : ι → E} (g : ι → ℝ) (hg : Summable g)
    (h : ∀ i, ‖f i‖ ≤ g i) : Summable f :=
  by
  rw [summable_iff_cauchySeq_finset]
  exact cauchySeq_finset_of_norm_bounded g hg h
#align summable_of_norm_bounded summable_of_norm_bounded

/- warning: has_sum.norm_le_of_bounded -> HasSum.norm_le_of_bounded is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {f : ι -> E} {g : ι -> Real} {a : E} {b : Real}, (HasSum.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) f a) -> (HasSum.{0, u1} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g b) -> (forall (i : ι), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f i)) (g i)) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) a) b)
but is expected to have type
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {f : ι -> E} {g : ι -> Real} {a : E} {b : Real}, (HasSum.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) f a) -> (HasSum.{0, u1} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g b) -> (forall (i : ι), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E (SeminormedAddCommGroup.toNorm.{u2} E _inst_1) (f i)) (g i)) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E (SeminormedAddCommGroup.toNorm.{u2} E _inst_1) a) b)
Case conversion may be inaccurate. Consider using '#align has_sum.norm_le_of_bounded HasSum.norm_le_of_boundedₓ'. -/
theorem HasSum.norm_le_of_bounded {f : ι → E} {g : ι → ℝ} {a : E} {b : ℝ} (hf : HasSum f a)
    (hg : HasSum g b) (h : ∀ i, ‖f i‖ ≤ g i) : ‖a‖ ≤ b :=
  le_of_tendsto_of_tendsto' hf.norm hg fun s => norm_sum_le_of_le _ fun i hi => h i
#align has_sum.norm_le_of_bounded HasSum.norm_le_of_bounded

/- warning: tsum_of_norm_bounded -> tsum_of_norm_bounded is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {f : ι -> E} {g : ι -> Real} {a : Real}, (HasSum.{0, u1} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g a) -> (forall (i : ι), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f i)) (g i)) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (tsum.{u2, u1} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) ι (fun (i : ι) => f i))) a)
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] {f : ι -> E} {g : ι -> Real} {a : Real}, (HasSum.{0, u2} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g a) -> (forall (i : ι), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (f i)) (g i)) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (tsum.{u1, u2} E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) ι (fun (i : ι) => f i))) a)
Case conversion may be inaccurate. Consider using '#align tsum_of_norm_bounded tsum_of_norm_boundedₓ'. -/
/-- Quantitative result associated to the direct comparison test for series:  If `∑' i, g i` is
summable, and for all `i`, `‖f i‖ ≤ g i`, then `‖∑' i, f i‖ ≤ ∑' i, g i`. Note that we do not
assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
theorem tsum_of_norm_bounded {f : ι → E} {g : ι → ℝ} {a : ℝ} (hg : HasSum g a)
    (h : ∀ i, ‖f i‖ ≤ g i) : ‖∑' i : ι, f i‖ ≤ a :=
  by
  by_cases hf : Summable f
  · exact hf.has_sum.norm_le_of_bounded hg h
  · rw [tsum_eq_zero_of_not_summable hf, norm_zero]
    exact ge_of_tendsto' hg fun s => sum_nonneg fun i hi => (norm_nonneg _).trans (h i)
#align tsum_of_norm_bounded tsum_of_norm_bounded

/- warning: norm_tsum_le_tsum_norm -> norm_tsum_le_tsum_norm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {f : ι -> E}, (Summable.{0, u1} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (i : ι) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f i))) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (tsum.{u2, u1} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) ι (fun (i : ι) => f i))) (tsum.{0, u1} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ι (fun (i : ι) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f i))))
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] {f : ι -> E}, (Summable.{0, u2} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (i : ι) => Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (f i))) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (tsum.{u1, u2} E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) ι (fun (i : ι) => f i))) (tsum.{0, u2} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ι (fun (i : ι) => Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (f i))))
Case conversion may be inaccurate. Consider using '#align norm_tsum_le_tsum_norm norm_tsum_le_tsum_normₓ'. -/
/-- If `∑' i, ‖f i‖` is summable, then `‖∑' i, f i‖ ≤ (∑' i, ‖f i‖)`. Note that we do not assume
that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
theorem norm_tsum_le_tsum_norm {f : ι → E} (hf : Summable fun i => ‖f i‖) :
    ‖∑' i, f i‖ ≤ ∑' i, ‖f i‖ :=
  tsum_of_norm_bounded hf.HasSum fun i => le_rfl
#align norm_tsum_le_tsum_norm norm_tsum_le_tsum_norm

/- warning: tsum_of_nnnorm_bounded -> tsum_of_nnnorm_bounded is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {f : ι -> E} {g : ι -> NNReal} {a : NNReal}, (HasSum.{0, u1} NNReal ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace g a) -> (forall (i : ι), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)) (f i)) (g i)) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)) (tsum.{u2, u1} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) ι (fun (i : ι) => f i))) a)
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] {f : ι -> E} {g : ι -> NNReal} {a : NNReal}, (HasSum.{0, u2} NNReal ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal g a) -> (forall (i : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1)) (f i)) (g i)) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1)) (tsum.{u1, u2} E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) ι (fun (i : ι) => f i))) a)
Case conversion may be inaccurate. Consider using '#align tsum_of_nnnorm_bounded tsum_of_nnnorm_boundedₓ'. -/
/-- Quantitative result associated to the direct comparison test for series: If `∑' i, g i` is
summable, and for all `i`, `‖f i‖₊ ≤ g i`, then `‖∑' i, f i‖₊ ≤ ∑' i, g i`. Note that we
do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
theorem tsum_of_nnnorm_bounded {f : ι → E} {g : ι → ℝ≥0} {a : ℝ≥0} (hg : HasSum g a)
    (h : ∀ i, ‖f i‖₊ ≤ g i) : ‖∑' i : ι, f i‖₊ ≤ a :=
  by
  simp only [← NNReal.coe_le_coe, ← NNReal.hasSum_coe, coe_nnnorm] at *
  exact tsum_of_norm_bounded hg h
#align tsum_of_nnnorm_bounded tsum_of_nnnorm_bounded

/- warning: nnnorm_tsum_le -> nnnorm_tsum_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {f : ι -> E}, (Summable.{0, u1} NNReal ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (i : ι) => NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)) (f i))) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)) (tsum.{u2, u1} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) ι (fun (i : ι) => f i))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace ι (fun (i : ι) => NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)) (f i))))
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] {f : ι -> E}, (Summable.{0, u2} NNReal ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (i : ι) => NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1)) (f i))) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1)) (tsum.{u1, u2} E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) ι (fun (i : ι) => f i))) (tsum.{0, u2} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal ι (fun (i : ι) => NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1)) (f i))))
Case conversion may be inaccurate. Consider using '#align nnnorm_tsum_le nnnorm_tsum_leₓ'. -/
/-- If `∑' i, ‖f i‖₊` is summable, then `‖∑' i, f i‖₊ ≤ ∑' i, ‖f i‖₊`. Note that
we do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
theorem nnnorm_tsum_le {f : ι → E} (hf : Summable fun i => ‖f i‖₊) : ‖∑' i, f i‖₊ ≤ ∑' i, ‖f i‖₊ :=
  tsum_of_nnnorm_bounded hf.HasSum fun i => le_rfl
#align nnnorm_tsum_le nnnorm_tsum_le

variable [CompleteSpace E]

/- warning: summable_of_norm_bounded_eventually -> summable_of_norm_bounded_eventually is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_3 : CompleteSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))] {f : ι -> E} (g : ι -> Real), (Summable.{0, u1} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (Filter.Eventually.{u1} ι (fun (i : ι) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f i)) (g i)) (Filter.cofinite.{u1} ι)) -> (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) f)
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] [_inst_3 : CompleteSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))] {f : ι -> E} (g : ι -> Real), (Summable.{0, u2} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (Filter.Eventually.{u2} ι (fun (i : ι) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (f i)) (g i)) (Filter.cofinite.{u2} ι)) -> (Summable.{u1, u2} E ι (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) f)
Case conversion may be inaccurate. Consider using '#align summable_of_norm_bounded_eventually summable_of_norm_bounded_eventuallyₓ'. -/
/-- Variant of the direct comparison test for series:  if the norm of `f` is eventually bounded by a
real function `g` which is summable, then `f` is summable. -/
theorem summable_of_norm_bounded_eventually {f : ι → E} (g : ι → ℝ) (hg : Summable g)
    (h : ∀ᶠ i in cofinite, ‖f i‖ ≤ g i) : Summable f :=
  summable_iff_cauchySeq_finset.2 <| cauchySeq_finset_of_norm_bounded_eventually hg h
#align summable_of_norm_bounded_eventually summable_of_norm_bounded_eventually

/- warning: summable_of_nnnorm_bounded -> summable_of_nnnorm_bounded is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_3 : CompleteSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))] {f : ι -> E} (g : ι -> NNReal), (Summable.{0, u1} NNReal ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace g) -> (forall (i : ι), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)) (f i)) (g i)) -> (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) f)
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] [_inst_3 : CompleteSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))] {f : ι -> E} (g : ι -> NNReal), (Summable.{0, u2} NNReal ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal g) -> (forall (i : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1)) (f i)) (g i)) -> (Summable.{u1, u2} E ι (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) f)
Case conversion may be inaccurate. Consider using '#align summable_of_nnnorm_bounded summable_of_nnnorm_boundedₓ'. -/
theorem summable_of_nnnorm_bounded {f : ι → E} (g : ι → ℝ≥0) (hg : Summable g)
    (h : ∀ i, ‖f i‖₊ ≤ g i) : Summable f :=
  summable_of_norm_bounded (fun i => (g i : ℝ)) (NNReal.summable_coe.2 hg) fun i => by
    exact_mod_cast h i
#align summable_of_nnnorm_bounded summable_of_nnnorm_bounded

/- warning: summable_of_summable_norm -> summable_of_summable_norm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_3 : CompleteSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))] {f : ι -> E}, (Summable.{0, u1} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : ι) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f a))) -> (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) f)
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] [_inst_3 : CompleteSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))] {f : ι -> E}, (Summable.{0, u2} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (a : ι) => Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (f a))) -> (Summable.{u1, u2} E ι (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) f)
Case conversion may be inaccurate. Consider using '#align summable_of_summable_norm summable_of_summable_normₓ'. -/
theorem summable_of_summable_norm {f : ι → E} (hf : Summable fun a => ‖f a‖) : Summable f :=
  summable_of_norm_bounded _ hf fun i => le_rfl
#align summable_of_summable_norm summable_of_summable_norm

/- warning: summable_of_summable_nnnorm -> summable_of_summable_nnnorm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] [_inst_3 : CompleteSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))] {f : ι -> E}, (Summable.{0, u1} NNReal ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (a : ι) => NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)) (f a))) -> (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_1))) f)
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] [_inst_3 : CompleteSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))] {f : ι -> E}, (Summable.{0, u2} NNReal ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (a : ι) => NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_1)) (f a))) -> (Summable.{u1, u2} E ι (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) f)
Case conversion may be inaccurate. Consider using '#align summable_of_summable_nnnorm summable_of_summable_nnnormₓ'. -/
theorem summable_of_summable_nnnorm {f : ι → E} (hf : Summable fun a => ‖f a‖₊) : Summable f :=
  summable_of_nnnorm_bounded _ hf fun i => le_rfl
#align summable_of_summable_nnnorm summable_of_summable_nnnorm

