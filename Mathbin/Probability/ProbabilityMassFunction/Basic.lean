/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma

! This file was ported from Lean 3 source module probability.probability_mass_function.basic
! leanprover-community/mathlib commit a2706b55e8d7f7e9b1f93143f0b88f2e34a11eea
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Instances.Ennreal
import Mathbin.MeasureTheory.Measure.MeasureSpace

/-!
# Probability mass functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0∞` such that the values have (infinite) sum `1`.

Construction of monadic `pure` and `bind` is found in `probability_mass_function/monad.lean`,
other constructions of `pmf`s are found in `probability_mass_function/constructions.lean`.

Given `p : pmf α`, `pmf.to_outer_measure` constructs an `outer_measure` on `α`,
by assigning each set the sum of the probabilities of each of its elements.
Under this outer measure, every set is Carathéodory-measurable,
so we can further extend this to a `measure` on `α`, see `pmf.to_measure`.
`pmf.to_measure.is_probability_measure` shows this associated measure is a probability measure.
Conversely, given a probability measure `μ` on a measurable space `α` with all singleton sets
measurable, `μ.to_pmf` constructs a `pmf` on `α`, setting the probability mass of a point `x`
to be the measure of the singleton set `{x}`.

## Tags

probability mass function, discrete probability measure
-/


noncomputable section

variable {α β γ : Type _}

open Classical BigOperators NNReal ENNReal MeasureTheory

#print Pmf /-
/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0∞` such
  that the values have (infinite) sum `1`. -/
def Pmf.{u} (α : Type u) : Type u :=
  { f : α → ℝ≥0∞ // HasSum f 1 }
#align pmf Pmf
-/

namespace Pmf

#print Pmf.funLike /-
instance funLike : FunLike (Pmf α) α fun p => ℝ≥0∞
    where
  coe p a := p.1 a
  coe_injective' p q h := Subtype.eq h
#align pmf.fun_like Pmf.funLike
-/

#print Pmf.ext /-
@[ext]
protected theorem ext {p q : Pmf α} (h : ∀ x, p x = q x) : p = q :=
  FunLike.ext p q h
#align pmf.ext Pmf.ext
-/

#print Pmf.ext_iff /-
theorem ext_iff {p q : Pmf α} : p = q ↔ ∀ x, p x = q x :=
  FunLike.ext_iff
#align pmf.ext_iff Pmf.ext_iff
-/

/- warning: pmf.has_sum_coe_one -> Pmf.hasSum_coe_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α), HasSum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α), HasSum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))
Case conversion may be inaccurate. Consider using '#align pmf.has_sum_coe_one Pmf.hasSum_coe_oneₓ'. -/
theorem hasSum_coe_one (p : Pmf α) : HasSum p 1 :=
  p.2
#align pmf.has_sum_coe_one Pmf.hasSum_coe_one

/- warning: pmf.tsum_coe -> Pmf.tsum_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α), Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α), Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))
Case conversion may be inaccurate. Consider using '#align pmf.tsum_coe Pmf.tsum_coeₓ'. -/
@[simp]
theorem tsum_coe (p : Pmf α) : (∑' a, p a) = 1 :=
  p.hasSum_coe_one.tsum_eq
#align pmf.tsum_coe Pmf.tsum_coe

/- warning: pmf.tsum_coe_ne_top -> Pmf.tsum_coe_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α), Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α), Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align pmf.tsum_coe_ne_top Pmf.tsum_coe_ne_topₓ'. -/
theorem tsum_coe_ne_top (p : Pmf α) : (∑' a, p a) ≠ ∞ :=
  p.tsum_coe.symm ▸ ENNReal.one_ne_top
#align pmf.tsum_coe_ne_top Pmf.tsum_coe_ne_top

/- warning: pmf.tsum_coe_indicator_ne_top -> Pmf.tsum_coe_indicator_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Set.{u1} α), Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p) a)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Set.{u1} α), Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero s (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p) a)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align pmf.tsum_coe_indicator_ne_top Pmf.tsum_coe_indicator_ne_topₓ'. -/
theorem tsum_coe_indicator_ne_top (p : Pmf α) (s : Set α) : (∑' a, s.indicator p a) ≠ ∞ :=
  ne_of_lt
    (lt_of_le_of_lt
      (tsum_le_tsum (fun a => Set.indicator_apply_le fun _ => le_rfl) ENNReal.summable
        ENNReal.summable)
      (lt_of_le_of_ne le_top p.tsum_coe_ne_top))
#align pmf.tsum_coe_indicator_ne_top Pmf.tsum_coe_indicator_ne_top

/- warning: pmf.coe_ne_zero -> Pmf.coe_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α), Ne.{succ u1} (α -> ENNReal) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p) (OfNat.ofNat.{u1} (α -> ENNReal) 0 (OfNat.mk.{u1} (α -> ENNReal) 0 (Zero.zero.{u1} (α -> ENNReal) (Pi.instZero.{u1, 0} α (fun (a : α) => ENNReal) (fun (i : α) => ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α), Ne.{succ u1} (forall (a : α), (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p) (OfNat.ofNat.{u1} (forall (a : α), (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{u1} (forall (a : α), (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (Pi.instZero.{u1, 0} α (fun (a : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (fun (i : α) => instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align pmf.coe_ne_zero Pmf.coe_ne_zeroₓ'. -/
@[simp]
theorem coe_ne_zero (p : Pmf α) : ⇑p ≠ 0 := fun hp =>
  zero_ne_one ((tsum_zero.symm.trans (tsum_congr fun x => symm (congr_fun hp x))).trans p.tsum_coe)
#align pmf.coe_ne_zero Pmf.coe_ne_zero

#print Pmf.support /-
/-- The support of a `pmf` is the set where it is nonzero. -/
def support (p : Pmf α) : Set α :=
  Function.support p
#align pmf.support Pmf.support
-/

/- warning: pmf.mem_support_iff -> Pmf.mem_support_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (a : α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (a : α), Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)) (Ne.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align pmf.mem_support_iff Pmf.mem_support_iffₓ'. -/
@[simp]
theorem mem_support_iff (p : Pmf α) (a : α) : a ∈ p.support ↔ p a ≠ 0 :=
  Iff.rfl
#align pmf.mem_support_iff Pmf.mem_support_iff

#print Pmf.support_nonempty /-
@[simp]
theorem support_nonempty (p : Pmf α) : p.support.Nonempty :=
  Function.support_nonempty_iff.2 p.coe_ne_zero
#align pmf.support_nonempty Pmf.support_nonempty
-/

/- warning: pmf.apply_eq_zero_iff -> Pmf.apply_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (a : α), Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (a : α), Iff (Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero))) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)))
Case conversion may be inaccurate. Consider using '#align pmf.apply_eq_zero_iff Pmf.apply_eq_zero_iffₓ'. -/
theorem apply_eq_zero_iff (p : Pmf α) (a : α) : p a = 0 ↔ a ∉ p.support := by
  rw [mem_support_iff, Classical.not_not]
#align pmf.apply_eq_zero_iff Pmf.apply_eq_zero_iff

/- warning: pmf.apply_pos_iff -> Pmf.apply_pos_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (a : α), Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (a : α), Iff (LT.lt.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (Preorder.toLT.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (PartialOrder.toPreorder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (OmegaCompletePartialOrder.toPartialOrder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CompleteLattice.instOmegaCompletePartialOrder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CompleteLinearOrder.toCompleteLattice.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero)) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p))
Case conversion may be inaccurate. Consider using '#align pmf.apply_pos_iff Pmf.apply_pos_iffₓ'. -/
theorem apply_pos_iff (p : Pmf α) (a : α) : 0 < p a ↔ a ∈ p.support :=
  pos_iff_ne_zero.trans (p.mem_support_iff a).symm
#align pmf.apply_pos_iff Pmf.apply_pos_iff

#print Pmf.apply_eq_one_iff /-
theorem apply_eq_one_iff (p : Pmf α) (a : α) : p a = 1 ↔ p.support = {a} :=
  by
  refine'
    ⟨fun h =>
      Set.Subset.antisymm (fun a' ha' => by_contra fun ha => _) fun a' ha' =>
        ha'.symm ▸ (p.mem_support_iff a).2 fun ha => zero_ne_one <| ha.symm.trans h,
      fun h =>
      trans (symm <| tsum_eq_single a fun a' ha' => (p.apply_eq_zero_iff a').2 (h.symm ▸ ha'))
        p.tsum_coe⟩
  suffices : 1 < ∑' a, p a
  exact ne_of_lt this p.tsum_coe.symm
  have : 0 < ∑' b, ite (b = a) 0 (p b) :=
    lt_of_le_of_ne' zero_le'
      ((tsum_ne_zero_iff ENNReal.summable).2
        ⟨a', ite_ne_left_iff.2 ⟨ha, Ne.symm <| (p.mem_support_iff a').2 ha'⟩⟩)
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ < p a + ∑' b, ite (b = a) 0 (p b) :=
      (ENNReal.add_lt_add_of_le_of_lt ENNReal.one_ne_top (le_of_eq h.symm) this)
    _ = ite (a = a) (p a) 0 + ∑' b, ite (b = a) 0 (p b) := by rw [eq_self_iff_true, if_true]
    _ = (∑' b, ite (b = a) (p b) 0) + ∑' b, ite (b = a) 0 (p b) := by congr ;
      exact symm (tsum_eq_single a fun b hb => if_neg hb)
    _ = ∑' b, ite (b = a) (p b) 0 + ite (b = a) 0 (p b) := ennreal.tsum_add.symm
    _ = ∑' b, p b := tsum_congr fun b => by split_ifs <;> simp only [zero_add, add_zero, le_rfl]
    
#align pmf.apply_eq_one_iff Pmf.apply_eq_one_iff
-/

/- warning: pmf.coe_le_one -> Pmf.coe_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (a : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (a : α), LE.le.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (Preorder.toLE.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (PartialOrder.toPreorder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (OmegaCompletePartialOrder.toPartialOrder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CompleteLattice.instOmegaCompletePartialOrder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CompleteLinearOrder.toCompleteLattice.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal.instCompleteLinearOrderENNReal))))) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CanonicallyOrderedCommSemiring.toOne.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal.instCanonicallyOrderedCommSemiringENNReal)))
Case conversion may be inaccurate. Consider using '#align pmf.coe_le_one Pmf.coe_le_oneₓ'. -/
theorem coe_le_one (p : Pmf α) (a : α) : p a ≤ 1 :=
  hasSum_le (by intro b; split_ifs <;> simp only [h, zero_le', le_rfl]) (hasSum_ite_eq a (p a))
    (hasSum_coe_one p)
#align pmf.coe_le_one Pmf.coe_le_one

/- warning: pmf.apply_ne_top -> Pmf.apply_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (a : α), Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (a : α), Ne.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align pmf.apply_ne_top Pmf.apply_ne_topₓ'. -/
theorem apply_ne_top (p : Pmf α) (a : α) : p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ENNReal.one_lt_top)
#align pmf.apply_ne_top Pmf.apply_ne_top

/- warning: pmf.apply_lt_top -> Pmf.apply_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (a : α), LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (a : α), LT.lt.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (Preorder.toLT.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (PartialOrder.toPreorder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (OmegaCompletePartialOrder.toPartialOrder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CompleteLattice.instOmegaCompletePartialOrder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CompleteLinearOrder.toCompleteLattice.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal.instCompleteLinearOrderENNReal))))) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align pmf.apply_lt_top Pmf.apply_lt_topₓ'. -/
theorem apply_lt_top (p : Pmf α) (a : α) : p a < ∞ :=
  lt_of_le_of_ne le_top (p.apply_ne_top a)
#align pmf.apply_lt_top Pmf.apply_lt_top

section OuterMeasure

open MeasureTheory MeasureTheory.OuterMeasure

#print Pmf.toOuterMeasure /-
/-- Construct an `outer_measure` from a `pmf`, by assigning measure to each set `s : set α` equal
  to the sum of `p x` for for each `x ∈ α` -/
def toOuterMeasure (p : Pmf α) : OuterMeasure α :=
  OuterMeasure.sum fun x : α => p x • dirac x
#align pmf.to_outer_measure Pmf.toOuterMeasure
-/

variable (p : Pmf α) (s t : Set α)

/- warning: pmf.to_outer_measure_apply -> Pmf.toOuterMeasure_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α p) s) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p) x))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α p) s) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero s (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p) x))
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_apply Pmf.toOuterMeasure_applyₓ'. -/
theorem toOuterMeasure_apply : p.toOuterMeasure s = ∑' x, s.indicator p x :=
  tsum_congr fun x => smul_dirac_apply (p x) x s
#align pmf.to_outer_measure_apply Pmf.toOuterMeasure_apply

/- warning: pmf.to_outer_measure_caratheodory -> Pmf.toOuterMeasure_caratheodory is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α), Eq.{succ u1} (MeasurableSpace.{u1} α) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (Pmf.toOuterMeasure.{u1} α p)) (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toHasTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α), Eq.{succ u1} (MeasurableSpace.{u1} α) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (Pmf.toOuterMeasure.{u1} α p)) (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} α)))
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_caratheodory Pmf.toOuterMeasure_caratheodoryₓ'. -/
@[simp]
theorem toOuterMeasure_caratheodory : p.toOuterMeasure.caratheodory = ⊤ :=
  by
  refine' eq_top_iff.2 <| le_trans (le_sInf fun x hx => _) (le_sum_caratheodory _)
  exact
    let ⟨y, hy⟩ := hx
    ((le_of_eq (dirac_caratheodory y).symm).trans (le_smul_caratheodory _ _)).trans (le_of_eq hy)
#align pmf.to_outer_measure_caratheodory Pmf.toOuterMeasure_caratheodory

/- warning: pmf.to_outer_measure_apply_finset -> Pmf.toOuterMeasure_apply_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Finset.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α p) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (x : α) => coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p x))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Finset.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α p) (Finset.toSet.{u1} α s)) (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (x : α) => FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p x))
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_apply_finset Pmf.toOuterMeasure_apply_finsetₓ'. -/
@[simp]
theorem toOuterMeasure_apply_finset (s : Finset α) : p.toOuterMeasure s = ∑ x in s, p x :=
  by
  refine' (to_outer_measure_apply p s).trans ((@tsum_eq_sum _ _ _ _ _ _ s _).trans _)
  · exact fun x hx => Set.indicator_of_not_mem hx _
  · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem hx _
#align pmf.to_outer_measure_apply_finset Pmf.toOuterMeasure_apply_finset

#print Pmf.toOuterMeasure_apply_singleton /-
theorem toOuterMeasure_apply_singleton (a : α) : p.toOuterMeasure {a} = p a :=
  by
  refine' (p.to_outer_measure_apply {a}).trans ((tsum_eq_single a fun b hb => _).trans _)
  · exact ite_eq_right_iff.2 fun hb' => False.elim <| hb hb'
  · exact ite_eq_left_iff.2 fun ha' => False.elim <| ha' rfl
#align pmf.to_outer_measure_apply_singleton Pmf.toOuterMeasure_apply_singleton
-/

#print Pmf.toOuterMeasure_injective /-
theorem toOuterMeasure_injective : (toOuterMeasure : Pmf α → OuterMeasure α).Injective :=
  fun p q h =>
  Pmf.ext fun x =>
    (p.toOuterMeasure_apply_singleton x).symm.trans
      ((congr_fun (congr_arg _ h) _).trans <| q.toOuterMeasure_apply_singleton x)
#align pmf.to_outer_measure_injective Pmf.toOuterMeasure_injective
-/

#print Pmf.toOuterMeasure_inj /-
@[simp]
theorem toOuterMeasure_inj {p q : Pmf α} : p.toOuterMeasure = q.toOuterMeasure ↔ p = q :=
  toOuterMeasure_injective.eq_iff
#align pmf.to_outer_measure_inj Pmf.toOuterMeasure_inj
-/

/- warning: pmf.to_outer_measure_apply_eq_zero_iff -> Pmf.toOuterMeasure_apply_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Set.{u1} α), Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α p) s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Pmf.support.{u1} α p) s)
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Set.{u1} α), Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α p) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Pmf.support.{u1} α p) s)
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_apply_eq_zero_iff Pmf.toOuterMeasure_apply_eq_zero_iffₓ'. -/
theorem toOuterMeasure_apply_eq_zero_iff : p.toOuterMeasure s = 0 ↔ Disjoint p.support s :=
  by
  rw [to_outer_measure_apply, ENNReal.tsum_eq_zero]
  exact function.funext_iff.symm.trans Set.indicator_eq_zero'
#align pmf.to_outer_measure_apply_eq_zero_iff Pmf.toOuterMeasure_apply_eq_zero_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ∉ » s) -/
#print Pmf.toOuterMeasure_apply_eq_one_iff /-
theorem toOuterMeasure_apply_eq_one_iff : p.toOuterMeasure s = 1 ↔ p.support ⊆ s :=
  by
  refine' (p.to_outer_measure_apply s).symm ▸ ⟨fun h a hap => _, fun h => _⟩
  · refine' by_contra fun hs => ne_of_lt _ (h.trans p.tsum_coe.symm)
    have hs' : s.indicator p a = 0 := Set.indicator_apply_eq_zero.2 fun hs' => False.elim <| hs hs'
    have hsa : s.indicator p a < p a := hs'.symm ▸ (p.apply_pos_iff a).2 hap
    exact
      ENNReal.tsum_lt_tsum (p.tsum_coe_indicator_ne_top s)
        (fun x => Set.indicator_apply_le fun _ => le_rfl) hsa
  · suffices : ∀ (x) (_ : x ∉ s), p x = 0
    exact
      trans
        (tsum_congr fun a => (Set.indicator_apply s p a).trans (ite_eq_left_iff.2 <| symm ∘ this a))
        p.tsum_coe
    exact fun a ha => (p.apply_eq_zero_iff a).2 <| Set.not_mem_subset h ha
#align pmf.to_outer_measure_apply_eq_one_iff Pmf.toOuterMeasure_apply_eq_one_iff
-/

/- warning: pmf.to_outer_measure_apply_inter_support -> Pmf.toOuterMeasure_apply_inter_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α p) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Pmf.support.{u1} α p))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α p) s)
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α p) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Pmf.support.{u1} α p))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α p) s)
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_apply_inter_support Pmf.toOuterMeasure_apply_inter_supportₓ'. -/
@[simp]
theorem toOuterMeasure_apply_inter_support :
    p.toOuterMeasure (s ∩ p.support) = p.toOuterMeasure s := by
  simp only [to_outer_measure_apply, Pmf.support, Set.indicator_inter_support]
#align pmf.to_outer_measure_apply_inter_support Pmf.toOuterMeasure_apply_inter_support

/- warning: pmf.to_outer_measure_mono -> Pmf.toOuterMeasure_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Pmf.support.{u1} α p)) t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α p) s) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α p) t))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Pmf.support.{u1} α p)) t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α p) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α p) t))
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_mono Pmf.toOuterMeasure_monoₓ'. -/
/-- Slightly stronger than `outer_measure.mono` having an intersection with `p.support` -/
theorem toOuterMeasure_mono {s t : Set α} (h : s ∩ p.support ⊆ t) :
    p.toOuterMeasure s ≤ p.toOuterMeasure t :=
  le_trans (le_of_eq (toOuterMeasure_apply_inter_support p s).symm) (p.toOuterMeasure.mono h)
#align pmf.to_outer_measure_mono Pmf.toOuterMeasure_mono

/- warning: pmf.to_outer_measure_apply_eq_of_inter_support_eq -> Pmf.toOuterMeasure_apply_eq_of_inter_support_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) {s : Set.{u1} α} {t : Set.{u1} α}, (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Pmf.support.{u1} α p)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t (Pmf.support.{u1} α p))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α p) s) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α p) t))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) {s : Set.{u1} α} {t : Set.{u1} α}, (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Pmf.support.{u1} α p)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t (Pmf.support.{u1} α p))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α p) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α p) t))
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_apply_eq_of_inter_support_eq Pmf.toOuterMeasure_apply_eq_of_inter_support_eqₓ'. -/
theorem toOuterMeasure_apply_eq_of_inter_support_eq {s t : Set α}
    (h : s ∩ p.support = t ∩ p.support) : p.toOuterMeasure s = p.toOuterMeasure t :=
  le_antisymm (p.toOuterMeasure_mono (h.symm ▸ Set.inter_subset_left t p.support))
    (p.toOuterMeasure_mono (h ▸ Set.inter_subset_left s p.support))
#align pmf.to_outer_measure_apply_eq_of_inter_support_eq Pmf.toOuterMeasure_apply_eq_of_inter_support_eq

/- warning: pmf.to_outer_measure_apply_fintype -> Pmf.toOuterMeasure_apply_fintype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Set.{u1} α) [_inst_1 : Fintype.{u1} α], Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α p) s) (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.univ.{u1} α _inst_1) (fun (x : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p) x))
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Set.{u1} α) [_inst_1 : Fintype.{u1} α], Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α p) s) (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.univ.{u1} α _inst_1) (fun (x : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero s (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p) x))
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_apply_fintype Pmf.toOuterMeasure_apply_fintypeₓ'. -/
@[simp]
theorem toOuterMeasure_apply_fintype [Fintype α] : p.toOuterMeasure s = ∑ x, s.indicator p x :=
  (p.to_outer_measure_apply s).trans (tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h)
#align pmf.to_outer_measure_apply_fintype Pmf.toOuterMeasure_apply_fintype

end OuterMeasure

section Measure

open MeasureTheory

#print Pmf.toMeasure /-
/-- Since every set is Carathéodory-measurable under `pmf.to_outer_measure`,
  we can further extend this `outer_measure` to a `measure` on `α` -/
def toMeasure [MeasurableSpace α] (p : Pmf α) : Measure α :=
  p.toOuterMeasure.toMeasure ((toOuterMeasure_caratheodory p).symm ▸ le_top)
#align pmf.to_measure Pmf.toMeasure
-/

variable [MeasurableSpace α] (p : Pmf α) (s t : Set α)

/- warning: pmf.to_outer_measure_apply_le_to_measure_apply -> Pmf.toOuterMeasure_apply_le_toMeasure_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α p) s) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 p) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α p) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 p)) s)
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_apply_le_to_measure_apply Pmf.toOuterMeasure_apply_le_toMeasure_applyₓ'. -/
theorem toOuterMeasure_apply_le_toMeasure_apply : p.toOuterMeasure s ≤ p.toMeasure s :=
  le_toMeasure_apply p.toOuterMeasure _ s
#align pmf.to_outer_measure_apply_le_to_measure_apply Pmf.toOuterMeasure_apply_le_toMeasure_apply

#print Pmf.toMeasure_apply_eq_toOuterMeasure_apply /-
theorem toMeasure_apply_eq_toOuterMeasure_apply (hs : MeasurableSet s) :
    p.toMeasure s = p.toOuterMeasure s :=
  toMeasure_apply p.toOuterMeasure _ hs
#align pmf.to_measure_apply_eq_to_outer_measure_apply Pmf.toMeasure_apply_eq_toOuterMeasure_apply
-/

/- warning: pmf.to_measure_apply -> Pmf.toMeasure_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 p) s) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p) x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 p)) s) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero s (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p) x)))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_apply Pmf.toMeasure_applyₓ'. -/
theorem toMeasure_apply (hs : MeasurableSet s) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s hs).trans (p.to_outer_measure_apply s)
#align pmf.to_measure_apply Pmf.toMeasure_apply

#print Pmf.toMeasure_apply_singleton /-
theorem toMeasure_apply_singleton (a : α) (h : MeasurableSet ({a} : Set α)) :
    p.toMeasure {a} = p a := by
  simp [to_measure_apply_eq_to_outer_measure_apply _ _ h, to_outer_measure_apply_singleton]
#align pmf.to_measure_apply_singleton Pmf.toMeasure_apply_singleton
-/

/- warning: pmf.to_measure_apply_eq_zero_iff -> Pmf.toMeasure_apply_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> (Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 p) s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Pmf.support.{u1} α p) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> (Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 p)) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Pmf.support.{u1} α p) s))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_apply_eq_zero_iff Pmf.toMeasure_apply_eq_zero_iffₓ'. -/
theorem toMeasure_apply_eq_zero_iff (hs : MeasurableSet s) :
    p.toMeasure s = 0 ↔ Disjoint p.support s := by
  rw [to_measure_apply_eq_to_outer_measure_apply p s hs, to_outer_measure_apply_eq_zero_iff]
#align pmf.to_measure_apply_eq_zero_iff Pmf.toMeasure_apply_eq_zero_iff

#print Pmf.toMeasure_apply_eq_one_iff /-
theorem toMeasure_apply_eq_one_iff (hs : MeasurableSet s) : p.toMeasure s = 1 ↔ p.support ⊆ s :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s hs : p.toMeasure s = p.toOuterMeasure s).symm ▸
    p.toOuterMeasure_apply_eq_one_iff s
#align pmf.to_measure_apply_eq_one_iff Pmf.toMeasure_apply_eq_one_iff
-/

/- warning: pmf.to_measure_apply_inter_support -> Pmf.toMeasure_apply_inter_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> (MeasurableSet.{u1} α _inst_1 (Pmf.support.{u1} α p)) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 p) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Pmf.support.{u1} α p))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 p) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> (MeasurableSet.{u1} α _inst_1 (Pmf.support.{u1} α p)) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 p)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Pmf.support.{u1} α p))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 p)) s))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_apply_inter_support Pmf.toMeasure_apply_inter_supportₓ'. -/
@[simp]
theorem toMeasure_apply_inter_support (hs : MeasurableSet s) (hp : MeasurableSet p.support) :
    p.toMeasure (s ∩ p.support) = p.toMeasure s := by
  simp [p.to_measure_apply_eq_to_outer_measure_apply s hs,
    p.to_measure_apply_eq_to_outer_measure_apply _ (hs.inter hp)]
#align pmf.to_measure_apply_inter_support Pmf.toMeasure_apply_inter_support

/- warning: pmf.to_measure_mono -> Pmf.toMeasure_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) {s : Set.{u1} α} {t : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (MeasurableSet.{u1} α _inst_1 t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Pmf.support.{u1} α p)) t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 p) s) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 p) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) {s : Set.{u1} α} {t : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (MeasurableSet.{u1} α _inst_1 t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Pmf.support.{u1} α p)) t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 p)) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 p)) t))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_mono Pmf.toMeasure_monoₓ'. -/
theorem toMeasure_mono {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : s ∩ p.support ⊆ t) : p.toMeasure s ≤ p.toMeasure t := by
  simpa only [p.to_measure_apply_eq_to_outer_measure_apply, hs, ht] using to_outer_measure_mono p h
#align pmf.to_measure_mono Pmf.toMeasure_mono

/- warning: pmf.to_measure_apply_eq_of_inter_support_eq -> Pmf.toMeasure_apply_eq_of_inter_support_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) {s : Set.{u1} α} {t : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (MeasurableSet.{u1} α _inst_1 t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Pmf.support.{u1} α p)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t (Pmf.support.{u1} α p))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 p) s) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 p) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) {s : Set.{u1} α} {t : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (MeasurableSet.{u1} α _inst_1 t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Pmf.support.{u1} α p)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t (Pmf.support.{u1} α p))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 p)) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 p)) t))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_apply_eq_of_inter_support_eq Pmf.toMeasure_apply_eq_of_inter_support_eqₓ'. -/
theorem toMeasure_apply_eq_of_inter_support_eq {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : s ∩ p.support = t ∩ p.support) : p.toMeasure s = p.toMeasure t := by
  simpa only [p.to_measure_apply_eq_to_outer_measure_apply, hs, ht] using
    to_outer_measure_apply_eq_of_inter_support_eq p h
#align pmf.to_measure_apply_eq_of_inter_support_eq Pmf.toMeasure_apply_eq_of_inter_support_eq

section MeasurableSingletonClass

variable [MeasurableSingletonClass α]

#print Pmf.toMeasure_injective /-
theorem toMeasure_injective : (toMeasure : Pmf α → Measure α).Injective := fun p q h =>
  Pmf.ext fun x =>
    (p.toMeasure_apply_singleton x <| measurableSet_singleton x).symm.trans
      ((congr_fun (congr_arg _ h) _).trans <|
        q.toMeasure_apply_singleton x <| measurableSet_singleton x)
#align pmf.to_measure_injective Pmf.toMeasure_injective
-/

#print Pmf.toMeasure_inj /-
@[simp]
theorem toMeasure_inj {p q : Pmf α} : p.toMeasure = q.toMeasure ↔ p = q :=
  toMeasure_injective.eq_iff
#align pmf.to_measure_inj Pmf.toMeasure_inj
-/

/- warning: pmf.to_measure_apply_finset -> Pmf.toMeasure_apply_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] (s : Finset.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 p) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (x : α) => coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] (s : Finset.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 p)) (Finset.toSet.{u1} α s)) (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (x : α) => FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p x))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_apply_finset Pmf.toMeasure_apply_finsetₓ'. -/
@[simp]
theorem toMeasure_apply_finset (s : Finset α) : p.toMeasure s = ∑ x in s, p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s s.MeasurableSet).trans
    (p.toOuterMeasure_apply_finset s)
#align pmf.to_measure_apply_finset Pmf.toMeasure_apply_finset

/- warning: pmf.to_measure_apply_of_finite -> Pmf.toMeasure_apply_of_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) (s : Set.{u1} α) [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1], (Set.Finite.{u1} α s) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 p) s) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p) x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) (s : Set.{u1} α) [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1], (Set.Finite.{u1} α s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 p)) s) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero s (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p) x)))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_apply_of_finite Pmf.toMeasure_apply_of_finiteₓ'. -/
theorem toMeasure_apply_of_finite (hs : s.Finite) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s hs.MeasurableSet).trans (p.to_outer_measure_apply s)
#align pmf.to_measure_apply_of_finite Pmf.toMeasure_apply_of_finite

/- warning: pmf.to_measure_apply_fintype -> Pmf.toMeasure_apply_fintype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) (s : Set.{u1} α) [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] [_inst_3 : Fintype.{u1} α], Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 p) s) (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.univ.{u1} α _inst_3) (fun (x : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (p : Pmf.{u1} α) (s : Set.{u1} α) [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] [_inst_3 : Fintype.{u1} α], Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 p)) s) (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.univ.{u1} α _inst_3) (fun (x : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero s (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p) x))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_apply_fintype Pmf.toMeasure_apply_fintypeₓ'. -/
@[simp]
theorem toMeasure_apply_fintype [Fintype α] : p.toMeasure s = ∑ x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s s.toFinite.MeasurableSet).trans
    (p.toOuterMeasure_apply_fintype s)
#align pmf.to_measure_apply_fintype Pmf.toMeasure_apply_fintype

end MeasurableSingletonClass

end Measure

end Pmf

namespace MeasureTheory

open Pmf

namespace Measure

#print MeasureTheory.Measure.toPmf /-
/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
we can convert any probability measure into a `pmf`, where the mass of a point
is the measure of the singleton set under the original measure. -/
def toPmf [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
    [h : ProbabilityMeasure μ] : Pmf α :=
  ⟨fun x => μ ({x} : Set α),
    ENNReal.summable.hasSum_iff.2
      (trans
        (symm <|
          (tsum_indicator_apply_singleton μ Set.univ MeasurableSet.univ).symm.trans
            (tsum_congr fun x => congr_fun (Set.indicator_univ _) x))
        h.measure_univ)⟩
#align measure_theory.measure.to_pmf MeasureTheory.Measure.toPmf
-/

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
  [ProbabilityMeasure μ]

#print MeasureTheory.Measure.toPmf_apply /-
theorem toPmf_apply (x : α) : μ.toPmf x = μ {x} :=
  rfl
#align measure_theory.measure.to_pmf_apply MeasureTheory.Measure.toPmf_apply
-/

#print MeasureTheory.Measure.toPmf_toMeasure /-
@[simp]
theorem toPmf_toMeasure : μ.toPmf.toMeasure = μ :=
  Measure.ext fun s hs => by
    simpa only [μ.to_pmf.to_measure_apply s hs, ← μ.tsum_indicator_apply_singleton s hs]
#align measure_theory.measure.to_pmf_to_measure MeasureTheory.Measure.toPmf_toMeasure
-/

end Measure

end MeasureTheory

namespace Pmf

open MeasureTheory

#print Pmf.toMeasure.probabilityMeasure /-
/-- The measure associated to a `pmf` by `to_measure` is a probability measure -/
instance toMeasure.probabilityMeasure [MeasurableSpace α] (p : Pmf α) :
    ProbabilityMeasure p.toMeasure :=
  ⟨by
    simpa only [MeasurableSet.univ, to_measure_apply_eq_to_outer_measure_apply, Set.indicator_univ,
      to_outer_measure_apply, ENNReal.coe_eq_one] using tsum_coe p⟩
#align pmf.to_measure.is_probability_measure Pmf.toMeasure.probabilityMeasure
-/

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (p : Pmf α) (μ : Measure α)
  [ProbabilityMeasure μ]

#print Pmf.toMeasure_toPmf /-
@[simp]
theorem toMeasure_toPmf : p.toMeasure.toPmf = p :=
  Pmf.ext fun x => by
    rw [← p.to_measure_apply_singleton x (measurable_set_singleton x), p.to_measure.to_pmf_apply]
#align pmf.to_measure_to_pmf Pmf.toMeasure_toPmf
-/

#print Pmf.toMeasure_eq_iff_eq_toPmf /-
theorem toMeasure_eq_iff_eq_toPmf (μ : Measure α) [ProbabilityMeasure μ] :
    p.toMeasure = μ ↔ p = μ.toPmf := by rw [← to_measure_inj, measure.to_pmf_to_measure]
#align pmf.to_measure_eq_iff_eq_to_pmf Pmf.toMeasure_eq_iff_eq_toPmf
-/

#print Pmf.toPmf_eq_iff_toMeasure_eq /-
theorem toPmf_eq_iff_toMeasure_eq (μ : Measure α) [ProbabilityMeasure μ] :
    μ.toPmf = p ↔ μ = p.toMeasure := by rw [← to_measure_inj, measure.to_pmf_to_measure]
#align pmf.to_pmf_eq_iff_to_measure_eq Pmf.toPmf_eq_iff_toMeasure_eq
-/

end Pmf

