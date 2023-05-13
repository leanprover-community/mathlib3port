/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Bhavik Mehta

! This file was ported from Lean 3 source module probability.cond_count
! leanprover-community/mathlib commit bd15ff41b70f5e2cc210f26f25a8d5c53b20d3de
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Probability.ConditionalProbability

/-!
# Classical probability

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The classical formulation of probability states that the probability of an event occurring in a
finite probability space is the ratio of that event to all possible events.
This notion can be expressed with measure theory using
the counting measure. In particular, given the sets `s` and `t`, we define the probability of `t`
occuring in `s` to be `|s|⁻¹ * |s ∩ t|`. With this definition, we recover the the probability over
the entire sample space when `s = set.univ`.

Classical probability is often used in combinatorics and we prove some useful lemmas in this file
for that purpose.

## Main definition

* `probability_theory.cond_count`: given a set `s`, `cond_count s` is the counting measure
  conditioned on `s`. This is a probability measure when `s` is finite and nonempty.

## Notes

The original aim of this file is to provide a measure theoretic method of describing the
probability an element of a set `s` satisfies some predicate `P`. Our current formulation still
allow us to describe this by abusing the definitional equality of sets and predicates by simply
writing `cond_count s P`. We should avoid this however as none of the lemmas are written for
predicates.
-/


noncomputable section

open ProbabilityTheory

open MeasureTheory MeasurableSpace

namespace ProbabilityTheory

variable {Ω : Type _} [MeasurableSpace Ω]

#print ProbabilityTheory.condCount /-
/-- Given a set `s`, `cond_count s` is the counting measure conditioned on `s`. In particular,
`cond_count s t` is the proportion of `s` that is contained in `t`.

This is a probability measure when `s` is finite and nonempty and is given by
`probability_theory.cond_count_is_probability_measure`. -/
def condCount (s : Set Ω) : Measure Ω :=
  Measure.count[|s]
#align probability_theory.cond_count ProbabilityTheory.condCount
-/

#print ProbabilityTheory.condCount_empty_meas /-
@[simp]
theorem condCount_empty_meas : (condCount ∅ : Measure Ω) = 0 := by simp [cond_count]
#align probability_theory.cond_count_empty_meas ProbabilityTheory.condCount_empty_meas
-/

/- warning: probability_theory.cond_count_empty -> ProbabilityTheory.condCount_empty is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] {s : Set.{u1} Ω}, Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} Ω) (Set.hasEmptyc.{u1} Ω))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] {s : Set.{u1} Ω}, Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 s)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} Ω) (Set.instEmptyCollectionSet.{u1} Ω))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align probability_theory.cond_count_empty ProbabilityTheory.condCount_emptyₓ'. -/
theorem condCount_empty {s : Set Ω} : condCount s ∅ = 0 := by simp
#align probability_theory.cond_count_empty ProbabilityTheory.condCount_empty

/- warning: probability_theory.finite_of_cond_count_ne_zero -> ProbabilityTheory.finite_of_condCount_ne_zero is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] {s : Set.{u1} Ω} {t : Set.{u1} Ω}, (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 s) t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Set.Finite.{u1} Ω s)
but is expected to have type
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] {s : Set.{u1} Ω} {t : Set.{u1} Ω}, (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 s)) t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Set.Finite.{u1} Ω s)
Case conversion may be inaccurate. Consider using '#align probability_theory.finite_of_cond_count_ne_zero ProbabilityTheory.finite_of_condCount_ne_zeroₓ'. -/
theorem finite_of_condCount_ne_zero {s t : Set Ω} (h : condCount s t ≠ 0) : s.Finite :=
  by
  by_contra hs'
  simpa [cond_count, cond, measure.count_apply_infinite hs'] using h
#align probability_theory.finite_of_cond_count_ne_zero ProbabilityTheory.finite_of_condCount_ne_zero

/- warning: probability_theory.cond_count_univ -> ProbabilityTheory.condCount_univ is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : Fintype.{u1} Ω] {s : Set.{u1} Ω}, Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Set.univ.{u1} Ω)) s) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (MeasureTheory.Measure.count.{u1} Ω _inst_1) s) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENNReal (HasLiftT.mk.{1, 1} Nat ENNReal (CoeTCₓ.coe.{1, 1} Nat ENNReal (Nat.castCoe.{0} ENNReal (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) (Fintype.card.{u1} Ω _inst_2)))
but is expected to have type
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : Fintype.{u1} Ω] {s : Set.{u1} Ω}, Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Set.univ.{u1} Ω))) s) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (MeasureTheory.Measure.count.{u1} Ω _inst_1)) s) (Nat.cast.{0} ENNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (Fintype.card.{u1} Ω _inst_2)))
Case conversion may be inaccurate. Consider using '#align probability_theory.cond_count_univ ProbabilityTheory.condCount_univₓ'. -/
theorem condCount_univ [Fintype Ω] {s : Set Ω} :
    condCount Set.univ s = Measure.count s / Fintype.card Ω :=
  by
  rw [cond_count, cond_apply _ MeasurableSet.univ, ← ENNReal.div_eq_inv_mul, Set.univ_inter]
  congr
  rw [← Finset.coe_univ, measure.count_apply, finset.univ.tsum_subtype' fun _ => (1 : ENNReal)]
  · simp [Finset.card_univ]
  · exact (@Finset.coe_univ Ω _).symm ▸ MeasurableSet.univ
#align probability_theory.cond_count_univ ProbabilityTheory.condCount_univ

variable [MeasurableSingletonClass Ω]

#print ProbabilityTheory.condCount_probabilityMeasure /-
theorem condCount_probabilityMeasure {s : Set Ω} (hs : s.Finite) (hs' : s.Nonempty) :
    ProbabilityMeasure (condCount s) :=
  {
    measure_univ :=
      by
      rw [cond_count, cond_apply _ hs.measurable_set, Set.inter_univ, ENNReal.inv_mul_cancel]
      · exact fun h => hs'.ne_empty <| measure.empty_of_count_eq_zero h
      · exact (measure.count_apply_lt_top.2 hs).Ne }
#align probability_theory.cond_count_is_probability_measure ProbabilityTheory.condCount_probabilityMeasure
-/

/- warning: probability_theory.cond_count_singleton -> ProbabilityTheory.condCount_singleton is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : MeasurableSingletonClass.{u1} Ω _inst_1] (ω : Ω) (t : Set.{u1} Ω) [_inst_3 : Decidable (Membership.Mem.{u1, u1} Ω (Set.{u1} Ω) (Set.hasMem.{u1} Ω) ω t)], Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Singleton.singleton.{u1, u1} Ω (Set.{u1} Ω) (Set.hasSingleton.{u1} Ω) ω)) t) (ite.{1} ENNReal (Membership.Mem.{u1, u1} Ω (Set.{u1} Ω) (Set.hasMem.{u1} Ω) ω t) _inst_3 (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : MeasurableSingletonClass.{u1} Ω _inst_1] (ω : Ω) (t : Set.{u1} Ω) [_inst_3 : Decidable (Membership.mem.{u1, u1} Ω (Set.{u1} Ω) (Set.instMembershipSet.{u1} Ω) ω t)], Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Singleton.singleton.{u1, u1} Ω (Set.{u1} Ω) (Set.instSingletonSet.{u1} Ω) ω))) t) (ite.{1} ENNReal (Membership.mem.{u1, u1} Ω (Set.{u1} Ω) (Set.instMembershipSet.{u1} Ω) ω t) _inst_3 (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align probability_theory.cond_count_singleton ProbabilityTheory.condCount_singletonₓ'. -/
theorem condCount_singleton (ω : Ω) (t : Set Ω) [Decidable (ω ∈ t)] :
    condCount {ω} t = if ω ∈ t then 1 else 0 :=
  by
  rw [cond_count, cond_apply _ (measurable_set_singleton ω), measure.count_singleton, inv_one,
    one_mul]
  split_ifs
  · rw [(by simpa : ({ω} : Set Ω) ∩ t = {ω}), measure.count_singleton]
  · rw [(by simpa : ({ω} : Set Ω) ∩ t = ∅), measure.count_empty]
#align probability_theory.cond_count_singleton ProbabilityTheory.condCount_singleton

variable {s t u : Set Ω}

#print ProbabilityTheory.condCount_inter_self /-
theorem condCount_inter_self (hs : s.Finite) : condCount s (s ∩ t) = condCount s t := by
  rw [cond_count, cond_inter_self _ hs.measurable_set]
#align probability_theory.cond_count_inter_self ProbabilityTheory.condCount_inter_self
-/

#print ProbabilityTheory.condCount_self /-
theorem condCount_self (hs : s.Finite) (hs' : s.Nonempty) : condCount s s = 1 :=
  by
  rw [cond_count, cond_apply _ hs.measurable_set, Set.inter_self, ENNReal.inv_mul_cancel]
  · exact fun h => hs'.ne_empty <| measure.empty_of_count_eq_zero h
  · exact (measure.count_apply_lt_top.2 hs).Ne
#align probability_theory.cond_count_self ProbabilityTheory.condCount_self
-/

#print ProbabilityTheory.condCount_eq_one_of /-
theorem condCount_eq_one_of (hs : s.Finite) (hs' : s.Nonempty) (ht : s ⊆ t) : condCount s t = 1 :=
  by
  haveI := cond_count_is_probability_measure hs hs'
  refine' eq_of_le_of_not_lt prob_le_one _
  rw [not_lt, ← cond_count_self hs hs']
  exact measure_mono ht
#align probability_theory.cond_count_eq_one_of ProbabilityTheory.condCount_eq_one_of
-/

#print ProbabilityTheory.pred_true_of_condCount_eq_one /-
theorem pred_true_of_condCount_eq_one (h : condCount s t = 1) : s ⊆ t :=
  by
  have hsf :=
    finite_of_cond_count_ne_zero
      (by
        rw [h]
        exact one_ne_zero)
  rw [cond_count, cond_apply _ hsf.measurable_set, mul_comm] at h
  replace h := ENNReal.eq_inv_of_mul_eq_one_left h
  rw [inv_inv, measure.count_apply_finite _ hsf, measure.count_apply_finite _ (hsf.inter_of_left _),
    Nat.cast_inj] at h
  suffices s ∩ t = s by exact this ▸ fun x hx => hx.2
  rw [← @Set.Finite.toFinset_inj _ _ _ (hsf.inter_of_left _) hsf]
  exact Finset.eq_of_subset_of_card_le (Set.Finite.toFinset_mono <| s.inter_subset_left t) h.ge
#align probability_theory.pred_true_of_cond_count_eq_one ProbabilityTheory.pred_true_of_condCount_eq_one
-/

/- warning: probability_theory.cond_count_eq_zero_iff -> ProbabilityTheory.condCount_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : MeasurableSingletonClass.{u1} Ω _inst_1] {s : Set.{u1} Ω} {t : Set.{u1} Ω}, (Set.Finite.{u1} Ω s) -> (Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 s) t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{succ u1} (Set.{u1} Ω) (Inter.inter.{u1} (Set.{u1} Ω) (Set.hasInter.{u1} Ω) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} Ω) (Set.hasEmptyc.{u1} Ω))))
but is expected to have type
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : MeasurableSingletonClass.{u1} Ω _inst_1] {s : Set.{u1} Ω} {t : Set.{u1} Ω}, (Set.Finite.{u1} Ω s) -> (Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 s)) t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{succ u1} (Set.{u1} Ω) (Inter.inter.{u1} (Set.{u1} Ω) (Set.instInterSet.{u1} Ω) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} Ω) (Set.instEmptyCollectionSet.{u1} Ω))))
Case conversion may be inaccurate. Consider using '#align probability_theory.cond_count_eq_zero_iff ProbabilityTheory.condCount_eq_zero_iffₓ'. -/
theorem condCount_eq_zero_iff (hs : s.Finite) : condCount s t = 0 ↔ s ∩ t = ∅ := by
  simp [cond_count, cond_apply _ hs.measurable_set, measure.count_apply_eq_top,
    Set.not_infinite.2 hs, measure.count_apply_finite _ (hs.inter_of_left _)]
#align probability_theory.cond_count_eq_zero_iff ProbabilityTheory.condCount_eq_zero_iff

#print ProbabilityTheory.condCount_of_univ /-
theorem condCount_of_univ (hs : s.Finite) (hs' : s.Nonempty) : condCount s Set.univ = 1 :=
  condCount_eq_one_of hs hs' s.subset_univ
#align probability_theory.cond_count_of_univ ProbabilityTheory.condCount_of_univ
-/

#print ProbabilityTheory.condCount_inter /-
theorem condCount_inter (hs : s.Finite) :
    condCount s (t ∩ u) = condCount (s ∩ t) u * condCount s t :=
  by
  by_cases hst : s ∩ t = ∅
  ·
    rw [hst, cond_count_empty_meas, measure.coe_zero, Pi.zero_apply, MulZeroClass.zero_mul,
      cond_count_eq_zero_iff hs, ← Set.inter_assoc, hst, Set.empty_inter]
  rw [cond_count, cond_count, cond_apply _ hs.measurable_set, cond_apply _ hs.measurable_set,
    cond_apply _ (hs.inter_of_left _).MeasurableSet, mul_comm _ (measure.count (s ∩ t)), ←
    mul_assoc, mul_comm _ (measure.count (s ∩ t)), ← mul_assoc, ENNReal.mul_inv_cancel, one_mul,
    mul_comm, Set.inter_assoc]
  · rwa [← measure.count_eq_zero_iff] at hst
  · exact (measure.count_apply_lt_top.2 <| hs.inter_of_left _).Ne
#align probability_theory.cond_count_inter ProbabilityTheory.condCount_inter
-/

#print ProbabilityTheory.condCount_inter' /-
theorem condCount_inter' (hs : s.Finite) :
    condCount s (t ∩ u) = condCount (s ∩ u) t * condCount s u :=
  by
  rw [← Set.inter_comm]
  exact cond_count_inter hs
#align probability_theory.cond_count_inter' ProbabilityTheory.condCount_inter'
-/

/- warning: probability_theory.cond_count_union -> ProbabilityTheory.condCount_union is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : MeasurableSingletonClass.{u1} Ω _inst_1] {s : Set.{u1} Ω} {t : Set.{u1} Ω} {u : Set.{u1} Ω}, (Set.Finite.{u1} Ω s) -> (Disjoint.{u1} (Set.{u1} Ω) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} Ω) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} Ω) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} Ω) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} Ω) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} Ω) (Set.completeBooleanAlgebra.{u1} Ω)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} Ω) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} Ω) (Set.booleanAlgebra.{u1} Ω))) t u) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 s) (Union.union.{u1} (Set.{u1} Ω) (Set.hasUnion.{u1} Ω) t u)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 s) t) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 s) u)))
but is expected to have type
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : MeasurableSingletonClass.{u1} Ω _inst_1] {s : Set.{u1} Ω} {t : Set.{u1} Ω} {u : Set.{u1} Ω}, (Set.Finite.{u1} Ω s) -> (Disjoint.{u1} (Set.{u1} Ω) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} Ω) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} Ω) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} Ω) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} Ω) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} Ω) (Set.instCompleteBooleanAlgebraSet.{u1} Ω)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} Ω) (Preorder.toLE.{u1} (Set.{u1} Ω) (PartialOrder.toPreorder.{u1} (Set.{u1} Ω) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} Ω) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} Ω) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} Ω) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} Ω) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} Ω) (Set.instCompleteBooleanAlgebraSet.{u1} Ω)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} Ω) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} Ω) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} Ω) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} Ω) (Set.instCompleteBooleanAlgebraSet.{u1} Ω)))))) t u) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 s)) (Union.union.{u1} (Set.{u1} Ω) (Set.instUnionSet.{u1} Ω) t u)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 s)) t) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 s)) u)))
Case conversion may be inaccurate. Consider using '#align probability_theory.cond_count_union ProbabilityTheory.condCount_unionₓ'. -/
theorem condCount_union (hs : s.Finite) (htu : Disjoint t u) :
    condCount s (t ∪ u) = condCount s t + condCount s u :=
  by
  rw [cond_count, cond_apply _ hs.measurable_set, cond_apply _ hs.measurable_set,
    cond_apply _ hs.measurable_set, Set.inter_union_distrib_left, measure_union, mul_add]
  exacts[htu.mono inf_le_right inf_le_right, (hs.inter_of_left _).MeasurableSet]
#align probability_theory.cond_count_union ProbabilityTheory.condCount_union

/- warning: probability_theory.cond_count_compl -> ProbabilityTheory.condCount_compl is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : MeasurableSingletonClass.{u1} Ω _inst_1] {s : Set.{u1} Ω} (t : Set.{u1} Ω), (Set.Finite.{u1} Ω s) -> (Set.Nonempty.{u1} Ω s) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 s) t) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 s) (HasCompl.compl.{u1} (Set.{u1} Ω) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} Ω) (Set.booleanAlgebra.{u1} Ω)) t))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))))
but is expected to have type
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : MeasurableSingletonClass.{u1} Ω _inst_1] {s : Set.{u1} Ω} (t : Set.{u1} Ω), (Set.Finite.{u1} Ω s) -> (Set.Nonempty.{u1} Ω s) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 s)) t) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 s)) (HasCompl.compl.{u1} (Set.{u1} Ω) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} Ω) (Set.instBooleanAlgebraSet.{u1} Ω)) t))) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))
Case conversion may be inaccurate. Consider using '#align probability_theory.cond_count_compl ProbabilityTheory.condCount_complₓ'. -/
theorem condCount_compl (t : Set Ω) (hs : s.Finite) (hs' : s.Nonempty) :
    condCount s t + condCount s (tᶜ) = 1 := by
  rw [← cond_count_union hs disjoint_compl_right, Set.union_compl_self,
    (cond_count_is_probability_measure hs hs').measure_univ]
#align probability_theory.cond_count_compl ProbabilityTheory.condCount_compl

/- warning: probability_theory.cond_count_disjoint_union -> ProbabilityTheory.condCount_disjoint_union is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : MeasurableSingletonClass.{u1} Ω _inst_1] {s : Set.{u1} Ω} {t : Set.{u1} Ω} {u : Set.{u1} Ω}, (Set.Finite.{u1} Ω s) -> (Set.Finite.{u1} Ω t) -> (Disjoint.{u1} (Set.{u1} Ω) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} Ω) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} Ω) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} Ω) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} Ω) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} Ω) (Set.completeBooleanAlgebra.{u1} Ω)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} Ω) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} Ω) (Set.booleanAlgebra.{u1} Ω))) s t) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 s) u) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Union.union.{u1} (Set.{u1} Ω) (Set.hasUnion.{u1} Ω) s t)) s)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 t) u) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Union.union.{u1} (Set.{u1} Ω) (Set.hasUnion.{u1} Ω) s t)) t))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Union.union.{u1} (Set.{u1} Ω) (Set.hasUnion.{u1} Ω) s t)) u))
but is expected to have type
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : MeasurableSingletonClass.{u1} Ω _inst_1] {s : Set.{u1} Ω} {t : Set.{u1} Ω} {u : Set.{u1} Ω}, (Set.Finite.{u1} Ω s) -> (Set.Finite.{u1} Ω t) -> (Disjoint.{u1} (Set.{u1} Ω) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} Ω) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} Ω) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} Ω) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} Ω) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} Ω) (Set.instCompleteBooleanAlgebraSet.{u1} Ω)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} Ω) (Preorder.toLE.{u1} (Set.{u1} Ω) (PartialOrder.toPreorder.{u1} (Set.{u1} Ω) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} Ω) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} Ω) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} Ω) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} Ω) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} Ω) (Set.instCompleteBooleanAlgebraSet.{u1} Ω)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} Ω) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} Ω) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} Ω) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} Ω) (Set.instCompleteBooleanAlgebraSet.{u1} Ω)))))) s t) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 s)) u) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Union.union.{u1} (Set.{u1} Ω) (Set.instUnionSet.{u1} Ω) s t))) s)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 t)) u) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Union.union.{u1} (Set.{u1} Ω) (Set.instUnionSet.{u1} Ω) s t))) t))) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Union.union.{u1} (Set.{u1} Ω) (Set.instUnionSet.{u1} Ω) s t))) u))
Case conversion may be inaccurate. Consider using '#align probability_theory.cond_count_disjoint_union ProbabilityTheory.condCount_disjoint_unionₓ'. -/
theorem condCount_disjoint_union (hs : s.Finite) (ht : t.Finite) (hst : Disjoint s t) :
    condCount s u * condCount (s ∪ t) s + condCount t u * condCount (s ∪ t) t =
      condCount (s ∪ t) u :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | hs') <;> rcases t.eq_empty_or_nonempty with (rfl | ht')
  · simp
  · simp [cond_count_self ht ht']
  · simp [cond_count_self hs hs']
  rw [cond_count, cond_count, cond_count, cond_apply _ hs.measurable_set,
    cond_apply _ ht.measurable_set, cond_apply _ (hs.union ht).MeasurableSet,
    cond_apply _ (hs.union ht).MeasurableSet, cond_apply _ (hs.union ht).MeasurableSet]
  conv_lhs =>
    rw [Set.union_inter_cancel_left, Set.union_inter_cancel_right,
      mul_comm (measure.count (s ∪ t))⁻¹, mul_comm (measure.count (s ∪ t))⁻¹, ← mul_assoc, ←
      mul_assoc, mul_comm _ (measure.count s), mul_comm _ (measure.count t), ← mul_assoc, ←
      mul_assoc]
  rw [ENNReal.mul_inv_cancel, ENNReal.mul_inv_cancel, one_mul, one_mul, ← add_mul, ← measure_union,
    Set.union_inter_distrib_right, mul_comm]
  exacts[hst.mono inf_le_left inf_le_left, (ht.inter_of_left _).MeasurableSet,
    measure.count_ne_zero ht', (measure.count_apply_lt_top.2 ht).Ne, measure.count_ne_zero hs',
    (measure.count_apply_lt_top.2 hs).Ne]
#align probability_theory.cond_count_disjoint_union ProbabilityTheory.condCount_disjoint_union

/- warning: probability_theory.cond_count_add_compl_eq -> ProbabilityTheory.condCount_add_compl_eq is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : MeasurableSingletonClass.{u1} Ω _inst_1] {s : Set.{u1} Ω} (u : Set.{u1} Ω) (t : Set.{u1} Ω), (Set.Finite.{u1} Ω s) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Inter.inter.{u1} (Set.{u1} Ω) (Set.hasInter.{u1} Ω) s u)) t) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 s) u)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Inter.inter.{u1} (Set.{u1} Ω) (Set.hasInter.{u1} Ω) s (HasCompl.compl.{u1} (Set.{u1} Ω) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} Ω) (Set.booleanAlgebra.{u1} Ω)) u))) t) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 s) (HasCompl.compl.{u1} (Set.{u1} Ω) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} Ω) (Set.booleanAlgebra.{u1} Ω)) u)))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} Ω _inst_1) (fun (_x : MeasureTheory.Measure.{u1} Ω _inst_1) => (Set.{u1} Ω) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} Ω _inst_1) (ProbabilityTheory.condCount.{u1} Ω _inst_1 s) t))
but is expected to have type
  forall {Ω : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} Ω] [_inst_2 : MeasurableSingletonClass.{u1} Ω _inst_1] {s : Set.{u1} Ω} (u : Set.{u1} Ω) (t : Set.{u1} Ω), (Set.Finite.{u1} Ω s) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Inter.inter.{u1} (Set.{u1} Ω) (Set.instInterSet.{u1} Ω) s u))) t) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 s)) u)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 (Inter.inter.{u1} (Set.{u1} Ω) (Set.instInterSet.{u1} Ω) s (HasCompl.compl.{u1} (Set.{u1} Ω) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} Ω) (Set.instBooleanAlgebraSet.{u1} Ω)) u)))) t) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 s)) (HasCompl.compl.{u1} (Set.{u1} Ω) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} Ω) (Set.instBooleanAlgebraSet.{u1} Ω)) u)))) (MeasureTheory.OuterMeasure.measureOf.{u1} Ω (MeasureTheory.Measure.toOuterMeasure.{u1} Ω _inst_1 (ProbabilityTheory.condCount.{u1} Ω _inst_1 s)) t))
Case conversion may be inaccurate. Consider using '#align probability_theory.cond_count_add_compl_eq ProbabilityTheory.condCount_add_compl_eqₓ'. -/
/-- A version of the law of total probability for counting probabilites. -/
theorem condCount_add_compl_eq (u t : Set Ω) (hs : s.Finite) :
    condCount (s ∩ u) t * condCount s u + condCount (s ∩ uᶜ) t * condCount s (uᶜ) = condCount s t :=
  by
  conv_rhs =>
    rw [(by simp : s = s ∩ u ∪ s ∩ uᶜ), ←
      cond_count_disjoint_union (hs.inter_of_left _) (hs.inter_of_left _)
        (disjoint_compl_right.mono inf_le_right inf_le_right)]
  simp [cond_count_inter_self hs]
#align probability_theory.cond_count_add_compl_eq ProbabilityTheory.condCount_add_compl_eq

end ProbabilityTheory

