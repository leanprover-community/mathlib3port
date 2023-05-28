/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module measure_theory.measure.outer_measure
! leanprover-community/mathlib commit 343e80208d29d2d15f8050b929aa50fe4ce71b55
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecificLimits.Basic
import Mathbin.MeasureTheory.PiSystem
import Mathbin.Data.Countable.Basic
import Mathbin.Data.Fin.VecNotation

/-!
# Outer Measures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An outer measure is a function `μ : set α → ℝ≥0∞`, from the powerset of a type to the extended
nonnegative real numbers that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is monotone;
3. `μ` is countably subadditive. This means that the outer measure of a countable union is at most
   the sum of the outer measure on the individual sets.

Note that we do not need `α` to be measurable to define an outer measure.

The outer measures on a type `α` form a complete lattice.

Given an arbitrary function `m : set α → ℝ≥0∞` that sends `∅` to `0` we can define an outer
measure on `α` that on `s` is defined to be the infimum of `∑ᵢ, m (sᵢ)` for all collections of sets
`sᵢ` that cover `s`. This is the unique maximal outer measure that is at most the given function.
We also define this for functions `m` defined on a subset of `set α`, by treating the function as
having value `∞` outside its domain.

Given an outer measure `m`, the Carathéodory-measurable sets are the sets `s` such that
for all sets `t` we have `m t = m (t ∩ s) + m (t \ s)`. This forms a measurable space.

## Main definitions and statements

* `outer_measure.bounded_by` is the greatest outer measure that is at most the given function.
  If you know that the given functions sends `∅` to `0`, then `outer_measure.of_function` is a
  special case.
* `caratheodory` is the Carathéodory-measurable space of an outer measure.
* `Inf_eq_of_function_Inf_gen` is a characterization of the infimum of outer measures.
* `induced_outer_measure` is the measure induced by a function on a subset of `set α`

## References

* <https://en.wikipedia.org/wiki/Outer_measure>
* <https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_criterion>

## Tags

outer measure, Carathéodory-measurable, Carathéodory's criterion
-/


noncomputable section

open Set Function Filter

open TopologicalSpace (SecondCountableTopology)

open Classical BigOperators NNReal Topology ENNReal MeasureTheory

namespace MeasureTheory

#print MeasureTheory.OuterMeasure /-
/-- An outer measure is a countably subadditive monotone function that sends `∅` to `0`. -/
structure OuterMeasure (α : Type _) where
  measureOf : Set α → ℝ≥0∞
  Empty : measure_of ∅ = 0
  mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measure_of s₁ ≤ measure_of s₂
  iUnion_nat : ∀ s : ℕ → Set α, measure_of (⋃ i, s i) ≤ ∑' i, measure_of (s i)
#align measure_theory.outer_measure MeasureTheory.OuterMeasure
-/

namespace OuterMeasure

section Basic

variable {α β R R' : Type _} {ms : Set (OuterMeasure α)} {m : OuterMeasure α}

instance : CoeFun (OuterMeasure α) fun _ => Set α → ℝ≥0∞ :=
  ⟨fun m => m.measureOf⟩

@[simp]
theorem measureOf_eq_coe (m : OuterMeasure α) : m.measureOf = m :=
  rfl
#align measure_theory.outer_measure.measure_of_eq_coe MeasureTheory.OuterMeasure.measureOf_eq_coe

/- warning: measure_theory.outer_measure.empty' -> MeasureTheory.OuterMeasure.empty' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.empty' MeasureTheory.OuterMeasure.empty'ₓ'. -/
@[simp]
theorem empty' (m : OuterMeasure α) : m ∅ = 0 :=
  m.Empty
#align measure_theory.outer_measure.empty' MeasureTheory.OuterMeasure.empty'

/- warning: measure_theory.outer_measure.mono' -> MeasureTheory.OuterMeasure.mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m s₁) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m s₂))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m s₁) (MeasureTheory.OuterMeasure.measureOf.{u1} α m s₂))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.mono' MeasureTheory.OuterMeasure.mono'ₓ'. -/
theorem mono' (m : OuterMeasure α) {s₁ s₂} (h : s₁ ⊆ s₂) : m s₁ ≤ m s₂ :=
  m.mono h
#align measure_theory.outer_measure.mono' MeasureTheory.OuterMeasure.mono'

/- warning: measure_theory.outer_measure.mono_null -> MeasureTheory.OuterMeasure.mono_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.mono_null MeasureTheory.OuterMeasure.mono_nullₓ'. -/
theorem mono_null (m : OuterMeasure α) {s t} (h : s ⊆ t) (ht : m t = 0) : m s = 0 :=
  nonpos_iff_eq_zero.mp <| ht ▸ m.mono' h
#align measure_theory.outer_measure.mono_null MeasureTheory.OuterMeasure.mono_null

/- warning: measure_theory.outer_measure.pos_of_subset_ne_zero -> MeasureTheory.OuterMeasure.pos_of_subset_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {a : Set.{u1} α} {b : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) a b) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m b))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {a : Set.{u1} α} {b : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) a b) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} α m b))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.pos_of_subset_ne_zero MeasureTheory.OuterMeasure.pos_of_subset_ne_zeroₓ'. -/
theorem pos_of_subset_ne_zero (m : OuterMeasure α) {a b : Set α} (hs : a ⊆ b) (hnz : m a ≠ 0) :
    0 < m b :=
  lt_of_lt_of_le (pos_iff_ne_zero.mpr hnz) (m.mono hs)
#align measure_theory.outer_measure.pos_of_subset_ne_zero MeasureTheory.OuterMeasure.pos_of_subset_ne_zero

/- warning: measure_theory.outer_measure.Union -> MeasureTheory.OuterMeasure.iUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {β : Type.{u2}} [_inst_1 : Countable.{succ u2} β] (s : β -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (i : β) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (s i)))
but is expected to have type
  forall {α : Type.{u2}} (m : MeasureTheory.OuterMeasure.{u2} α) {β : Type.{u1}} [_inst_1 : Countable.{succ u1} β] (s : β -> (Set.{u2} α)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u2} α m (Set.iUnion.{u2, succ u1} α β (fun (i : β) => s i))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (i : β) => MeasureTheory.OuterMeasure.measureOf.{u2} α m (s i)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.Union MeasureTheory.OuterMeasure.iUnionₓ'. -/
protected theorem iUnion (m : OuterMeasure α) {β} [Countable β] (s : β → Set α) :
    m (⋃ i, s i) ≤ ∑' i, m (s i) :=
  rel_iSup_tsum m m.Empty (· ≤ ·) m.iUnion_nat s
#align measure_theory.outer_measure.Union MeasureTheory.OuterMeasure.iUnion

/- warning: measure_theory.outer_measure.Union_null -> MeasureTheory.OuterMeasure.iUnion_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Countable.{succ u2} β] (m : MeasureTheory.OuterMeasure.{u1} α) {s : β -> (Set.{u1} α)}, (forall (i : β), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (s i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Countable.{succ u2} β] (m : MeasureTheory.OuterMeasure.{u1} α) {s : β -> (Set.{u1} α)}, (forall (i : β), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (s i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.Union_null MeasureTheory.OuterMeasure.iUnion_nullₓ'. -/
theorem iUnion_null [Countable β] (m : OuterMeasure α) {s : β → Set α} (h : ∀ i, m (s i) = 0) :
    m (⋃ i, s i) = 0 := by simpa [h] using m.Union s
#align measure_theory.outer_measure.Union_null MeasureTheory.OuterMeasure.iUnion_null

/- warning: measure_theory.outer_measure.Union_null_iff -> MeasureTheory.OuterMeasure.iUnion_null_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Countable.{succ u2} β] (m : MeasureTheory.OuterMeasure.{u1} α) {s : β -> (Set.{u1} α)}, Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (forall (i : β), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (s i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Countable.{succ u2} β] (m : MeasureTheory.OuterMeasure.{u1} α) {s : β -> (Set.{u1} α)}, Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall (i : β), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (s i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.Union_null_iff MeasureTheory.OuterMeasure.iUnion_null_iffₓ'. -/
@[simp]
theorem iUnion_null_iff [Countable β] (m : OuterMeasure α) {s : β → Set α} :
    m (⋃ i, s i) = 0 ↔ ∀ i, m (s i) = 0 :=
  ⟨fun h i => m.mono_null (subset_iUnion _ _) h, m.iUnion_null⟩
#align measure_theory.outer_measure.Union_null_iff MeasureTheory.OuterMeasure.iUnion_null_iff

/- warning: measure_theory.outer_measure.Union_null_iff' -> MeasureTheory.OuterMeasure.iUnion_null_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {ι : Prop} {s : ι -> (Set.{u1} α)}, Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Set.iUnion.{u1, 0} α ι (fun (i : ι) => s i))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (forall (i : ι), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (s i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {ι : Prop} {s : ι -> (Set.{u1} α)}, Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Set.iUnion.{u1, 0} α ι (fun (i : ι) => s i))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall (i : ι), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (s i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.Union_null_iff' MeasureTheory.OuterMeasure.iUnion_null_iff'ₓ'. -/
/-- A version of `Union_null_iff` for unions indexed by Props.
TODO: in the long run it would be better to combine this with `Union_null_iff` by
generalising to `Sort`. -/
@[simp]
theorem iUnion_null_iff' (m : OuterMeasure α) {ι : Prop} {s : ι → Set α} :
    m (⋃ i, s i) = 0 ↔ ∀ i, m (s i) = 0 := by by_cases i : ι <;> simp [i]
#align measure_theory.outer_measure.Union_null_iff' MeasureTheory.OuterMeasure.iUnion_null_iff'

/- warning: measure_theory.outer_measure.bUnion_null_iff -> MeasureTheory.OuterMeasure.biUnion_null_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Set.{u2} β}, (Set.Countable.{u2} β s) -> (forall {t : β -> (Set.{u1} α)}, Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Set.iUnion.{u1, succ u2} α β (fun (i : β) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) => t i)))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (forall (i : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (t i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u2} α) {s : Set.{u1} β}, (Set.Countable.{u1} β s) -> (forall {t : β -> (Set.{u2} α)}, Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} α m (Set.iUnion.{u2, succ u1} α β (fun (i : β) => Set.iUnion.{u2, 0} α (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) i s) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) i s) => t i)))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall (i : β), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) i s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} α m (t i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.bUnion_null_iff MeasureTheory.OuterMeasure.biUnion_null_iffₓ'. -/
theorem biUnion_null_iff (m : OuterMeasure α) {s : Set β} (hs : s.Countable) {t : β → Set α} :
    m (⋃ i ∈ s, t i) = 0 ↔ ∀ i ∈ s, m (t i) = 0 := by haveI := hs.to_encodable;
  rw [bUnion_eq_Union, Union_null_iff, SetCoe.forall']
#align measure_theory.outer_measure.bUnion_null_iff MeasureTheory.OuterMeasure.biUnion_null_iff

/- warning: measure_theory.outer_measure.sUnion_null_iff -> MeasureTheory.OuterMeasure.sUnion_null_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {S : Set.{u1} (Set.{u1} α)}, (Set.Countable.{u1} (Set.{u1} α) S) -> (Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Set.sUnion.{u1} α S)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s S) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {S : Set.{u1} (Set.{u1} α)}, (Set.Countable.{u1} (Set.{u1} α) S) -> (Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Set.sUnion.{u1} α S)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s S) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.sUnion_null_iff MeasureTheory.OuterMeasure.sUnion_null_iffₓ'. -/
theorem sUnion_null_iff (m : OuterMeasure α) {S : Set (Set α)} (hS : S.Countable) :
    m (⋃₀ S) = 0 ↔ ∀ s ∈ S, m s = 0 := by rw [sUnion_eq_bUnion, m.bUnion_null_iff hS]
#align measure_theory.outer_measure.sUnion_null_iff MeasureTheory.OuterMeasure.sUnion_null_iff

/- warning: measure_theory.outer_measure.Union_finset -> MeasureTheory.OuterMeasure.iUnion_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (m : MeasureTheory.OuterMeasure.{u1} α) (s : β -> (Set.{u1} α)) (t : Finset.{u2} β), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Set.iUnion.{u1, succ u2} α β (fun (i : β) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) i t) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) i t) => s i)))) (Finset.sum.{0, u2} ENNReal β (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) t (fun (i : β) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (s i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u2} α) (s : β -> (Set.{u2} α)) (t : Finset.{u1} β), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u2} α m (Set.iUnion.{u2, succ u1} α β (fun (i : β) => Set.iUnion.{u2, 0} α (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) i t) (fun (H : Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) i t) => s i)))) (Finset.sum.{0, u1} ENNReal β (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) t (fun (i : β) => MeasureTheory.OuterMeasure.measureOf.{u2} α m (s i)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.Union_finset MeasureTheory.OuterMeasure.iUnion_finsetₓ'. -/
protected theorem iUnion_finset (m : OuterMeasure α) (s : β → Set α) (t : Finset β) :
    m (⋃ i ∈ t, s i) ≤ ∑ i in t, m (s i) :=
  rel_iSup_sum m m.Empty (· ≤ ·) m.iUnion_nat s t
#align measure_theory.outer_measure.Union_finset MeasureTheory.OuterMeasure.iUnion_finset

/- warning: measure_theory.outer_measure.union -> MeasureTheory.OuterMeasure.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) (s₁ : Set.{u1} α) (s₂ : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m s₁) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m s₂))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) (s₁ : Set.{u1} α) (s₂ : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m s₁) (MeasureTheory.OuterMeasure.measureOf.{u1} α m s₂))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.union MeasureTheory.OuterMeasure.unionₓ'. -/
protected theorem union (m : OuterMeasure α) (s₁ s₂ : Set α) : m (s₁ ∪ s₂) ≤ m s₁ + m s₂ :=
  rel_sup_add m m.Empty (· ≤ ·) m.iUnion_nat s₁ s₂
#align measure_theory.outer_measure.union MeasureTheory.OuterMeasure.union

/- warning: measure_theory.outer_measure.null_of_locally_null -> MeasureTheory.OuterMeasure.null_of_locally_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.SecondCountableTopology.{u1} α _inst_1] (m : MeasureTheory.OuterMeasure.{u1} α) (s : Set.{u1} α), (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u (nhdsWithin.{u1} α _inst_1 x s)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u (nhdsWithin.{u1} α _inst_1 x s)) => Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m u) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.SecondCountableTopology.{u1} α _inst_1] (m : MeasureTheory.OuterMeasure.{u1} α) (s : Set.{u1} α), (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) u (nhdsWithin.{u1} α _inst_1 x s)) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m u) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.null_of_locally_null MeasureTheory.OuterMeasure.null_of_locally_nullₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/-- If a set has zero measure in a neighborhood of each of its points, then it has zero measure
in a second-countable space. -/
theorem null_of_locally_null [TopologicalSpace α] [SecondCountableTopology α] (m : OuterMeasure α)
    (s : Set α) (hs : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, m u = 0) : m s = 0 :=
  by
  choose! u hxu hu₀ using hs
  obtain ⟨t, ts, t_count, ht⟩ : ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ s ⊆ ⋃ x ∈ t, u x :=
    TopologicalSpace.countable_cover_nhdsWithin hxu
  apply m.mono_null ht
  exact (m.bUnion_null_iff t_count).2 fun x hx => hu₀ x (ts hx)
#align measure_theory.outer_measure.null_of_locally_null MeasureTheory.OuterMeasure.null_of_locally_null

/- warning: measure_theory.outer_measure.exists_mem_forall_mem_nhds_within_pos -> MeasureTheory.OuterMeasure.exists_mem_forall_mem_nhds_within_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.SecondCountableTopology.{u1} α _inst_1] (m : MeasureTheory.OuterMeasure.{u1} α) {s : Set.{u1} α}, (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => forall (t : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (nhdsWithin.{u1} α _inst_1 x s)) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m t)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.SecondCountableTopology.{u1} α _inst_1] (m : MeasureTheory.OuterMeasure.{u1} α) {s : Set.{u1} α}, (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (forall (t : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t (nhdsWithin.{u1} α _inst_1 x s)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} α m t)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.exists_mem_forall_mem_nhds_within_pos MeasureTheory.OuterMeasure.exists_mem_forall_mem_nhds_within_posₓ'. -/
/-- If `m s ≠ 0`, then for some point `x ∈ s` and any `t ∈ 𝓝[s] x` we have `0 < m t`. -/
theorem exists_mem_forall_mem_nhds_within_pos [TopologicalSpace α] [SecondCountableTopology α]
    (m : OuterMeasure α) {s : Set α} (hs : m s ≠ 0) : ∃ x ∈ s, ∀ t ∈ 𝓝[s] x, 0 < m t :=
  by
  contrapose! hs
  simp only [nonpos_iff_eq_zero, ← exists_prop] at hs
  exact m.null_of_locally_null s hs
#align measure_theory.outer_measure.exists_mem_forall_mem_nhds_within_pos MeasureTheory.OuterMeasure.exists_mem_forall_mem_nhds_within_pos

/- warning: measure_theory.outer_measure.Union_of_tendsto_zero -> MeasureTheory.OuterMeasure.iUnion_of_tendsto_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : ι -> (Set.{u1} α)} (l : Filter.{u2} ι) [_inst_1 : Filter.NeBot.{u2} ι l], (Filter.Tendsto.{u2, 0} ι ENNReal (fun (k : ι) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.iUnion.{u1, succ u2} α ι (fun (n : ι) => s n)) (s k))) l (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Set.iUnion.{u1, succ u2} α ι (fun (n : ι) => s n))) (iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (n : ι) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (s n))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : ι -> (Set.{u1} α)} (l : Filter.{u2} ι) [_inst_1 : Filter.NeBot.{u2} ι l], (Filter.Tendsto.{u2, 0} ι ENNReal (fun (k : ι) => MeasureTheory.OuterMeasure.measureOf.{u1} α m (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (n : ι) => s n)) (s k))) l (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Set.iUnion.{u1, succ u2} α ι (fun (n : ι) => s n))) (iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (n : ι) => MeasureTheory.OuterMeasure.measureOf.{u1} α m (s n))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.Union_of_tendsto_zero MeasureTheory.OuterMeasure.iUnion_of_tendsto_zeroₓ'. -/
/-- If `s : ι → set α` is a sequence of sets, `S = ⋃ n, s n`, and `m (S \ s n)` tends to zero along
some nontrivial filter (usually `at_top` on `ι = ℕ`), then `m S = ⨆ n, m (s n)`. -/
theorem iUnion_of_tendsto_zero {ι} (m : OuterMeasure α) {s : ι → Set α} (l : Filter ι) [NeBot l]
    (h0 : Tendsto (fun k => m ((⋃ n, s n) \ s k)) l (𝓝 0)) : m (⋃ n, s n) = ⨆ n, m (s n) :=
  by
  set S := ⋃ n, s n
  set M := ⨆ n, m (s n)
  have hsS : ∀ {k}, s k ⊆ S := fun k => subset_Union _ _
  refine' le_antisymm _ (iSup_le fun n => m.mono hsS)
  have A : ∀ k, m S ≤ M + m (S \ s k) := fun k =>
    calc
      m S = m (s k ∪ S \ s k) := by rw [union_diff_self, union_eq_self_of_subset_left hsS]
      _ ≤ m (s k) + m (S \ s k) := (m.union _ _)
      _ ≤ M + m (S \ s k) := add_le_add_right (le_iSup _ k) _
      
  have B : tendsto (fun k => M + m (S \ s k)) l (𝓝 (M + 0)) := tendsto_const_nhds.add h0
  rw [add_zero] at B
  exact ge_of_tendsto' B A
#align measure_theory.outer_measure.Union_of_tendsto_zero MeasureTheory.OuterMeasure.iUnion_of_tendsto_zero

/- warning: measure_theory.outer_measure.Union_nat_of_monotone_of_tsum_ne_top -> MeasureTheory.OuterMeasure.iUnion_nat_of_monotone_of_tsum_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Nat -> (Set.{u1} α)}, (forall (n : Nat), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s n) (s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) -> (Ne.{1} ENNReal (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (k : Nat) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (s k)))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => s n))) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (s n))))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Nat -> (Set.{u1} α)}, (forall (n : Nat), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (s n) (s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) -> (Ne.{1} ENNReal (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (k : Nat) => MeasureTheory.OuterMeasure.measureOf.{u1} α m (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (s k)))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall [inst._@.Mathlib.MeasureTheory.Measure.OuterMeasure._hyg.2629 : forall (i : Nat), DecidablePred.{succ u1} α (fun (x._@.Mathlib.MeasureTheory.Measure.OuterMeasure._hyg.2641 : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x._@.Mathlib.MeasureTheory.Measure.OuterMeasure._hyg.2641 (s i))], Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => s n))) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => MeasureTheory.OuterMeasure.measureOf.{u1} α m (s n))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.Union_nat_of_monotone_of_tsum_ne_top MeasureTheory.OuterMeasure.iUnion_nat_of_monotone_of_tsum_ne_topₓ'. -/
/-- If `s : ℕ → set α` is a monotone sequence of sets such that `∑' k, m (s (k + 1) \ s k) ≠ ∞`,
then `m (⋃ n, s n) = ⨆ n, m (s n)`. -/
theorem iUnion_nat_of_monotone_of_tsum_ne_top (m : OuterMeasure α) {s : ℕ → Set α}
    (h_mono : ∀ n, s n ⊆ s (n + 1)) (h0 : (∑' k, m (s (k + 1) \ s k)) ≠ ∞) :
    m (⋃ n, s n) = ⨆ n, m (s n) :=
  by
  refine' m.Union_of_tendsto_zero at_top _
  refine' tendsto_nhds_bot_mono' (ENNReal.tendsto_sum_nat_add _ h0) fun n => _
  refine' (m.mono _).trans (m.Union _)
  -- Current goal: `(⋃ k, s k) \ s n ⊆ ⋃ k, s (k + n + 1) \ s (k + n)`
  have h' : Monotone s := @monotone_nat_of_le_succ (Set α) _ _ h_mono
  simp only [diff_subset_iff, Union_subset_iff]
  intro i x hx
  rcases Nat.findX ⟨i, hx⟩ with ⟨j, hj, hlt⟩; clear hx i
  cases' le_or_lt j n with hjn hnj; · exact Or.inl (h' hjn hj)
  have : j - (n + 1) + n + 1 = j := by rw [add_assoc, tsub_add_cancel_of_le hnj.nat_succ_le]
  refine' Or.inr (mem_Union.2 ⟨j - (n + 1), _, hlt _ _⟩)
  · rwa [this]
  · rw [← Nat.succ_le_iff, Nat.succ_eq_add_one, this]
#align measure_theory.outer_measure.Union_nat_of_monotone_of_tsum_ne_top MeasureTheory.OuterMeasure.iUnion_nat_of_monotone_of_tsum_ne_top

/- warning: measure_theory.outer_measure.le_inter_add_diff -> MeasureTheory.OuterMeasure.le_inter_add_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasureTheory.OuterMeasure.{u1} α} {t : Set.{u1} α} (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m t) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasureTheory.OuterMeasure.{u1} α} {t : Set.{u1} α} (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m t) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)) (MeasureTheory.OuterMeasure.measureOf.{u1} α m (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.le_inter_add_diff MeasureTheory.OuterMeasure.le_inter_add_diffₓ'. -/
theorem le_inter_add_diff {m : OuterMeasure α} {t : Set α} (s : Set α) :
    m t ≤ m (t ∩ s) + m (t \ s) := by convert m.union _ _; rw [inter_union_diff t s]
#align measure_theory.outer_measure.le_inter_add_diff MeasureTheory.OuterMeasure.le_inter_add_diff

/- warning: measure_theory.outer_measure.diff_null -> MeasureTheory.OuterMeasure.diff_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) (s : Set.{u1} α) {t : Set.{u1} α}, (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m s))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) (s : Set.{u1} α) {t : Set.{u1} α}, (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)) (MeasureTheory.OuterMeasure.measureOf.{u1} α m s))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.diff_null MeasureTheory.OuterMeasure.diff_nullₓ'. -/
theorem diff_null (m : OuterMeasure α) (s : Set α) {t : Set α} (ht : m t = 0) : m (s \ t) = m s :=
  by
  refine' le_antisymm (m.mono <| diff_subset _ _) _
  calc
    m s ≤ m (s ∩ t) + m (s \ t) := le_inter_add_diff _
    _ ≤ m t + m (s \ t) := (add_le_add_right (m.mono <| inter_subset_right _ _) _)
    _ = m (s \ t) := by rw [ht, zero_add]
    
#align measure_theory.outer_measure.diff_null MeasureTheory.OuterMeasure.diff_null

/- warning: measure_theory.outer_measure.union_null -> MeasureTheory.OuterMeasure.union_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m s₁) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m s₂) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m s₁) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m s₂) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.union_null MeasureTheory.OuterMeasure.union_nullₓ'. -/
theorem union_null (m : OuterMeasure α) {s₁ s₂ : Set α} (h₁ : m s₁ = 0) (h₂ : m s₂ = 0) :
    m (s₁ ∪ s₂) = 0 := by simpa [h₁, h₂] using m.union s₁ s₂
#align measure_theory.outer_measure.union_null MeasureTheory.OuterMeasure.union_null

#print MeasureTheory.OuterMeasure.coe_fn_injective /-
theorem coe_fn_injective : Injective fun (μ : OuterMeasure α) (s : Set α) => μ s := fun μ₁ μ₂ h =>
  by cases μ₁; cases μ₂; congr ; exact h
#align measure_theory.outer_measure.coe_fn_injective MeasureTheory.OuterMeasure.coe_fn_injective
-/

#print MeasureTheory.OuterMeasure.ext /-
@[ext]
theorem ext {μ₁ μ₂ : OuterMeasure α} (h : ∀ s, μ₁ s = μ₂ s) : μ₁ = μ₂ :=
  coe_fn_injective <| funext h
#align measure_theory.outer_measure.ext MeasureTheory.OuterMeasure.ext
-/

#print MeasureTheory.OuterMeasure.ext_nonempty /-
/-- A version of `measure_theory.outer_measure.ext` that assumes `μ₁ s = μ₂ s` on all *nonempty*
sets `s`, and gets `μ₁ ∅ = μ₂ ∅` from `measure_theory.outer_measure.empty'`. -/
theorem ext_nonempty {μ₁ μ₂ : OuterMeasure α} (h : ∀ s : Set α, s.Nonempty → μ₁ s = μ₂ s) :
    μ₁ = μ₂ :=
  ext fun s => s.eq_empty_or_nonempty.elim (fun he => by rw [he, empty', empty']) (h s)
#align measure_theory.outer_measure.ext_nonempty MeasureTheory.OuterMeasure.ext_nonempty
-/

instance : Zero (OuterMeasure α) :=
  ⟨{  measureOf := fun _ => 0
      Empty := rfl
      mono := fun _ _ _ => le_refl 0
      iUnion_nat := fun s => zero_le _ }⟩

/- warning: measure_theory.outer_measure.coe_zero -> MeasureTheory.OuterMeasure.coe_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} ((Set.{u1} α) -> ENNReal) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (OfNat.ofNat.{u1} (MeasureTheory.OuterMeasure.{u1} α) 0 (OfNat.mk.{u1} (MeasureTheory.OuterMeasure.{u1} α) 0 (Zero.zero.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instZero.{u1} α))))) (OfNat.ofNat.{u1} ((Set.{u1} α) -> ENNReal) 0 (OfNat.mk.{u1} ((Set.{u1} α) -> ENNReal) 0 (Zero.zero.{u1} ((Set.{u1} α) -> ENNReal) (Pi.instZero.{u1, 0} (Set.{u1} α) (fun (ᾰ : Set.{u1} α) => ENNReal) (fun (i : Set.{u1} α) => ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} ((Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.measureOf.{u1} α (OfNat.ofNat.{u1} (MeasureTheory.OuterMeasure.{u1} α) 0 (Zero.toOfNat0.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instZero.{u1} α)))) (OfNat.ofNat.{u1} ((Set.{u1} α) -> ENNReal) 0 (Zero.toOfNat0.{u1} ((Set.{u1} α) -> ENNReal) (Pi.instZero.{u1, 0} (Set.{u1} α) (fun (a._@.Mathlib.MeasureTheory.Measure.OuterMeasure._hyg.11 : Set.{u1} α) => ENNReal) (fun (i : Set.{u1} α) => instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.coe_zero MeasureTheory.OuterMeasure.coe_zeroₓ'. -/
@[simp]
theorem coe_zero : ⇑(0 : OuterMeasure α) = 0 :=
  rfl
#align measure_theory.outer_measure.coe_zero MeasureTheory.OuterMeasure.coe_zero

instance : Inhabited (OuterMeasure α) :=
  ⟨0⟩

instance : Add (OuterMeasure α) :=
  ⟨fun m₁ m₂ =>
    { measureOf := fun s => m₁ s + m₂ s
      Empty := show m₁ ∅ + m₂ ∅ = 0 by simp [outer_measure.empty]
      mono := fun s₁ s₂ h => add_le_add (m₁.mono h) (m₂.mono h)
      iUnion_nat := fun s =>
        calc
          m₁ (⋃ i, s i) + m₂ (⋃ i, s i) ≤ (∑' i, m₁ (s i)) + ∑' i, m₂ (s i) :=
            add_le_add (m₁.iUnion_nat s) (m₂.iUnion_nat s)
          _ = _ := ENNReal.tsum_add.symm
           }⟩

/- warning: measure_theory.outer_measure.coe_add -> MeasureTheory.OuterMeasure.coe_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m₁ : MeasureTheory.OuterMeasure.{u1} α) (m₂ : MeasureTheory.OuterMeasure.{u1} α), Eq.{succ u1} ((Set.{u1} α) -> ENNReal) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (instHAdd.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instAdd.{u1} α)) m₁ m₂)) (HAdd.hAdd.{u1, u1, u1} ((Set.{u1} α) -> ENNReal) ((Set.{u1} α) -> ENNReal) ((Set.{u1} α) -> ENNReal) (instHAdd.{u1} ((Set.{u1} α) -> ENNReal) (Pi.instAdd.{u1, 0} (Set.{u1} α) (fun (ᾰ : Set.{u1} α) => ENNReal) (fun (i : Set.{u1} α) => Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m₁) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m₂))
but is expected to have type
  forall {α : Type.{u1}} (m₁ : MeasureTheory.OuterMeasure.{u1} α) (m₂ : MeasureTheory.OuterMeasure.{u1} α), Eq.{succ u1} ((Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.measureOf.{u1} α (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (instHAdd.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instAdd.{u1} α)) m₁ m₂)) (HAdd.hAdd.{u1, u1, u1} ((Set.{u1} α) -> ENNReal) ((Set.{u1} α) -> ENNReal) ((Set.{u1} α) -> ENNReal) (instHAdd.{u1} ((Set.{u1} α) -> ENNReal) (Pi.instAdd.{u1, 0} (Set.{u1} α) (fun (ᾰ : Set.{u1} α) => ENNReal) (fun (i : Set.{u1} α) => Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m₁) (MeasureTheory.OuterMeasure.measureOf.{u1} α m₂))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.coe_add MeasureTheory.OuterMeasure.coe_addₓ'. -/
@[simp]
theorem coe_add (m₁ m₂ : OuterMeasure α) : ⇑(m₁ + m₂) = m₁ + m₂ :=
  rfl
#align measure_theory.outer_measure.coe_add MeasureTheory.OuterMeasure.coe_add

/- warning: measure_theory.outer_measure.add_apply -> MeasureTheory.OuterMeasure.add_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m₁ : MeasureTheory.OuterMeasure.{u1} α) (m₂ : MeasureTheory.OuterMeasure.{u1} α) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (instHAdd.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instAdd.{u1} α)) m₁ m₂) s) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m₁ s) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m₂ s))
but is expected to have type
  forall {α : Type.{u1}} (m₁ : MeasureTheory.OuterMeasure.{u1} α) (m₂ : MeasureTheory.OuterMeasure.{u1} α) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (instHAdd.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instAdd.{u1} α)) m₁ m₂) s) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m₁ s) (MeasureTheory.OuterMeasure.measureOf.{u1} α m₂ s))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.add_apply MeasureTheory.OuterMeasure.add_applyₓ'. -/
theorem add_apply (m₁ m₂ : OuterMeasure α) (s : Set α) : (m₁ + m₂) s = m₁ s + m₂ s :=
  rfl
#align measure_theory.outer_measure.add_apply MeasureTheory.OuterMeasure.add_apply

section SMul

variable [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]

variable [SMul R' ℝ≥0∞] [IsScalarTower R' ℝ≥0∞ ℝ≥0∞]

instance : SMul R (OuterMeasure α) :=
  ⟨fun c m =>
    { measureOf := fun s => c • m s
      Empty := by rw [← smul_one_mul c (_ : ℝ≥0∞), empty', MulZeroClass.mul_zero]
      mono := fun s t h => by
        rw [← smul_one_mul c (m s), ← smul_one_mul c (m t)]
        exact ENNReal.mul_left_mono (m.mono h)
      iUnion_nat := fun s =>
        by
        simp_rw [← smul_one_mul c (m _), ENNReal.tsum_mul_left]
        exact ENNReal.mul_left_mono (m.Union _) }⟩

/- warning: measure_theory.outer_measure.coe_smul -> MeasureTheory.OuterMeasure.coe_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : SMul.{u2, 0} R ENNReal] [_inst_2 : IsScalarTower.{u2, 0, 0} R ENNReal ENNReal _inst_1 (Mul.toSMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) _inst_1] (c : R) (m : MeasureTheory.OuterMeasure.{u1} α), Eq.{succ u1} ((Set.{u1} α) -> ENNReal) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (SMul.smul.{u2, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.hasSmul.{u1, u2} α R _inst_1 _inst_2) c m)) (SMul.smul.{u2, u1} R ((Set.{u1} α) -> ENNReal) (Function.hasSMul.{u1, u2, 0} (Set.{u1} α) R ENNReal _inst_1) c (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m))
but is expected to have type
  forall {α : Type.{u2}} {R : Type.{u1}} [_inst_1 : SMul.{u1, 0} R ENNReal] [_inst_2 : IsScalarTower.{u1, 0, 0} R ENNReal ENNReal _inst_1 (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) _inst_1] (c : R) (m : MeasureTheory.OuterMeasure.{u2} α), Eq.{succ u2} ((Set.{u2} α) -> ENNReal) (MeasureTheory.OuterMeasure.measureOf.{u2} α (HSMul.hSMul.{u1, u2, u2} R (MeasureTheory.OuterMeasure.{u2} α) (MeasureTheory.OuterMeasure.{u2} α) (instHSMul.{u1, u2} R (MeasureTheory.OuterMeasure.{u2} α) (MeasureTheory.OuterMeasure.instSMul.{u2, u1} α R _inst_1 _inst_2)) c m)) (HSMul.hSMul.{u1, u2, u2} R ((Set.{u2} α) -> ENNReal) ((Set.{u2} α) -> ENNReal) (instHSMul.{u1, u2} R ((Set.{u2} α) -> ENNReal) (Pi.instSMul.{u2, 0, u1} (Set.{u2} α) R (fun (a._@.Mathlib.MeasureTheory.Measure.OuterMeasure._hyg.11 : Set.{u2} α) => ENNReal) (fun (i : Set.{u2} α) => _inst_1))) c (MeasureTheory.OuterMeasure.measureOf.{u2} α m))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.coe_smul MeasureTheory.OuterMeasure.coe_smulₓ'. -/
@[simp]
theorem coe_smul (c : R) (m : OuterMeasure α) : ⇑(c • m) = c • m :=
  rfl
#align measure_theory.outer_measure.coe_smul MeasureTheory.OuterMeasure.coe_smul

/- warning: measure_theory.outer_measure.smul_apply -> MeasureTheory.OuterMeasure.smul_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : SMul.{u2, 0} R ENNReal] [_inst_2 : IsScalarTower.{u2, 0, 0} R ENNReal ENNReal _inst_1 (Mul.toSMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) _inst_1] (c : R) (m : MeasureTheory.OuterMeasure.{u1} α) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (SMul.smul.{u2, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.hasSmul.{u1, u2} α R _inst_1 _inst_2) c m) s) (SMul.smul.{u2, 0} R ENNReal _inst_1 c (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m s))
but is expected to have type
  forall {α : Type.{u2}} {R : Type.{u1}} [_inst_1 : SMul.{u1, 0} R ENNReal] [_inst_2 : IsScalarTower.{u1, 0, 0} R ENNReal ENNReal _inst_1 (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) _inst_1] (c : R) (m : MeasureTheory.OuterMeasure.{u2} α) (s : Set.{u2} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} α (HSMul.hSMul.{u1, u2, u2} R (MeasureTheory.OuterMeasure.{u2} α) (MeasureTheory.OuterMeasure.{u2} α) (instHSMul.{u1, u2} R (MeasureTheory.OuterMeasure.{u2} α) (MeasureTheory.OuterMeasure.instSMul.{u2, u1} α R _inst_1 _inst_2)) c m) s) (HSMul.hSMul.{u1, 0, 0} R ENNReal ENNReal (instHSMul.{u1, 0} R ENNReal _inst_1) c (MeasureTheory.OuterMeasure.measureOf.{u2} α m s))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.smul_apply MeasureTheory.OuterMeasure.smul_applyₓ'. -/
theorem smul_apply (c : R) (m : OuterMeasure α) (s : Set α) : (c • m) s = c • m s :=
  rfl
#align measure_theory.outer_measure.smul_apply MeasureTheory.OuterMeasure.smul_apply

instance [SMulCommClass R R' ℝ≥0∞] : SMulCommClass R R' (OuterMeasure α) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

instance [SMul R R'] [IsScalarTower R R' ℝ≥0∞] : IsScalarTower R R' (OuterMeasure α) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

instance [SMul Rᵐᵒᵖ ℝ≥0∞] [IsCentralScalar R ℝ≥0∞] : IsCentralScalar R (OuterMeasure α) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

end SMul

instance [Monoid R] [MulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] : MulAction R (OuterMeasure α) :=
  Injective.mulAction _ coe_fn_injective coe_smul

#print MeasureTheory.OuterMeasure.addCommMonoid /-
instance addCommMonoid : AddCommMonoid (OuterMeasure α) :=
  Injective.addCommMonoid (show OuterMeasure α → Set α → ℝ≥0∞ from coeFn) coe_fn_injective rfl
    (fun _ _ => rfl) fun _ _ => rfl
#align measure_theory.outer_measure.add_comm_monoid MeasureTheory.OuterMeasure.addCommMonoid
-/

#print MeasureTheory.OuterMeasure.coeFnAddMonoidHom /-
/-- `coe_fn` as an `add_monoid_hom`. -/
@[simps]
def coeFnAddMonoidHom : OuterMeasure α →+ Set α → ℝ≥0∞ :=
  ⟨coeFn, coe_zero, coe_add⟩
#align measure_theory.outer_measure.coe_fn_add_monoid_hom MeasureTheory.OuterMeasure.coeFnAddMonoidHom
-/

instance [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] :
    DistribMulAction R (OuterMeasure α) :=
  Injective.distribMulAction coeFnAddMonoidHom coe_fn_injective coe_smul

instance [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] : Module R (OuterMeasure α) :=
  Injective.module R coeFnAddMonoidHom coe_fn_injective coe_smul

instance : Bot (OuterMeasure α) :=
  ⟨0⟩

#print MeasureTheory.OuterMeasure.coe_bot /-
@[simp]
theorem coe_bot : (⊥ : OuterMeasure α) = 0 :=
  rfl
#align measure_theory.outer_measure.coe_bot MeasureTheory.OuterMeasure.coe_bot
-/

#print MeasureTheory.OuterMeasure.instPartialOrder /-
instance MeasureTheory.OuterMeasure.instPartialOrder : PartialOrder (OuterMeasure α)
    where
  le m₁ m₂ := ∀ s, m₁ s ≤ m₂ s
  le_refl a s := le_rfl
  le_trans a b c hab hbc s := le_trans (hab s) (hbc s)
  le_antisymm a b hab hba := ext fun s => le_antisymm (hab s) (hba s)
#align measure_theory.outer_measure.outer_measure.partial_order MeasureTheory.OuterMeasure.instPartialOrder
-/

/- warning: measure_theory.outer_measure.outer_measure.order_bot -> MeasureTheory.OuterMeasure.OuterMeasure.orderBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, OrderBot.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toHasLe.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, OrderBot.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toLE.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.outer_measure.order_bot MeasureTheory.OuterMeasure.OuterMeasure.orderBotₓ'. -/
instance OuterMeasure.orderBot : OrderBot (OuterMeasure α) :=
  { OuterMeasure.instBot with
    bot_le := fun a s => by simp only [coe_zero, Pi.zero_apply, coe_bot, zero_le] }
#align measure_theory.outer_measure.outer_measure.order_bot MeasureTheory.OuterMeasure.OuterMeasure.orderBot

/- warning: measure_theory.outer_measure.univ_eq_zero_iff -> MeasureTheory.OuterMeasure.univ_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α), Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Set.univ.{u1} α)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{succ u1} (MeasureTheory.OuterMeasure.{u1} α) m (OfNat.ofNat.{u1} (MeasureTheory.OuterMeasure.{u1} α) 0 (OfNat.mk.{u1} (MeasureTheory.OuterMeasure.{u1} α) 0 (Zero.zero.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instZero.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α), Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Set.univ.{u1} α)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{succ u1} (MeasureTheory.OuterMeasure.{u1} α) m (OfNat.ofNat.{u1} (MeasureTheory.OuterMeasure.{u1} α) 0 (Zero.toOfNat0.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instZero.{u1} α))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.univ_eq_zero_iff MeasureTheory.OuterMeasure.univ_eq_zero_iffₓ'. -/
theorem univ_eq_zero_iff (m : OuterMeasure α) : m univ = 0 ↔ m = 0 :=
  ⟨fun h => bot_unique fun s => (m.mono' <| subset_univ s).trans_eq h, fun h => h.symm ▸ rfl⟩
#align measure_theory.outer_measure.univ_eq_zero_iff MeasureTheory.OuterMeasure.univ_eq_zero_iff

section Supremum

instance : SupSet (OuterMeasure α) :=
  ⟨fun ms =>
    { measureOf := fun s => ⨆ m ∈ ms, (m : OuterMeasure α) s
      Empty := nonpos_iff_eq_zero.1 <| iSup₂_le fun m h => le_of_eq m.Empty
      mono := fun s₁ s₂ hs => iSup₂_mono fun m hm => m.mono hs
      iUnion_nat := fun f =>
        iSup₂_le fun m hm =>
          calc
            m (⋃ i, f i) ≤ ∑' i : ℕ, m (f i) := m.iUnion_nat _
            _ ≤ ∑' i, ⨆ m ∈ ms, (m : OuterMeasure α) (f i) :=
              ENNReal.tsum_le_tsum fun i => le_iSup₂ m hm
             }⟩

instance : CompleteLattice (OuterMeasure α) :=
  { OuterMeasure.orderBot,
    completeLatticeOfSup (OuterMeasure α) fun ms =>
      ⟨fun m hm s => le_iSup₂ m hm, fun m hm s => iSup₂_le fun m' hm' => hm hm' s⟩ with }

/- warning: measure_theory.outer_measure.Sup_apply -> MeasureTheory.OuterMeasure.sSup_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (ms : Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (SupSet.sSup.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSupSet.{u1} α) ms) s) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (MeasureTheory.OuterMeasure.{u1} α) (fun (m : MeasureTheory.OuterMeasure.{u1} α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.hasMem.{u1} (MeasureTheory.OuterMeasure.{u1} α)) m ms) (fun (H : Membership.Mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.hasMem.{u1} (MeasureTheory.OuterMeasure.{u1} α)) m ms) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m s)))
but is expected to have type
  forall {α : Type.{u1}} (ms : Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (SupSet.sSup.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSupSet.{u1} α) ms) s) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasureTheory.OuterMeasure.{u1} α) (fun (m : MeasureTheory.OuterMeasure.{u1} α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.instMembershipSet.{u1} (MeasureTheory.OuterMeasure.{u1} α)) m ms) (fun (H : Membership.mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.instMembershipSet.{u1} (MeasureTheory.OuterMeasure.{u1} α)) m ms) => MeasureTheory.OuterMeasure.measureOf.{u1} α m s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.Sup_apply MeasureTheory.OuterMeasure.sSup_applyₓ'. -/
@[simp]
theorem sSup_apply (ms : Set (OuterMeasure α)) (s : Set α) :
    (sSup ms) s = ⨆ m ∈ ms, (m : OuterMeasure α) s :=
  rfl
#align measure_theory.outer_measure.Sup_apply MeasureTheory.OuterMeasure.sSup_apply

/- warning: measure_theory.outer_measure.supr_apply -> MeasureTheory.OuterMeasure.iSup_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (MeasureTheory.OuterMeasure.{u1} α)) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (iSup.{u1, u2} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSupSet.{u1} α) ι (fun (i : ι) => f i)) s) (iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (f i) s))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (MeasureTheory.OuterMeasure.{u1} α)) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (iSup.{u1, u2} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSupSet.{u1} α) ι (fun (i : ι) => f i)) s) (iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => MeasureTheory.OuterMeasure.measureOf.{u1} α (f i) s))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.supr_apply MeasureTheory.OuterMeasure.iSup_applyₓ'. -/
@[simp]
theorem iSup_apply {ι} (f : ι → OuterMeasure α) (s : Set α) : (⨆ i : ι, f i) s = ⨆ i, f i s := by
  rw [iSup, sSup_apply, iSup_range, iSup]
#align measure_theory.outer_measure.supr_apply MeasureTheory.OuterMeasure.iSup_apply

/- warning: measure_theory.outer_measure.coe_supr -> MeasureTheory.OuterMeasure.coe_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (MeasureTheory.OuterMeasure.{u1} α)), Eq.{succ u1} ((Set.{u1} α) -> ENNReal) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (iSup.{u1, u2} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSupSet.{u1} α) ι (fun (i : ι) => f i))) (iSup.{u1, u2} ((Set.{u1} α) -> ENNReal) (Pi.supSet.{u1, 0} (Set.{u1} α) (fun (ᾰ : Set.{u1} α) => ENNReal) (fun (i : Set.{u1} α) => ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) ι (fun (i : ι) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (MeasureTheory.OuterMeasure.{u1} α)), Eq.{succ u1} ((Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.measureOf.{u1} α (iSup.{u1, u2} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSupSet.{u1} α) ι (fun (i : ι) => f i))) (iSup.{u1, u2} ((Set.{u1} α) -> ENNReal) (Pi.supSet.{u1, 0} (Set.{u1} α) (fun (ᾰ : Set.{u1} α) => ENNReal) (fun (i : Set.{u1} α) => ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ι (fun (i : ι) => MeasureTheory.OuterMeasure.measureOf.{u1} α (f i)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.coe_supr MeasureTheory.OuterMeasure.coe_iSupₓ'. -/
@[norm_cast]
theorem coe_iSup {ι} (f : ι → OuterMeasure α) : ⇑(⨆ i, f i) = ⨆ i, f i :=
  funext fun s => by rw [iSup_apply, _root_.supr_apply]
#align measure_theory.outer_measure.coe_supr MeasureTheory.OuterMeasure.coe_iSup

/- warning: measure_theory.outer_measure.sup_apply -> MeasureTheory.OuterMeasure.sup_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m₁ : MeasureTheory.OuterMeasure.{u1} α) (m₂ : MeasureTheory.OuterMeasure.{u1} α) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Sup.sup.{u1} (MeasureTheory.OuterMeasure.{u1} α) (SemilatticeSup.toHasSup.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Lattice.toSemilatticeSup.{u1} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))))) m₁ m₂) s) (Sup.sup.{0} ENNReal (SemilatticeSup.toHasSup.{0} ENNReal ENNReal.semilatticeSup) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m₁ s) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m₂ s))
but is expected to have type
  forall {α : Type.{u1}} (m₁ : MeasureTheory.OuterMeasure.{u1} α) (m₂ : MeasureTheory.OuterMeasure.{u1} α) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (Sup.sup.{u1} (MeasureTheory.OuterMeasure.{u1} α) (SemilatticeSup.toSup.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Lattice.toSemilatticeSup.{u1} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))))) m₁ m₂) s) (Sup.sup.{0} ENNReal (SemilatticeSup.toSup.{0} ENNReal instENNRealSemilatticeSup) (MeasureTheory.OuterMeasure.measureOf.{u1} α m₁ s) (MeasureTheory.OuterMeasure.measureOf.{u1} α m₂ s))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.sup_apply MeasureTheory.OuterMeasure.sup_applyₓ'. -/
@[simp]
theorem sup_apply (m₁ m₂ : OuterMeasure α) (s : Set α) : (m₁ ⊔ m₂) s = m₁ s ⊔ m₂ s := by
  have := iSup_apply (fun b => cond b m₁ m₂) s <;> rwa [iSup_bool_eq, iSup_bool_eq] at this
#align measure_theory.outer_measure.sup_apply MeasureTheory.OuterMeasure.sup_apply

/- warning: measure_theory.outer_measure.smul_supr -> MeasureTheory.OuterMeasure.smul_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : SMul.{u2, 0} R ENNReal] [_inst_2 : IsScalarTower.{u2, 0, 0} R ENNReal ENNReal _inst_1 (Mul.toSMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) _inst_1] {ι : Sort.{u3}} (f : ι -> (MeasureTheory.OuterMeasure.{u1} α)) (c : R), Eq.{succ u1} (MeasureTheory.OuterMeasure.{u1} α) (SMul.smul.{u2, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.hasSmul.{u1, u2} α R _inst_1 _inst_2) c (iSup.{u1, u3} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSupSet.{u1} α) ι (fun (i : ι) => f i))) (iSup.{u1, u3} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSupSet.{u1} α) ι (fun (i : ι) => SMul.smul.{u2, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.hasSmul.{u1, u2} α R _inst_1 _inst_2) c (f i)))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u3}} [_inst_1 : SMul.{u3, 0} R ENNReal] [_inst_2 : IsScalarTower.{u3, 0, 0} R ENNReal ENNReal _inst_1 (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) _inst_1] {ι : Sort.{u2}} (f : ι -> (MeasureTheory.OuterMeasure.{u1} α)) (c : R), Eq.{succ u1} (MeasureTheory.OuterMeasure.{u1} α) (HSMul.hSMul.{u3, u1, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (instHSMul.{u3, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSMul.{u1, u3} α R _inst_1 _inst_2)) c (iSup.{u1, u2} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSupSet.{u1} α) ι (fun (i : ι) => f i))) (iSup.{u1, u2} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSupSet.{u1} α) ι (fun (i : ι) => HSMul.hSMul.{u3, u1, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (instHSMul.{u3, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSMul.{u1, u3} α R _inst_1 _inst_2)) c (f i)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.smul_supr MeasureTheory.OuterMeasure.smul_iSupₓ'. -/
theorem smul_iSup [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] {ι} (f : ι → OuterMeasure α) (c : R) :
    (c • ⨆ i, f i) = ⨆ i, c • f i :=
  ext fun s => by simp only [smul_apply, iSup_apply, ENNReal.smul_iSup]
#align measure_theory.outer_measure.smul_supr MeasureTheory.OuterMeasure.smul_iSup

end Supremum

/- warning: measure_theory.outer_measure.mono'' -> MeasureTheory.OuterMeasure.mono'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m₁ : MeasureTheory.OuterMeasure.{u1} α} {m₂ : MeasureTheory.OuterMeasure.{u1} α} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toHasLe.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) m₁ m₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m₁ s₁) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m₂ s₂))
but is expected to have type
  forall {α : Type.{u1}} {m₁ : MeasureTheory.OuterMeasure.{u1} α} {m₂ : MeasureTheory.OuterMeasure.{u1} α} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toLE.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) m₁ m₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m₁ s₁) (MeasureTheory.OuterMeasure.measureOf.{u1} α m₂ s₂))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.mono'' MeasureTheory.OuterMeasure.mono''ₓ'. -/
@[mono]
theorem mono'' {m₁ m₂ : OuterMeasure α} {s₁ s₂ : Set α} (hm : m₁ ≤ m₂) (hs : s₁ ⊆ s₂) :
    m₁ s₁ ≤ m₂ s₂ :=
  (hm s₁).trans (m₂.mono hs)
#align measure_theory.outer_measure.mono'' MeasureTheory.OuterMeasure.mono''

/- warning: measure_theory.outer_measure.map -> MeasureTheory.OuterMeasure.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (LinearMap.{0, 0, u1, u2} ENNReal ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (RingHom.id.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u2} β) (MeasureTheory.OuterMeasure.addCommMonoid.{u1} α) (MeasureTheory.OuterMeasure.addCommMonoid.{u2} β) (MeasureTheory.OuterMeasure.instModule.{u1, 0} α ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Semiring.toModule.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) MeasureTheory.OuterMeasure.map._proof_1) (MeasureTheory.OuterMeasure.instModule.{u2, 0} β ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Semiring.toModule.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) MeasureTheory.OuterMeasure.map._proof_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (LinearMap.{0, 0, u1, u2} ENNReal ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (RingHom.id.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u2} β) (MeasureTheory.OuterMeasure.addCommMonoid.{u1} α) (MeasureTheory.OuterMeasure.addCommMonoid.{u2} β) (MeasureTheory.OuterMeasure.instModule.{u1, 0} α ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Semiring.toModule.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (MeasureTheory.OuterMeasure.instModule.{u2, 0} β ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Semiring.toModule.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map MeasureTheory.OuterMeasure.mapₓ'. -/
/-- The pushforward of `m` along `f`. The outer measure on `s` is defined to be `m (f ⁻¹' s)`. -/
def map {β} (f : α → β) : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β
    where
  toFun m :=
    { measureOf := fun s => m (f ⁻¹' s)
      Empty := m.Empty
      mono := fun s t h => m.mono (preimage_mono h)
      iUnion_nat := fun s => by rw [preimage_Union] <;> exact m.Union_nat fun i => f ⁻¹' s i }
  map_add' m₁ m₂ := coe_fn_injective rfl
  map_smul' c m := coe_fn_injective rfl
#align measure_theory.outer_measure.map MeasureTheory.OuterMeasure.map

/- warning: measure_theory.outer_measure.map_apply -> MeasureTheory.OuterMeasure.map_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_apply MeasureTheory.OuterMeasure.map_applyₓ'. -/
@[simp]
theorem map_apply {β} (f : α → β) (m : OuterMeasure α) (s : Set β) : map f m s = m (f ⁻¹' s) :=
  rfl
#align measure_theory.outer_measure.map_apply MeasureTheory.OuterMeasure.map_apply

/- warning: measure_theory.outer_measure.map_id -> MeasureTheory.OuterMeasure.map_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_id MeasureTheory.OuterMeasure.map_idₓ'. -/
@[simp]
theorem map_id (m : OuterMeasure α) : map id m = m :=
  ext fun s => rfl
#align measure_theory.outer_measure.map_id MeasureTheory.OuterMeasure.map_id

/- warning: measure_theory.outer_measure.map_map -> MeasureTheory.OuterMeasure.map_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_map MeasureTheory.OuterMeasure.map_mapₓ'. -/
@[simp]
theorem map_map {β γ} (f : α → β) (g : β → γ) (m : OuterMeasure α) :
    map g (map f m) = map (g ∘ f) m :=
  ext fun s => rfl
#align measure_theory.outer_measure.map_map MeasureTheory.OuterMeasure.map_map

/- warning: measure_theory.outer_measure.map_mono -> MeasureTheory.OuterMeasure.map_mono is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_mono MeasureTheory.OuterMeasure.map_monoₓ'. -/
@[mono]
theorem map_mono {β} (f : α → β) : Monotone (map f) := fun m m' h s => h _
#align measure_theory.outer_measure.map_mono MeasureTheory.OuterMeasure.map_mono

/- warning: measure_theory.outer_measure.map_sup -> MeasureTheory.OuterMeasure.map_sup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_sup MeasureTheory.OuterMeasure.map_supₓ'. -/
@[simp]
theorem map_sup {β} (f : α → β) (m m' : OuterMeasure α) : map f (m ⊔ m') = map f m ⊔ map f m' :=
  ext fun s => by simp only [map_apply, sup_apply]
#align measure_theory.outer_measure.map_sup MeasureTheory.OuterMeasure.map_sup

/- warning: measure_theory.outer_measure.map_supr -> MeasureTheory.OuterMeasure.map_iSup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_supr MeasureTheory.OuterMeasure.map_iSupₓ'. -/
@[simp]
theorem map_iSup {β ι} (f : α → β) (m : ι → OuterMeasure α) : map f (⨆ i, m i) = ⨆ i, map f (m i) :=
  ext fun s => by simp only [map_apply, iSup_apply]
#align measure_theory.outer_measure.map_supr MeasureTheory.OuterMeasure.map_iSup

instance : Functor OuterMeasure where map α β f := map f

instance : LawfulFunctor OuterMeasure
    where
  id_map α := map_id
  comp_map α β γ f g m := (map_map f g m).symm

#print MeasureTheory.OuterMeasure.dirac /-
/-- The dirac outer measure. -/
def dirac (a : α) : OuterMeasure α
    where
  measureOf s := indicator s (fun _ => 1) a
  Empty := by simp
  mono s t h := indicator_le_indicator_of_subset h (fun _ => zero_le _) a
  iUnion_nat s :=
    if hs : a ∈ ⋃ n, s n then
      let ⟨i, hi⟩ := mem_iUnion.1 hs
      calc
        indicator (⋃ n, s n) (fun _ => (1 : ℝ≥0∞)) a = 1 := indicator_of_mem hs _
        _ = indicator (s i) (fun _ => 1) a := (indicator_of_mem hi _).symm
        _ ≤ ∑' n, indicator (s n) (fun _ => 1) a := ENNReal.le_tsum _
        
    else by simp only [indicator_of_not_mem hs, zero_le]
#align measure_theory.outer_measure.dirac MeasureTheory.OuterMeasure.dirac
-/

/- warning: measure_theory.outer_measure.dirac_apply -> MeasureTheory.OuterMeasure.dirac_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.dirac.{u1} α a) s) (Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s (fun (_x : α) => OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) a)
but is expected to have type
  forall {α : Type.{u1}} (a : α) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.dirac.{u1} α a) s) (Set.indicator.{u1, 0} α ENNReal instENNRealZero s (fun (_x : α) => OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) a)
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.dirac_apply MeasureTheory.OuterMeasure.dirac_applyₓ'. -/
@[simp]
theorem dirac_apply (a : α) (s : Set α) : dirac a s = indicator s (fun _ => 1) a :=
  rfl
#align measure_theory.outer_measure.dirac_apply MeasureTheory.OuterMeasure.dirac_apply

#print MeasureTheory.OuterMeasure.sum /-
/-- The sum of an (arbitrary) collection of outer measures. -/
def sum {ι} (f : ι → OuterMeasure α) : OuterMeasure α
    where
  measureOf s := ∑' i, f i s
  Empty := by simp
  mono s t h := ENNReal.tsum_le_tsum fun i => (f i).mono' h
  iUnion_nat s := by
    rw [ENNReal.tsum_comm] <;> exact ENNReal.tsum_le_tsum fun i => (f i).iUnion_nat _
#align measure_theory.outer_measure.sum MeasureTheory.OuterMeasure.sum
-/

/- warning: measure_theory.outer_measure.sum_apply -> MeasureTheory.OuterMeasure.sum_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (f : ι -> (MeasureTheory.OuterMeasure.{u1} α)) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.sum.{u1, u2} α ι f) s) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace ι (fun (i : ι) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (f i) s))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} (f : ι -> (MeasureTheory.OuterMeasure.{u1} α)) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.sum.{u1, u2} α ι f) s) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal ι (fun (i : ι) => MeasureTheory.OuterMeasure.measureOf.{u1} α (f i) s))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.sum_apply MeasureTheory.OuterMeasure.sum_applyₓ'. -/
@[simp]
theorem sum_apply {ι} (f : ι → OuterMeasure α) (s : Set α) : sum f s = ∑' i, f i s :=
  rfl
#align measure_theory.outer_measure.sum_apply MeasureTheory.OuterMeasure.sum_apply

/- warning: measure_theory.outer_measure.smul_dirac_apply -> MeasureTheory.OuterMeasure.smul_dirac_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : ENNReal) (b : α) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (SMul.smul.{0, u1} ENNReal (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.hasSmul.{u1, 0} α ENNReal (SMulZeroClass.toHasSmul.{0, 0} ENNReal ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (SMulWithZero.toSmulZeroClass.{0, 0} ENNReal ENNReal (MulZeroClass.toHasZero.{0} ENNReal (MulZeroOneClass.toMulZeroClass.{0} ENNReal (MonoidWithZero.toMulZeroOneClass.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (MulActionWithZero.toSMulWithZero.{0, 0} ENNReal ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (Module.toMulActionWithZero.{0, 0} ENNReal ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Algebra.toModule.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) a (MeasureTheory.OuterMeasure.dirac.{u1} α b)) s) (Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s (fun (_x : α) => a) b)
but is expected to have type
  forall {α : Type.{u1}} (a : ENNReal) (b : α) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (HSMul.hSMul.{0, u1, u1} ENNReal (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (instHSMul.{0, u1} ENNReal (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSMul.{u1, 0} α ENNReal (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) a (MeasureTheory.OuterMeasure.dirac.{u1} α b)) s) (Set.indicator.{u1, 0} α ENNReal instENNRealZero s (fun (_x : α) => a) b)
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.smul_dirac_apply MeasureTheory.OuterMeasure.smul_dirac_applyₓ'. -/
theorem smul_dirac_apply (a : ℝ≥0∞) (b : α) (s : Set α) :
    (a • dirac b) s = indicator s (fun _ => a) b := by
  simp only [smul_apply, smul_eq_mul, dirac_apply, ← indicator_mul_right _ fun _ => a, mul_one]
#align measure_theory.outer_measure.smul_dirac_apply MeasureTheory.OuterMeasure.smul_dirac_apply

/- warning: measure_theory.outer_measure.comap -> MeasureTheory.OuterMeasure.comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (LinearMap.{0, 0, u2, u1} ENNReal ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (RingHom.id.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))) (MeasureTheory.OuterMeasure.{u2} β) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.addCommMonoid.{u2} β) (MeasureTheory.OuterMeasure.addCommMonoid.{u1} α) (MeasureTheory.OuterMeasure.instModule.{u2, 0} β ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Semiring.toModule.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) MeasureTheory.OuterMeasure.comap._proof_1) (MeasureTheory.OuterMeasure.instModule.{u1, 0} α ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Semiring.toModule.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) MeasureTheory.OuterMeasure.comap._proof_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (LinearMap.{0, 0, u2, u1} ENNReal ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (RingHom.id.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) (MeasureTheory.OuterMeasure.{u2} β) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.addCommMonoid.{u2} β) (MeasureTheory.OuterMeasure.addCommMonoid.{u1} α) (MeasureTheory.OuterMeasure.instModule.{u2, 0} β ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Semiring.toModule.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (MeasureTheory.OuterMeasure.instModule.{u1, 0} α ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Semiring.toModule.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.comap MeasureTheory.OuterMeasure.comapₓ'. -/
/-- Pullback of an `outer_measure`: `comap f μ s = μ (f '' s)`. -/
def comap {β} (f : α → β) : OuterMeasure β →ₗ[ℝ≥0∞] OuterMeasure α
    where
  toFun m :=
    { measureOf := fun s => m (f '' s)
      Empty := by simp
      mono := fun s t h => m.mono <| image_subset f h
      iUnion_nat := fun s => by rw [image_Union]; apply m.Union_nat }
  map_add' m₁ m₂ := rfl
  map_smul' c m := rfl
#align measure_theory.outer_measure.comap MeasureTheory.OuterMeasure.comap

/- warning: measure_theory.outer_measure.comap_apply -> MeasureTheory.OuterMeasure.comap_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.comap_apply MeasureTheory.OuterMeasure.comap_applyₓ'. -/
@[simp]
theorem comap_apply {β} (f : α → β) (m : OuterMeasure β) (s : Set α) : comap f m s = m (f '' s) :=
  rfl
#align measure_theory.outer_measure.comap_apply MeasureTheory.OuterMeasure.comap_apply

/- warning: measure_theory.outer_measure.comap_mono -> MeasureTheory.OuterMeasure.comap_mono is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.comap_mono MeasureTheory.OuterMeasure.comap_monoₓ'. -/
@[mono]
theorem comap_mono {β} (f : α → β) : Monotone (comap f) := fun m m' h s => h _
#align measure_theory.outer_measure.comap_mono MeasureTheory.OuterMeasure.comap_mono

/- warning: measure_theory.outer_measure.comap_supr -> MeasureTheory.OuterMeasure.comap_iSup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.comap_supr MeasureTheory.OuterMeasure.comap_iSupₓ'. -/
@[simp]
theorem comap_iSup {β ι} (f : α → β) (m : ι → OuterMeasure β) :
    comap f (⨆ i, m i) = ⨆ i, comap f (m i) :=
  ext fun s => by simp only [comap_apply, iSup_apply]
#align measure_theory.outer_measure.comap_supr MeasureTheory.OuterMeasure.comap_iSup

/- warning: measure_theory.outer_measure.restrict -> MeasureTheory.OuterMeasure.restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, (Set.{u1} α) -> (LinearMap.{0, 0, u1, u1} ENNReal ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (RingHom.id.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.addCommMonoid.{u1} α) (MeasureTheory.OuterMeasure.addCommMonoid.{u1} α) (MeasureTheory.OuterMeasure.instModule.{u1, 0} α ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Semiring.toModule.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) MeasureTheory.OuterMeasure.restrict._proof_1) (MeasureTheory.OuterMeasure.instModule.{u1, 0} α ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Semiring.toModule.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) MeasureTheory.OuterMeasure.restrict._proof_1))
but is expected to have type
  forall {α : Type.{u1}}, (Set.{u1} α) -> (LinearMap.{0, 0, u1, u1} ENNReal ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (RingHom.id.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.addCommMonoid.{u1} α) (MeasureTheory.OuterMeasure.addCommMonoid.{u1} α) (MeasureTheory.OuterMeasure.instModule.{u1, 0} α ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Semiring.toModule.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (MeasureTheory.OuterMeasure.instModule.{u1, 0} α ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Semiring.toModule.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.restrict MeasureTheory.OuterMeasure.restrictₓ'. -/
/-- Restrict an `outer_measure` to a set. -/
def restrict (s : Set α) : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure α :=
  (map coe).comp (comap (coe : s → α))
#align measure_theory.outer_measure.restrict MeasureTheory.OuterMeasure.restrict

/- warning: measure_theory.outer_measure.restrict_apply -> MeasureTheory.OuterMeasure.restrict_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.restrict_apply MeasureTheory.OuterMeasure.restrict_applyₓ'. -/
@[simp]
theorem restrict_apply (s t : Set α) (m : OuterMeasure α) : restrict s m t = m (t ∩ s) := by
  simp [restrict]
#align measure_theory.outer_measure.restrict_apply MeasureTheory.OuterMeasure.restrict_apply

/- warning: measure_theory.outer_measure.restrict_mono -> MeasureTheory.OuterMeasure.restrict_mono is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.restrict_mono MeasureTheory.OuterMeasure.restrict_monoₓ'. -/
@[mono]
theorem restrict_mono {s t : Set α} (h : s ⊆ t) {m m' : OuterMeasure α} (hm : m ≤ m') :
    restrict s m ≤ restrict t m' := fun u => by simp only [restrict_apply];
  exact (hm _).trans (m'.mono <| inter_subset_inter_right _ h)
#align measure_theory.outer_measure.restrict_mono MeasureTheory.OuterMeasure.restrict_mono

/- warning: measure_theory.outer_measure.restrict_univ -> MeasureTheory.OuterMeasure.restrict_univ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.restrict_univ MeasureTheory.OuterMeasure.restrict_univₓ'. -/
@[simp]
theorem restrict_univ (m : OuterMeasure α) : restrict univ m = m :=
  ext fun s => by simp
#align measure_theory.outer_measure.restrict_univ MeasureTheory.OuterMeasure.restrict_univ

/- warning: measure_theory.outer_measure.restrict_empty -> MeasureTheory.OuterMeasure.restrict_empty is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.restrict_empty MeasureTheory.OuterMeasure.restrict_emptyₓ'. -/
@[simp]
theorem restrict_empty (m : OuterMeasure α) : restrict ∅ m = 0 :=
  ext fun s => by simp
#align measure_theory.outer_measure.restrict_empty MeasureTheory.OuterMeasure.restrict_empty

/- warning: measure_theory.outer_measure.restrict_supr -> MeasureTheory.OuterMeasure.restrict_iSup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.restrict_supr MeasureTheory.OuterMeasure.restrict_iSupₓ'. -/
@[simp]
theorem restrict_iSup {ι} (s : Set α) (m : ι → OuterMeasure α) :
    restrict s (⨆ i, m i) = ⨆ i, restrict s (m i) := by simp [restrict]
#align measure_theory.outer_measure.restrict_supr MeasureTheory.OuterMeasure.restrict_iSup

/- warning: measure_theory.outer_measure.map_comap -> MeasureTheory.OuterMeasure.map_comap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_comap MeasureTheory.OuterMeasure.map_comapₓ'. -/
theorem map_comap {β} (f : α → β) (m : OuterMeasure β) : map f (comap f m) = restrict (range f) m :=
  ext fun s => congr_arg m <| by simp only [image_preimage_eq_inter_range, Subtype.range_coe]
#align measure_theory.outer_measure.map_comap MeasureTheory.OuterMeasure.map_comap

/- warning: measure_theory.outer_measure.map_comap_le -> MeasureTheory.OuterMeasure.map_comap_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_comap_le MeasureTheory.OuterMeasure.map_comap_leₓ'. -/
theorem map_comap_le {β} (f : α → β) (m : OuterMeasure β) : map f (comap f m) ≤ m := fun s =>
  m.mono <| image_preimage_subset _ _
#align measure_theory.outer_measure.map_comap_le MeasureTheory.OuterMeasure.map_comap_le

/- warning: measure_theory.outer_measure.restrict_le_self -> MeasureTheory.OuterMeasure.restrict_le_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.restrict_le_self MeasureTheory.OuterMeasure.restrict_le_selfₓ'. -/
theorem restrict_le_self (m : OuterMeasure α) (s : Set α) : restrict s m ≤ m :=
  map_comap_le _ _
#align measure_theory.outer_measure.restrict_le_self MeasureTheory.OuterMeasure.restrict_le_self

/- warning: measure_theory.outer_measure.map_le_restrict_range -> MeasureTheory.OuterMeasure.map_le_restrict_range is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_le_restrict_range MeasureTheory.OuterMeasure.map_le_restrict_rangeₓ'. -/
@[simp]
theorem map_le_restrict_range {β} {ma : OuterMeasure α} {mb : OuterMeasure β} {f : α → β} :
    map f ma ≤ restrict (range f) mb ↔ map f ma ≤ mb :=
  ⟨fun h => h.trans (restrict_le_self _ _), fun h s => by simpa using h (s ∩ range f)⟩
#align measure_theory.outer_measure.map_le_restrict_range MeasureTheory.OuterMeasure.map_le_restrict_range

/- warning: measure_theory.outer_measure.map_comap_of_surjective -> MeasureTheory.OuterMeasure.map_comap_of_surjective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_comap_of_surjective MeasureTheory.OuterMeasure.map_comap_of_surjectiveₓ'. -/
theorem map_comap_of_surjective {β} {f : α → β} (hf : Surjective f) (m : OuterMeasure β) :
    map f (comap f m) = m :=
  ext fun s => by rw [map_apply, comap_apply, hf.image_preimage]
#align measure_theory.outer_measure.map_comap_of_surjective MeasureTheory.OuterMeasure.map_comap_of_surjective

/- warning: measure_theory.outer_measure.le_comap_map -> MeasureTheory.OuterMeasure.le_comap_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.le_comap_map MeasureTheory.OuterMeasure.le_comap_mapₓ'. -/
theorem le_comap_map {β} (f : α → β) (m : OuterMeasure α) : m ≤ comap f (map f m) := fun s =>
  m.mono <| subset_preimage_image _ _
#align measure_theory.outer_measure.le_comap_map MeasureTheory.OuterMeasure.le_comap_map

/- warning: measure_theory.outer_measure.comap_map -> MeasureTheory.OuterMeasure.comap_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.comap_map MeasureTheory.OuterMeasure.comap_mapₓ'. -/
theorem comap_map {β} {f : α → β} (hf : Injective f) (m : OuterMeasure α) : comap f (map f m) = m :=
  ext fun s => by rw [comap_apply, map_apply, hf.preimage_image]
#align measure_theory.outer_measure.comap_map MeasureTheory.OuterMeasure.comap_map

/- warning: measure_theory.outer_measure.top_apply -> MeasureTheory.OuterMeasure.top_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Top.top.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toHasTop.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (Top.top.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toTop.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.top_apply MeasureTheory.OuterMeasure.top_applyₓ'. -/
@[simp]
theorem top_apply {s : Set α} (h : s.Nonempty) : (⊤ : OuterMeasure α) s = ∞ :=
  let ⟨a, as⟩ := h
  top_unique <| le_trans (by simp [smul_dirac_apply, as]) (le_iSup₂ (∞ • dirac a) trivial)
#align measure_theory.outer_measure.top_apply MeasureTheory.OuterMeasure.top_apply

/- warning: measure_theory.outer_measure.top_apply' -> MeasureTheory.OuterMeasure.top_apply' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Top.top.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toHasTop.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) s) (iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (fun (h : Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) => OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (Top.top.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toTop.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) s) (iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (fun (h : Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) => OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.top_apply' MeasureTheory.OuterMeasure.top_apply'ₓ'. -/
theorem top_apply' (s : Set α) : (⊤ : OuterMeasure α) s = ⨅ h : s = ∅, 0 :=
  s.eq_empty_or_nonempty.elim (fun h => by simp [h]) fun h => by simp [h, h.ne_empty]
#align measure_theory.outer_measure.top_apply' MeasureTheory.OuterMeasure.top_apply'

/- warning: measure_theory.outer_measure.comap_top -> MeasureTheory.OuterMeasure.comap_top is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.comap_top MeasureTheory.OuterMeasure.comap_topₓ'. -/
@[simp]
theorem comap_top (f : α → β) : comap f ⊤ = ⊤ :=
  ext_nonempty fun s hs => by rw [comap_apply, top_apply hs, top_apply (hs.image _)]
#align measure_theory.outer_measure.comap_top MeasureTheory.OuterMeasure.comap_top

/- warning: measure_theory.outer_measure.map_top -> MeasureTheory.OuterMeasure.map_top is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_top MeasureTheory.OuterMeasure.map_topₓ'. -/
theorem map_top (f : α → β) : map f ⊤ = restrict (range f) ⊤ :=
  ext fun s => by
    rw [map_apply, restrict_apply, ← image_preimage_eq_inter_range, top_apply', top_apply',
      Set.image_eq_empty]
#align measure_theory.outer_measure.map_top MeasureTheory.OuterMeasure.map_top

/- warning: measure_theory.outer_measure.map_top_of_surjective -> MeasureTheory.OuterMeasure.map_top_of_surjective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_top_of_surjective MeasureTheory.OuterMeasure.map_top_of_surjectiveₓ'. -/
theorem map_top_of_surjective (f : α → β) (hf : Surjective f) : map f ⊤ = ⊤ := by
  rw [map_top, hf.range_eq, restrict_univ]
#align measure_theory.outer_measure.map_top_of_surjective MeasureTheory.OuterMeasure.map_top_of_surjective

end Basic

section OfFunction

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option eqn_compiler.zeta -/
set_option eqn_compiler.zeta true

variable {α : Type _} (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0)

include m_empty

/- warning: measure_theory.outer_measure.of_function -> MeasureTheory.OuterMeasure.ofFunction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : (Set.{u1} α) -> ENNReal), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (MeasureTheory.OuterMeasure.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (m : (Set.{u1} α) -> ENNReal), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (MeasureTheory.OuterMeasure.{u1} α)
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.of_function MeasureTheory.OuterMeasure.ofFunctionₓ'. -/
/-- Given any function `m` assigning measures to sets satisying `m ∅ = 0`, there is
  a unique maximal outer measure `μ` satisfying `μ s ≤ m s` for all `s : set α`. -/
protected def ofFunction : OuterMeasure α :=
  let μ s := ⨅ (f : ℕ → Set α) (h : s ⊆ ⋃ i, f i), ∑' i, m (f i)
  { measureOf := μ
    Empty :=
      le_antisymm
        ((iInf_le_of_le fun _ => ∅) <| iInf_le_of_le (empty_subset _) <| by simp [m_empty])
        (zero_le _)
    mono := fun s₁ s₂ hs => iInf_mono fun f => iInf_mono' fun hb => ⟨hs.trans hb, le_rfl⟩
    iUnion_nat := fun s =>
      ENNReal.le_of_forall_pos_le_add <|
        by
        intro ε hε(hb : (∑' i, μ (s i)) < ∞)
        rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 hε).ne' ℕ with ⟨ε', hε', hl⟩
        refine' le_trans _ (add_le_add_left (le_of_lt hl) _)
        rw [← ENNReal.tsum_add]
        choose f hf using
          show ∀ i, ∃ f : ℕ → Set α, (s i ⊆ ⋃ i, f i) ∧ (∑' i, m (f i)) < μ (s i) + ε' i
            by
            intro
            have : μ (s i) < μ (s i) + ε' i :=
              ENNReal.lt_add_right (ne_top_of_le_ne_top hb.ne <| ENNReal.le_tsum _)
                (by simpa using (hε' i).ne')
            simpa [μ, iInf_lt_iff]
        refine' le_trans _ (ENNReal.tsum_le_tsum fun i => le_of_lt (hf i).2)
        rw [← ENNReal.tsum_prod, ← nat.mkpair_equiv.symm.tsum_eq]
        swap; · infer_instance
        refine' iInf_le_of_le _ (iInf_le _ _)
        exact
          Union_subset fun i =>
            subset.trans (hf i).1 <|
              Union_subset fun j =>
                subset.trans (by simp) <| subset_Union _ <| Nat.pairEquiv (i, j) }
#align measure_theory.outer_measure.of_function MeasureTheory.OuterMeasure.ofFunction

/- warning: measure_theory.outer_measure.of_function_apply -> MeasureTheory.OuterMeasure.ofFunction_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : (Set.{u1} α) -> ENNReal) (m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (n : Nat) => m (t n)))))
but is expected to have type
  forall {α : Type.{u1}} (m : (Set.{u1} α) -> ENNReal) (m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (n : Nat) => m (t n)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.of_function_apply MeasureTheory.OuterMeasure.ofFunction_applyₓ'. -/
theorem ofFunction_apply (s : Set α) :
    OuterMeasure.ofFunction m m_empty s = ⨅ (t : ℕ → Set α) (h : s ⊆ iUnion t), ∑' n, m (t n) :=
  rfl
#align measure_theory.outer_measure.of_function_apply MeasureTheory.OuterMeasure.ofFunction_apply

variable {m m_empty}

/- warning: measure_theory.outer_measure.of_function_le -> MeasureTheory.OuterMeasure.ofFunction_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))} (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) s) (m s)
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))} (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) s) (m s)
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.of_function_le MeasureTheory.OuterMeasure.ofFunction_leₓ'. -/
theorem ofFunction_le (s : Set α) : OuterMeasure.ofFunction m m_empty s ≤ m s :=
  let f : ℕ → Set α := fun i => Nat.casesOn i s fun _ => ∅
  iInf_le_of_le f <|
    iInf_le_of_le (subset_iUnion f 0) <|
      le_of_eq <| tsum_eq_single 0 <| by rintro (_ | i) <;> simp [f, m_empty]
#align measure_theory.outer_measure.of_function_le MeasureTheory.OuterMeasure.ofFunction_le

/- warning: measure_theory.outer_measure.of_function_eq -> MeasureTheory.OuterMeasure.ofFunction_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))} (s : Set.{u1} α), (forall {{t : Set.{u1} α}}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m s) (m t))) -> (forall (s : Nat -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i))) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (s i)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) s) (m s))
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))} (s : Set.{u1} α), (forall {{t : Set.{u1} α}}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m s) (m t))) -> (forall (s : Nat -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i))) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (s i)))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) s) (m s))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.of_function_eq MeasureTheory.OuterMeasure.ofFunction_eqₓ'. -/
theorem ofFunction_eq (s : Set α) (m_mono : ∀ ⦃t : Set α⦄, s ⊆ t → m s ≤ m t)
    (m_subadd : ∀ s : ℕ → Set α, m (⋃ i, s i) ≤ ∑' i, m (s i)) :
    OuterMeasure.ofFunction m m_empty s = m s :=
  le_antisymm (ofFunction_le s) <|
    le_iInf fun f => le_iInf fun hf => le_trans (m_mono hf) (m_subadd f)
#align measure_theory.outer_measure.of_function_eq MeasureTheory.OuterMeasure.ofFunction_eq

/- warning: measure_theory.outer_measure.le_of_function -> MeasureTheory.OuterMeasure.le_ofFunction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))} {μ : MeasureTheory.OuterMeasure.{u1} α}, Iff (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toHasLe.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) μ (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty)) (forall (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) μ s) (m s))
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))} {μ : MeasureTheory.OuterMeasure.{u1} α}, Iff (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toLE.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) μ (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty)) (forall (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α μ s) (m s))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.le_of_function MeasureTheory.OuterMeasure.le_ofFunctionₓ'. -/
theorem le_ofFunction {μ : OuterMeasure α} :
    μ ≤ OuterMeasure.ofFunction m m_empty ↔ ∀ s, μ s ≤ m s :=
  ⟨fun H s => le_trans (H s) (ofFunction_le s), fun H s =>
    le_iInf fun f =>
      le_iInf fun hs =>
        le_trans (μ.mono hs) <| le_trans (μ.iUnion f) <| ENNReal.tsum_le_tsum fun i => H _⟩
#align measure_theory.outer_measure.le_of_function MeasureTheory.OuterMeasure.le_ofFunction

/- warning: measure_theory.outer_measure.is_greatest_of_function -> MeasureTheory.OuterMeasure.isGreatest_ofFunction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))}, IsGreatest.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α)) (setOf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (μ : MeasureTheory.OuterMeasure.{u1} α) => forall (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) μ s) (m s))) (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty)
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))}, IsGreatest.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α)) (setOf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (μ : MeasureTheory.OuterMeasure.{u1} α) => forall (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α μ s) (m s))) (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty)
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.is_greatest_of_function MeasureTheory.OuterMeasure.isGreatest_ofFunctionₓ'. -/
theorem isGreatest_ofFunction :
    IsGreatest { μ : OuterMeasure α | ∀ s, μ s ≤ m s } (OuterMeasure.ofFunction m m_empty) :=
  ⟨fun s => ofFunction_le _, fun μ => le_ofFunction.2⟩
#align measure_theory.outer_measure.is_greatest_of_function MeasureTheory.OuterMeasure.isGreatest_ofFunction

/- warning: measure_theory.outer_measure.of_function_eq_Sup -> MeasureTheory.OuterMeasure.ofFunction_eq_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))}, Eq.{succ u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) (SupSet.sSup.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSupSet.{u1} α) (setOf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (μ : MeasureTheory.OuterMeasure.{u1} α) => forall (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) μ s) (m s))))
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))}, Eq.{succ u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) (SupSet.sSup.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSupSet.{u1} α) (setOf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (μ : MeasureTheory.OuterMeasure.{u1} α) => forall (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α μ s) (m s))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.of_function_eq_Sup MeasureTheory.OuterMeasure.ofFunction_eq_sSupₓ'. -/
theorem ofFunction_eq_sSup : OuterMeasure.ofFunction m m_empty = sSup { μ | ∀ s, μ s ≤ m s } :=
  (@isGreatest_ofFunction α m m_empty).IsLUB.sSup_eq.symm
#align measure_theory.outer_measure.of_function_eq_Sup MeasureTheory.OuterMeasure.ofFunction_eq_sSup

/- warning: measure_theory.outer_measure.of_function_union_of_top_of_nonempty_inter -> MeasureTheory.OuterMeasure.ofFunction_union_of_top_of_nonempty_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))} {s : Set.{u1} α} {t : Set.{u1} α}, (forall (u : Set.{u1} α), (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u)) -> (Eq.{1} ENNReal (m u) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) s) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) t)))
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))} {s : Set.{u1} α} {t : Set.{u1} α}, (forall (u : Set.{u1} α), (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u)) -> (Eq.{1} ENNReal (m u) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) t)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.of_function_union_of_top_of_nonempty_inter MeasureTheory.OuterMeasure.ofFunction_union_of_top_of_nonempty_interₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (u «expr ⊆ » «expr ∪ »(s, t)) -/
/-- If `m u = ∞` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = measure_theory.outer_measure.of_function m m_empty`.

E.g., if `α` is an (e)metric space and `m u = ∞` on any set of diameter `≥ r`, then this lemma
implies that `μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s`
and `y ∈ t`.  -/
theorem ofFunction_union_of_top_of_nonempty_inter {s t : Set α}
    (h : ∀ u, (s ∩ u).Nonempty → (t ∩ u).Nonempty → m u = ∞) :
    OuterMeasure.ofFunction m m_empty (s ∪ t) =
      OuterMeasure.ofFunction m m_empty s + OuterMeasure.ofFunction m m_empty t :=
  by
  refine' le_antisymm (outer_measure.union _ _ _) (le_iInf fun f => le_iInf fun hf => _)
  set μ := outer_measure.of_function m m_empty
  rcases em (∃ i, (s ∩ f i).Nonempty ∧ (t ∩ f i).Nonempty) with (⟨i, hs, ht⟩ | he)
  ·
    calc
      μ s + μ t ≤ ∞ := le_top
      _ = m (f i) := (h (f i) hs ht).symm
      _ ≤ ∑' i, m (f i) := ENNReal.le_tsum i
      
  set I := fun s => { i : ℕ | (s ∩ f i).Nonempty }
  have hd : Disjoint (I s) (I t) := disjoint_iff_inf_le.mpr fun i hi => he ⟨i, hi⟩
  have hI : ∀ (u) (_ : u ⊆ s ∪ t), μ u ≤ ∑' i : I u, μ (f i) := fun u hu =>
    calc
      μ u ≤ μ (⋃ i : I u, f i) :=
        μ.mono fun x hx =>
          let ⟨i, hi⟩ := mem_Union.1 (hf (hu hx))
          mem_Union.2 ⟨⟨i, ⟨x, hx, hi⟩⟩, hi⟩
      _ ≤ ∑' i : I u, μ (f i) := μ.Union _
      
  calc
    μ s + μ t ≤ (∑' i : I s, μ (f i)) + ∑' i : I t, μ (f i) :=
      add_le_add (hI _ <| subset_union_left _ _) (hI _ <| subset_union_right _ _)
    _ = ∑' i : I s ∪ I t, μ (f i) :=
      (@tsum_union_disjoint _ _ _ _ _ (fun i => μ (f i)) _ _ _ hd ENNReal.summable
          ENNReal.summable).symm
    _ ≤ ∑' i, μ (f i) :=
      (tsum_le_tsum_of_inj coe Subtype.coe_injective (fun _ _ => zero_le _) (fun _ => le_rfl)
        ENNReal.summable ENNReal.summable)
    _ ≤ ∑' i, m (f i) := ENNReal.tsum_le_tsum fun i => of_function_le _
    
#align measure_theory.outer_measure.of_function_union_of_top_of_nonempty_inter MeasureTheory.OuterMeasure.ofFunction_union_of_top_of_nonempty_inter

/- warning: measure_theory.outer_measure.comap_of_function -> MeasureTheory.OuterMeasure.comap_ofFunction is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.comap_of_function MeasureTheory.OuterMeasure.comap_ofFunctionₓ'. -/
theorem comap_ofFunction {β} (f : β → α) (h : Monotone m ∨ Surjective f) :
    comap f (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun s => m (f '' s)) (by rwa [Set.image_empty]) :=
  by
  refine' le_antisymm (le_of_function.2 fun s => _) fun s => _
  · rw [comap_apply]; apply of_function_le
  · rw [comap_apply, of_function_apply, of_function_apply]
    refine' iInf_mono' fun t => ⟨fun k => f ⁻¹' t k, _⟩
    refine' iInf_mono' fun ht => _
    rw [Set.image_subset_iff, preimage_Union] at ht
    refine' ⟨ht, ENNReal.tsum_le_tsum fun n => _⟩
    cases h
    exacts[h (image_preimage_subset _ _), (congr_arg m (h.image_preimage (t n))).le]
#align measure_theory.outer_measure.comap_of_function MeasureTheory.OuterMeasure.comap_ofFunction

/- warning: measure_theory.outer_measure.map_of_function_le -> MeasureTheory.OuterMeasure.map_ofFunction_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_of_function_le MeasureTheory.OuterMeasure.map_ofFunction_leₓ'. -/
theorem map_ofFunction_le {β} (f : α → β) :
    map f (OuterMeasure.ofFunction m m_empty) ≤
      OuterMeasure.ofFunction (fun s => m (f ⁻¹' s)) m_empty :=
  le_ofFunction.2 fun s => by rw [map_apply]; apply of_function_le
#align measure_theory.outer_measure.map_of_function_le MeasureTheory.OuterMeasure.map_ofFunction_le

/- warning: measure_theory.outer_measure.map_of_function -> MeasureTheory.OuterMeasure.map_ofFunction is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_of_function MeasureTheory.OuterMeasure.map_ofFunctionₓ'. -/
theorem map_ofFunction {β} {f : α → β} (hf : Injective f) :
    map f (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun s => m (f ⁻¹' s)) m_empty :=
  by
  refine' (map_of_function_le _).antisymm fun s => _
  simp only [of_function_apply, map_apply, le_iInf_iff]
  intro t ht
  refine' iInf_le_of_le (fun n => range fᶜ ∪ f '' t n) (iInf_le_of_le _ _)
  · rw [← union_Union, ← inter_subset, ← image_preimage_eq_inter_range, ← image_Union]
    exact image_subset _ ht
  · refine' ENNReal.tsum_le_tsum fun n => le_of_eq _
    simp [hf.preimage_image]
#align measure_theory.outer_measure.map_of_function MeasureTheory.OuterMeasure.map_ofFunction

/- warning: measure_theory.outer_measure.restrict_of_function -> MeasureTheory.OuterMeasure.restrict_ofFunction is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.restrict_of_function MeasureTheory.OuterMeasure.restrict_ofFunctionₓ'. -/
theorem restrict_ofFunction (s : Set α) (hm : Monotone m) :
    restrict s (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun t => m (t ∩ s)) (by rwa [Set.empty_inter]) :=
  by
  simp only [restrict, LinearMap.comp_apply, comap_of_function _ (Or.inl hm),
    map_of_function Subtype.coe_injective, Subtype.image_preimage_coe]
#align measure_theory.outer_measure.restrict_of_function MeasureTheory.OuterMeasure.restrict_ofFunction

/- warning: measure_theory.outer_measure.smul_of_function -> MeasureTheory.OuterMeasure.smul_ofFunction is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.smul_of_function MeasureTheory.OuterMeasure.smul_ofFunctionₓ'. -/
theorem smul_ofFunction {c : ℝ≥0∞} (hc : c ≠ ∞) :
    c • OuterMeasure.ofFunction m m_empty = OuterMeasure.ofFunction (c • m) (by simp [m_empty]) :=
  by
  ext1 s
  haveI : Nonempty { t : ℕ → Set α // s ⊆ ⋃ i, t i } := ⟨⟨fun _ => s, subset_Union (fun _ => s) 0⟩⟩
  simp only [smul_apply, of_function_apply, ENNReal.tsum_mul_left, Pi.smul_apply, smul_eq_mul,
    iInf_subtype', ENNReal.iInf_mul_left fun h => (hc h).elim]
#align measure_theory.outer_measure.smul_of_function MeasureTheory.OuterMeasure.smul_ofFunction

end OfFunction

section BoundedBy

variable {α : Type _} (m : Set α → ℝ≥0∞)

#print MeasureTheory.OuterMeasure.boundedBy /-
/-- Given any function `m` assigning measures to sets, there is a unique maximal outer measure `μ`
  satisfying `μ s ≤ m s` for all `s : set α`. This is the same as `outer_measure.of_function`,
  except that it doesn't require `m ∅ = 0`. -/
def boundedBy : OuterMeasure α :=
  OuterMeasure.ofFunction (fun s => ⨆ h : s.Nonempty, m s) (by simp [not_nonempty_empty])
#align measure_theory.outer_measure.bounded_by MeasureTheory.OuterMeasure.boundedBy
-/

variable {m}

/- warning: measure_theory.outer_measure.bounded_by_le -> MeasureTheory.OuterMeasure.boundedBy_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) s) (m s)
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) s) (m s)
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.bounded_by_le MeasureTheory.OuterMeasure.boundedBy_leₓ'. -/
theorem boundedBy_le (s : Set α) : boundedBy m s ≤ m s :=
  (ofFunction_le _).trans iSup_const_le
#align measure_theory.outer_measure.bounded_by_le MeasureTheory.OuterMeasure.boundedBy_le

/- warning: measure_theory.outer_measure.bounded_by_eq_of_function -> MeasureTheory.OuterMeasure.boundedBy_eq_ofFunction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} (m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) s) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) s)
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} (m_empty : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.ofFunction.{u1} α m m_empty) s)
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.bounded_by_eq_of_function MeasureTheory.OuterMeasure.boundedBy_eq_ofFunctionₓ'. -/
theorem boundedBy_eq_ofFunction (m_empty : m ∅ = 0) (s : Set α) :
    boundedBy m s = OuterMeasure.ofFunction m m_empty s :=
  by
  have : (fun s : Set α => ⨆ h : s.Nonempty, m s) = m := by ext1 t;
    cases' t.eq_empty_or_nonempty with h h <;> simp [h, not_nonempty_empty, m_empty]
  simp [bounded_by, this]
#align measure_theory.outer_measure.bounded_by_eq_of_function MeasureTheory.OuterMeasure.boundedBy_eq_ofFunction

/- warning: measure_theory.outer_measure.bounded_by_apply -> MeasureTheory.OuterMeasure.boundedBy_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (n : Nat) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Set.Nonempty.{u1} α (t n)) (fun (h : Set.Nonempty.{u1} α (t n)) => m (t n))))))
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (n : Nat) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.Nonempty.{u1} α (t n)) (fun (h : Set.Nonempty.{u1} α (t n)) => m (t n))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.bounded_by_apply MeasureTheory.OuterMeasure.boundedBy_applyₓ'. -/
theorem boundedBy_apply (s : Set α) :
    boundedBy m s = ⨅ (t : ℕ → Set α) (h : s ⊆ iUnion t), ∑' n, ⨆ h : (t n).Nonempty, m (t n) := by
  simp [bounded_by, of_function_apply]
#align measure_theory.outer_measure.bounded_by_apply MeasureTheory.OuterMeasure.boundedBy_apply

/- warning: measure_theory.outer_measure.bounded_by_eq -> MeasureTheory.OuterMeasure.boundedBy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} (s : Set.{u1} α), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (forall {{t : Set.{u1} α}}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m s) (m t))) -> (forall (s : Nat -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i))) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (s i)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) s) (m s))
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} (s : Set.{u1} α), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (forall {{t : Set.{u1} α}}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m s) (m t))) -> (forall (s : Nat -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i))) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (s i)))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) s) (m s))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.bounded_by_eq MeasureTheory.OuterMeasure.boundedBy_eqₓ'. -/
theorem boundedBy_eq (s : Set α) (m_empty : m ∅ = 0) (m_mono : ∀ ⦃t : Set α⦄, s ⊆ t → m s ≤ m t)
    (m_subadd : ∀ s : ℕ → Set α, m (⋃ i, s i) ≤ ∑' i, m (s i)) : boundedBy m s = m s := by
  rw [bounded_by_eq_of_function m_empty, of_function_eq s m_mono m_subadd]
#align measure_theory.outer_measure.bounded_by_eq MeasureTheory.OuterMeasure.boundedBy_eq

#print MeasureTheory.OuterMeasure.boundedBy_eq_self /-
@[simp]
theorem boundedBy_eq_self (m : OuterMeasure α) : boundedBy m = m :=
  ext fun s => boundedBy_eq _ m.empty' (fun t ht => m.mono' ht) m.iUnion
#align measure_theory.outer_measure.bounded_by_eq_self MeasureTheory.OuterMeasure.boundedBy_eq_self
-/

/- warning: measure_theory.outer_measure.le_bounded_by -> MeasureTheory.OuterMeasure.le_boundedBy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {μ : MeasureTheory.OuterMeasure.{u1} α}, Iff (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toHasLe.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) μ (MeasureTheory.OuterMeasure.boundedBy.{u1} α m)) (forall (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) μ s) (m s))
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {μ : MeasureTheory.OuterMeasure.{u1} α}, Iff (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toLE.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) μ (MeasureTheory.OuterMeasure.boundedBy.{u1} α m)) (forall (s : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α μ s) (m s))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.le_bounded_by MeasureTheory.OuterMeasure.le_boundedByₓ'. -/
theorem le_boundedBy {μ : OuterMeasure α} : μ ≤ boundedBy m ↔ ∀ s, μ s ≤ m s :=
  by
  rw [bounded_by, le_of_function, forall_congr']; intro s
  cases' s.eq_empty_or_nonempty with h h <;> simp [h, not_nonempty_empty]
#align measure_theory.outer_measure.le_bounded_by MeasureTheory.OuterMeasure.le_boundedBy

/- warning: measure_theory.outer_measure.le_bounded_by' -> MeasureTheory.OuterMeasure.le_boundedBy' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {μ : MeasureTheory.OuterMeasure.{u1} α}, Iff (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toHasLe.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) μ (MeasureTheory.OuterMeasure.boundedBy.{u1} α m)) (forall (s : Set.{u1} α), (Set.Nonempty.{u1} α s) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) μ s) (m s)))
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {μ : MeasureTheory.OuterMeasure.{u1} α}, Iff (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toLE.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) μ (MeasureTheory.OuterMeasure.boundedBy.{u1} α m)) (forall (s : Set.{u1} α), (Set.Nonempty.{u1} α s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α μ s) (m s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.le_bounded_by' MeasureTheory.OuterMeasure.le_boundedBy'ₓ'. -/
theorem le_boundedBy' {μ : OuterMeasure α} :
    μ ≤ boundedBy m ↔ ∀ s : Set α, s.Nonempty → μ s ≤ m s := by rw [le_bounded_by, forall_congr'];
  intro s; cases' s.eq_empty_or_nonempty with h h <;> simp [h]
#align measure_theory.outer_measure.le_bounded_by' MeasureTheory.OuterMeasure.le_boundedBy'

#print MeasureTheory.OuterMeasure.boundedBy_top /-
@[simp]
theorem boundedBy_top : boundedBy (⊤ : Set α → ℝ≥0∞) = ⊤ :=
  by
  rw [eq_top_iff, le_bounded_by']
  intro s hs
  rw [top_apply hs]
  exact le_rfl
#align measure_theory.outer_measure.bounded_by_top MeasureTheory.OuterMeasure.boundedBy_top
-/

#print MeasureTheory.OuterMeasure.boundedBy_zero /-
@[simp]
theorem boundedBy_zero : boundedBy (0 : Set α → ℝ≥0∞) = 0 :=
  by
  rw [← coe_bot, eq_bot_iff]
  apply bounded_by_le
#align measure_theory.outer_measure.bounded_by_zero MeasureTheory.OuterMeasure.boundedBy_zero
-/

/- warning: measure_theory.outer_measure.smul_bounded_by -> MeasureTheory.OuterMeasure.smul_boundedBy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {c : ENNReal}, (Ne.{1} ENNReal c (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{succ u1} (MeasureTheory.OuterMeasure.{u1} α) (SMul.smul.{0, u1} ENNReal (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.hasSmul.{u1, 0} α ENNReal (SMulZeroClass.toHasSmul.{0, 0} ENNReal ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (SMulWithZero.toSmulZeroClass.{0, 0} ENNReal ENNReal (MulZeroClass.toHasZero.{0} ENNReal (MulZeroOneClass.toMulZeroClass.{0} ENNReal (MonoidWithZero.toMulZeroOneClass.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (MulActionWithZero.toSMulWithZero.{0, 0} ENNReal ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (Module.toMulActionWithZero.{0, 0} ENNReal ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Algebra.toModule.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) c (MeasureTheory.OuterMeasure.boundedBy.{u1} α m)) (MeasureTheory.OuterMeasure.boundedBy.{u1} α (SMul.smul.{0, u1} ENNReal ((Set.{u1} α) -> ENNReal) (Function.hasSMul.{u1, 0, 0} (Set.{u1} α) ENNReal ENNReal (Mul.toSMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) c m)))
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {c : ENNReal}, (Ne.{1} ENNReal c (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{succ u1} (MeasureTheory.OuterMeasure.{u1} α) (HSMul.hSMul.{0, u1, u1} ENNReal (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (instHSMul.{0, u1} ENNReal (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSMul.{u1, 0} α ENNReal (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) c (MeasureTheory.OuterMeasure.boundedBy.{u1} α m)) (MeasureTheory.OuterMeasure.boundedBy.{u1} α (HSMul.hSMul.{0, u1, u1} ENNReal ((Set.{u1} α) -> ENNReal) ((Set.{u1} α) -> ENNReal) (instHSMul.{0, u1} ENNReal ((Set.{u1} α) -> ENNReal) (Pi.instSMul.{u1, 0, 0} (Set.{u1} α) ENNReal (fun (a._@.Mathlib.MeasureTheory.Measure.OuterMeasure._hyg.12526 : Set.{u1} α) => ENNReal) (fun (i : Set.{u1} α) => Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) c m)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.smul_bounded_by MeasureTheory.OuterMeasure.smul_boundedByₓ'. -/
theorem smul_boundedBy {c : ℝ≥0∞} (hc : c ≠ ∞) : c • boundedBy m = boundedBy (c • m) :=
  by
  simp only [bounded_by, smul_of_function hc]
  congr 1 with s : 1
  rcases s.eq_empty_or_nonempty with (rfl | hs) <;> simp [*]
#align measure_theory.outer_measure.smul_bounded_by MeasureTheory.OuterMeasure.smul_boundedBy

/- warning: measure_theory.outer_measure.comap_bounded_by -> MeasureTheory.OuterMeasure.comap_boundedBy is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.comap_bounded_by MeasureTheory.OuterMeasure.comap_boundedByₓ'. -/
theorem comap_boundedBy {β} (f : β → α)
    (h : (Monotone fun s : { s : Set α // s.Nonempty } => m s) ∨ Surjective f) :
    comap f (boundedBy m) = boundedBy fun s => m (f '' s) :=
  by
  refine' (comap_of_function _ _).trans _
  · refine' h.imp (fun H s t hst => iSup_le fun hs => _) id
    have ht : t.nonempty := hs.mono hst
    exact (@H ⟨s, hs⟩ ⟨t, ht⟩ hst).trans (le_iSup (fun h : t.nonempty => m t) ht)
  · dsimp only [bounded_by]
    congr with s : 1
    rw [nonempty_image_iff]
#align measure_theory.outer_measure.comap_bounded_by MeasureTheory.OuterMeasure.comap_boundedBy

/- warning: measure_theory.outer_measure.bounded_by_union_of_top_of_nonempty_inter -> MeasureTheory.OuterMeasure.boundedBy_union_of_top_of_nonempty_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {s : Set.{u1} α} {t : Set.{u1} α}, (forall (u : Set.{u1} α), (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u)) -> (Eq.{1} ENNReal (m u) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) s) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) t)))
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {s : Set.{u1} α} {t : Set.{u1} α}, (forall (u : Set.{u1} α), (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u)) -> (Eq.{1} ENNReal (m u) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.boundedBy.{u1} α m) t)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.bounded_by_union_of_top_of_nonempty_inter MeasureTheory.OuterMeasure.boundedBy_union_of_top_of_nonempty_interₓ'. -/
/-- If `m u = ∞` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = measure_theory.outer_measure.bounded_by m`.

E.g., if `α` is an (e)metric space and `m u = ∞` on any set of diameter `≥ r`, then this lemma
implies that `μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s`
and `y ∈ t`.  -/
theorem boundedBy_union_of_top_of_nonempty_inter {s t : Set α}
    (h : ∀ u, (s ∩ u).Nonempty → (t ∩ u).Nonempty → m u = ∞) :
    boundedBy m (s ∪ t) = boundedBy m s + boundedBy m t :=
  ofFunction_union_of_top_of_nonempty_inter fun u hs ht =>
    top_unique <| (h u hs ht).ge.trans <| le_iSup (fun h => m u) (hs.mono <| inter_subset_right s u)
#align measure_theory.outer_measure.bounded_by_union_of_top_of_nonempty_inter MeasureTheory.OuterMeasure.boundedBy_union_of_top_of_nonempty_inter

end BoundedBy

section CaratheodoryMeasurable

universe u

parameter {α : Type u}(m : OuterMeasure α)

include m

attribute [local simp] Set.inter_comm Set.inter_left_comm Set.inter_assoc

variable {s s₁ s₂ : Set α}

#print MeasureTheory.OuterMeasure.IsCaratheodory /-
/-- A set `s` is Carathéodory-measurable for an outer measure `m` if for all sets `t` we have
  `m t = m (t ∩ s) + m (t \ s)`. -/
def IsCaratheodory (s : Set α) : Prop :=
  ∀ t, m t = m (t ∩ s) + m (t \ s)
#align measure_theory.outer_measure.is_caratheodory MeasureTheory.OuterMeasure.IsCaratheodory
-/

/- warning: measure_theory.outer_measure.is_caratheodory_iff_le' -> MeasureTheory.OuterMeasure.isCaratheodory_iff_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Set.{u1} α}, Iff (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s) (forall (t : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m t))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Set.{u1} α}, Iff (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s) (forall (t : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)) (MeasureTheory.OuterMeasure.measureOf.{u1} α m (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m t))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.is_caratheodory_iff_le' MeasureTheory.OuterMeasure.isCaratheodory_iff_le'ₓ'. -/
theorem isCaratheodory_iff_le' {s : Set α} : is_caratheodory s ↔ ∀ t, m (t ∩ s) + m (t \ s) ≤ m t :=
  forall_congr' fun t => le_antisymm_iff.trans <| and_iff_right <| le_inter_add_diff _
#align measure_theory.outer_measure.is_caratheodory_iff_le' MeasureTheory.OuterMeasure.isCaratheodory_iff_le'

#print MeasureTheory.OuterMeasure.isCaratheodory_empty /-
@[simp]
theorem isCaratheodory_empty : is_caratheodory ∅ := by simp [is_caratheodory, m.empty, diff_empty]
#align measure_theory.outer_measure.is_caratheodory_empty MeasureTheory.OuterMeasure.isCaratheodory_empty
-/

/- warning: measure_theory.outer_measure.is_caratheodory_compl -> MeasureTheory.OuterMeasure.isCaratheodory_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s₁ : Set.{u1} α}, (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s₁) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s₁))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s₁ : Set.{u1} α}, (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s₁) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s₁))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.is_caratheodory_compl MeasureTheory.OuterMeasure.isCaratheodory_complₓ'. -/
theorem isCaratheodory_compl : is_caratheodory s₁ → is_caratheodory (s₁ᶜ) := by
  simp [is_caratheodory, diff_eq, add_comm]
#align measure_theory.outer_measure.is_caratheodory_compl MeasureTheory.OuterMeasure.isCaratheodory_compl

/- warning: measure_theory.outer_measure.is_caratheodory_compl_iff -> MeasureTheory.OuterMeasure.isCaratheodory_compl_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Set.{u1} α}, Iff (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s)
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Set.{u1} α}, Iff (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s)
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.is_caratheodory_compl_iff MeasureTheory.OuterMeasure.isCaratheodory_compl_iffₓ'. -/
@[simp]
theorem isCaratheodory_compl_iff : is_caratheodory (sᶜ) ↔ is_caratheodory s :=
  ⟨fun h => by simpa using is_caratheodory_compl m h, is_caratheodory_compl⟩
#align measure_theory.outer_measure.is_caratheodory_compl_iff MeasureTheory.OuterMeasure.isCaratheodory_compl_iff

/- warning: measure_theory.outer_measure.is_caratheodory_union -> MeasureTheory.OuterMeasure.isCaratheodory_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s₁) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s₂) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s₁) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s₂) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.is_caratheodory_union MeasureTheory.OuterMeasure.isCaratheodory_unionₓ'. -/
theorem isCaratheodory_union (h₁ : is_caratheodory s₁) (h₂ : is_caratheodory s₂) :
    is_caratheodory (s₁ ∪ s₂) := fun t =>
  by
  rw [h₁ t, h₂ (t ∩ s₁), h₂ (t \ s₁), h₁ (t ∩ (s₁ ∪ s₂)), inter_diff_assoc _ _ s₁,
    Set.inter_assoc _ _ s₁, inter_eq_self_of_subset_right (Set.subset_union_left _ _),
    union_diff_left, h₂ (t ∩ s₁)]
  simp [diff_eq, add_assoc]
#align measure_theory.outer_measure.is_caratheodory_union MeasureTheory.OuterMeasure.isCaratheodory_union

/- warning: measure_theory.outer_measure.measure_inter_union -> MeasureTheory.OuterMeasure.measure_inter_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s₁) -> (forall {t : Set.{u1} α}, Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s₁)) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s₂))))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s₁) -> (forall {t : Set.{u1} α}, Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s₁)) (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s₂))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.measure_inter_union MeasureTheory.OuterMeasure.measure_inter_unionₓ'. -/
theorem measure_inter_union (h : s₁ ∩ s₂ ⊆ ∅) (h₁ : is_caratheodory s₁) {t : Set α} :
    m (t ∩ (s₁ ∪ s₂)) = m (t ∩ s₁) + m (t ∩ s₂) := by
  rw [h₁, Set.inter_assoc, Set.union_inter_cancel_left, inter_diff_assoc, union_diff_cancel_left h]
#align measure_theory.outer_measure.measure_inter_union MeasureTheory.OuterMeasure.measure_inter_union

#print MeasureTheory.OuterMeasure.isCaratheodory_iUnion_lt /-
theorem isCaratheodory_iUnion_lt {s : ℕ → Set α} :
    ∀ {n : ℕ}, (∀ i < n, is_caratheodory (s i)) → is_caratheodory (⋃ i < n, s i)
  | 0, h => by simp [Nat.not_lt_zero]
  | n + 1, h => by
    rw [bUnion_lt_succ] <;>
      exact
        is_caratheodory_union m
          (is_caratheodory_Union_lt fun i hi => h i <| lt_of_lt_of_le hi <| Nat.le_succ _)
          (h n (le_refl (n + 1)))
#align measure_theory.outer_measure.is_caratheodory_Union_lt MeasureTheory.OuterMeasure.isCaratheodory_iUnion_lt
-/

/- warning: measure_theory.outer_measure.is_caratheodory_inter -> MeasureTheory.OuterMeasure.isCaratheodory_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s₁) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s₂) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s₁) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m s₂) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.is_caratheodory_inter MeasureTheory.OuterMeasure.isCaratheodory_interₓ'. -/
theorem isCaratheodory_inter (h₁ : is_caratheodory s₁) (h₂ : is_caratheodory s₂) :
    is_caratheodory (s₁ ∩ s₂) :=
  by
  rw [← is_caratheodory_compl_iff, Set.compl_inter]
  exact is_caratheodory_union _ (is_caratheodory_compl _ h₁) (is_caratheodory_compl _ h₂)
#align measure_theory.outer_measure.is_caratheodory_inter MeasureTheory.OuterMeasure.isCaratheodory_inter

/- warning: measure_theory.outer_measure.is_caratheodory_sum -> MeasureTheory.OuterMeasure.isCaratheodory_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Nat -> (Set.{u1} α)}, (forall (i : Nat), MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (s i)) -> (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) s)) -> (forall {t : Set.{u1} α} {n : Nat}, Eq.{1} ENNReal (Finset.sum.{0, 0} ENNReal Nat (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.range n) (fun (i : Nat) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t (s i)))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => Set.iUnion.{u1, 0} α (LT.lt.{0} Nat Nat.hasLt i n) (fun (H : LT.lt.{0} Nat Nat.hasLt i n) => s i))))))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Nat -> (Set.{u1} α)}, (forall (i : Nat), MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (s i)) -> (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) s)) -> (forall {t : Set.{u1} α} {n : Nat}, Eq.{1} ENNReal (Finset.sum.{0, 0} ENNReal Nat (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.range n) (fun (i : Nat) => MeasureTheory.OuterMeasure.measureOf.{u1} α m (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t (s i)))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => Set.iUnion.{u1, 0} α (LT.lt.{0} Nat instLTNat i n) (fun (H : LT.lt.{0} Nat instLTNat i n) => s i))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.is_caratheodory_sum MeasureTheory.OuterMeasure.isCaratheodory_sumₓ'. -/
theorem isCaratheodory_sum {s : ℕ → Set α} (h : ∀ i, is_caratheodory (s i))
    (hd : Pairwise (Disjoint on s)) {t : Set α} :
    ∀ {n}, (∑ i in Finset.range n, m (t ∩ s i)) = m (t ∩ ⋃ i < n, s i)
  | 0 => by simp [Nat.not_lt_zero, m.empty]
  | Nat.succ n =>
    by
    rw [bUnion_lt_succ, Finset.sum_range_succ, Set.union_comm, is_caratheodory_sum,
      m.measure_inter_union _ (h n), add_comm]
    intro a
    simpa using fun (h₁ : a ∈ s n) i (hi : i < n) h₂ => (hd (ne_of_gt hi)).le_bot ⟨h₁, h₂⟩
#align measure_theory.outer_measure.is_caratheodory_sum MeasureTheory.OuterMeasure.isCaratheodory_sum

/- warning: measure_theory.outer_measure.is_caratheodory_Union_nat -> MeasureTheory.OuterMeasure.isCaratheodory_iUnion_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Nat -> (Set.{u1} α)}, (forall (i : Nat), MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (s i)) -> (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) s)) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i)))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Nat -> (Set.{u1} α)}, (forall (i : Nat), MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (s i)) -> (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) s)) -> (MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.is_caratheodory_Union_nat MeasureTheory.OuterMeasure.isCaratheodory_iUnion_natₓ'. -/
theorem isCaratheodory_iUnion_nat {s : ℕ → Set α} (h : ∀ i, is_caratheodory (s i))
    (hd : Pairwise (Disjoint on s)) : is_caratheodory (⋃ i, s i) :=
  is_caratheodory_iff_le'.2 fun t =>
    by
    have hp : m (t ∩ ⋃ i, s i) ≤ ⨆ n, m (t ∩ ⋃ i < n, s i) :=
      by
      convert m.Union fun i => t ∩ s i
      · rw [inter_Union]
      · simp [ENNReal.tsum_eq_iSup_nat, is_caratheodory_sum m h hd]
    refine' le_trans (add_le_add_right hp _) _
    rw [ENNReal.iSup_add]
    refine'
      iSup_le fun n =>
        le_trans (add_le_add_left _ _) (ge_of_eq (is_caratheodory_Union_lt m (fun i _ => h i) _))
    refine' m.mono (diff_subset_diff_right _)
    exact Union₂_subset fun i _ => subset_Union _ i
#align measure_theory.outer_measure.is_caratheodory_Union_nat MeasureTheory.OuterMeasure.isCaratheodory_iUnion_nat

/- warning: measure_theory.outer_measure.f_Union -> MeasureTheory.OuterMeasure.f_iUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Nat -> (Set.{u1} α)}, (forall (i : Nat), MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (s i)) -> (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) s)) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i))) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (s i))))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Nat -> (Set.{u1} α)}, (forall (i : Nat), MeasureTheory.OuterMeasure.IsCaratheodory.{u1} α m (s i)) -> (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) s)) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i))) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => MeasureTheory.OuterMeasure.measureOf.{u1} α m (s i))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.f_Union MeasureTheory.OuterMeasure.f_iUnionₓ'. -/
theorem f_iUnion {s : ℕ → Set α} (h : ∀ i, is_caratheodory (s i)) (hd : Pairwise (Disjoint on s)) :
    m (⋃ i, s i) = ∑' i, m (s i) :=
  by
  refine' le_antisymm (m.Union_nat s) _
  rw [ENNReal.tsum_eq_iSup_nat]
  refine' iSup_le fun n => _
  have := @is_caratheodory_sum _ m _ h hd univ n
  simp at this; simp [this]
  exact m.mono (Union₂_subset fun i _ => subset_Union _ i)
#align measure_theory.outer_measure.f_Union MeasureTheory.OuterMeasure.f_iUnion

#print MeasureTheory.OuterMeasure.caratheodoryDynkin /-
/-- The Carathéodory-measurable sets for an outer measure `m` form a Dynkin system.  -/
def caratheodoryDynkin : MeasurableSpace.DynkinSystem α
    where
  Has := is_caratheodory
  has_empty := is_caratheodory_empty
  HasCompl s := is_caratheodory_compl
  has_iUnion_nat f hf hn := is_caratheodory_Union_nat hn hf
#align measure_theory.outer_measure.caratheodory_dynkin MeasureTheory.OuterMeasure.caratheodoryDynkin
-/

#print MeasureTheory.OuterMeasure.caratheodory /-
/-- Given an outer measure `μ`, the Carathéodory-measurable space is
  defined such that `s` is measurable if `∀t, μ t = μ (t ∩ s) + μ (t \ s)`. -/
protected def caratheodory : MeasurableSpace α :=
  caratheodory_dynkin.toMeasurableSpace fun s₁ s₂ => is_caratheodory_inter
#align measure_theory.outer_measure.caratheodory MeasureTheory.OuterMeasure.caratheodory
-/

/- warning: measure_theory.outer_measure.is_caratheodory_iff -> MeasureTheory.OuterMeasure.isCaratheodory_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Set.{u1} α}, Iff (MeasurableSet.{u1} α (MeasureTheory.OuterMeasure.caratheodory.{u1} α m) s) (forall (t : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m t) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s))))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Set.{u1} α}, Iff (MeasurableSet.{u1} α (MeasureTheory.OuterMeasure.caratheodory.{u1} α m) s) (forall (t : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m t) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)) (MeasureTheory.OuterMeasure.measureOf.{u1} α m (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.is_caratheodory_iff MeasureTheory.OuterMeasure.isCaratheodory_iffₓ'. -/
theorem isCaratheodory_iff {s : Set α} :
    measurable_set[caratheodory] s ↔ ∀ t, m t = m (t ∩ s) + m (t \ s) :=
  Iff.rfl
#align measure_theory.outer_measure.is_caratheodory_iff MeasureTheory.OuterMeasure.isCaratheodory_iff

/- warning: measure_theory.outer_measure.is_caratheodory_iff_le -> MeasureTheory.OuterMeasure.isCaratheodory_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Set.{u1} α}, Iff (MeasurableSet.{u1} α (MeasureTheory.OuterMeasure.caratheodory.{u1} α m) s) (forall (t : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m t))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Set.{u1} α}, Iff (MeasurableSet.{u1} α (MeasureTheory.OuterMeasure.caratheodory.{u1} α m) s) (forall (t : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)) (MeasureTheory.OuterMeasure.measureOf.{u1} α m (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m t))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.is_caratheodory_iff_le MeasureTheory.OuterMeasure.isCaratheodory_iff_leₓ'. -/
theorem isCaratheodory_iff_le {s : Set α} :
    measurable_set[caratheodory] s ↔ ∀ t, m (t ∩ s) + m (t \ s) ≤ m t :=
  is_caratheodory_iff_le'
#align measure_theory.outer_measure.is_caratheodory_iff_le MeasureTheory.OuterMeasure.isCaratheodory_iff_le

/- warning: measure_theory.outer_measure.Union_eq_of_caratheodory -> MeasureTheory.OuterMeasure.iUnion_eq_of_caratheodory is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Nat -> (Set.{u1} α)}, (forall (i : Nat), MeasurableSet.{u1} α (MeasureTheory.OuterMeasure.caratheodory.{u1} α m) (s i)) -> (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) s)) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i))) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m (s i))))
but is expected to have type
  forall {α : Type.{u1}} (m : MeasureTheory.OuterMeasure.{u1} α) {s : Nat -> (Set.{u1} α)}, (forall (i : Nat), MeasurableSet.{u1} α (MeasureTheory.OuterMeasure.caratheodory.{u1} α m) (s i)) -> (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) s)) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i))) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => MeasureTheory.OuterMeasure.measureOf.{u1} α m (s i))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.Union_eq_of_caratheodory MeasureTheory.OuterMeasure.iUnion_eq_of_caratheodoryₓ'. -/
protected theorem iUnion_eq_of_caratheodory {s : ℕ → Set α}
    (h : ∀ i, measurable_set[caratheodory] (s i)) (hd : Pairwise (Disjoint on s)) :
    m (⋃ i, s i) = ∑' i, m (s i) :=
  f_Union h hd
#align measure_theory.outer_measure.Union_eq_of_caratheodory MeasureTheory.OuterMeasure.iUnion_eq_of_caratheodory

end CaratheodoryMeasurable

variable {α : Type _}

/- warning: measure_theory.outer_measure.of_function_caratheodory -> MeasureTheory.OuterMeasure.ofFunction_caratheodory is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {s : Set.{u1} α} {h₀ : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))}, (forall (t : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (m (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)) (m (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s))) (m t)) -> (MeasurableSet.{u1} α (MeasureTheory.OuterMeasure.caratheodory.{u1} α (MeasureTheory.OuterMeasure.ofFunction.{u1} α m h₀)) s)
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {s : Set.{u1} α} {h₀ : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))}, (forall (t : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (m (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)) (m (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s))) (m t)) -> (MeasurableSet.{u1} α (MeasureTheory.OuterMeasure.caratheodory.{u1} α (MeasureTheory.OuterMeasure.ofFunction.{u1} α m h₀)) s)
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.of_function_caratheodory MeasureTheory.OuterMeasure.ofFunction_caratheodoryₓ'. -/
theorem ofFunction_caratheodory {m : Set α → ℝ≥0∞} {s : Set α} {h₀ : m ∅ = 0}
    (hs : ∀ t, m (t ∩ s) + m (t \ s) ≤ m t) :
    measurable_set[(OuterMeasure.ofFunction m h₀).caratheodory] s :=
  by
  apply (is_caratheodory_iff_le _).mpr
  refine' fun t => le_iInf fun f => le_iInf fun hf => _
  refine'
    le_trans
      (add_le_add ((iInf_le_of_le fun i => f i ∩ s) <| iInf_le _ _)
        ((iInf_le_of_le fun i => f i \ s) <| iInf_le _ _))
      _
  · rw [← Union_inter]; exact inter_subset_inter_left _ hf
  · rw [← Union_diff]; exact diff_subset_diff_left hf
  · rw [← ENNReal.tsum_add]; exact ENNReal.tsum_le_tsum fun i => hs _
#align measure_theory.outer_measure.of_function_caratheodory MeasureTheory.OuterMeasure.ofFunction_caratheodory

/- warning: measure_theory.outer_measure.bounded_by_caratheodory -> MeasureTheory.OuterMeasure.boundedBy_caratheodory is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {s : Set.{u1} α}, (forall (t : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (m (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)) (m (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s))) (m t)) -> (MeasurableSet.{u1} α (MeasureTheory.OuterMeasure.caratheodory.{u1} α (MeasureTheory.OuterMeasure.boundedBy.{u1} α m)) s)
but is expected to have type
  forall {α : Type.{u1}} {m : (Set.{u1} α) -> ENNReal} {s : Set.{u1} α}, (forall (t : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (m (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)) (m (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s))) (m t)) -> (MeasurableSet.{u1} α (MeasureTheory.OuterMeasure.caratheodory.{u1} α (MeasureTheory.OuterMeasure.boundedBy.{u1} α m)) s)
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.bounded_by_caratheodory MeasureTheory.OuterMeasure.boundedBy_caratheodoryₓ'. -/
theorem boundedBy_caratheodory {m : Set α → ℝ≥0∞} {s : Set α}
    (hs : ∀ t, m (t ∩ s) + m (t \ s) ≤ m t) : measurable_set[(boundedBy m).caratheodory] s :=
  by
  apply of_function_caratheodory; intro t
  cases' t.eq_empty_or_nonempty with h h
  · simp [h, not_nonempty_empty]
  · convert le_trans _ (hs t); · simp [h]; exact add_le_add iSup_const_le iSup_const_le
#align measure_theory.outer_measure.bounded_by_caratheodory MeasureTheory.OuterMeasure.boundedBy_caratheodory

/- warning: measure_theory.outer_measure.zero_caratheodory -> MeasureTheory.OuterMeasure.zero_caratheodory is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (MeasurableSpace.{u1} α) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (OfNat.ofNat.{u1} (MeasureTheory.OuterMeasure.{u1} α) 0 (OfNat.mk.{u1} (MeasureTheory.OuterMeasure.{u1} α) 0 (Zero.zero.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instZero.{u1} α))))) (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toHasTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (MeasurableSpace.{u1} α) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (OfNat.ofNat.{u1} (MeasureTheory.OuterMeasure.{u1} α) 0 (Zero.toOfNat0.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instZero.{u1} α)))) (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} α)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.zero_caratheodory MeasureTheory.OuterMeasure.zero_caratheodoryₓ'. -/
@[simp]
theorem zero_caratheodory : (0 : OuterMeasure α).caratheodory = ⊤ :=
  top_unique fun s _ t => (add_zero _).symm
#align measure_theory.outer_measure.zero_caratheodory MeasureTheory.OuterMeasure.zero_caratheodory

/- warning: measure_theory.outer_measure.top_caratheodory -> MeasureTheory.OuterMeasure.top_caratheodory is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (MeasurableSpace.{u1} α) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (Top.top.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toHasTop.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α)))) (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toHasTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (MeasurableSpace.{u1} α) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (Top.top.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toTop.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α)))) (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} α)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.top_caratheodory MeasureTheory.OuterMeasure.top_caratheodoryₓ'. -/
theorem top_caratheodory : (⊤ : OuterMeasure α).caratheodory = ⊤ :=
  top_unique fun s hs =>
    (isCaratheodory_iff_le _).2 fun t =>
      t.eq_empty_or_nonempty.elim (fun ht => by simp [ht]) fun ht => by
        simp only [ht, top_apply, le_top]
#align measure_theory.outer_measure.top_caratheodory MeasureTheory.OuterMeasure.top_caratheodory

/- warning: measure_theory.outer_measure.le_add_caratheodory -> MeasureTheory.OuterMeasure.le_add_caratheodory is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m₁ : MeasureTheory.OuterMeasure.{u1} α) (m₂ : MeasureTheory.OuterMeasure.{u1} α), LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) (Inf.inf.{u1} (MeasurableSpace.{u1} α) (SemilatticeInf.toHasInf.{u1} (MeasurableSpace.{u1} α) (Lattice.toSemilatticeInf.{u1} (MeasurableSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α))))) (MeasureTheory.OuterMeasure.caratheodory.{u1} α m₁) (MeasureTheory.OuterMeasure.caratheodory.{u1} α m₂)) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (instHAdd.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instAdd.{u1} α)) m₁ m₂))
but is expected to have type
  forall {α : Type.{u1}} (m₁ : MeasureTheory.OuterMeasure.{u1} α) (m₂ : MeasureTheory.OuterMeasure.{u1} α), LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instLEMeasurableSpace.{u1} α) (Inf.inf.{u1} (MeasurableSpace.{u1} α) (Lattice.toInf.{u1} (MeasurableSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} α)))) (MeasureTheory.OuterMeasure.caratheodory.{u1} α m₁) (MeasureTheory.OuterMeasure.caratheodory.{u1} α m₂)) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (instHAdd.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instAdd.{u1} α)) m₁ m₂))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.le_add_caratheodory MeasureTheory.OuterMeasure.le_add_caratheodoryₓ'. -/
theorem le_add_caratheodory (m₁ m₂ : OuterMeasure α) :
    m₁.caratheodory ⊓ m₂.caratheodory ≤ (m₁ + m₂ : OuterMeasure α).caratheodory :=
  fun s ⟨hs₁, hs₂⟩ t => by simp [hs₁ t, hs₂ t, add_left_comm, add_assoc]
#align measure_theory.outer_measure.le_add_caratheodory MeasureTheory.OuterMeasure.le_add_caratheodory

/- warning: measure_theory.outer_measure.le_sum_caratheodory -> MeasureTheory.OuterMeasure.le_sum_caratheodory is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (m : ι -> (MeasureTheory.OuterMeasure.{u1} α)), LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) (iInf.{u1, succ u2} (MeasurableSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α))) ι (fun (i : ι) => MeasureTheory.OuterMeasure.caratheodory.{u1} α (m i))) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (MeasureTheory.OuterMeasure.sum.{u1, u2} α ι m))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} (m : ι -> (MeasureTheory.OuterMeasure.{u1} α)), LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instLEMeasurableSpace.{u1} α) (iInf.{u1, succ u2} (MeasurableSpace.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} α))) ι (fun (i : ι) => MeasureTheory.OuterMeasure.caratheodory.{u1} α (m i))) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (MeasureTheory.OuterMeasure.sum.{u1, u2} α ι m))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.le_sum_caratheodory MeasureTheory.OuterMeasure.le_sum_caratheodoryₓ'. -/
theorem le_sum_caratheodory {ι} (m : ι → OuterMeasure α) :
    (⨅ i, (m i).caratheodory) ≤ (sum m).caratheodory := fun s h t => by
  simp [fun i => MeasurableSpace.measurableSet_iInf.1 h i t, ENNReal.tsum_add]
#align measure_theory.outer_measure.le_sum_caratheodory MeasureTheory.OuterMeasure.le_sum_caratheodory

/- warning: measure_theory.outer_measure.le_smul_caratheodory -> MeasureTheory.OuterMeasure.le_smul_caratheodory is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : ENNReal) (m : MeasureTheory.OuterMeasure.{u1} α), LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) (MeasureTheory.OuterMeasure.caratheodory.{u1} α m) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (SMul.smul.{0, u1} ENNReal (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.hasSmul.{u1, 0} α ENNReal (SMulZeroClass.toHasSmul.{0, 0} ENNReal ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (SMulWithZero.toSmulZeroClass.{0, 0} ENNReal ENNReal (MulZeroClass.toHasZero.{0} ENNReal (MulZeroOneClass.toMulZeroClass.{0} ENNReal (MonoidWithZero.toMulZeroOneClass.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (MulActionWithZero.toSMulWithZero.{0, 0} ENNReal ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (Module.toMulActionWithZero.{0, 0} ENNReal ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Algebra.toModule.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) a m))
but is expected to have type
  forall {α : Type.{u1}} (a : ENNReal) (m : MeasureTheory.OuterMeasure.{u1} α), LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instLEMeasurableSpace.{u1} α) (MeasureTheory.OuterMeasure.caratheodory.{u1} α m) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (HSMul.hSMul.{0, u1, u1} ENNReal (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (instHSMul.{0, u1} ENNReal (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSMul.{u1, 0} α ENNReal (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) a m))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.le_smul_caratheodory MeasureTheory.OuterMeasure.le_smul_caratheodoryₓ'. -/
theorem le_smul_caratheodory (a : ℝ≥0∞) (m : OuterMeasure α) :
    m.caratheodory ≤ (a • m).caratheodory := fun s h t => by simp [h t, mul_add]
#align measure_theory.outer_measure.le_smul_caratheodory MeasureTheory.OuterMeasure.le_smul_caratheodory

/- warning: measure_theory.outer_measure.dirac_caratheodory -> MeasureTheory.OuterMeasure.dirac_caratheodory is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α), Eq.{succ u1} (MeasurableSpace.{u1} α) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (MeasureTheory.OuterMeasure.dirac.{u1} α a)) (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toHasTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} (a : α), Eq.{succ u1} (MeasurableSpace.{u1} α) (MeasureTheory.OuterMeasure.caratheodory.{u1} α (MeasureTheory.OuterMeasure.dirac.{u1} α a)) (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} α)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.dirac_caratheodory MeasureTheory.OuterMeasure.dirac_caratheodoryₓ'. -/
@[simp]
theorem dirac_caratheodory (a : α) : (dirac a).caratheodory = ⊤ :=
  top_unique fun s _ t => by
    by_cases ht : a ∈ t; swap; · simp [ht]
    by_cases hs : a ∈ s <;> simp [*]
#align measure_theory.outer_measure.dirac_caratheodory MeasureTheory.OuterMeasure.dirac_caratheodory

section InfGen

#print MeasureTheory.OuterMeasure.sInfGen /-
/-- Given a set of outer measures, we define a new function that on a set `s` is defined to be the
  infimum of `μ(s)` for the outer measures `μ` in the collection. We ensure that this
  function is defined to be `0` on `∅`, even if the collection of outer measures is empty.
  The outer measure generated by this function is the infimum of the given outer measures. -/
def sInfGen (m : Set (OuterMeasure α)) (s : Set α) : ℝ≥0∞ :=
  ⨅ (μ : OuterMeasure α) (h : μ ∈ m), μ s
#align measure_theory.outer_measure.Inf_gen MeasureTheory.OuterMeasure.sInfGen
-/

/- warning: measure_theory.outer_measure.Inf_gen_def -> MeasureTheory.OuterMeasure.sInfGen_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (t : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.sInfGen.{u1} α m t) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (MeasureTheory.OuterMeasure.{u1} α) (fun (μ : MeasureTheory.OuterMeasure.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.hasMem.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) (fun (h : Membership.Mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.hasMem.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) μ t)))
but is expected to have type
  forall {α : Type.{u1}} (m : Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (t : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.sInfGen.{u1} α m t) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasureTheory.OuterMeasure.{u1} α) (fun (μ : MeasureTheory.OuterMeasure.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.instMembershipSet.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) (fun (h : Membership.mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.instMembershipSet.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) => MeasureTheory.OuterMeasure.measureOf.{u1} α μ t)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.Inf_gen_def MeasureTheory.OuterMeasure.sInfGen_defₓ'. -/
theorem sInfGen_def (m : Set (OuterMeasure α)) (t : Set α) :
    sInfGen m t = ⨅ (μ : OuterMeasure α) (h : μ ∈ m), μ t :=
  rfl
#align measure_theory.outer_measure.Inf_gen_def MeasureTheory.OuterMeasure.sInfGen_def

/- warning: measure_theory.outer_measure.Inf_eq_bounded_by_Inf_gen -> MeasureTheory.OuterMeasure.sInf_eq_boundedBy_sInfGen is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (m : Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)), Eq.{succ u1} (MeasureTheory.OuterMeasure.{u1} α) (InfSet.sInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) m) (MeasureTheory.OuterMeasure.boundedBy.{u1} α (MeasureTheory.OuterMeasure.sInfGen.{u1} α m))
but is expected to have type
  forall {α : Type.{u1}} (m : Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)), Eq.{succ u1} (MeasureTheory.OuterMeasure.{u1} α) (InfSet.sInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) m) (MeasureTheory.OuterMeasure.boundedBy.{u1} α (MeasureTheory.OuterMeasure.sInfGen.{u1} α m))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.Inf_eq_bounded_by_Inf_gen MeasureTheory.OuterMeasure.sInf_eq_boundedBy_sInfGenₓ'. -/
theorem sInf_eq_boundedBy_sInfGen (m : Set (OuterMeasure α)) :
    sInf m = OuterMeasure.boundedBy (sInfGen m) :=
  by
  refine' le_antisymm _ _
  · refine' le_bounded_by.2 fun s => le_iInf₂ fun μ hμ => _
    exact (show Inf m ≤ μ from sInf_le hμ) s
  · refine' le_sInf _; intro μ hμ t; refine' le_trans (bounded_by_le t) (iInf₂_le μ hμ)
#align measure_theory.outer_measure.Inf_eq_bounded_by_Inf_gen MeasureTheory.OuterMeasure.sInf_eq_boundedBy_sInfGen

/- warning: measure_theory.outer_measure.supr_Inf_gen_nonempty -> MeasureTheory.OuterMeasure.iSup_sInfGen_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)}, (Set.Nonempty.{u1} (MeasureTheory.OuterMeasure.{u1} α) m) -> (forall (t : Set.{u1} α), Eq.{1} ENNReal (iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Set.Nonempty.{u1} α t) (fun (h : Set.Nonempty.{u1} α t) => MeasureTheory.OuterMeasure.sInfGen.{u1} α m t)) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (MeasureTheory.OuterMeasure.{u1} α) (fun (μ : MeasureTheory.OuterMeasure.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.hasMem.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) (fun (h : Membership.Mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.hasMem.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) μ t))))
but is expected to have type
  forall {α : Type.{u1}} {m : Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)}, (Set.Nonempty.{u1} (MeasureTheory.OuterMeasure.{u1} α) m) -> (forall (t : Set.{u1} α), Eq.{1} ENNReal (iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.Nonempty.{u1} α t) (fun (h : Set.Nonempty.{u1} α t) => MeasureTheory.OuterMeasure.sInfGen.{u1} α m t)) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasureTheory.OuterMeasure.{u1} α) (fun (μ : MeasureTheory.OuterMeasure.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.instMembershipSet.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) (fun (h : Membership.mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.instMembershipSet.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) => MeasureTheory.OuterMeasure.measureOf.{u1} α μ t))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.supr_Inf_gen_nonempty MeasureTheory.OuterMeasure.iSup_sInfGen_nonemptyₓ'. -/
theorem iSup_sInfGen_nonempty {m : Set (OuterMeasure α)} (h : m.Nonempty) (t : Set α) :
    (⨆ h : t.Nonempty, sInfGen m t) = ⨅ (μ : OuterMeasure α) (h : μ ∈ m), μ t :=
  by
  rcases t.eq_empty_or_nonempty with (rfl | ht)
  · rcases h with ⟨μ, hμ⟩
    rw [eq_false not_nonempty_empty, iSup_false, eq_comm]
    simp_rw [empty']
    apply bot_unique
    refine' iInf_le_of_le μ (iInf_le _ hμ)
  · simp [ht, Inf_gen_def]
#align measure_theory.outer_measure.supr_Inf_gen_nonempty MeasureTheory.OuterMeasure.iSup_sInfGen_nonempty

/- warning: measure_theory.outer_measure.Inf_apply -> MeasureTheory.OuterMeasure.sInf_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)} {s : Set.{u1} α}, (Set.Nonempty.{u1} (MeasureTheory.OuterMeasure.{u1} α) m) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (InfSet.sInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) m) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h2 : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (n : Nat) => iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (MeasureTheory.OuterMeasure.{u1} α) (fun (μ : MeasureTheory.OuterMeasure.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.hasMem.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) (fun (h3 : Membership.Mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.hasMem.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) μ (t n))))))))
but is expected to have type
  forall {α : Type.{u1}} {m : Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)} {s : Set.{u1} α}, (Set.Nonempty.{u1} (MeasureTheory.OuterMeasure.{u1} α) m) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (InfSet.sInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) m) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h2 : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (n : Nat) => iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasureTheory.OuterMeasure.{u1} α) (fun (μ : MeasureTheory.OuterMeasure.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.instMembershipSet.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) (fun (h3 : Membership.mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.instMembershipSet.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) => MeasureTheory.OuterMeasure.measureOf.{u1} α μ (t n))))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.Inf_apply MeasureTheory.OuterMeasure.sInf_applyₓ'. -/
/-- The value of the Infimum of a nonempty set of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem sInf_apply {m : Set (OuterMeasure α)} {s : Set α} (h : m.Nonempty) :
    sInf m s =
      ⨅ (t : ℕ → Set α) (h2 : s ⊆ iUnion t), ∑' n, ⨅ (μ : OuterMeasure α) (h3 : μ ∈ m), μ (t n) :=
  by simp_rw [Inf_eq_bounded_by_Inf_gen, bounded_by_apply, supr_Inf_gen_nonempty h]
#align measure_theory.outer_measure.Inf_apply MeasureTheory.OuterMeasure.sInf_apply

/- warning: measure_theory.outer_measure.Inf_apply' -> MeasureTheory.OuterMeasure.sInf_apply' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)} {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (InfSet.sInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) m) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h2 : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (n : Nat) => iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (MeasureTheory.OuterMeasure.{u1} α) (fun (μ : MeasureTheory.OuterMeasure.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.hasMem.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) (fun (h3 : Membership.Mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.hasMem.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) μ (t n))))))))
but is expected to have type
  forall {α : Type.{u1}} {m : Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)} {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (InfSet.sInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) m) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h2 : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (n : Nat) => iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasureTheory.OuterMeasure.{u1} α) (fun (μ : MeasureTheory.OuterMeasure.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.instMembershipSet.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) (fun (h3 : Membership.mem.{u1, u1} (MeasureTheory.OuterMeasure.{u1} α) (Set.{u1} (MeasureTheory.OuterMeasure.{u1} α)) (Set.instMembershipSet.{u1} (MeasureTheory.OuterMeasure.{u1} α)) μ m) => MeasureTheory.OuterMeasure.measureOf.{u1} α μ (t n))))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.Inf_apply' MeasureTheory.OuterMeasure.sInf_apply'ₓ'. -/
/-- The value of the Infimum of a set of outer measures on a nonempty set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem sInf_apply' {m : Set (OuterMeasure α)} {s : Set α} (h : s.Nonempty) :
    sInf m s =
      ⨅ (t : ℕ → Set α) (h2 : s ⊆ iUnion t), ∑' n, ⨅ (μ : OuterMeasure α) (h3 : μ ∈ m), μ (t n) :=
  m.eq_empty_or_nonempty.elim (fun hm => by simp [hm, h]) sInf_apply
#align measure_theory.outer_measure.Inf_apply' MeasureTheory.OuterMeasure.sInf_apply'

/- warning: measure_theory.outer_measure.infi_apply -> MeasureTheory.OuterMeasure.iInf_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (m : ι -> (MeasureTheory.OuterMeasure.{u1} α)) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (iInf.{u1, u2} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) ι (fun (i : ι) => m i)) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h2 : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (n : Nat) => iInf.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (m i) (t n))))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (m : ι -> (MeasureTheory.OuterMeasure.{u1} α)) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (iInf.{u1, u2} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) ι (fun (i : ι) => m i)) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h2 : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (n : Nat) => iInf.{0, u2} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => MeasureTheory.OuterMeasure.measureOf.{u1} α (m i) (t n))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.infi_apply MeasureTheory.OuterMeasure.iInf_applyₓ'. -/
/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem iInf_apply {ι} [Nonempty ι] (m : ι → OuterMeasure α) (s : Set α) :
    (⨅ i, m i) s = ⨅ (t : ℕ → Set α) (h2 : s ⊆ iUnion t), ∑' n, ⨅ i, m i (t n) := by
  rw [iInf, sInf_apply (range_nonempty m)]; simp only [iInf_range]
#align measure_theory.outer_measure.infi_apply MeasureTheory.OuterMeasure.iInf_apply

/- warning: measure_theory.outer_measure.infi_apply' -> MeasureTheory.OuterMeasure.iInf_apply' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (m : ι -> (MeasureTheory.OuterMeasure.{u1} α)) {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (iInf.{u1, u2} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) ι (fun (i : ι) => m i)) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h2 : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (n : Nat) => iInf.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (m i) (t n)))))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} (m : ι -> (MeasureTheory.OuterMeasure.{u1} α)) {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (iInf.{u1, u2} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) ι (fun (i : ι) => m i)) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h2 : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (n : Nat) => iInf.{0, u2} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => MeasureTheory.OuterMeasure.measureOf.{u1} α (m i) (t n)))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.infi_apply' MeasureTheory.OuterMeasure.iInf_apply'ₓ'. -/
/-- The value of the Infimum of a family of outer measures on a nonempty set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem iInf_apply' {ι} (m : ι → OuterMeasure α) {s : Set α} (hs : s.Nonempty) :
    (⨅ i, m i) s = ⨅ (t : ℕ → Set α) (h2 : s ⊆ iUnion t), ∑' n, ⨅ i, m i (t n) := by
  rw [iInf, Inf_apply' hs]; simp only [iInf_range]
#align measure_theory.outer_measure.infi_apply' MeasureTheory.OuterMeasure.iInf_apply'

/- warning: measure_theory.outer_measure.binfi_apply -> MeasureTheory.OuterMeasure.biInf_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {I : Set.{u2} ι}, (Set.Nonempty.{u2} ι I) -> (forall (m : ι -> (MeasureTheory.OuterMeasure.{u1} α)) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (iInf.{u1, succ u2} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) ι (fun (i : ι) => iInf.{u1, 0} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) => m i))) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h2 : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (n : Nat) => iInf.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (m i) (t n))))))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {I : Set.{u2} ι}, (Set.Nonempty.{u2} ι I) -> (forall (m : ι -> (MeasureTheory.OuterMeasure.{u1} α)) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (iInf.{u1, succ u2} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) ι (fun (i : ι) => iInf.{u1, 0} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) => m i))) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h2 : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (n : Nat) => iInf.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) => MeasureTheory.OuterMeasure.measureOf.{u1} α (m i) (t n))))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.binfi_apply MeasureTheory.OuterMeasure.biInf_applyₓ'. -/
/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem biInf_apply {ι} {I : Set ι} (hI : I.Nonempty) (m : ι → OuterMeasure α) (s : Set α) :
    (⨅ i ∈ I, m i) s = ⨅ (t : ℕ → Set α) (h2 : s ⊆ iUnion t), ∑' n, ⨅ i ∈ I, m i (t n) := by
  haveI := hI.to_subtype; simp only [← iInf_subtype'', iInf_apply]
#align measure_theory.outer_measure.binfi_apply MeasureTheory.OuterMeasure.biInf_apply

/- warning: measure_theory.outer_measure.binfi_apply' -> MeasureTheory.OuterMeasure.biInf_apply' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (I : Set.{u2} ι) (m : ι -> (MeasureTheory.OuterMeasure.{u1} α)) {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (iInf.{u1, succ u2} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) ι (fun (i : ι) => iInf.{u1, 0} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) => m i))) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h2 : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (n : Nat) => iInf.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (m i) (t n))))))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} (I : Set.{u2} ι) (m : ι -> (MeasureTheory.OuterMeasure.{u1} α)) {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (iInf.{u1, succ u2} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) ι (fun (i : ι) => iInf.{u1, 0} (MeasureTheory.OuterMeasure.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (MeasureTheory.OuterMeasure.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instCompleteLattice.{u1} α))) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) => m i))) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Nat -> (Set.{u1} α)) (fun (t : Nat -> (Set.{u1} α)) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) (fun (h2 : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, 1} α Nat t)) => tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (n : Nat) => iInf.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) => MeasureTheory.OuterMeasure.measureOf.{u1} α (m i) (t n))))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.binfi_apply' MeasureTheory.OuterMeasure.biInf_apply'ₓ'. -/
/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem biInf_apply' {ι} (I : Set ι) (m : ι → OuterMeasure α) {s : Set α} (hs : s.Nonempty) :
    (⨅ i ∈ I, m i) s = ⨅ (t : ℕ → Set α) (h2 : s ⊆ iUnion t), ∑' n, ⨅ i ∈ I, m i (t n) := by
  simp only [← iInf_subtype'', infi_apply' _ hs]
#align measure_theory.outer_measure.binfi_apply' MeasureTheory.OuterMeasure.biInf_apply'

/- warning: measure_theory.outer_measure.map_infi_le -> MeasureTheory.OuterMeasure.map_iInf_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_infi_le MeasureTheory.OuterMeasure.map_iInf_leₓ'. -/
theorem map_iInf_le {ι β} (f : α → β) (m : ι → OuterMeasure α) :
    map f (⨅ i, m i) ≤ ⨅ i, map f (m i) :=
  (map_mono f).map_iInf_le
#align measure_theory.outer_measure.map_infi_le MeasureTheory.OuterMeasure.map_iInf_le

/- warning: measure_theory.outer_measure.comap_infi -> MeasureTheory.OuterMeasure.comap_iInf is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.comap_infi MeasureTheory.OuterMeasure.comap_iInfₓ'. -/
theorem comap_iInf {ι β} (f : α → β) (m : ι → OuterMeasure β) :
    comap f (⨅ i, m i) = ⨅ i, comap f (m i) :=
  by
  refine' ext_nonempty fun s hs => _
  refine' ((comap_mono f).map_iInf_le s).antisymm _
  simp only [comap_apply, infi_apply' _ hs, infi_apply' _ (hs.image _), le_iInf_iff,
    Set.image_subset_iff, preimage_Union]
  refine' fun t ht => iInf_le_of_le _ (iInf_le_of_le ht <| ENNReal.tsum_le_tsum fun k => _)
  exact iInf_mono fun i => (m i).mono (image_preimage_subset _ _)
#align measure_theory.outer_measure.comap_infi MeasureTheory.OuterMeasure.comap_iInf

/- warning: measure_theory.outer_measure.map_infi -> MeasureTheory.OuterMeasure.map_iInf is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_infi MeasureTheory.OuterMeasure.map_iInfₓ'. -/
theorem map_iInf {ι β} {f : α → β} (hf : Injective f) (m : ι → OuterMeasure α) :
    map f (⨅ i, m i) = restrict (range f) (⨅ i, map f (m i)) :=
  by
  refine' Eq.trans _ (map_comap _ _)
  simp only [comap_infi, comap_map hf]
#align measure_theory.outer_measure.map_infi MeasureTheory.OuterMeasure.map_iInf

/- warning: measure_theory.outer_measure.map_infi_comap -> MeasureTheory.OuterMeasure.map_iInf_comap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_infi_comap MeasureTheory.OuterMeasure.map_iInf_comapₓ'. -/
theorem map_iInf_comap {ι β} [Nonempty ι] {f : α → β} (m : ι → OuterMeasure β) :
    map f (⨅ i, comap f (m i)) = ⨅ i, map f (comap f (m i)) :=
  by
  refine' (map_infi_le _ _).antisymm fun s => _
  simp only [map_apply, comap_apply, iInf_apply, le_iInf_iff]
  refine' fun t ht => iInf_le_of_le (fun n => f '' t n ∪ range fᶜ) (iInf_le_of_le _ _)
  · rw [← Union_union, Set.union_comm, ← inter_subset, ← image_Union, ←
      image_preimage_eq_inter_range]
    exact image_subset _ ht
  · refine' ENNReal.tsum_le_tsum fun n => iInf_mono fun i => (m i).mono _
    simp
#align measure_theory.outer_measure.map_infi_comap MeasureTheory.OuterMeasure.map_iInf_comap

/- warning: measure_theory.outer_measure.map_binfi_comap -> MeasureTheory.OuterMeasure.map_biInf_comap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.map_binfi_comap MeasureTheory.OuterMeasure.map_biInf_comapₓ'. -/
theorem map_biInf_comap {ι β} {I : Set ι} (hI : I.Nonempty) {f : α → β} (m : ι → OuterMeasure β) :
    map f (⨅ i ∈ I, comap f (m i)) = ⨅ i ∈ I, map f (comap f (m i)) := by haveI := hI.to_subtype;
  rw [← iInf_subtype'', ← iInf_subtype'']; exact map_infi_comap _
#align measure_theory.outer_measure.map_binfi_comap MeasureTheory.OuterMeasure.map_biInf_comap

/- warning: measure_theory.outer_measure.restrict_infi_restrict -> MeasureTheory.OuterMeasure.restrict_iInf_restrict is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.restrict_infi_restrict MeasureTheory.OuterMeasure.restrict_iInf_restrictₓ'. -/
theorem restrict_iInf_restrict {ι} (s : Set α) (m : ι → OuterMeasure α) :
    restrict s (⨅ i, restrict s (m i)) = restrict s (⨅ i, m i) :=
  calc
    restrict s (⨅ i, restrict s (m i)) = restrict (range (coe : s → α)) (⨅ i, restrict s (m i)) :=
      by rw [Subtype.range_coe]
    _ = map (coe : s → α) (⨅ i, comap coe (m i)) := (map_iInf Subtype.coe_injective _).symm
    _ = restrict s (⨅ i, m i) := congr_arg (map coe) (comap_iInf _ _).symm
    
#align measure_theory.outer_measure.restrict_infi_restrict MeasureTheory.OuterMeasure.restrict_iInf_restrict

/- warning: measure_theory.outer_measure.restrict_infi -> MeasureTheory.OuterMeasure.restrict_iInf is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.restrict_infi MeasureTheory.OuterMeasure.restrict_iInfₓ'. -/
theorem restrict_iInf {ι} [Nonempty ι] (s : Set α) (m : ι → OuterMeasure α) :
    restrict s (⨅ i, m i) = ⨅ i, restrict s (m i) :=
  (congr_arg (map coe) (comap_iInf _ _)).trans (map_iInf_comap _)
#align measure_theory.outer_measure.restrict_infi MeasureTheory.OuterMeasure.restrict_iInf

/- warning: measure_theory.outer_measure.restrict_binfi -> MeasureTheory.OuterMeasure.restrict_biInf is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.restrict_binfi MeasureTheory.OuterMeasure.restrict_biInfₓ'. -/
theorem restrict_biInf {ι} {I : Set ι} (hI : I.Nonempty) (s : Set α) (m : ι → OuterMeasure α) :
    restrict s (⨅ i ∈ I, m i) = ⨅ i ∈ I, restrict s (m i) := by haveI := hI.to_subtype;
  rw [← iInf_subtype'', ← iInf_subtype'']; exact restrict_infi _ _
#align measure_theory.outer_measure.restrict_binfi MeasureTheory.OuterMeasure.restrict_biInf

/- warning: measure_theory.outer_measure.restrict_Inf_eq_Inf_restrict -> MeasureTheory.OuterMeasure.restrict_sInf_eq_sInf_restrict is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.restrict_Inf_eq_Inf_restrict MeasureTheory.OuterMeasure.restrict_sInf_eq_sInf_restrictₓ'. -/
/-- This proves that Inf and restrict commute for outer measures, so long as the set of
outer measures is nonempty. -/
theorem restrict_sInf_eq_sInf_restrict (m : Set (OuterMeasure α)) {s : Set α} (hm : m.Nonempty) :
    restrict s (sInf m) = sInf (restrict s '' m) := by
  simp only [sInf_eq_iInf, restrict_binfi, hm, iInf_image]
#align measure_theory.outer_measure.restrict_Inf_eq_Inf_restrict MeasureTheory.OuterMeasure.restrict_sInf_eq_sInf_restrict

end InfGen

end OuterMeasure

open OuterMeasure

/-! ### Induced Outer Measure

  We can extend a function defined on a subset of `set α` to an outer measure.
  The underlying function is called `extend`, and the measure it induces is called
  `induced_outer_measure`.

  Some lemmas below are proven twice, once in the general case, and one where the function `m`
  is only defined on measurable sets (i.e. when `P = measurable_set`). In the latter cases, we can
  remove some hypotheses in the statement. The general version has the same name, but with a prime
  at the end. -/


section Extend

variable {α : Type _} {P : α → Prop}

variable (m : ∀ s : α, P s → ℝ≥0∞)

#print MeasureTheory.extend /-
/-- We can trivially extend a function defined on a subclass of objects (with codomain `ℝ≥0∞`)
  to all objects by defining it to be `∞` on the objects not in the class. -/
def extend (s : α) : ℝ≥0∞ :=
  ⨅ h : P s, m s h
#align measure_theory.extend MeasureTheory.extend
-/

/- warning: measure_theory.smul_extend -> MeasureTheory.smul_extend is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : α -> Prop} (m : forall (s : α), (P s) -> ENNReal) {R : Type.{u2}} [_inst_1 : Zero.{u2} R] [_inst_2 : SMulWithZero.{u2, 0} R ENNReal _inst_1 ENNReal.hasZero] [_inst_3 : IsScalarTower.{u2, 0, 0} R ENNReal ENNReal (SMulZeroClass.toHasSmul.{u2, 0} R ENNReal ENNReal.hasZero (SMulWithZero.toSmulZeroClass.{u2, 0} R ENNReal _inst_1 ENNReal.hasZero _inst_2)) (Mul.toSMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (SMulZeroClass.toHasSmul.{u2, 0} R ENNReal ENNReal.hasZero (SMulWithZero.toSmulZeroClass.{u2, 0} R ENNReal _inst_1 ENNReal.hasZero _inst_2))] [_inst_4 : NoZeroSMulDivisors.{u2, 0} R ENNReal _inst_1 ENNReal.hasZero (SMulZeroClass.toHasSmul.{u2, 0} R ENNReal ENNReal.hasZero (SMulWithZero.toSmulZeroClass.{u2, 0} R ENNReal _inst_1 ENNReal.hasZero _inst_2))] {c : R}, (Ne.{succ u2} R c (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R _inst_1)))) -> (Eq.{succ u1} (α -> ENNReal) (SMul.smul.{u2, u1} R (α -> ENNReal) (Function.hasSMul.{u1, u2, 0} α R ENNReal (SMulZeroClass.toHasSmul.{u2, 0} R ENNReal ENNReal.hasZero (SMulWithZero.toSmulZeroClass.{u2, 0} R ENNReal _inst_1 ENNReal.hasZero _inst_2))) c (MeasureTheory.extend.{u1} α (fun (s : α) => P s) m)) (MeasureTheory.extend.{u1} α (fun (s : α) => P s) (fun (s : α) (h : P s) => SMul.smul.{u2, 0} R ENNReal (SMulZeroClass.toHasSmul.{u2, 0} R ENNReal ENNReal.hasZero (SMulWithZero.toSmulZeroClass.{u2, 0} R ENNReal _inst_1 ENNReal.hasZero _inst_2)) c (m s h))))
but is expected to have type
  forall {α : Type.{u1}} {P : α -> Prop} (m : forall (s : α), (P s) -> ENNReal) {R : Type.{u2}} [_inst_1 : Zero.{u2} R] [_inst_2 : SMulWithZero.{u2, 0} R ENNReal _inst_1 instENNRealZero] [_inst_3 : IsScalarTower.{u2, 0, 0} R ENNReal ENNReal (SMulZeroClass.toSMul.{u2, 0} R ENNReal instENNRealZero (SMulWithZero.toSMulZeroClass.{u2, 0} R ENNReal _inst_1 instENNRealZero _inst_2)) (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (SMulZeroClass.toSMul.{u2, 0} R ENNReal instENNRealZero (SMulWithZero.toSMulZeroClass.{u2, 0} R ENNReal _inst_1 instENNRealZero _inst_2))] [_inst_4 : NoZeroSMulDivisors.{u2, 0} R ENNReal _inst_1 instENNRealZero (SMulZeroClass.toSMul.{u2, 0} R ENNReal instENNRealZero (SMulWithZero.toSMulZeroClass.{u2, 0} R ENNReal _inst_1 instENNRealZero _inst_2))] {c : R}, (Ne.{succ u2} R c (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R _inst_1))) -> (Eq.{succ u1} (α -> ENNReal) (HSMul.hSMul.{u2, u1, u1} R (α -> ENNReal) (α -> ENNReal) (instHSMul.{u2, u1} R (α -> ENNReal) (Pi.instSMul.{u1, 0, u2} α R (fun (s : α) => ENNReal) (fun (i : α) => SMulZeroClass.toSMul.{u2, 0} R ENNReal instENNRealZero (SMulWithZero.toSMulZeroClass.{u2, 0} R ENNReal _inst_1 instENNRealZero _inst_2)))) c (MeasureTheory.extend.{u1} α (fun (s : α) => P s) m)) (MeasureTheory.extend.{u1} α (fun (s : α) => P s) (fun (s : α) (h : P s) => HSMul.hSMul.{u2, 0, 0} R ENNReal ENNReal (instHSMul.{u2, 0} R ENNReal (SMulZeroClass.toSMul.{u2, 0} R ENNReal instENNRealZero (SMulWithZero.toSMulZeroClass.{u2, 0} R ENNReal _inst_1 instENNRealZero _inst_2))) c (m s h))))
Case conversion may be inaccurate. Consider using '#align measure_theory.smul_extend MeasureTheory.smul_extendₓ'. -/
theorem smul_extend {R} [Zero R] [SMulWithZero R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [NoZeroSMulDivisors R ℝ≥0∞] {c : R} (hc : c ≠ 0) : c • extend m = extend fun s h => c • m s h :=
  by
  ext1 s
  dsimp [extend]
  by_cases h : P s
  · simp [h]
  · simp [h, ENNReal.smul_top, hc]
#align measure_theory.smul_extend MeasureTheory.smul_extend

#print MeasureTheory.extend_eq /-
theorem extend_eq {s : α} (h : P s) : extend m s = m s h := by simp [extend, h]
#align measure_theory.extend_eq MeasureTheory.extend_eq
-/

/- warning: measure_theory.extend_eq_top -> MeasureTheory.extend_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : α -> Prop} (m : forall (s : α), (P s) -> ENNReal) {s : α}, (Not (P s)) -> (Eq.{1} ENNReal (MeasureTheory.extend.{u1} α (fun (s : α) => P s) m s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} {P : α -> Prop} (m : forall (s : α), (P s) -> ENNReal) {s : α}, (Not (P s)) -> (Eq.{1} ENNReal (MeasureTheory.extend.{u1} α (fun (s : α) => P s) m s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.extend_eq_top MeasureTheory.extend_eq_topₓ'. -/
theorem extend_eq_top {s : α} (h : ¬P s) : extend m s = ∞ := by simp [extend, h]
#align measure_theory.extend_eq_top MeasureTheory.extend_eq_top

/- warning: measure_theory.le_extend -> MeasureTheory.le_extend is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : α -> Prop} (m : forall (s : α), (P s) -> ENNReal) {s : α} (h : P s), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m s h) (MeasureTheory.extend.{u1} α (fun (s : α) => P s) m s)
but is expected to have type
  forall {α : Type.{u1}} {P : α -> Prop} (m : forall (s : α), (P s) -> ENNReal) {s : α} (h : P s), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m s h) (MeasureTheory.extend.{u1} α (fun (s : α) => P s) m s)
Case conversion may be inaccurate. Consider using '#align measure_theory.le_extend MeasureTheory.le_extendₓ'. -/
theorem le_extend {s : α} (h : P s) : m s h ≤ extend m s := by simp only [extend, le_iInf_iff];
  intro ; rfl
#align measure_theory.le_extend MeasureTheory.le_extend

#print MeasureTheory.extend_congr /-
-- TODO: why this is a bad `congr` lemma?
theorem extend_congr {β : Type _} {Pb : β → Prop} {mb : ∀ s : β, Pb s → ℝ≥0∞} {sa : α} {sb : β}
    (hP : P sa ↔ Pb sb) (hm : ∀ (ha : P sa) (hb : Pb sb), m sa ha = mb sb hb) :
    extend m sa = extend mb sb :=
  iInf_congr_Prop hP fun h => hm _ _
#align measure_theory.extend_congr MeasureTheory.extend_congr
-/

/- warning: measure_theory.extend_top -> MeasureTheory.extend_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : α -> Prop}, Eq.{succ u1} (α -> ENNReal) (MeasureTheory.extend.{u1} α (fun (s : α) => P s) (fun (s : α) (h : P s) => Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Top.top.{u1} (α -> ENNReal) (Pi.hasTop.{u1, 0} α (fun (s : α) => ENNReal) (fun (i : α) => CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} {P : α -> Prop}, Eq.{succ u1} (α -> ENNReal) (MeasureTheory.extend.{u1} α (fun (s : α) => P s) (fun (s : α) (h : P s) => Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Top.top.{u1} (α -> ENNReal) (Pi.instTopForAll.{u1, 0} α (fun (s : α) => ENNReal) (fun (i : α) => CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.extend_top MeasureTheory.extend_topₓ'. -/
@[simp]
theorem extend_top {α : Type _} {P : α → Prop} : extend (fun s h => ∞ : ∀ s : α, P s → ℝ≥0∞) = ⊤ :=
  funext fun x => iInf_eq_top.mpr fun i => rfl
#align measure_theory.extend_top MeasureTheory.extend_top

end Extend

section ExtendSet

variable {α : Type _} {P : Set α → Prop}

variable {m : ∀ s : Set α, P s → ℝ≥0∞}

variable (P0 : P ∅) (m0 : m ∅ P0 = 0)

variable (PU : ∀ ⦃f : ℕ → Set α⦄ (hm : ∀ i, P (f i)), P (⋃ i, f i))

variable
  (mU :
    ∀ ⦃f : ℕ → Set α⦄ (hm : ∀ i, P (f i)),
      Pairwise (Disjoint on f) → m (⋃ i, f i) (PU hm) = ∑' i, m (f i) (hm i))

variable (msU : ∀ ⦃f : ℕ → Set α⦄ (hm : ∀ i, P (f i)), m (⋃ i, f i) (PU hm) ≤ ∑' i, m (f i) (hm i))

variable (m_mono : ∀ ⦃s₁ s₂ : Set α⦄ (hs₁ : P s₁) (hs₂ : P s₂), s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)

/- warning: measure_theory.extend_empty -> MeasureTheory.extend_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} (P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} (P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.extend_empty MeasureTheory.extend_emptyₓ'. -/
theorem extend_empty : extend m ∅ = 0 :=
  (extend_eq _ P0).trans m0
#align measure_theory.extend_empty MeasureTheory.extend_empty

/- warning: measure_theory.extend_Union_nat -> MeasureTheory.extend_iUnion_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))) {f : Nat -> (Set.{u1} α)} (hm : forall (i : Nat), P (f i)), (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i)))) -> (Eq.{1} ENNReal (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i))) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (f i))))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))) {f : Nat -> (Set.{u1} α)} (hm : forall (i : Nat), P (f i)), (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i)))) -> (Eq.{1} ENNReal (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i))) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (f i))))
Case conversion may be inaccurate. Consider using '#align measure_theory.extend_Union_nat MeasureTheory.extend_iUnion_natₓ'. -/
theorem extend_iUnion_nat {f : ℕ → Set α} (hm : ∀ i, P (f i))
    (mU : m (⋃ i, f i) (PU hm) = ∑' i, m (f i) (hm i)) :
    extend m (⋃ i, f i) = ∑' i, extend m (f i) :=
  (extend_eq _ _).trans <| mU.trans <| by congr with i; rw [extend_eq]
#align measure_theory.extend_Union_nat MeasureTheory.extend_iUnion_nat

section Subadditive

include PU msU

/- warning: measure_theory.extend_Union_le_tsum_nat' -> MeasureTheory.extend_iUnion_le_tsum_nat' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall (s : Nat -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i))) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (s i))))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall (s : Nat -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i))) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (s i))))
Case conversion may be inaccurate. Consider using '#align measure_theory.extend_Union_le_tsum_nat' MeasureTheory.extend_iUnion_le_tsum_nat'ₓ'. -/
theorem extend_iUnion_le_tsum_nat' (s : ℕ → Set α) : extend m (⋃ i, s i) ≤ ∑' i, extend m (s i) :=
  by
  by_cases h : ∀ i, P (s i)
  · rw [extend_eq _ (PU h), congr_arg tsum _]
    · apply msU h
    funext i; apply extend_eq _ (h i)
  · cases' not_forall.1 h with i hi
    exact le_trans (le_iInf fun h => hi.elim h) (ENNReal.le_tsum i)
#align measure_theory.extend_Union_le_tsum_nat' MeasureTheory.extend_iUnion_le_tsum_nat'

end Subadditive

section Mono

include m_mono

/- warning: measure_theory.extend_mono' -> MeasureTheory.extend_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal}, (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}}, (P s₁) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m s₁) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m s₂)))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal}, (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}}, (P s₁) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m s₁) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m s₂)))
Case conversion may be inaccurate. Consider using '#align measure_theory.extend_mono' MeasureTheory.extend_mono'ₓ'. -/
theorem extend_mono' ⦃s₁ s₂ : Set α⦄ (h₁ : P s₁) (hs : s₁ ⊆ s₂) : extend m s₁ ≤ extend m s₂ := by
  refine' le_iInf _; intro h₂; rw [extend_eq m h₁]; exact m_mono h₁ h₂ hs
#align measure_theory.extend_mono' MeasureTheory.extend_mono'

end Mono

section Unions

include P0 m0 PU mU

/- warning: measure_theory.extend_Union -> MeasureTheory.extend_iUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} (P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (forall (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i))))) -> (forall {β : Type.{u2}} [_inst_1 : Countable.{succ u2} β] {f : β -> (Set.{u1} α)}, (Pairwise.{u2} β (Function.onFun.{succ u2, succ u1, 1} β (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (forall (i : β), P (f i)) -> (Eq.{1} ENNReal (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (Set.iUnion.{u1, succ u2} α β (fun (i : β) => f i))) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (i : β) => MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (f i))))))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} (P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (forall (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i))))) -> (forall {β : Type.{u2}} [_inst_1 : Countable.{succ u2} β] {f : β -> (Set.{u1} α)}, (Pairwise.{u2} β (Function.onFun.{succ u2, succ u1, 1} β (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f)) -> (forall (i : β), P (f i)) -> (Eq.{1} ENNReal (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (Set.iUnion.{u1, succ u2} α β (fun (i : β) => f i))) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (i : β) => MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (f i))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.extend_Union MeasureTheory.extend_iUnionₓ'. -/
theorem extend_iUnion {β} [Countable β] {f : β → Set α} (hd : Pairwise (Disjoint on f))
    (hm : ∀ i, P (f i)) : extend m (⋃ i, f i) = ∑' i, extend m (f i) :=
  by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂, ← tsum_iUnion_decode₂]
  ·
    exact
      extend_Union_nat PU (fun n => Encodable.iUnion_decode₂_cases P0 hm)
        (mU _ (Encodable.iUnion_decode₂_disjoint_on hd))
  · exact extend_empty P0 m0
#align measure_theory.extend_Union MeasureTheory.extend_iUnion

/- warning: measure_theory.extend_union -> MeasureTheory.extend_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} (P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (forall (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i))))) -> (forall {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s₁ s₂) -> (P s₁) -> (P s₂) -> (Eq.{1} ENNReal (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m s₁) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m s₂)))))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} (P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (forall (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i))))) -> (forall {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s₁ s₂) -> (P s₁) -> (P s₂) -> (Eq.{1} ENNReal (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m s₁) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m s₂)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.extend_union MeasureTheory.extend_unionₓ'. -/
theorem extend_union {s₁ s₂ : Set α} (hd : Disjoint s₁ s₂) (h₁ : P s₁) (h₂ : P s₂) :
    extend m (s₁ ∪ s₂) = extend m s₁ + extend m s₂ :=
  by
  rw [union_eq_Union,
    extend_Union P0 m0 PU mU (pairwise_disjoint_on_bool.2 hd) (Bool.forall_bool.2 ⟨h₂, h₁⟩),
    tsum_fintype]
  simp
#align measure_theory.extend_union MeasureTheory.extend_union

end Unions

variable (m)

/- warning: measure_theory.induced_outer_measure -> MeasureTheory.inducedOuterMeasure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} (m : forall (s : Set.{u1} α), (P s) -> ENNReal) (P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (MeasureTheory.OuterMeasure.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} (m : forall (s : Set.{u1} α), (P s) -> ENNReal) (P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (MeasureTheory.OuterMeasure.{u1} α)
Case conversion may be inaccurate. Consider using '#align measure_theory.induced_outer_measure MeasureTheory.inducedOuterMeasureₓ'. -/
/-- Given an arbitrary function on a subset of sets, we can define the outer measure corresponding
  to it (this is the unique maximal outer measure that is at most `m` on the domain of `m`). -/
def inducedOuterMeasure : OuterMeasure α :=
  OuterMeasure.ofFunction (extend m) (extend_empty P0 m0)
#align measure_theory.induced_outer_measure MeasureTheory.inducedOuterMeasure

variable {m P0 m0}

/- warning: measure_theory.le_induced_outer_measure -> MeasureTheory.le_inducedOuterMeasure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))} {μ : MeasureTheory.OuterMeasure.{u1} α}, Iff (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toHasLe.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) μ (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0)) (forall (s : Set.{u1} α) (hs : P s), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) μ s) (m s hs))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))} {μ : MeasureTheory.OuterMeasure.{u1} α}, Iff (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toLE.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) μ (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0)) (forall (s : Set.{u1} α) (hs : P s), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α μ s) (m s hs))
Case conversion may be inaccurate. Consider using '#align measure_theory.le_induced_outer_measure MeasureTheory.le_inducedOuterMeasureₓ'. -/
theorem le_inducedOuterMeasure {μ : OuterMeasure α} :
    μ ≤ inducedOuterMeasure m P0 m0 ↔ ∀ (s) (hs : P s), μ s ≤ m s hs :=
  le_ofFunction.trans <| forall_congr' fun s => le_iInf_iff
#align measure_theory.le_induced_outer_measure MeasureTheory.le_inducedOuterMeasure

/- warning: measure_theory.induced_outer_measure_union_of_false_of_nonempty_inter -> MeasureTheory.inducedOuterMeasure_union_of_false_of_nonempty_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))} {s : Set.{u1} α} {t : Set.{u1} α}, (forall (u : Set.{u1} α), (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u)) -> (Not (P u))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) s) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) t)))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))} {s : Set.{u1} α} {t : Set.{u1} α}, (forall (u : Set.{u1} α), (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u)) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u)) -> (Not (P u))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) t)))
Case conversion may be inaccurate. Consider using '#align measure_theory.induced_outer_measure_union_of_false_of_nonempty_inter MeasureTheory.inducedOuterMeasure_union_of_false_of_nonempty_interₓ'. -/
/-- If `P u` is `false` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = induced_outer_measure m P0 m0`.

E.g., if `α` is an (e)metric space and `P u = diam u < r`, then this lemma implies that
`μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s` and `y ∈ t`. -/
theorem inducedOuterMeasure_union_of_false_of_nonempty_inter {s t : Set α}
    (h : ∀ u, (s ∩ u).Nonempty → (t ∩ u).Nonempty → ¬P u) :
    inducedOuterMeasure m P0 m0 (s ∪ t) =
      inducedOuterMeasure m P0 m0 s + inducedOuterMeasure m P0 m0 t :=
  ofFunction_union_of_top_of_nonempty_inter fun u hsu htu => @iInf_of_empty _ _ _ ⟨h u hsu htu⟩ _
#align measure_theory.induced_outer_measure_union_of_false_of_nonempty_inter MeasureTheory.inducedOuterMeasure_union_of_false_of_nonempty_inter

include msU m_mono

/- warning: measure_theory.induced_outer_measure_eq_extend' -> MeasureTheory.inducedOuterMeasure_eq_extend' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall {s : Set.{u1} α}, (P s) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) s) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m s)))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall {s : Set.{u1} α}, (P s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) s) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => P s) m s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.induced_outer_measure_eq_extend' MeasureTheory.inducedOuterMeasure_eq_extend'ₓ'. -/
theorem inducedOuterMeasure_eq_extend' {s : Set α} (hs : P s) :
    inducedOuterMeasure m P0 m0 s = extend m s :=
  ofFunction_eq s (fun t => extend_mono' m_mono hs) (extend_iUnion_le_tsum_nat' PU msU)
#align measure_theory.induced_outer_measure_eq_extend' MeasureTheory.inducedOuterMeasure_eq_extend'

/- warning: measure_theory.induced_outer_measure_eq' -> MeasureTheory.inducedOuterMeasure_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall {s : Set.{u1} α} (hs : P s), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) s) (m s hs))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall {s : Set.{u1} α} (hs : P s), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) s) (m s hs))
Case conversion may be inaccurate. Consider using '#align measure_theory.induced_outer_measure_eq' MeasureTheory.inducedOuterMeasure_eq'ₓ'. -/
theorem inducedOuterMeasure_eq' {s : Set α} (hs : P s) : inducedOuterMeasure m P0 m0 s = m s hs :=
  (inducedOuterMeasure_eq_extend' PU msU m_mono hs).trans <| extend_eq _ _
#align measure_theory.induced_outer_measure_eq' MeasureTheory.inducedOuterMeasure_eq'

/- warning: measure_theory.induced_outer_measure_eq_infi -> MeasureTheory.inducedOuterMeasure_eq_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Set.{u1} α) (fun (t : Set.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (P t) (fun (ht : P t) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (fun (h : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) => m t ht)))))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.{u1} α) (fun (t : Set.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (P t) (fun (ht : P t) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (fun (h : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) => m t ht)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.induced_outer_measure_eq_infi MeasureTheory.inducedOuterMeasure_eq_iInfₓ'. -/
theorem inducedOuterMeasure_eq_iInf (s : Set α) :
    inducedOuterMeasure m P0 m0 s = ⨅ (t : Set α) (ht : P t) (h : s ⊆ t), m t ht :=
  by
  apply le_antisymm
  · simp only [le_iInf_iff]; intro t ht hs
    refine' le_trans (mono' _ hs) _
    exact le_of_eq (induced_outer_measure_eq' _ msU m_mono _)
  · refine' le_iInf _; intro f; refine' le_iInf _; intro hf
    refine' le_trans _ (extend_Union_le_tsum_nat' _ msU _)
    refine' le_iInf _; intro h2f
    refine' iInf_le_of_le _ (iInf_le_of_le h2f <| iInf_le _ hf)
#align measure_theory.induced_outer_measure_eq_infi MeasureTheory.inducedOuterMeasure_eq_iInf

/- warning: measure_theory.induced_outer_measure_preimage -> MeasureTheory.inducedOuterMeasure_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall (f : Equiv.{succ u1, succ u1} α α) (Pm : forall (s : Set.{u1} α), Iff (P (Set.preimage.{u1, u1} α α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) f) s)) (P s)), (forall (s : Set.{u1} α) (hs : P s), Eq.{1} ENNReal (m (Set.preimage.{u1, u1} α α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) f) s) (Iff.mpr (P (Set.preimage.{u1, u1} α α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) f) s)) (P s) (Pm s) hs)) (m s hs)) -> (forall {A : Set.{u1} α}, Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) (Set.preimage.{u1, u1} α α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) f) A)) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) A)))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall (f : Equiv.{succ u1, succ u1} α α) (Pm : forall (s : Set.{u1} α), Iff (P (Set.preimage.{u1, u1} α α (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α α) f) s)) (P s)), (forall (s : Set.{u1} α) (hs : P s), Eq.{1} ENNReal (m (Set.preimage.{u1, u1} α α (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α α) f) s) (Iff.mpr (P (Set.preimage.{u1, u1} α α (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α α) f) s)) (P s) (Pm s) hs)) (m s hs)) -> (forall {A : Set.{u1} α}, Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) (Set.preimage.{u1, u1} α α (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α α) f) A)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) A)))
Case conversion may be inaccurate. Consider using '#align measure_theory.induced_outer_measure_preimage MeasureTheory.inducedOuterMeasure_preimageₓ'. -/
theorem inducedOuterMeasure_preimage (f : α ≃ α) (Pm : ∀ s : Set α, P (f ⁻¹' s) ↔ P s)
    (mm : ∀ (s : Set α) (hs : P s), m (f ⁻¹' s) ((Pm _).mpr hs) = m s hs) {A : Set α} :
    inducedOuterMeasure m P0 m0 (f ⁻¹' A) = inducedOuterMeasure m P0 m0 A :=
  by
  simp only [induced_outer_measure_eq_infi _ msU m_mono]; symm
  refine' f.injective.preimage_surjective.infi_congr (preimage f) fun s => _
  refine' iInf_congr_Prop (Pm s) _; intro hs
  refine' iInf_congr_Prop f.surjective.preimage_subset_preimage_iff _
  intro h2s; exact mm s hs
#align measure_theory.induced_outer_measure_preimage MeasureTheory.inducedOuterMeasure_preimage

/- warning: measure_theory.induced_outer_measure_exists_set -> MeasureTheory.inducedOuterMeasure_exists_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall {s : Set.{u1} α}, (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (P t) (fun (ht : P t) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) t) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) s) ε)))))))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall {s : Set.{u1} α}, (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (P t) (fun (ht : P t) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) t) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) s) ε)))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.induced_outer_measure_exists_set MeasureTheory.inducedOuterMeasure_exists_setₓ'. -/
theorem inducedOuterMeasure_exists_set {s : Set α} (hs : inducedOuterMeasure m P0 m0 s ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (t : Set α)(ht : P t),
      s ⊆ t ∧ inducedOuterMeasure m P0 m0 t ≤ inducedOuterMeasure m P0 m0 s + ε :=
  by
  have := ENNReal.lt_add_right hs hε
  conv at this =>
    lhs
    rw [induced_outer_measure_eq_infi _ msU m_mono]
  simp only [iInf_lt_iff] at this
  rcases this with ⟨t, h1t, h2t, h3t⟩
  exact
    ⟨t, h1t, h2t, le_trans (le_of_eq <| induced_outer_measure_eq' _ msU m_mono h1t) (le_of_lt h3t)⟩
#align measure_theory.induced_outer_measure_exists_set MeasureTheory.inducedOuterMeasure_exists_set

/- warning: measure_theory.induced_outer_measure_caratheodory -> MeasureTheory.inducedOuterMeasure_caratheodory is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall (s : Set.{u1} α), Iff (MeasurableSet.{u1} α (MeasureTheory.OuterMeasure.caratheodory.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0)) s) (forall (t : Set.{u1} α), (P t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) t))))
but is expected to have type
  forall {α : Type.{u1}} {P : (Set.{u1} α) -> Prop} {m : forall (s : Set.{u1} α), (P s) -> ENNReal} {P0 : P (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) P0) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))} (PU : forall {{f : Nat -> (Set.{u1} α)}}, (forall (i : Nat), P (f i)) -> (P (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), P (f i)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (PU (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i)))) -> (forall {{s₁ : Set.{u1} α}} {{s₂ : Set.{u1} α}} (hs₁ : P s₁) (hs₂ : P s₂), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (m s₁ hs₁) (m s₂ hs₂))) -> (forall (s : Set.{u1} α), Iff (MeasurableSet.{u1} α (MeasureTheory.OuterMeasure.caratheodory.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0)) s) (forall (t : Set.{u1} α), (P t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => P s) m P0 m0) t))))
Case conversion may be inaccurate. Consider using '#align measure_theory.induced_outer_measure_caratheodory MeasureTheory.inducedOuterMeasure_caratheodoryₓ'. -/
/-- To test whether `s` is Carathéodory-measurable we only need to check the sets `t` for which
  `P t` holds. See `of_function_caratheodory` for another way to show the Carathéodory-measurability
  of `s`.
-/
theorem inducedOuterMeasure_caratheodory (s : Set α) :
    measurable_set[(inducedOuterMeasure m P0 m0).caratheodory] s ↔
      ∀ t : Set α,
        P t →
          inducedOuterMeasure m P0 m0 (t ∩ s) + inducedOuterMeasure m P0 m0 (t \ s) ≤
            inducedOuterMeasure m P0 m0 t :=
  by
  rw [is_caratheodory_iff_le]
  constructor
  · intro h t ht; exact h t
  · intro h u; conv_rhs => rw [induced_outer_measure_eq_infi _ msU m_mono]
    refine' le_iInf _; intro t; refine' le_iInf _; intro ht; refine' le_iInf _; intro h2t
    refine' le_trans _ (le_trans (h t ht) <| le_of_eq <| induced_outer_measure_eq' _ msU m_mono ht)
    refine'
      add_le_add (mono' _ <| Set.inter_subset_inter_left _ h2t)
        (mono' _ <| diff_subset_diff_left h2t)
#align measure_theory.induced_outer_measure_caratheodory MeasureTheory.inducedOuterMeasure_caratheodory

end ExtendSet

/-! If `P` is `measurable_set` for some measurable space, then we can remove some hypotheses of the
  above lemmas. -/


section MeasurableSpace

variable {α : Type _} [MeasurableSpace α]

variable {m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞}

variable (m0 : m ∅ MeasurableSet.empty = 0)

variable
  (mU :
    ∀ ⦃f : ℕ → Set α⦄ (hm : ∀ i, MeasurableSet (f i)),
      Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion hm) = ∑' i, m (f i) (hm i))

include m0 mU

/- warning: measure_theory.extend_mono -> MeasureTheory.extend_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m : forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> ENNReal}, (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) (MeasurableSet.empty.{u1} α _inst_1)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), MeasurableSet.{u1} α _inst_1 (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (MeasurableSet.iUnion.{u1, 1} α Nat _inst_1 Nat.countable (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i))))) -> (forall {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s₁) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m s₁) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m s₂)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m : forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> ENNReal}, (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) (MeasurableSet.empty.{u1} α _inst_1)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), MeasurableSet.{u1} α _inst_1 (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (MeasurableSet.iUnion.{u1, 1} α Nat _inst_1 instCountableNat (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i))))) -> (forall {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s₁) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m s₁) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m s₂)))
Case conversion may be inaccurate. Consider using '#align measure_theory.extend_mono MeasureTheory.extend_monoₓ'. -/
theorem extend_mono {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (hs : s₁ ⊆ s₂) :
    extend m s₁ ≤ extend m s₂ := by
  refine' le_iInf _; intro h₂
  have :=
    extend_union MeasurableSet.empty m0 MeasurableSet.iUnion mU disjoint_sdiff_self_right h₁
      (h₂.diff h₁)
  rw [union_diff_cancel hs] at this
  rw [← extend_eq m]
  exact le_iff_exists_add.2 ⟨_, this⟩
#align measure_theory.extend_mono MeasureTheory.extend_mono

/- warning: measure_theory.extend_Union_le_tsum_nat -> MeasureTheory.extend_iUnion_le_tsum_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m : forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> ENNReal}, (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) (MeasurableSet.empty.{u1} α _inst_1)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), MeasurableSet.{u1} α _inst_1 (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (MeasurableSet.iUnion.{u1, 1} α Nat _inst_1 Nat.countable (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i))))) -> (forall (s : Nat -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i))) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m (s i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m : forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> ENNReal}, (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) (MeasurableSet.empty.{u1} α _inst_1)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), MeasurableSet.{u1} α _inst_1 (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (MeasurableSet.iUnion.{u1, 1} α Nat _inst_1 instCountableNat (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i))))) -> (forall (s : Nat -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i))) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m (s i))))
Case conversion may be inaccurate. Consider using '#align measure_theory.extend_Union_le_tsum_nat MeasureTheory.extend_iUnion_le_tsum_natₓ'. -/
theorem extend_iUnion_le_tsum_nat : ∀ s : ℕ → Set α, extend m (⋃ i, s i) ≤ ∑' i, extend m (s i) :=
  by
  refine' extend_Union_le_tsum_nat' MeasurableSet.iUnion _; intro f h
  simp (config := { singlePass := true }) [Union_disjointed.symm]
  rw [mU (MeasurableSet.disjointed h) (disjoint_disjointed _)]
  refine' ENNReal.tsum_le_tsum fun i => _
  rw [← extend_eq m, ← extend_eq m]
  exact extend_mono m0 mU (MeasurableSet.disjointed h _) (disjointed_le f _)
#align measure_theory.extend_Union_le_tsum_nat MeasureTheory.extend_iUnion_le_tsum_nat

/- warning: measure_theory.induced_outer_measure_eq_extend -> MeasureTheory.inducedOuterMeasure_eq_extend is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m : forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> ENNReal} (m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) (MeasurableSet.empty.{u1} α _inst_1)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), MeasurableSet.{u1} α _inst_1 (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (MeasurableSet.iUnion.{u1, 1} α Nat _inst_1 Nat.countable (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i))))) -> (forall {s : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m (MeasurableSet.empty.{u1} α _inst_1) m0) s) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m : forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> ENNReal} (m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) (MeasurableSet.empty.{u1} α _inst_1)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), MeasurableSet.{u1} α _inst_1 (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (MeasurableSet.iUnion.{u1, 1} α Nat _inst_1 instCountableNat (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i))))) -> (forall {s : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m (MeasurableSet.empty.{u1} α _inst_1) m0) s) (MeasureTheory.extend.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.induced_outer_measure_eq_extend MeasureTheory.inducedOuterMeasure_eq_extendₓ'. -/
theorem inducedOuterMeasure_eq_extend {s : Set α} (hs : MeasurableSet s) :
    inducedOuterMeasure m MeasurableSet.empty m0 s = extend m s :=
  ofFunction_eq s (fun t => extend_mono m0 mU hs) (extend_iUnion_le_tsum_nat m0 mU)
#align measure_theory.induced_outer_measure_eq_extend MeasureTheory.inducedOuterMeasure_eq_extend

/- warning: measure_theory.induced_outer_measure_eq -> MeasureTheory.inducedOuterMeasure_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m : forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> ENNReal} (m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) (MeasurableSet.empty.{u1} α _inst_1)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), MeasurableSet.{u1} α _inst_1 (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (MeasurableSet.iUnion.{u1, 1} α Nat _inst_1 Nat.countable (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (hm i))))) -> (forall {s : Set.{u1} α} (hs : MeasurableSet.{u1} α _inst_1 s), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m (MeasurableSet.empty.{u1} α _inst_1) m0) s) (m s hs))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m : forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> ENNReal} (m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) (MeasurableSet.empty.{u1} α _inst_1)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))), (forall {{f : Nat -> (Set.{u1} α)}} (hm : forall (i : Nat), MeasurableSet.{u1} α _inst_1 (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (MeasurableSet.iUnion.{u1, 1} α Nat _inst_1 instCountableNat (fun (i : Nat) => f i) hm)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (hm i))))) -> (forall {s : Set.{u1} α} (hs : MeasurableSet.{u1} α _inst_1 s), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.inducedOuterMeasure.{u1} α (fun (s : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 s) m (MeasurableSet.empty.{u1} α _inst_1) m0) s) (m s hs))
Case conversion may be inaccurate. Consider using '#align measure_theory.induced_outer_measure_eq MeasureTheory.inducedOuterMeasure_eqₓ'. -/
theorem inducedOuterMeasure_eq {s : Set α} (hs : MeasurableSet s) :
    inducedOuterMeasure m MeasurableSet.empty m0 s = m s hs :=
  (inducedOuterMeasure_eq_extend m0 mU hs).trans <| extend_eq _ _
#align measure_theory.induced_outer_measure_eq MeasureTheory.inducedOuterMeasure_eq

end MeasurableSpace

namespace OuterMeasure

variable {α : Type _} [MeasurableSpace α] (m : OuterMeasure α)

#print MeasureTheory.OuterMeasure.trim /-
/-- Given an outer measure `m` we can forget its value on non-measurable sets, and then consider
  `m.trim`, the unique maximal outer measure less than that function. -/
def trim : OuterMeasure α :=
  inducedOuterMeasure (fun s _ => m s) MeasurableSet.empty m.Empty
#align measure_theory.outer_measure.trim MeasureTheory.OuterMeasure.trim
-/

/- warning: measure_theory.outer_measure.le_trim -> MeasureTheory.OuterMeasure.le_trim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (m : MeasureTheory.OuterMeasure.{u1} α), LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toHasLe.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) m (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (m : MeasureTheory.OuterMeasure.{u1} α), LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toLE.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) m (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m)
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.le_trim MeasureTheory.OuterMeasure.le_trimₓ'. -/
theorem le_trim : m ≤ m.trim :=
  le_ofFunction.mpr fun s => le_iInf fun _ => le_rfl
#align measure_theory.outer_measure.le_trim MeasureTheory.OuterMeasure.le_trim

#print MeasureTheory.OuterMeasure.trim_eq /-
theorem trim_eq {s : Set α} (hs : MeasurableSet s) : m.trim s = m s :=
  inducedOuterMeasure_eq' MeasurableSet.iUnion (fun f hf => m.iUnion_nat f)
    (fun _ _ _ _ h => m.mono h) hs
#align measure_theory.outer_measure.trim_eq MeasureTheory.OuterMeasure.trim_eq
-/

#print MeasureTheory.OuterMeasure.trim_congr /-
theorem trim_congr {m₁ m₂ : OuterMeasure α} (H : ∀ {s : Set α}, MeasurableSet s → m₁ s = m₂ s) :
    m₁.trim = m₂.trim := by unfold trim; congr ; funext s hs; exact H hs
#align measure_theory.outer_measure.trim_congr MeasureTheory.OuterMeasure.trim_congr
-/

#print MeasureTheory.OuterMeasure.trim_mono /-
@[mono]
theorem trim_mono : Monotone (trim : OuterMeasure α → OuterMeasure α) := fun m₁ m₂ H s =>
  iInf₂_mono fun f hs => ENNReal.tsum_le_tsum fun b => iInf_mono fun hf => H _
#align measure_theory.outer_measure.trim_mono MeasureTheory.OuterMeasure.trim_mono
-/

/- warning: measure_theory.outer_measure.le_trim_iff -> MeasureTheory.OuterMeasure.le_trim_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m₁ : MeasureTheory.OuterMeasure.{u1} α} {m₂ : MeasureTheory.OuterMeasure.{u1} α}, Iff (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toHasLe.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) m₁ (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m₂)) (forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m₁ s) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m₂ s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m₁ : MeasureTheory.OuterMeasure.{u1} α} {m₂ : MeasureTheory.OuterMeasure.{u1} α}, Iff (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toLE.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) m₁ (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m₂)) (forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m₁ s) (MeasureTheory.OuterMeasure.measureOf.{u1} α m₂ s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.le_trim_iff MeasureTheory.OuterMeasure.le_trim_iffₓ'. -/
theorem le_trim_iff {m₁ m₂ : OuterMeasure α} : m₁ ≤ m₂.trim ↔ ∀ s, MeasurableSet s → m₁ s ≤ m₂ s :=
  le_ofFunction.trans <| forall_congr' fun s => le_iInf_iff
#align measure_theory.outer_measure.le_trim_iff MeasureTheory.OuterMeasure.le_trim_iff

/- warning: measure_theory.outer_measure.trim_le_trim_iff -> MeasureTheory.OuterMeasure.trim_le_trim_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m₁ : MeasureTheory.OuterMeasure.{u1} α} {m₂ : MeasureTheory.OuterMeasure.{u1} α}, Iff (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toHasLe.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m₁) (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m₂)) (forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m₁ s) (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m₂ s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m₁ : MeasureTheory.OuterMeasure.{u1} α} {m₂ : MeasureTheory.OuterMeasure.{u1} α}, Iff (LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toLE.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m₁) (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m₂)) (forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α m₁ s) (MeasureTheory.OuterMeasure.measureOf.{u1} α m₂ s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.trim_le_trim_iff MeasureTheory.OuterMeasure.trim_le_trim_iffₓ'. -/
theorem trim_le_trim_iff {m₁ m₂ : OuterMeasure α} :
    m₁.trim ≤ m₂.trim ↔ ∀ s, MeasurableSet s → m₁ s ≤ m₂ s :=
  le_trim_iff.trans <| forall₂_congr fun s hs => by rw [trim_eq _ hs]
#align measure_theory.outer_measure.trim_le_trim_iff MeasureTheory.OuterMeasure.trim_le_trim_iff

#print MeasureTheory.OuterMeasure.trim_eq_trim_iff /-
theorem trim_eq_trim_iff {m₁ m₂ : OuterMeasure α} :
    m₁.trim = m₂.trim ↔ ∀ s, MeasurableSet s → m₁ s = m₂ s := by
  simp only [le_antisymm_iff, trim_le_trim_iff, forall_and]
#align measure_theory.outer_measure.trim_eq_trim_iff MeasureTheory.OuterMeasure.trim_eq_trim_iff
-/

/- warning: measure_theory.outer_measure.trim_eq_infi -> MeasureTheory.OuterMeasure.trim_eq_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (m : MeasureTheory.OuterMeasure.{u1} α) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Set.{u1} α) (fun (t : Set.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (fun (st : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (MeasurableSet.{u1} α _inst_1 t) (fun (ht : MeasurableSet.{u1} α _inst_1 t) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m t))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (m : MeasureTheory.OuterMeasure.{u1} α) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.{u1} α) (fun (t : Set.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (fun (st : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasurableSet.{u1} α _inst_1 t) (fun (ht : MeasurableSet.{u1} α _inst_1 t) => MeasureTheory.OuterMeasure.measureOf.{u1} α m t))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.trim_eq_infi MeasureTheory.OuterMeasure.trim_eq_iInfₓ'. -/
theorem trim_eq_iInf (s : Set α) : m.trim s = ⨅ (t) (st : s ⊆ t) (ht : MeasurableSet t), m t := by
  simp (config := { singlePass := true }) only [iInf_comm];
  exact
    induced_outer_measure_eq_infi MeasurableSet.iUnion (fun f _ => m.Union_nat f)
      (fun _ _ _ _ h => m.mono h) s
#align measure_theory.outer_measure.trim_eq_infi MeasureTheory.OuterMeasure.trim_eq_iInf

/- warning: measure_theory.outer_measure.trim_eq_infi' -> MeasureTheory.OuterMeasure.trim_eq_iInf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (m : MeasureTheory.OuterMeasure.{u1} α) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) (fun (t : Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) => coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t)))))) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (m : MeasureTheory.OuterMeasure.{u1} α) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) (fun (t : Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) => MeasureTheory.OuterMeasure.measureOf.{u1} α m (Subtype.val.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t)) t)))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.trim_eq_infi' MeasureTheory.OuterMeasure.trim_eq_iInf'ₓ'. -/
theorem trim_eq_iInf' (s : Set α) : m.trim s = ⨅ t : { t // s ⊆ t ∧ MeasurableSet t }, m t := by
  simp [iInf_subtype, iInf_and, trim_eq_infi]
#align measure_theory.outer_measure.trim_eq_infi' MeasureTheory.OuterMeasure.trim_eq_iInf'

#print MeasureTheory.OuterMeasure.trim_trim /-
theorem trim_trim (m : OuterMeasure α) : m.trim.trim = m.trim :=
  trim_eq_trim_iff.2 fun s => m.trim_eq
#align measure_theory.outer_measure.trim_trim MeasureTheory.OuterMeasure.trim_trim
-/

#print MeasureTheory.OuterMeasure.trim_top /-
@[simp]
theorem trim_top : (⊤ : OuterMeasure α).trim = ⊤ :=
  eq_top_iff.2 <| le_trim _
#align measure_theory.outer_measure.trim_top MeasureTheory.OuterMeasure.trim_top
-/

#print MeasureTheory.OuterMeasure.trim_zero /-
@[simp]
theorem trim_zero : (0 : OuterMeasure α).trim = 0 :=
  ext fun s =>
    le_antisymm
      (le_trans ((trim 0).mono (subset_univ s)) <| le_of_eq <| trim_eq _ MeasurableSet.univ)
      (zero_le _)
#align measure_theory.outer_measure.trim_zero MeasureTheory.OuterMeasure.trim_zero
-/

/- warning: measure_theory.outer_measure.trim_sum_ge -> MeasureTheory.OuterMeasure.trim_sum_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {ι : Type.{u2}} (m : ι -> (MeasureTheory.OuterMeasure.{u1} α)), LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toHasLe.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) (MeasureTheory.OuterMeasure.sum.{u1, u2} α ι (fun (i : ι) => MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 (m i))) (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 (MeasureTheory.OuterMeasure.sum.{u1, u2} α ι m))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {ι : Type.{u2}} (m : ι -> (MeasureTheory.OuterMeasure.{u1} α)), LE.le.{u1} (MeasureTheory.OuterMeasure.{u1} α) (Preorder.toLE.{u1} (MeasureTheory.OuterMeasure.{u1} α) (PartialOrder.toPreorder.{u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instPartialOrder.{u1} α))) (MeasureTheory.OuterMeasure.sum.{u1, u2} α ι (fun (i : ι) => MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 (m i))) (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 (MeasureTheory.OuterMeasure.sum.{u1, u2} α ι m))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.trim_sum_ge MeasureTheory.OuterMeasure.trim_sum_geₓ'. -/
theorem trim_sum_ge {ι} (m : ι → OuterMeasure α) : (sum fun i => (m i).trim) ≤ (sum m).trim :=
  fun s => by
  simp [trim_eq_infi] <;>
    exact fun t st ht =>
      ENNReal.tsum_le_tsum fun i => iInf_le_of_le t <| iInf_le_of_le st <| iInf_le _ ht
#align measure_theory.outer_measure.trim_sum_ge MeasureTheory.OuterMeasure.trim_sum_ge

#print MeasureTheory.OuterMeasure.exists_measurable_superset_eq_trim /-
theorem exists_measurable_superset_eq_trim (m : OuterMeasure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ m t = m.trim s :=
  by
  simp only [trim_eq_infi]; set ms := ⨅ (t : Set α) (st : s ⊆ t) (ht : MeasurableSet t), m t
  by_cases hs : ms = ∞
  · simp only [hs]
    simp only [iInf_eq_top] at hs
    exact ⟨univ, subset_univ s, MeasurableSet.univ, hs _ (subset_univ s) MeasurableSet.univ⟩
  · have : ∀ r > ms, ∃ t, s ⊆ t ∧ MeasurableSet t ∧ m t < r :=
      by
      intro r hs
      simpa [iInf_lt_iff] using hs
    have : ∀ n : ℕ, ∃ t, s ⊆ t ∧ MeasurableSet t ∧ m t < ms + n⁻¹ :=
      by
      intro n
      refine' this _ (ENNReal.lt_add_right hs _)
      simp
    choose t hsub hm hm'
    refine' ⟨⋂ n, t n, subset_Inter hsub, MeasurableSet.iInter hm, _⟩
    have : tendsto (fun n : ℕ => ms + n⁻¹) at_top (𝓝 (ms + 0)) :=
      tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
    rw [add_zero] at this
    refine' le_antisymm (ge_of_tendsto' this fun n => _) _
    · exact le_trans (m.mono' <| Inter_subset t n) (hm' n).le
    · refine' iInf_le_of_le (⋂ n, t n) _
      refine' iInf_le_of_le (subset_Inter hsub) _
      refine' iInf_le _ (MeasurableSet.iInter hm)
#align measure_theory.outer_measure.exists_measurable_superset_eq_trim MeasureTheory.OuterMeasure.exists_measurable_superset_eq_trim
-/

/- warning: measure_theory.outer_measure.exists_measurable_superset_of_trim_eq_zero -> MeasureTheory.OuterMeasure.exists_measurable_superset_of_trim_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m : MeasureTheory.OuterMeasure.{u1} α} {s : Set.{u1} α}, (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m) s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (And (MeasurableSet.{u1} α _inst_1 t) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) m t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m : MeasureTheory.OuterMeasure.{u1} α} {s : Set.{u1} α}, (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (And (MeasurableSet.{u1} α _inst_1 t) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α m t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.exists_measurable_superset_of_trim_eq_zero MeasureTheory.OuterMeasure.exists_measurable_superset_of_trim_eq_zeroₓ'. -/
theorem exists_measurable_superset_of_trim_eq_zero {m : OuterMeasure α} {s : Set α}
    (h : m.trim s = 0) : ∃ t, s ⊆ t ∧ MeasurableSet t ∧ m t = 0 :=
  by
  rcases exists_measurable_superset_eq_trim m s with ⟨t, hst, ht, hm⟩
  exact ⟨t, hst, ht, h ▸ hm⟩
#align measure_theory.outer_measure.exists_measurable_superset_of_trim_eq_zero MeasureTheory.OuterMeasure.exists_measurable_superset_of_trim_eq_zero

#print MeasureTheory.OuterMeasure.exists_measurable_superset_forall_eq_trim /-
/-- If `μ i` is a countable family of outer measures, then for every set `s` there exists
a measurable set `t ⊇ s` such that `μ i t = (μ i).trim s` for all `i`. -/
theorem exists_measurable_superset_forall_eq_trim {ι} [Countable ι] (μ : ι → OuterMeasure α)
    (s : Set α) : ∃ t, s ⊆ t ∧ MeasurableSet t ∧ ∀ i, μ i t = (μ i).trim s :=
  by
  choose t hst ht hμt using fun i => (μ i).exists_measurable_superset_eq_trim s
  replace hst := subset_Inter hst
  replace ht := MeasurableSet.iInter ht
  refine' ⟨⋂ i, t i, hst, ht, fun i => le_antisymm _ _⟩
  exacts[hμt i ▸ (μ i).mono (Inter_subset _ _), (mono' _ hst).trans_eq ((μ i).trim_eq ht)]
#align measure_theory.outer_measure.exists_measurable_superset_forall_eq_trim MeasureTheory.OuterMeasure.exists_measurable_superset_forall_eq_trim
-/

#print MeasureTheory.OuterMeasure.trim_binop /-
/-- If `m₁ s = op (m₂ s) (m₃ s)` for all `s`, then the same is true for `m₁.trim`, `m₂.trim`,
and `m₃ s`. -/
theorem trim_binop {m₁ m₂ m₃ : OuterMeasure α} {op : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}
    (h : ∀ s, m₁ s = op (m₂ s) (m₃ s)) (s : Set α) : m₁.trim s = op (m₂.trim s) (m₃.trim s) :=
  by
  rcases exists_measurable_superset_forall_eq_trim ![m₁, m₂, m₃] s with ⟨t, hst, ht, htm⟩
  simp only [Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ] at htm
  rw [← htm.1, ← htm.2.1, ← htm.2.2.1, h]
#align measure_theory.outer_measure.trim_binop MeasureTheory.OuterMeasure.trim_binop
-/

#print MeasureTheory.OuterMeasure.trim_op /-
/-- If `m₁ s = op (m₂ s)` for all `s`, then the same is true for `m₁.trim` and `m₂.trim`. -/
theorem trim_op {m₁ m₂ : OuterMeasure α} {op : ℝ≥0∞ → ℝ≥0∞} (h : ∀ s, m₁ s = op (m₂ s))
    (s : Set α) : m₁.trim s = op (m₂.trim s) :=
  @trim_binop α _ m₁ m₂ 0 (fun a b => op a) h s
#align measure_theory.outer_measure.trim_op MeasureTheory.OuterMeasure.trim_op
-/

#print MeasureTheory.OuterMeasure.trim_add /-
/-- `trim` is additive. -/
theorem trim_add (m₁ m₂ : OuterMeasure α) : (m₁ + m₂).trim = m₁.trim + m₂.trim :=
  ext <| trim_binop (add_apply m₁ m₂)
#align measure_theory.outer_measure.trim_add MeasureTheory.OuterMeasure.trim_add
-/

/- warning: measure_theory.outer_measure.trim_smul -> MeasureTheory.OuterMeasure.trim_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {R : Type.{u2}} [_inst_2 : SMul.{u2, 0} R ENNReal] [_inst_3 : IsScalarTower.{u2, 0, 0} R ENNReal ENNReal _inst_2 (Mul.toSMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) _inst_2] (c : R) (m : MeasureTheory.OuterMeasure.{u1} α), Eq.{succ u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 (SMul.smul.{u2, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.hasSmul.{u1, u2} α R _inst_2 _inst_3) c m)) (SMul.smul.{u2, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.hasSmul.{u1, u2} α R _inst_2 _inst_3) c (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {R : Type.{u2}} [_inst_2 : SMul.{u2, 0} R ENNReal] [_inst_3 : IsScalarTower.{u2, 0, 0} R ENNReal ENNReal _inst_2 (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) _inst_2] (c : R) (m : MeasureTheory.OuterMeasure.{u1} α), Eq.{succ u1} (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 (HSMul.hSMul.{u2, u1, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (instHSMul.{u2, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSMul.{u1, u2} α R _inst_2 _inst_3)) c m)) (HSMul.hSMul.{u2, u1, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.{u1} α) (instHSMul.{u2, u1} R (MeasureTheory.OuterMeasure.{u1} α) (MeasureTheory.OuterMeasure.instSMul.{u1, u2} α R _inst_2 _inst_3)) c (MeasureTheory.OuterMeasure.trim.{u1} α _inst_1 m))
Case conversion may be inaccurate. Consider using '#align measure_theory.outer_measure.trim_smul MeasureTheory.OuterMeasure.trim_smulₓ'. -/
/-- `trim` respects scalar multiplication. -/
theorem trim_smul {R : Type _} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R)
    (m : OuterMeasure α) : (c • m).trim = c • m.trim :=
  ext <| trim_op (smul_apply c m)
#align measure_theory.outer_measure.trim_smul MeasureTheory.OuterMeasure.trim_smul

#print MeasureTheory.OuterMeasure.trim_sup /-
/-- `trim` sends the supremum of two outer measures to the supremum of the trimmed measures. -/
theorem trim_sup (m₁ m₂ : OuterMeasure α) : (m₁ ⊔ m₂).trim = m₁.trim ⊔ m₂.trim :=
  ext fun s => (trim_binop (sup_apply m₁ m₂) s).trans (sup_apply _ _ _).symm
#align measure_theory.outer_measure.trim_sup MeasureTheory.OuterMeasure.trim_sup
-/

#print MeasureTheory.OuterMeasure.trim_iSup /-
/-- `trim` sends the supremum of a countable family of outer measures to the supremum
of the trimmed measures. -/
theorem trim_iSup {ι} [Countable ι] (μ : ι → OuterMeasure α) : trim (⨆ i, μ i) = ⨆ i, trim (μ i) :=
  by
  simp_rw [← @iSup_plift_down _ ι]
  ext1 s
  haveI : Countable (Option <| PLift ι) := @Option.countable (PLift ι) _
  obtain ⟨t, hst, ht, hμt⟩ :=
    exists_measurable_superset_forall_eq_trim
      (Option.elim' (⨆ i, μ (PLift.down i)) (μ ∘ PLift.down)) s
  simp only [Option.forall, Option.elim'] at hμt
  simp only [iSup_apply, ← hμt.1, ← hμt.2]
#align measure_theory.outer_measure.trim_supr MeasureTheory.OuterMeasure.trim_iSup
-/

#print MeasureTheory.OuterMeasure.restrict_trim /-
/-- The trimmed property of a measure μ states that `μ.to_outer_measure.trim = μ.to_outer_measure`.
This theorem shows that a restricted trimmed outer measure is a trimmed outer measure. -/
theorem restrict_trim {μ : OuterMeasure α} {s : Set α} (hs : MeasurableSet s) :
    (restrict s μ).trim = restrict s μ.trim :=
  by
  refine' le_antisymm (fun t => _) (le_trim_iff.2 fun t ht => _)
  · rw [restrict_apply]
    rcases μ.exists_measurable_superset_eq_trim (t ∩ s) with ⟨t', htt', ht', hμt'⟩
    rw [← hμt']; rw [inter_subset] at htt'
    refine' (mono' _ htt').trans _
    rw [trim_eq _ (hs.compl.union ht'), restrict_apply, union_inter_distrib_right, compl_inter_self,
      Set.empty_union]
    exact μ.mono' (inter_subset_left _ _)
  · rw [restrict_apply, trim_eq _ (ht.inter hs), restrict_apply]
    exact le_rfl
#align measure_theory.outer_measure.restrict_trim MeasureTheory.OuterMeasure.restrict_trim
-/

end OuterMeasure

end MeasureTheory

