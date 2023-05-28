/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module measure_theory.measure.measure_space_def
! leanprover-community/mathlib commit b5ad141426bb005414324f89719c77c0aa3ec612
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.OuterMeasure
import Mathbin.Order.Filter.CountableInter

/-!
# Measure spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines measure spaces, the almost-everywhere filter and ae_measurable functions.
See `measure_theory.measure_space` for their properties and for extended documentation.

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the sum of the measures of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, an outer measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

## Implementation notes

Given `μ : measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

See the documentation of `measure_theory.measure_space` for ways to construct measures and proving
that two measure are equal.

A `measure_space` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

This file does not import `measure_theory.measurable_space`, but only `measurable_space_def`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space
-/


noncomputable section

open Classical Set

open Filter hiding map

open Function MeasurableSpace

open Classical Topology BigOperators Filter ENNReal NNReal

variable {α β γ δ ι : Type _}

namespace MeasureTheory

#print MeasureTheory.Measure /-
/-- A measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure. -/
structure Measure (α : Type _) [MeasurableSpace α] extends OuterMeasure α where
  m_iUnion ⦃f : ℕ → Set α⦄ :
    (∀ i, MeasurableSet (f i)) →
      Pairwise (Disjoint on f) → measure_of (⋃ i, f i) = ∑' i, measure_of (f i)
  trimmed : to_outer_measure.trim = to_outer_measure
#align measure_theory.measure MeasureTheory.Measure
-/

#print MeasureTheory.Measure.instCoeFun /-
/-- Measure projections for a measure space.

For measurable sets this returns the measure assigned by the `measure_of` field in `measure`.
But we can extend this to _all_ sets, but using the outer measure. This gives us monotonicity and
subadditivity for all sets.
-/
instance Measure.instCoeFun [MeasurableSpace α] : CoeFun (Measure α) fun _ => Set α → ℝ≥0∞ :=
  ⟨fun m => m.toOuterMeasure⟩
#align measure_theory.measure.has_coe_to_fun MeasureTheory.Measure.instCoeFun
-/

section

variable [MeasurableSpace α] {μ μ₁ μ₂ : Measure α} {s s₁ s₂ t : Set α}

namespace Measure

/-! ### General facts about measures -/


/- warning: measure_theory.measure.of_measurable -> MeasureTheory.Measure.ofMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (m : forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> ENNReal), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) (MeasurableSet.empty.{u1} α _inst_1)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (forall {{f : Nat -> (Set.{u1} α)}} (h : forall (i : Nat), MeasurableSet.{u1} α _inst_1 (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (MeasureTheory.Measure.ofMeasurable._proof_1.{u1} α _inst_1 f h)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (h i))))) -> (MeasureTheory.Measure.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (m : forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> ENNReal), (Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) (MeasurableSet.empty.{u1} α _inst_1)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (forall {{f : Nat -> (Set.{u1} α)}} (h : forall (i : Nat), MeasurableSet.{u1} α _inst_1 (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (MeasurableSet.iUnion.{u1, 1} α Nat _inst_1 instCountableNat (fun (i : Nat) => f i) h)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (h i))))) -> (MeasureTheory.Measure.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.of_measurable MeasureTheory.Measure.ofMeasurableₓ'. -/
/-- Obtain a measure by giving a countably additive function that sends `∅` to `0`. -/
def ofMeasurable (m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞) (m0 : m ∅ MeasurableSet.empty = 0)
    (mU :
      ∀ ⦃f : ℕ → Set α⦄ (h : ∀ i, MeasurableSet (f i)),
        Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, m (f i) (h i)) :
    Measure α :=
  {
    inducedOuterMeasure m _
      m0 with
    m_iUnion := fun f hf hd =>
      show inducedOuterMeasure m _ m0 (iUnion f) = ∑' i, inducedOuterMeasure m _ m0 (f i)
        by
        rw [induced_outer_measure_eq m0 mU, mU hf hd]
        congr ; funext n; rw [induced_outer_measure_eq m0 mU]
    trimmed :=
      show (inducedOuterMeasure m _ m0).trim = inducedOuterMeasure m _ m0
        by
        unfold outer_measure.trim
        congr ; funext s hs
        exact induced_outer_measure_eq m0 mU hs }
#align measure_theory.measure.of_measurable MeasureTheory.Measure.ofMeasurable

/- warning: measure_theory.measure.of_measurable_apply -> MeasureTheory.Measure.ofMeasurable_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m : forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> ENNReal} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) (MeasurableSet.empty.{u1} α _inst_1)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))} {mU : forall {{f : Nat -> (Set.{u1} α)}} (h : forall (i : Nat), MeasurableSet.{u1} α _inst_1 (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (MeasurableSet.iUnion.{u1, 1} α Nat _inst_1 Nat.countable (fun (i : Nat) => f i) h)) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (i : Nat) => m (f i) (h i))))} (s : Set.{u1} α) (hs : MeasurableSet.{u1} α _inst_1 s), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (MeasureTheory.Measure.ofMeasurable.{u1} α _inst_1 m m0 mU) s) (m s hs)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {m : forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> ENNReal} {m0 : Eq.{1} ENNReal (m (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) (MeasurableSet.empty.{u1} α _inst_1)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))} {mU : forall {{f : Nat -> (Set.{u1} α)}} (h : forall (i : Nat), MeasurableSet.{u1} α _inst_1 (f i)), (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Set.instLESet.{u1} α) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f)) -> (Eq.{1} ENNReal (m (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => f i)) (MeasurableSet.iUnion.{u1, 1} α Nat _inst_1 instCountableNat (fun (i : Nat) => f i) h)) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (i : Nat) => m (f i) (h i))))} (s : Set.{u1} α) (hs : MeasurableSet.{u1} α _inst_1 s), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (MeasureTheory.Measure.ofMeasurable.{u1} α _inst_1 m m0 mU)) s) (m s hs)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.of_measurable_apply MeasureTheory.Measure.ofMeasurable_applyₓ'. -/
theorem ofMeasurable_apply {m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞}
    {m0 : m ∅ MeasurableSet.empty = 0}
    {mU :
      ∀ ⦃f : ℕ → Set α⦄ (h : ∀ i, MeasurableSet (f i)),
        Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, m (f i) (h i)}
    (s : Set α) (hs : MeasurableSet s) : ofMeasurable m m0 mU s = m s hs :=
  inducedOuterMeasure_eq m0 mU hs
#align measure_theory.measure.of_measurable_apply MeasureTheory.Measure.ofMeasurable_apply

#print MeasureTheory.Measure.toOuterMeasure_injective /-
theorem toOuterMeasure_injective : Injective (toOuterMeasure : Measure α → OuterMeasure α) :=
  fun ⟨m₁, u₁, h₁⟩ ⟨m₂, u₂, h₂⟩ h => by congr ; exact h
#align measure_theory.measure.to_outer_measure_injective MeasureTheory.Measure.toOuterMeasure_injective
-/

#print MeasureTheory.Measure.ext /-
@[ext]
theorem ext (h : ∀ s, MeasurableSet s → μ₁ s = μ₂ s) : μ₁ = μ₂ :=
  toOuterMeasure_injective <| by rw [← trimmed, outer_measure.trim_congr h, trimmed]
#align measure_theory.measure.ext MeasureTheory.Measure.ext
-/

#print MeasureTheory.Measure.ext_iff /-
theorem ext_iff : μ₁ = μ₂ ↔ ∀ s, MeasurableSet s → μ₁ s = μ₂ s :=
  ⟨by rintro rfl s hs; rfl, Measure.ext⟩
#align measure_theory.measure.ext_iff MeasureTheory.Measure.ext_iff
-/

end Measure

/- warning: measure_theory.coe_to_outer_measure clashes with [anonymous] -> [anonymous]
warning: measure_theory.coe_to_outer_measure -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MeasurableSpace.{u_1} α] {μ : MeasureTheory.Measure.{u_1} α _inst_1}, Eq.{max (succ u_1) 1} ((Set.{u_1} α) -> ENNReal) (coeFn.{succ u_1, max (succ u_1) 1} (MeasureTheory.OuterMeasure.{u_1} α) (fun (_x : MeasureTheory.OuterMeasure.{u_1} α) => (Set.{u_1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u_1} α) (MeasureTheory.Measure.toOuterMeasure.{u_1} α _inst_1 μ)) (coeFn.{succ u_1, max (succ u_1) 1} (MeasureTheory.Measure.{u_1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u_1} α _inst_1) => (Set.{u_1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u_1} α _inst_1) μ)
but is expected to have type
  forall {α : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> α -> _inst_1) -> Nat -> (List.{u} α) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align measure_theory.coe_to_outer_measure [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] : ⇑μ.toOuterMeasure = μ :=
  rfl
#align measure_theory.coe_to_outer_measure [anonymous]

/- warning: measure_theory.to_outer_measure_apply clashes with [anonymous] -> [anonymous]
warning: measure_theory.to_outer_measure_apply -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MeasurableSpace.{u_1} α] {μ : MeasureTheory.Measure.{u_1} α _inst_1} (s : Set.{u_1} α), Eq.{1} ENNReal (coeFn.{succ u_1, max (succ u_1) 1} (MeasureTheory.OuterMeasure.{u_1} α) (fun (_x : MeasureTheory.OuterMeasure.{u_1} α) => (Set.{u_1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u_1} α) (MeasureTheory.Measure.toOuterMeasure.{u_1} α _inst_1 μ) s) (coeFn.{succ u_1, max (succ u_1) 1} (MeasureTheory.Measure.{u_1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u_1} α _inst_1) => (Set.{u_1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u_1} α _inst_1) μ s)
but is expected to have type
  forall {α : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> α -> _inst_1) -> Nat -> (List.{u} α) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align measure_theory.to_outer_measure_apply [anonymous]ₓ'. -/
theorem [anonymous] (s : Set α) : μ.toOuterMeasure s = μ s :=
  rfl
#align measure_theory.to_outer_measure_apply [anonymous]

#print MeasureTheory.measure_eq_trim /-
theorem measure_eq_trim (s : Set α) : μ s = μ.toOuterMeasure.trim s := by rw [μ.trimmed] <;> rfl
#align measure_theory.measure_eq_trim MeasureTheory.measure_eq_trim
-/

/- warning: measure_theory.measure_eq_infi -> MeasureTheory.measure_eq_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Set.{u1} α) (fun (t : Set.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (fun (st : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (MeasurableSet.{u1} α _inst_1 t) (fun (ht : MeasurableSet.{u1} α _inst_1 t) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ t))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.{u1} α) (fun (t : Set.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (fun (st : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasurableSet.{u1} α _inst_1 t) (fun (ht : MeasurableSet.{u1} α _inst_1 t) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) t))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_eq_infi MeasureTheory.measure_eq_iInfₓ'. -/
theorem measure_eq_iInf (s : Set α) : μ s = ⨅ (t) (st : s ⊆ t) (ht : MeasurableSet t), μ t := by
  rw [measure_eq_trim, outer_measure.trim_eq_infi] <;> rfl
#align measure_theory.measure_eq_infi MeasureTheory.measure_eq_iInf

/- warning: measure_theory.measure_eq_infi' -> MeasureTheory.measure_eq_iInf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_1) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) (fun (t : Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t)))))) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_1) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) (fun (t : Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t))) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Subtype.val.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (MeasurableSet.{u1} α _inst_1 t)) t)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_eq_infi' MeasureTheory.measure_eq_iInf'ₓ'. -/
/-- A variant of `measure_eq_infi` which has a single `infi`. This is useful when applying a
  lemma next that only works for non-empty infima, in which case you can use
  `nonempty_measurable_superset`. -/
theorem measure_eq_iInf' (μ : Measure α) (s : Set α) :
    μ s = ⨅ t : { t // s ⊆ t ∧ MeasurableSet t }, μ t := by
  simp_rw [iInf_subtype, iInf_and, Subtype.coe_mk, ← measure_eq_infi]
#align measure_theory.measure_eq_infi' MeasureTheory.measure_eq_iInf'

#print MeasureTheory.measure_eq_inducedOuterMeasure /-
theorem measure_eq_inducedOuterMeasure :
    μ s = inducedOuterMeasure (fun s _ => μ s) MeasurableSet.empty μ.Empty s :=
  measure_eq_trim _
#align measure_theory.measure_eq_induced_outer_measure MeasureTheory.measure_eq_inducedOuterMeasure
-/

#print MeasureTheory.toOuterMeasure_eq_inducedOuterMeasure /-
theorem toOuterMeasure_eq_inducedOuterMeasure :
    μ.toOuterMeasure = inducedOuterMeasure (fun s _ => μ s) MeasurableSet.empty μ.Empty :=
  μ.trimmed.symm
#align measure_theory.to_outer_measure_eq_induced_outer_measure MeasureTheory.toOuterMeasure_eq_inducedOuterMeasure
-/

#print MeasureTheory.measure_eq_extend /-
theorem measure_eq_extend (hs : MeasurableSet s) :
    μ s = extend (fun t (ht : MeasurableSet t) => μ t) s :=
  (extend_eq _ hs).symm
#align measure_theory.measure_eq_extend MeasureTheory.measure_eq_extend
-/

/- warning: measure_theory.measure_empty -> MeasureTheory.measure_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1}, Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1}, Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_empty MeasureTheory.measure_emptyₓ'. -/
@[simp]
theorem measure_empty : μ ∅ = 0 :=
  μ.Empty
#align measure_theory.measure_empty MeasureTheory.measure_empty

/- warning: measure_theory.nonempty_of_measure_ne_zero -> MeasureTheory.nonempty_of_measure_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Set.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Set.Nonempty.{u1} α s)
Case conversion may be inaccurate. Consider using '#align measure_theory.nonempty_of_measure_ne_zero MeasureTheory.nonempty_of_measure_ne_zeroₓ'. -/
theorem nonempty_of_measure_ne_zero (h : μ s ≠ 0) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h' => h <| h'.symm ▸ measure_empty
#align measure_theory.nonempty_of_measure_ne_zero MeasureTheory.nonempty_of_measure_ne_zero

/- warning: measure_theory.measure_mono -> MeasureTheory.measure_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s₁) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s₁) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s₂))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_mono MeasureTheory.measure_monoₓ'. -/
theorem measure_mono (h : s₁ ⊆ s₂) : μ s₁ ≤ μ s₂ :=
  μ.mono h
#align measure_theory.measure_mono MeasureTheory.measure_mono

/- warning: measure_theory.measure_mono_null -> MeasureTheory.measure_mono_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s₂) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s₁) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s₂) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s₁) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_mono_null MeasureTheory.measure_mono_nullₓ'. -/
theorem measure_mono_null (h : s₁ ⊆ s₂) (h₂ : μ s₂ = 0) : μ s₁ = 0 :=
  nonpos_iff_eq_zero.1 <| h₂ ▸ measure_mono h
#align measure_theory.measure_mono_null MeasureTheory.measure_mono_null

/- warning: measure_theory.measure_mono_top -> MeasureTheory.measure_mono_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s₁) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s₂) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s₁) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s₂) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_mono_top MeasureTheory.measure_mono_topₓ'. -/
theorem measure_mono_top (h : s₁ ⊆ s₂) (h₁ : μ s₁ = ∞) : μ s₂ = ∞ :=
  top_unique <| h₁ ▸ measure_mono h
#align measure_theory.measure_mono_top MeasureTheory.measure_mono_top

#print MeasureTheory.exists_measurable_superset /-
/-- For every set there exists a measurable superset of the same measure. -/
theorem exists_measurable_superset (μ : Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = μ s := by
  simpa only [← measure_eq_trim] using μ.to_outer_measure.exists_measurable_superset_eq_trim s
#align measure_theory.exists_measurable_superset MeasureTheory.exists_measurable_superset
-/

#print MeasureTheory.exists_measurable_superset_forall_eq /-
/-- For every set `s` and a countable collection of measures `μ i` there exists a measurable
superset `t ⊇ s` such that each measure `μ i` takes the same value on `s` and `t`. -/
theorem exists_measurable_superset_forall_eq {ι} [Countable ι] (μ : ι → Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ ∀ i, μ i t = μ i s := by
  simpa only [← measure_eq_trim] using
    outer_measure.exists_measurable_superset_forall_eq_trim (fun i => (μ i).toOuterMeasure) s
#align measure_theory.exists_measurable_superset_forall_eq MeasureTheory.exists_measurable_superset_forall_eq
-/

#print MeasureTheory.exists_measurable_superset₂ /-
theorem exists_measurable_superset₂ (μ ν : Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = μ s ∧ ν t = ν s := by
  simpa only [bool.forall_bool.trans and_comm] using
    exists_measurable_superset_forall_eq (fun b => cond b μ ν) s
#align measure_theory.exists_measurable_superset₂ MeasureTheory.exists_measurable_superset₂
-/

/- warning: measure_theory.exists_measurable_superset_of_null -> MeasureTheory.exists_measurable_superset_of_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (And (MeasurableSet.{u1} α _inst_1 t) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (And (MeasurableSet.{u1} α _inst_1 t) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.exists_measurable_superset_of_null MeasureTheory.exists_measurable_superset_of_nullₓ'. -/
theorem exists_measurable_superset_of_null (h : μ s = 0) : ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = 0 :=
  h ▸ exists_measurable_superset μ s
#align measure_theory.exists_measurable_superset_of_null MeasureTheory.exists_measurable_superset_of_null

/- warning: measure_theory.exists_measurable_superset_iff_measure_eq_zero -> MeasureTheory.exists_measurable_superset_iff_measure_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (And (MeasurableSet.{u1} α _inst_1 t) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))))) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (And (MeasurableSet.{u1} α _inst_1 t) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))))) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.exists_measurable_superset_iff_measure_eq_zero MeasureTheory.exists_measurable_superset_iff_measure_eq_zeroₓ'. -/
theorem exists_measurable_superset_iff_measure_eq_zero :
    (∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = 0) ↔ μ s = 0 :=
  ⟨fun ⟨t, hst, _, ht⟩ => measure_mono_null hst ht, exists_measurable_superset_of_null⟩
#align measure_theory.exists_measurable_superset_iff_measure_eq_zero MeasureTheory.exists_measurable_superset_iff_measure_eq_zero

/- warning: measure_theory.measure_Union_le -> MeasureTheory.measure_iUnion_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : Countable.{succ u2} β] (s : β -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (i : β) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (s i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : Countable.{succ u2} β] (s : β -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (i : β) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (s i)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_Union_le MeasureTheory.measure_iUnion_leₓ'. -/
theorem measure_iUnion_le [Countable β] (s : β → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  μ.toOuterMeasure.iUnion _
#align measure_theory.measure_Union_le MeasureTheory.measure_iUnion_le

/- warning: measure_theory.measure_bUnion_le -> MeasureTheory.measure_biUnion_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u2} β}, (Set.Countable.{u2} β s) -> (forall (f : β -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.iUnion.{u1, succ u2} α β (fun (b : β) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b s) => f b)))) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (p : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) p)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u2} β}, (Set.Countable.{u2} β s) -> (forall (f : β -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Set.iUnion.{u1, succ u2} α β (fun (b : β) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b s) => f b)))) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u2} β s) (fun (p : Set.Elem.{u2} β s) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) p)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_bUnion_le MeasureTheory.measure_biUnion_leₓ'. -/
theorem measure_biUnion_le {s : Set β} (hs : s.Countable) (f : β → Set α) :
    μ (⋃ b ∈ s, f b) ≤ ∑' p : s, μ (f p) := by haveI := hs.to_subtype; rw [bUnion_eq_Union];
  apply measure_Union_le
#align measure_theory.measure_bUnion_le MeasureTheory.measure_biUnion_le

/- warning: measure_theory.measure_bUnion_finset_le -> MeasureTheory.measure_biUnion_finset_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (s : Finset.{u2} β) (f : β -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.iUnion.{u1, succ u2} α β (fun (b : β) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) => f b)))) (Finset.sum.{0, u2} ENNReal β (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (p : β) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (f p)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (s : Finset.{u2} β) (f : β -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Set.iUnion.{u1, succ u2} α β (fun (b : β) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) (fun (H : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) => f b)))) (Finset.sum.{0, u2} ENNReal β (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (p : β) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (f p)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_bUnion_finset_le MeasureTheory.measure_biUnion_finset_leₓ'. -/
theorem measure_biUnion_finset_le (s : Finset β) (f : β → Set α) :
    μ (⋃ b ∈ s, f b) ≤ ∑ p in s, μ (f p) :=
  by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, ← tsum_fintype]
  exact measure_bUnion_le s.countable_to_set f
#align measure_theory.measure_bUnion_finset_le MeasureTheory.measure_biUnion_finset_le

/- warning: measure_theory.measure_Union_fintype_le -> MeasureTheory.measure_iUnion_fintype_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : Fintype.{u2} β] (f : β -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.iUnion.{u1, succ u2} α β (fun (b : β) => f b))) (Finset.sum.{0, u2} ENNReal β (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.univ.{u2} β _inst_2) (fun (p : β) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (f p)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : Fintype.{u2} β] (f : β -> (Set.{u1} α)), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Set.iUnion.{u1, succ u2} α β (fun (b : β) => f b))) (Finset.sum.{0, u2} ENNReal β (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.univ.{u2} β _inst_2) (fun (p : β) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (f p)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_Union_fintype_le MeasureTheory.measure_iUnion_fintype_leₓ'. -/
theorem measure_iUnion_fintype_le [Fintype β] (f : β → Set α) : μ (⋃ b, f b) ≤ ∑ p, μ (f p) := by
  convert measure_bUnion_finset_le Finset.univ f; simp
#align measure_theory.measure_Union_fintype_le MeasureTheory.measure_iUnion_fintype_le

/- warning: measure_theory.measure_bUnion_lt_top -> MeasureTheory.measure_biUnion_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u2} β} {f : β -> (Set.{u1} α)}, (Set.Finite.{u2} β s) -> (forall (i : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (f i)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.iUnion.{u1, succ u2} α β (fun (i : β) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i s) => f i)))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u2} β} {f : β -> (Set.{u1} α)}, (Set.Finite.{u2} β s) -> (forall (i : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i s) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (f i)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Set.iUnion.{u1, succ u2} α β (fun (i : β) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i s) => f i)))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_bUnion_lt_top MeasureTheory.measure_biUnion_lt_topₓ'. -/
theorem measure_biUnion_lt_top {s : Set β} {f : β → Set α} (hs : s.Finite)
    (hfin : ∀ i ∈ s, μ (f i) ≠ ∞) : μ (⋃ i ∈ s, f i) < ∞ :=
  by
  convert(measure_bUnion_finset_le hs.to_finset f).trans_lt _
  · ext; rw [finite.mem_to_finset]
  apply ENNReal.sum_lt_top; simpa only [finite.mem_to_finset]
#align measure_theory.measure_bUnion_lt_top MeasureTheory.measure_biUnion_lt_top

/- warning: measure_theory.measure_Union_null -> MeasureTheory.measure_iUnion_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : Countable.{succ u2} β] {s : β -> (Set.{u1} α)}, (forall (i : β), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (s i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : Countable.{succ u2} β] {s : β -> (Set.{u1} α)}, (forall (i : β), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (s i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_Union_null MeasureTheory.measure_iUnion_nullₓ'. -/
theorem measure_iUnion_null [Countable β] {s : β → Set α} : (∀ i, μ (s i) = 0) → μ (⋃ i, s i) = 0 :=
  μ.toOuterMeasure.iUnion_null
#align measure_theory.measure_Union_null MeasureTheory.measure_iUnion_null

/- warning: measure_theory.measure_Union_null_iff -> MeasureTheory.measure_iUnion_null_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : Countable.{succ u2} ι] {s : ι -> (Set.{u1} α)}, Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => s i))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (forall (i : ι), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (s i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : Countable.{succ u2} ι] {s : ι -> (Set.{u1} α)}, Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => s i))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall (i : ι), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (s i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_Union_null_iff MeasureTheory.measure_iUnion_null_iffₓ'. -/
@[simp]
theorem measure_iUnion_null_iff [Countable ι] {s : ι → Set α} :
    μ (⋃ i, s i) = 0 ↔ ∀ i, μ (s i) = 0 :=
  μ.toOuterMeasure.iUnion_null_iff
#align measure_theory.measure_Union_null_iff MeasureTheory.measure_iUnion_null_iff

/- warning: measure_theory.measure_Union_null_iff' -> MeasureTheory.measure_iUnion_null_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {ι : Prop} {s : ι -> (Set.{u1} α)}, Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.iUnion.{u1, 0} α ι (fun (i : ι) => s i))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (forall (i : ι), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (s i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {ι : Prop} {s : ι -> (Set.{u1} α)}, Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Set.iUnion.{u1, 0} α ι (fun (i : ι) => s i))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall (i : ι), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (s i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_Union_null_iff' MeasureTheory.measure_iUnion_null_iff'ₓ'. -/
/-- A version of `measure_Union_null_iff` for unions indexed by Props
TODO: in the long run it would be better to combine this with `measure_Union_null_iff` by
generalising to `Sort`. -/
@[simp]
theorem measure_iUnion_null_iff' {ι : Prop} {s : ι → Set α} : μ (⋃ i, s i) = 0 ↔ ∀ i, μ (s i) = 0 :=
  μ.toOuterMeasure.iUnion_null_iff'
#align measure_theory.measure_Union_null_iff' MeasureTheory.measure_iUnion_null_iff'

/- warning: measure_theory.measure_bUnion_null_iff -> MeasureTheory.measure_biUnion_null_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u2} ι}, (Set.Countable.{u2} ι s) -> (forall {t : ι -> (Set.{u1} α)}, Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => t i)))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (t i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u2} ι}, (Set.Countable.{u2} ι s) -> (forall {t : ι -> (Set.{u1} α)}, Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => t i)))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (t i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_bUnion_null_iff MeasureTheory.measure_biUnion_null_iffₓ'. -/
theorem measure_biUnion_null_iff {s : Set ι} (hs : s.Countable) {t : ι → Set α} :
    μ (⋃ i ∈ s, t i) = 0 ↔ ∀ i ∈ s, μ (t i) = 0 :=
  μ.toOuterMeasure.biUnion_null_iff hs
#align measure_theory.measure_bUnion_null_iff MeasureTheory.measure_biUnion_null_iff

/- warning: measure_theory.measure_sUnion_null_iff -> MeasureTheory.measure_sUnion_null_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {S : Set.{u1} (Set.{u1} α)}, (Set.Countable.{u1} (Set.{u1} α) S) -> (Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.sUnion.{u1} α S)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s S) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {S : Set.{u1} (Set.{u1} α)}, (Set.Countable.{u1} (Set.{u1} α) S) -> (Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Set.sUnion.{u1} α S)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s S) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_sUnion_null_iff MeasureTheory.measure_sUnion_null_iffₓ'. -/
theorem measure_sUnion_null_iff {S : Set (Set α)} (hS : S.Countable) :
    μ (⋃₀ S) = 0 ↔ ∀ s ∈ S, μ s = 0 :=
  μ.toOuterMeasure.sUnion_null_iff hS
#align measure_theory.measure_sUnion_null_iff MeasureTheory.measure_sUnion_null_iff

/- warning: measure_theory.measure_union_le -> MeasureTheory.measure_union_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (s₁ : Set.{u1} α) (s₂ : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s₁) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (s₁ : Set.{u1} α) (s₂ : Set.{u1} α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s₁) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s₂))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_union_le MeasureTheory.measure_union_leₓ'. -/
theorem measure_union_le (s₁ s₂ : Set α) : μ (s₁ ∪ s₂) ≤ μ s₁ + μ s₂ :=
  μ.toOuterMeasure.union _ _
#align measure_theory.measure_union_le MeasureTheory.measure_union_le

/- warning: measure_theory.measure_union_null -> MeasureTheory.measure_union_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s₁) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s₂) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s₁) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s₂) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_union_null MeasureTheory.measure_union_nullₓ'. -/
theorem measure_union_null : μ s₁ = 0 → μ s₂ = 0 → μ (s₁ ∪ s₂) = 0 :=
  μ.toOuterMeasure.union_null
#align measure_theory.measure_union_null MeasureTheory.measure_union_null

/- warning: measure_theory.measure_union_null_iff -> MeasureTheory.measure_union_null_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (And (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s₁) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s₂) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (And (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s₁) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s₂) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_union_null_iff MeasureTheory.measure_union_null_iffₓ'. -/
@[simp]
theorem measure_union_null_iff : μ (s₁ ∪ s₂) = 0 ↔ μ s₁ = 0 ∧ μ s₂ = 0 :=
  ⟨fun h =>
    ⟨measure_mono_null (subset_union_left _ _) h, measure_mono_null (subset_union_right _ _) h⟩,
    fun h => measure_union_null h.1 h.2⟩
#align measure_theory.measure_union_null_iff MeasureTheory.measure_union_null_iff

/- warning: measure_theory.measure_union_lt_top -> MeasureTheory.measure_union_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_union_lt_top MeasureTheory.measure_union_lt_topₓ'. -/
theorem measure_union_lt_top (hs : μ s < ∞) (ht : μ t < ∞) : μ (s ∪ t) < ∞ :=
  (measure_union_le s t).trans_lt (ENNReal.add_lt_top.mpr ⟨hs, ht⟩)
#align measure_theory.measure_union_lt_top MeasureTheory.measure_union_lt_top

/- warning: measure_theory.measure_union_lt_top_iff -> MeasureTheory.measure_union_lt_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (And (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (And (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_union_lt_top_iff MeasureTheory.measure_union_lt_top_iffₓ'. -/
@[simp]
theorem measure_union_lt_top_iff : μ (s ∪ t) < ∞ ↔ μ s < ∞ ∧ μ t < ∞ :=
  by
  refine' ⟨fun h => ⟨_, _⟩, fun h => measure_union_lt_top h.1 h.2⟩
  · exact (measure_mono (Set.subset_union_left s t)).trans_lt h
  · exact (measure_mono (Set.subset_union_right s t)).trans_lt h
#align measure_theory.measure_union_lt_top_iff MeasureTheory.measure_union_lt_top_iff

/- warning: measure_theory.measure_union_ne_top -> MeasureTheory.measure_union_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_union_ne_top MeasureTheory.measure_union_ne_topₓ'. -/
theorem measure_union_ne_top (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) : μ (s ∪ t) ≠ ∞ :=
  (measure_union_lt_top hs.lt_top ht.lt_top).Ne
#align measure_theory.measure_union_ne_top MeasureTheory.measure_union_ne_top

/- warning: measure_theory.measure_union_eq_top_iff -> MeasureTheory.measure_union_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Or (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Or (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_union_eq_top_iff MeasureTheory.measure_union_eq_top_iffₓ'. -/
@[simp]
theorem measure_union_eq_top_iff : μ (s ∪ t) = ∞ ↔ μ s = ∞ ∨ μ t = ∞ :=
  not_iff_not.1 <| by simp only [← lt_top_iff_ne_top, ← Ne.def, not_or, measure_union_lt_top_iff]
#align measure_theory.measure_union_eq_top_iff MeasureTheory.measure_union_eq_top_iff

/- warning: measure_theory.exists_measure_pos_of_not_measure_Union_null -> MeasureTheory.exists_measure_pos_of_not_measure_iUnion_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : Countable.{succ u2} β] {s : β -> (Set.{u1} α)}, (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.iUnion.{u1, succ u2} α β (fun (n : β) => s n))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u2} β (fun (n : β) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (s n))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : Countable.{succ u2} β] {s : β -> (Set.{u1} α)}, (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Set.iUnion.{u1, succ u2} α β (fun (n : β) => s n))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u2} β (fun (n : β) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (s n))))
Case conversion may be inaccurate. Consider using '#align measure_theory.exists_measure_pos_of_not_measure_Union_null MeasureTheory.exists_measure_pos_of_not_measure_iUnion_nullₓ'. -/
theorem exists_measure_pos_of_not_measure_iUnion_null [Countable β] {s : β → Set α}
    (hs : μ (⋃ n, s n) ≠ 0) : ∃ n, 0 < μ (s n) :=
  by
  contrapose! hs
  exact measure_Union_null fun n => nonpos_iff_eq_zero.1 (hs n)
#align measure_theory.exists_measure_pos_of_not_measure_Union_null MeasureTheory.exists_measure_pos_of_not_measure_iUnion_null

/- warning: measure_theory.measure_inter_lt_top_of_left_ne_top -> MeasureTheory.measure_inter_lt_top_of_left_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_inter_lt_top_of_left_ne_top MeasureTheory.measure_inter_lt_top_of_left_ne_topₓ'. -/
theorem measure_inter_lt_top_of_left_ne_top (hs_finite : μ s ≠ ∞) : μ (s ∩ t) < ∞ :=
  (measure_mono (Set.inter_subset_left s t)).trans_lt hs_finite.lt_top
#align measure_theory.measure_inter_lt_top_of_left_ne_top MeasureTheory.measure_inter_lt_top_of_left_ne_top

/- warning: measure_theory.measure_inter_lt_top_of_right_ne_top -> MeasureTheory.measure_inter_lt_top_of_right_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ t) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) t) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_inter_lt_top_of_right_ne_top MeasureTheory.measure_inter_lt_top_of_right_ne_topₓ'. -/
theorem measure_inter_lt_top_of_right_ne_top (ht_finite : μ t ≠ ∞) : μ (s ∩ t) < ∞ :=
  inter_comm t s ▸ measure_inter_lt_top_of_left_ne_top ht_finite
#align measure_theory.measure_inter_lt_top_of_right_ne_top MeasureTheory.measure_inter_lt_top_of_right_ne_top

/- warning: measure_theory.measure_inter_null_of_null_right -> MeasureTheory.measure_inter_null_of_null_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (S : Set.{u1} α) {T : Set.{u1} α}, (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ T) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) S T)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (S : Set.{u1} α) {T : Set.{u1} α}, (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) T) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) S T)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_inter_null_of_null_right MeasureTheory.measure_inter_null_of_null_rightₓ'. -/
theorem measure_inter_null_of_null_right (S : Set α) {T : Set α} (h : μ T = 0) : μ (S ∩ T) = 0 :=
  measure_mono_null (inter_subset_right S T) h
#align measure_theory.measure_inter_null_of_null_right MeasureTheory.measure_inter_null_of_null_right

/- warning: measure_theory.measure_inter_null_of_null_left -> MeasureTheory.measure_inter_null_of_null_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {S : Set.{u1} α} (T : Set.{u1} α), (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ S) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) S T)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {S : Set.{u1} α} (T : Set.{u1} α), (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) S) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) S T)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_inter_null_of_null_left MeasureTheory.measure_inter_null_of_null_leftₓ'. -/
theorem measure_inter_null_of_null_left {S : Set α} (T : Set α) (h : μ S = 0) : μ (S ∩ T) = 0 :=
  measure_mono_null (inter_subset_left S T) h
#align measure_theory.measure_inter_null_of_null_left MeasureTheory.measure_inter_null_of_null_left

/-! ### The almost everywhere filter -/


#print MeasureTheory.Measure.ae /-
/-- The “almost everywhere” filter of co-null sets. -/
def Measure.ae {α} {m : MeasurableSpace α} (μ : Measure α) : Filter α
    where
  sets := { s | μ (sᶜ) = 0 }
  univ_sets := by simp
  inter_sets s t hs ht := by
    simp only [compl_inter, mem_set_of_eq] <;> exact measure_union_null hs ht
  sets_of_superset s t hs hst := measure_mono_null (Set.compl_subset_compl.2 hst) hs
#align measure_theory.measure.ae MeasureTheory.Measure.ae
-/

-- mathport name: «expr∀ᵐ ∂ , »
notation3"∀ᵐ "(...)" ∂"μ", "r:(scoped P => Filter.Eventually P Measure.ae μ) => r

-- mathport name: «expr∃ᵐ ∂ , »
notation3"∃ᵐ "(...)" ∂"μ", "r:(scoped P => Filter.Frequently P Measure.ae μ) => r

-- mathport name: «expr =ᵐ[ ] »
notation:50 f " =ᵐ[" μ:50 "] " g:50 => f =ᶠ[Measure.ae μ] g

-- mathport name: «expr ≤ᵐ[ ] »
notation:50 f " ≤ᵐ[" μ:50 "] " g:50 => f ≤ᶠ[Measure.ae μ] g

/- warning: measure_theory.mem_ae_iff -> MeasureTheory.mem_ae_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.mem_ae_iff MeasureTheory.mem_ae_iffₓ'. -/
theorem mem_ae_iff {s : Set α} : s ∈ μ.ae ↔ μ (sᶜ) = 0 :=
  Iff.rfl
#align measure_theory.mem_ae_iff MeasureTheory.mem_ae_iff

/- warning: measure_theory.ae_iff -> MeasureTheory.ae_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (a : α) => p a) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (setOf.{u1} α (fun (a : α) => Not (p a)))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (a : α) => p a) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (setOf.{u1} α (fun (a : α) => Not (p a)))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_iff MeasureTheory.ae_iffₓ'. -/
theorem ae_iff {p : α → Prop} : (∀ᵐ a ∂μ, p a) ↔ μ { a | ¬p a } = 0 :=
  Iff.rfl
#align measure_theory.ae_iff MeasureTheory.ae_iff

/- warning: measure_theory.compl_mem_ae_iff -> MeasureTheory.compl_mem_ae_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.compl_mem_ae_iff MeasureTheory.compl_mem_ae_iffₓ'. -/
theorem compl_mem_ae_iff {s : Set α} : sᶜ ∈ μ.ae ↔ μ s = 0 := by simp only [mem_ae_iff, compl_compl]
#align measure_theory.compl_mem_ae_iff MeasureTheory.compl_mem_ae_iff

/- warning: measure_theory.frequently_ae_iff -> MeasureTheory.frequently_ae_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : α -> Prop}, Iff (Filter.Frequently.{u1} α (fun (a : α) => p a) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)) (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (setOf.{u1} α (fun (a : α) => p a))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : α -> Prop}, Iff (Filter.Frequently.{u1} α (fun (a : α) => p a) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)) (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (setOf.{u1} α (fun (a : α) => p a))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.frequently_ae_iff MeasureTheory.frequently_ae_iffₓ'. -/
theorem frequently_ae_iff {p : α → Prop} : (∃ᵐ a ∂μ, p a) ↔ μ { a | p a } ≠ 0 :=
  not_congr compl_mem_ae_iff
#align measure_theory.frequently_ae_iff MeasureTheory.frequently_ae_iff

/- warning: measure_theory.frequently_ae_mem_iff -> MeasureTheory.frequently_ae_mem_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Filter.Frequently.{u1} α (fun (a : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)) (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Filter.Frequently.{u1} α (fun (a : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)) (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.frequently_ae_mem_iff MeasureTheory.frequently_ae_mem_iffₓ'. -/
theorem frequently_ae_mem_iff {s : Set α} : (∃ᵐ a ∂μ, a ∈ s) ↔ μ s ≠ 0 :=
  not_congr compl_mem_ae_iff
#align measure_theory.frequently_ae_mem_iff MeasureTheory.frequently_ae_mem_iff

/- warning: measure_theory.measure_zero_iff_ae_nmem -> MeasureTheory.measure_zero_iff_ae_nmem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Filter.Eventually.{u1} α (fun (a : α) => Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Filter.Eventually.{u1} α (fun (a : α) => Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_zero_iff_ae_nmem MeasureTheory.measure_zero_iff_ae_nmemₓ'. -/
theorem measure_zero_iff_ae_nmem {s : Set α} : μ s = 0 ↔ ∀ᵐ a ∂μ, a ∉ s :=
  compl_mem_ae_iff.symm
#align measure_theory.measure_zero_iff_ae_nmem MeasureTheory.measure_zero_iff_ae_nmem

#print MeasureTheory.ae_of_all /-
theorem ae_of_all {p : α → Prop} (μ : Measure α) : (∀ a, p a) → ∀ᵐ a ∂μ, p a :=
  eventually_of_forall
#align measure_theory.ae_of_all MeasureTheory.ae_of_all
-/

--instance ae_is_measurably_generated : is_measurably_generated μ.ae :=
--⟨λ s hs, let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs in
--  ⟨tᶜ, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩
instance : CountableInterFilter μ.ae :=
  ⟨by
    intro S hSc hS
    rw [mem_ae_iff, compl_sInter, sUnion_image]
    exact (measure_bUnion_null_iff hSc).2 hS⟩

#print MeasureTheory.ae_all_iff /-
theorem ae_all_iff {ι : Sort _} [Countable ι] {p : α → ι → Prop} :
    (∀ᵐ a ∂μ, ∀ i, p a i) ↔ ∀ i, ∀ᵐ a ∂μ, p a i :=
  eventually_countable_forall
#align measure_theory.ae_all_iff MeasureTheory.ae_all_iff
-/

#print MeasureTheory.ae_ball_iff /-
theorem ae_ball_iff {S : Set ι} (hS : S.Countable) {p : ∀ (x : α), ∀ i ∈ S, Prop} :
    (∀ᵐ x ∂μ, ∀ i ∈ S, p x i ‹_›) ↔ ∀ i ∈ S, ∀ᵐ x ∂μ, p x i ‹_› :=
  eventually_countable_ball hS
#align measure_theory.ae_ball_iff MeasureTheory.ae_ball_iff
-/

/- warning: measure_theory.ae_eq_refl -> MeasureTheory.ae_eq_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (f : α -> δ), Filter.EventuallyEq.{u1, u2} α δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) f f
but is expected to have type
  forall {α : Type.{u2}} {δ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} (f : α -> δ), Filter.EventuallyEq.{u2, u1} α δ (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) f f
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_refl MeasureTheory.ae_eq_reflₓ'. -/
theorem ae_eq_refl (f : α → δ) : f =ᵐ[μ] f :=
  EventuallyEq.rfl
#align measure_theory.ae_eq_refl MeasureTheory.ae_eq_refl

/- warning: measure_theory.ae_eq_symm -> MeasureTheory.ae_eq_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {f : α -> δ} {g : α -> δ}, (Filter.EventuallyEq.{u1, u2} α δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) f g) -> (Filter.EventuallyEq.{u1, u2} α δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) g f)
but is expected to have type
  forall {α : Type.{u2}} {δ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} {f : α -> δ} {g : α -> δ}, (Filter.EventuallyEq.{u2, u1} α δ (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) f g) -> (Filter.EventuallyEq.{u2, u1} α δ (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) g f)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_symm MeasureTheory.ae_eq_symmₓ'. -/
theorem ae_eq_symm {f g : α → δ} (h : f =ᵐ[μ] g) : g =ᵐ[μ] f :=
  h.symm
#align measure_theory.ae_eq_symm MeasureTheory.ae_eq_symm

/- warning: measure_theory.ae_eq_trans -> MeasureTheory.ae_eq_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {f : α -> δ} {g : α -> δ} {h : α -> δ}, (Filter.EventuallyEq.{u1, u2} α δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) f g) -> (Filter.EventuallyEq.{u1, u2} α δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) g h) -> (Filter.EventuallyEq.{u1, u2} α δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) f h)
but is expected to have type
  forall {α : Type.{u2}} {δ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} {f : α -> δ} {g : α -> δ} {h : α -> δ}, (Filter.EventuallyEq.{u2, u1} α δ (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) f g) -> (Filter.EventuallyEq.{u2, u1} α δ (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) g h) -> (Filter.EventuallyEq.{u2, u1} α δ (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) f h)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_trans MeasureTheory.ae_eq_transₓ'. -/
theorem ae_eq_trans {f g h : α → δ} (h₁ : f =ᵐ[μ] g) (h₂ : g =ᵐ[μ] h) : f =ᵐ[μ] h :=
  h₁.trans h₂
#align measure_theory.ae_eq_trans MeasureTheory.ae_eq_trans

/- warning: measure_theory.ae_le_of_ae_lt -> MeasureTheory.ae_le_of_ae_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {f : α -> ENNReal} {g : α -> ENNReal}, (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) (g x)) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)) -> (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) f g)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {f : α -> ENNReal} {g : α -> ENNReal}, (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (g x)) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)) -> (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) f g)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_le_of_ae_lt MeasureTheory.ae_le_of_ae_ltₓ'. -/
theorem ae_le_of_ae_lt {f g : α → ℝ≥0∞} (h : ∀ᵐ x ∂μ, f x < g x) : f ≤ᵐ[μ] g :=
  by
  rw [Filter.EventuallyLE, ae_iff]
  rw [ae_iff] at h
  refine' measure_mono_null (fun x hx => _) h
  exact not_lt.2 (le_of_lt (not_le.1 hx))
#align measure_theory.ae_le_of_ae_lt MeasureTheory.ae_le_of_ae_lt

/- warning: measure_theory.ae_eq_empty -> MeasureTheory.ae_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_empty MeasureTheory.ae_eq_emptyₓ'. -/
@[simp]
theorem ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0 :=
  eventuallyEq_empty.trans <| by simp only [ae_iff, Classical.not_not, set_of_mem_eq]
#align measure_theory.ae_eq_empty MeasureTheory.ae_eq_empty

/- warning: measure_theory.ae_eq_univ -> MeasureTheory.ae_eq_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s (Set.univ.{u1} α)) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s (Set.univ.{u1} α)) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_univ MeasureTheory.ae_eq_univₓ'. -/
@[simp]
theorem ae_eq_univ : s =ᵐ[μ] (univ : Set α) ↔ μ (sᶜ) = 0 :=
  eventuallyEq_univ
#align measure_theory.ae_eq_univ MeasureTheory.ae_eq_univ

/- warning: measure_theory.ae_le_set -> MeasureTheory.ae_le_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_le_set MeasureTheory.ae_le_setₓ'. -/
theorem ae_le_set : s ≤ᵐ[μ] t ↔ μ (s \ t) = 0 :=
  calc
    s ≤ᵐ[μ] t ↔ ∀ᵐ x ∂μ, x ∈ s → x ∈ t := Iff.rfl
    _ ↔ μ (s \ t) = 0 := by simp [ae_iff] <;> rfl
    
#align measure_theory.ae_le_set MeasureTheory.ae_le_set

/- warning: measure_theory.ae_le_set_inter -> MeasureTheory.ae_le_set_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α}, (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s' t') -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s s') (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t t'))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α}, (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s' t') -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s s') (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t t'))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_le_set_inter MeasureTheory.ae_le_set_interₓ'. -/
theorem ae_le_set_inter {s' t' : Set α} (h : s ≤ᵐ[μ] t) (h' : s' ≤ᵐ[μ] t') :
    (s ∩ s' : Set α) ≤ᵐ[μ] (t ∩ t' : Set α) :=
  h.inter h'
#align measure_theory.ae_le_set_inter MeasureTheory.ae_le_set_inter

/- warning: measure_theory.ae_le_set_union -> MeasureTheory.ae_le_set_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α}, (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s' t') -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s s') (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t t'))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α}, (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s' t') -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s s') (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t t'))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_le_set_union MeasureTheory.ae_le_set_unionₓ'. -/
theorem ae_le_set_union {s' t' : Set α} (h : s ≤ᵐ[μ] t) (h' : s' ≤ᵐ[μ] t') :
    (s ∪ s' : Set α) ≤ᵐ[μ] (t ∪ t' : Set α) :=
  h.union h'
#align measure_theory.ae_le_set_union MeasureTheory.ae_le_set_union

/- warning: measure_theory.union_ae_eq_right -> MeasureTheory.union_ae_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) t) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) t) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.union_ae_eq_right MeasureTheory.union_ae_eq_rightₓ'. -/
theorem union_ae_eq_right : (s ∪ t : Set α) =ᵐ[μ] t ↔ μ (s \ t) = 0 := by
  simp [eventually_le_antisymm_iff, ae_le_set, union_diff_right,
    diff_eq_empty.2 (Set.subset_union_right _ _)]
#align measure_theory.union_ae_eq_right MeasureTheory.union_ae_eq_right

/- warning: measure_theory.diff_ae_eq_self -> MeasureTheory.diff_ae_eq_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) s) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) s) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.diff_ae_eq_self MeasureTheory.diff_ae_eq_selfₓ'. -/
theorem diff_ae_eq_self : (s \ t : Set α) =ᵐ[μ] s ↔ μ (s ∩ t) = 0 := by
  simp [eventually_le_antisymm_iff, ae_le_set, diff_diff_right, diff_diff,
    diff_eq_empty.2 (Set.subset_union_right _ _)]
#align measure_theory.diff_ae_eq_self MeasureTheory.diff_ae_eq_self

/- warning: measure_theory.diff_null_ae_eq_self -> MeasureTheory.diff_null_ae_eq_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) s)
Case conversion may be inaccurate. Consider using '#align measure_theory.diff_null_ae_eq_self MeasureTheory.diff_null_ae_eq_selfₓ'. -/
theorem diff_null_ae_eq_self (ht : μ t = 0) : (s \ t : Set α) =ᵐ[μ] s :=
  diff_ae_eq_self.mpr (measure_mono_null (inter_subset_right _ _) ht)
#align measure_theory.diff_null_ae_eq_self MeasureTheory.diff_null_ae_eq_self

/- warning: measure_theory.ae_eq_set -> MeasureTheory.ae_eq_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) (And (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) (And (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_set MeasureTheory.ae_eq_setₓ'. -/
theorem ae_eq_set {s t : Set α} : s =ᵐ[μ] t ↔ μ (s \ t) = 0 ∧ μ (t \ s) = 0 := by
  simp [eventually_le_antisymm_iff, ae_le_set]
#align measure_theory.ae_eq_set MeasureTheory.ae_eq_set

/- warning: measure_theory.measure_symm_diff_eq_zero_iff -> MeasureTheory.measure_symmDiff_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Set.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Set.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (Set.instSDiffSet.{u1} α) s t)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_symm_diff_eq_zero_iff MeasureTheory.measure_symmDiff_eq_zero_iffₓ'. -/
@[simp]
theorem measure_symmDiff_eq_zero_iff {s t : Set α} : μ (s ∆ t) = 0 ↔ s =ᵐ[μ] t := by
  simp [ae_eq_set, symmDiff_def]
#align measure_theory.measure_symm_diff_eq_zero_iff MeasureTheory.measure_symmDiff_eq_zero_iff

#print MeasureTheory.ae_eq_set_compl_compl /-
@[simp]
theorem ae_eq_set_compl_compl {s t : Set α} : sᶜ =ᵐ[μ] tᶜ ↔ s =ᵐ[μ] t := by
  simp only [← measure_symm_diff_eq_zero_iff, compl_symmDiff_compl]
#align measure_theory.ae_eq_set_compl_compl MeasureTheory.ae_eq_set_compl_compl
-/

#print MeasureTheory.ae_eq_set_compl /-
theorem ae_eq_set_compl {s t : Set α} : sᶜ =ᵐ[μ] t ↔ s =ᵐ[μ] tᶜ := by
  rw [← ae_eq_set_compl_compl, compl_compl]
#align measure_theory.ae_eq_set_compl MeasureTheory.ae_eq_set_compl
-/

/- warning: measure_theory.ae_eq_set_inter -> MeasureTheory.ae_eq_set_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s' t') -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s s') (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t t'))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s' t') -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s s') (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t t'))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_set_inter MeasureTheory.ae_eq_set_interₓ'. -/
theorem ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') :
    (s ∩ s' : Set α) =ᵐ[μ] (t ∩ t' : Set α) :=
  h.inter h'
#align measure_theory.ae_eq_set_inter MeasureTheory.ae_eq_set_inter

/- warning: measure_theory.ae_eq_set_union -> MeasureTheory.ae_eq_set_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s' t') -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s s') (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t t'))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α} {s' : Set.{u1} α} {t' : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s' t') -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s s') (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t t'))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_set_union MeasureTheory.ae_eq_set_unionₓ'. -/
theorem ae_eq_set_union {s' t' : Set α} (h : s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') :
    (s ∪ s' : Set α) =ᵐ[μ] (t ∪ t' : Set α) :=
  h.union h'
#align measure_theory.ae_eq_set_union MeasureTheory.ae_eq_set_union

/- warning: measure_theory.union_ae_eq_univ_of_ae_eq_univ_left -> MeasureTheory.union_ae_eq_univ_of_ae_eq_univ_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s (Set.univ.{u1} α)) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s (Set.univ.{u1} α)) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align measure_theory.union_ae_eq_univ_of_ae_eq_univ_left MeasureTheory.union_ae_eq_univ_of_ae_eq_univ_leftₓ'. -/
theorem union_ae_eq_univ_of_ae_eq_univ_left (h : s =ᵐ[μ] univ) : (s ∪ t : Set α) =ᵐ[μ] univ := by
  convert ae_eq_set_union h (ae_eq_refl t); rw [univ_union]
#align measure_theory.union_ae_eq_univ_of_ae_eq_univ_left MeasureTheory.union_ae_eq_univ_of_ae_eq_univ_left

/- warning: measure_theory.union_ae_eq_univ_of_ae_eq_univ_right -> MeasureTheory.union_ae_eq_univ_of_ae_eq_univ_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) t (Set.univ.{u1} α)) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) t (Set.univ.{u1} α)) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align measure_theory.union_ae_eq_univ_of_ae_eq_univ_right MeasureTheory.union_ae_eq_univ_of_ae_eq_univ_rightₓ'. -/
theorem union_ae_eq_univ_of_ae_eq_univ_right (h : t =ᵐ[μ] univ) : (s ∪ t : Set α) =ᵐ[μ] univ := by
  convert ae_eq_set_union (ae_eq_refl s) h; rw [union_univ]
#align measure_theory.union_ae_eq_univ_of_ae_eq_univ_right MeasureTheory.union_ae_eq_univ_of_ae_eq_univ_right

/- warning: measure_theory.union_ae_eq_right_of_ae_eq_empty -> MeasureTheory.union_ae_eq_right_of_ae_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) t)
Case conversion may be inaccurate. Consider using '#align measure_theory.union_ae_eq_right_of_ae_eq_empty MeasureTheory.union_ae_eq_right_of_ae_eq_emptyₓ'. -/
theorem union_ae_eq_right_of_ae_eq_empty (h : s =ᵐ[μ] (∅ : Set α)) : (s ∪ t : Set α) =ᵐ[μ] t := by
  convert ae_eq_set_union h (ae_eq_refl t); rw [empty_union]
#align measure_theory.union_ae_eq_right_of_ae_eq_empty MeasureTheory.union_ae_eq_right_of_ae_eq_empty

/- warning: measure_theory.union_ae_eq_left_of_ae_eq_empty -> MeasureTheory.union_ae_eq_left_of_ae_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) s)
Case conversion may be inaccurate. Consider using '#align measure_theory.union_ae_eq_left_of_ae_eq_empty MeasureTheory.union_ae_eq_left_of_ae_eq_emptyₓ'. -/
theorem union_ae_eq_left_of_ae_eq_empty (h : t =ᵐ[μ] (∅ : Set α)) : (s ∪ t : Set α) =ᵐ[μ] s := by
  convert ae_eq_set_union (ae_eq_refl s) h; rw [union_empty]
#align measure_theory.union_ae_eq_left_of_ae_eq_empty MeasureTheory.union_ae_eq_left_of_ae_eq_empty

/- warning: measure_theory.inter_ae_eq_right_of_ae_eq_univ -> MeasureTheory.inter_ae_eq_right_of_ae_eq_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s (Set.univ.{u1} α)) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s (Set.univ.{u1} α)) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) t)
Case conversion may be inaccurate. Consider using '#align measure_theory.inter_ae_eq_right_of_ae_eq_univ MeasureTheory.inter_ae_eq_right_of_ae_eq_univₓ'. -/
theorem inter_ae_eq_right_of_ae_eq_univ (h : s =ᵐ[μ] univ) : (s ∩ t : Set α) =ᵐ[μ] t := by
  convert ae_eq_set_inter h (ae_eq_refl t); rw [univ_inter]
#align measure_theory.inter_ae_eq_right_of_ae_eq_univ MeasureTheory.inter_ae_eq_right_of_ae_eq_univ

/- warning: measure_theory.inter_ae_eq_left_of_ae_eq_univ -> MeasureTheory.inter_ae_eq_left_of_ae_eq_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) t (Set.univ.{u1} α)) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) t (Set.univ.{u1} α)) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) s)
Case conversion may be inaccurate. Consider using '#align measure_theory.inter_ae_eq_left_of_ae_eq_univ MeasureTheory.inter_ae_eq_left_of_ae_eq_univₓ'. -/
theorem inter_ae_eq_left_of_ae_eq_univ (h : t =ᵐ[μ] univ) : (s ∩ t : Set α) =ᵐ[μ] s := by
  convert ae_eq_set_inter (ae_eq_refl s) h; rw [inter_univ]
#align measure_theory.inter_ae_eq_left_of_ae_eq_univ MeasureTheory.inter_ae_eq_left_of_ae_eq_univ

/- warning: measure_theory.inter_ae_eq_empty_of_ae_eq_empty_left -> MeasureTheory.inter_ae_eq_empty_of_ae_eq_empty_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align measure_theory.inter_ae_eq_empty_of_ae_eq_empty_left MeasureTheory.inter_ae_eq_empty_of_ae_eq_empty_leftₓ'. -/
theorem inter_ae_eq_empty_of_ae_eq_empty_left (h : s =ᵐ[μ] (∅ : Set α)) :
    (s ∩ t : Set α) =ᵐ[μ] (∅ : Set α) := by convert ae_eq_set_inter h (ae_eq_refl t);
  rw [empty_inter]
#align measure_theory.inter_ae_eq_empty_of_ae_eq_empty_left MeasureTheory.inter_ae_eq_empty_of_ae_eq_empty_left

/- warning: measure_theory.inter_ae_eq_empty_of_ae_eq_empty_right -> MeasureTheory.inter_ae_eq_empty_of_ae_eq_empty_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align measure_theory.inter_ae_eq_empty_of_ae_eq_empty_right MeasureTheory.inter_ae_eq_empty_of_ae_eq_empty_rightₓ'. -/
theorem inter_ae_eq_empty_of_ae_eq_empty_right (h : t =ᵐ[μ] (∅ : Set α)) :
    (s ∩ t : Set α) =ᵐ[μ] (∅ : Set α) := by convert ae_eq_set_inter (ae_eq_refl s) h;
  rw [inter_empty]
#align measure_theory.inter_ae_eq_empty_of_ae_eq_empty_right MeasureTheory.inter_ae_eq_empty_of_ae_eq_empty_right

/- warning: set.mul_indicator_ae_eq_one -> MeasureTheory.Set.mulIndicator_ae_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {M : Type.{u2}} [_inst_2 : One.{u2} M] {f : α -> M} {s : Set.{u1} α}, (Filter.EventuallyEq.{u1, u2} α M (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Set.mulIndicator.{u1, u2} α M _inst_2 s f) (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_2)))))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M _inst_2 f))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {M : Type.{u2}} [_inst_2 : One.{u2} M] {f : α -> M} {s : Set.{u1} α}, (Filter.EventuallyEq.{u1, u2} α M (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (Set.mulIndicator.{u1, u2} α M _inst_2 s f) (OfNat.ofNat.{max u1 u2} (α -> M) 1 (One.toOfNat1.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19136 : α) => M) (fun (i : α) => _inst_2))))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Function.mulSupport.{u1, u2} α M _inst_2 f))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_ae_eq_one MeasureTheory.Set.mulIndicator_ae_eq_oneₓ'. -/
@[to_additive]
theorem MeasureTheory.Set.mulIndicator_ae_eq_one {M : Type _} [One M] {f : α → M} {s : Set α}
    (h : s.mulIndicator f =ᵐ[μ] 1) : μ (s ∩ Function.mulSupport f) = 0 := by
  simpa [Filter.EventuallyEq, ae_iff] using h
#align set.mul_indicator_ae_eq_one MeasureTheory.Set.mulIndicator_ae_eq_one
#align set.indicator_ae_eq_zero MeasureTheory.Set.indicator_ae_eq_zero

/- warning: measure_theory.measure_mono_ae -> MeasureTheory.measure_mono_ae is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) t))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_mono_ae MeasureTheory.measure_mono_aeₓ'. -/
/-- If `s ⊆ t` modulo a set of measure `0`, then `μ s ≤ μ t`. -/
@[mono]
theorem measure_mono_ae (H : s ≤ᵐ[μ] t) : μ s ≤ μ t :=
  calc
    μ s ≤ μ (s ∪ t) := measure_mono <| subset_union_left s t
    _ = μ (t ∪ s \ t) := by rw [union_diff_self, Set.union_comm]
    _ ≤ μ t + μ (s \ t) := (measure_union_le _ _)
    _ = μ t := by rw [ae_le_set.1 H, add_zero]
    
#align measure_theory.measure_mono_ae MeasureTheory.measure_mono_ae

/- warning: filter.eventually_le.measure_le -> Filter.EventuallyLE.measure_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) t))
Case conversion may be inaccurate. Consider using '#align filter.eventually_le.measure_le Filter.EventuallyLE.measure_leₓ'. -/
alias measure_mono_ae ← _root_.filter.eventually_le.measure_le
#align filter.eventually_le.measure_le Filter.EventuallyLE.measure_le

#print MeasureTheory.measure_congr /-
/-- If two sets are equal modulo a set of measure zero, then `μ s = μ t`. -/
theorem measure_congr (H : s =ᵐ[μ] t) : μ s = μ t :=
  le_antisymm H.le.measure_le H.symm.le.measure_le
#align measure_theory.measure_congr MeasureTheory.measure_congr
-/

alias measure_congr ← _root_.filter.eventually_eq.measure_eq
#align filter.eventually_eq.measure_eq Filter.EventuallyEq.measure_eq

/- warning: measure_theory.measure_mono_null_ae -> MeasureTheory.measure_mono_null_ae is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {s : Set.{u1} α} {t : Set.{u1} α}, (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) s t) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_mono_null_ae MeasureTheory.measure_mono_null_aeₓ'. -/
theorem measure_mono_null_ae (H : s ≤ᵐ[μ] t) (ht : μ t = 0) : μ s = 0 :=
  nonpos_iff_eq_zero.1 <| ht ▸ H.measure_le
#align measure_theory.measure_mono_null_ae MeasureTheory.measure_mono_null_ae

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊇ » s) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊇ » s) -/
#print MeasureTheory.toMeasurable /-
/-- A measurable set `t ⊇ s` such that `μ t = μ s`. It even satisfies `μ (t ∩ u) = μ (s ∩ u)` for
any measurable set `u` if `μ s ≠ ∞`, see `measure_to_measurable_inter`.
(This property holds without the assumption `μ s ≠ ∞` when the space is sigma-finite,
see `measure_to_measurable_inter_of_sigma_finite`).
If `s` is a null measurable set, then
we also have `t =ᵐ[μ] s`, see `null_measurable_set.to_measurable_ae_eq`.
This notion is sometimes called a "measurable hull" in the literature. -/
irreducible_def toMeasurable (μ : Measure α) (s : Set α) : Set α :=
  if h : ∃ (t : _)(_ : t ⊇ s), MeasurableSet t ∧ t =ᵐ[μ] s then h.some
  else
    if h' :
        ∃ (t : _)(_ : t ⊇ s), MeasurableSet t ∧ ∀ u, MeasurableSet u → μ (t ∩ u) = μ (s ∩ u) then
      h'.some
    else (exists_measurable_superset μ s).some
#align measure_theory.to_measurable MeasureTheory.toMeasurable
-/

#print MeasureTheory.subset_toMeasurable /-
theorem subset_toMeasurable (μ : Measure α) (s : Set α) : s ⊆ toMeasurable μ s :=
  by
  rw [to_measurable]; split_ifs with hs h's
  exacts[hs.some_spec.fst, h's.some_spec.fst, (exists_measurable_superset μ s).choose_spec.1]
#align measure_theory.subset_to_measurable MeasureTheory.subset_toMeasurable
-/

#print MeasureTheory.ae_le_toMeasurable /-
theorem ae_le_toMeasurable : s ≤ᵐ[μ] toMeasurable μ s :=
  (subset_toMeasurable _ _).EventuallyLE
#align measure_theory.ae_le_to_measurable MeasureTheory.ae_le_toMeasurable
-/

#print MeasureTheory.measurableSet_toMeasurable /-
@[simp]
theorem measurableSet_toMeasurable (μ : Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s) :=
  by
  rw [to_measurable]; split_ifs with hs h's
  exacts[hs.some_spec.snd.1, h's.some_spec.snd.1, (exists_measurable_superset μ s).choose_spec.2.1]
#align measure_theory.measurable_set_to_measurable MeasureTheory.measurableSet_toMeasurable
-/

#print MeasureTheory.measure_toMeasurable /-
@[simp]
theorem measure_toMeasurable (s : Set α) : μ (toMeasurable μ s) = μ s :=
  by
  rw [to_measurable]; split_ifs with hs h's
  · exact measure_congr hs.some_spec.snd.2
  · simpa only [inter_univ] using h's.some_spec.snd.2 univ MeasurableSet.univ
  · exact (exists_measurable_superset μ s).choose_spec.2.2
#align measure_theory.measure_to_measurable MeasureTheory.measure_toMeasurable
-/

#print MeasureTheory.MeasureSpace /-
/-- A measure space is a measurable space equipped with a
  measure, referred to as `volume`. -/
class MeasureSpace (α : Type _) extends MeasurableSpace α where
  volume : Measure α
#align measure_theory.measure_space MeasureTheory.MeasureSpace
-/

export MeasureSpace (volume)

/-- `volume` is the canonical  measure on `α`. -/
add_decl_doc volume

section MeasureSpace

-- mathport name: «expr∀ᵐ , »
notation3"∀ᵐ "(...)", "r:(scoped P =>
  Filter.Eventually P MeasureTheory.Measure.ae MeasureTheory.MeasureSpace.volume) => r

-- mathport name: «expr∃ᵐ , »
notation3"∃ᵐ "(...)", "r:(scoped P =>
  Filter.Frequently P MeasureTheory.Measure.ae MeasureTheory.MeasureSpace.volume) => r

/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/-- The tactic `exact volume`, to be used in optional (`auto_param`) arguments. -/
unsafe def volume_tac : tactic Unit :=
  sorry
#align measure_theory.volume_tac measure_theory.volume_tac

end MeasureSpace

end

end MeasureTheory

section

open MeasureTheory

/-!
# Almost everywhere measurable functions

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. We define this property, called `ae_measurable f μ`. It's properties are discussed in
`measure_theory.measure_space`.
-/


variable {m : MeasurableSpace α} [MeasurableSpace β] {f g : α → β} {μ ν : Measure α}

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic measure_theory.volume_tac -/
#print AEMeasurable /-
/-- A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. -/
def AEMeasurable {m : MeasurableSpace α} (f : α → β)
    (μ : Measure α := by
      run_tac
        measure_theory.volume_tac) :
    Prop :=
  ∃ g : α → β, Measurable g ∧ f =ᵐ[μ] g
#align ae_measurable AEMeasurable
-/

/- warning: measurable.ae_measurable -> Measurable.aemeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m}, (Measurable.{u1, u2} α β m _inst_1 f) -> (AEMeasurable.{u1, u2} α β _inst_1 m f μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m}, (Measurable.{u2, u1} α β m _inst_1 f) -> (AEMeasurable.{u2, u1} α β _inst_1 m f μ)
Case conversion may be inaccurate. Consider using '#align measurable.ae_measurable Measurable.aemeasurableₓ'. -/
theorem Measurable.aemeasurable (h : Measurable f) : AEMeasurable f μ :=
  ⟨f, h, ae_eq_refl f⟩
#align measurable.ae_measurable Measurable.aemeasurable

namespace AEMeasurable

#print AEMeasurable.mk /-
/-- Given an almost everywhere measurable function `f`, associate to it a measurable function
that coincides with it almost everywhere. `f` is explicit in the definition to make sure that
it shows in pretty-printing. -/
def mk (f : α → β) (h : AEMeasurable f μ) : α → β :=
  Classical.choose h
#align ae_measurable.mk AEMeasurable.mk
-/

/- warning: ae_measurable.measurable_mk -> AEMeasurable.measurable_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m} (h : AEMeasurable.{u1, u2} α β _inst_1 m f μ), Measurable.{u1, u2} α β m _inst_1 (AEMeasurable.mk.{u1, u2} α β m _inst_1 μ f h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m} (h : AEMeasurable.{u2, u1} α β _inst_1 m f μ), Measurable.{u2, u1} α β m _inst_1 (AEMeasurable.mk.{u2, u1} α β m _inst_1 μ f h)
Case conversion may be inaccurate. Consider using '#align ae_measurable.measurable_mk AEMeasurable.measurable_mkₓ'. -/
theorem measurable_mk (h : AEMeasurable f μ) : Measurable (h.mk f) :=
  (Classical.choose_spec h).1
#align ae_measurable.measurable_mk AEMeasurable.measurable_mk

/- warning: ae_measurable.ae_eq_mk -> AEMeasurable.ae_eq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m} (h : AEMeasurable.{u1, u2} α β _inst_1 m f μ), Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m μ) f (AEMeasurable.mk.{u1, u2} α β m _inst_1 μ f h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m} (h : AEMeasurable.{u2, u1} α β _inst_1 m f μ), Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α m μ) f (AEMeasurable.mk.{u2, u1} α β m _inst_1 μ f h)
Case conversion may be inaccurate. Consider using '#align ae_measurable.ae_eq_mk AEMeasurable.ae_eq_mkₓ'. -/
theorem ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f :=
  (Classical.choose_spec h).2
#align ae_measurable.ae_eq_mk AEMeasurable.ae_eq_mk

/- warning: ae_measurable.congr -> AEMeasurable.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {g : α -> β} {μ : MeasureTheory.Measure.{u1} α m}, (AEMeasurable.{u1, u2} α β _inst_1 m f μ) -> (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m μ) f g) -> (AEMeasurable.{u1, u2} α β _inst_1 m g μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {g : α -> β} {μ : MeasureTheory.Measure.{u2} α m}, (AEMeasurable.{u2, u1} α β _inst_1 m f μ) -> (Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α m μ) f g) -> (AEMeasurable.{u2, u1} α β _inst_1 m g μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.congr AEMeasurable.congrₓ'. -/
theorem congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMeasurable g μ :=
  ⟨hf.mk f, hf.measurable_mk, h.symm.trans hf.ae_eq_mk⟩
#align ae_measurable.congr AEMeasurable.congr

end AEMeasurable

/- warning: ae_measurable_congr -> aemeasurable_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {g : α -> β} {μ : MeasureTheory.Measure.{u1} α m}, (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m μ) f g) -> (Iff (AEMeasurable.{u1, u2} α β _inst_1 m f μ) (AEMeasurable.{u1, u2} α β _inst_1 m g μ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {g : α -> β} {μ : MeasureTheory.Measure.{u2} α m}, (Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α m μ) f g) -> (Iff (AEMeasurable.{u2, u1} α β _inst_1 m f μ) (AEMeasurable.{u2, u1} α β _inst_1 m g μ))
Case conversion may be inaccurate. Consider using '#align ae_measurable_congr aemeasurable_congrₓ'. -/
theorem aemeasurable_congr (h : f =ᵐ[μ] g) : AEMeasurable f μ ↔ AEMeasurable g μ :=
  ⟨fun hf => AEMeasurable.congr hf h, fun hg => AEMeasurable.congr hg h.symm⟩
#align ae_measurable_congr aemeasurable_congr

/- warning: ae_measurable_const -> aemeasurable_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {μ : MeasureTheory.Measure.{u1} α m} {b : β}, AEMeasurable.{u1, u2} α β _inst_1 m (fun (a : α) => b) μ
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {μ : MeasureTheory.Measure.{u2} α m} {b : β}, AEMeasurable.{u2, u1} α β _inst_1 m (fun (a : α) => b) μ
Case conversion may be inaccurate. Consider using '#align ae_measurable_const aemeasurable_constₓ'. -/
@[simp]
theorem aemeasurable_const {b : β} : AEMeasurable (fun a : α => b) μ :=
  measurable_const.AEMeasurable
#align ae_measurable_const aemeasurable_const

#print aemeasurable_id /-
theorem aemeasurable_id : AEMeasurable id μ :=
  measurable_id.AEMeasurable
#align ae_measurable_id aemeasurable_id
-/

#print aemeasurable_id' /-
theorem aemeasurable_id' : AEMeasurable (fun x => x) μ :=
  measurable_id.AEMeasurable
#align ae_measurable_id' aemeasurable_id'
-/

#print Measurable.comp_aemeasurable /-
theorem Measurable.comp_aemeasurable [MeasurableSpace δ] {f : α → δ} {g : δ → β} (hg : Measurable g)
    (hf : AEMeasurable f μ) : AEMeasurable (g ∘ f) μ :=
  ⟨g ∘ hf.mk f, hg.comp hf.measurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk _⟩
#align measurable.comp_ae_measurable Measurable.comp_aemeasurable
-/

end

