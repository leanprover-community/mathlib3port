/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.measure.open_pos
! leanprover-community/mathlib commit 781cb2eed038c4caf53bdbd8d20a95e5822d77df
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.MeasureSpace

/-!
# Measures positive on nonempty opens

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define a typeclass for measures that are positive on nonempty opens, see
`measure_theory.measure.is_open_pos_measure`. Examples include (additive) Haar measures, as well as
measures that have positive density with respect to a Haar measure. We also prove some basic facts
about these measures.

-/


open Topology ENNReal MeasureTheory

open Set Function Filter

namespace MeasureTheory

namespace Measure

section Basic

variable {X Y : Type _} [TopologicalSpace X] {m : MeasurableSpace X} [TopologicalSpace Y]
  [T2Space Y] (μ ν : Measure X)

#print MeasureTheory.Measure.OpenPosMeasure /-
/-- A measure is said to be `is_open_pos_measure` if it is positive on nonempty open sets. -/
class OpenPosMeasure : Prop where
  open_pos : ∀ U : Set X, IsOpen U → U.Nonempty → μ U ≠ 0
#align measure_theory.measure.is_open_pos_measure MeasureTheory.Measure.OpenPosMeasure
-/

variable [OpenPosMeasure μ] {s U : Set X} {x : X}

/- warning: is_open.measure_ne_zero -> IsOpen.measure_ne_zero is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {U : Set.{u1} X}, (IsOpen.{u1} X _inst_1 U) -> (Set.Nonempty.{u1} X U) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ U) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {U : Set.{u1} X}, (IsOpen.{u1} X _inst_1 U) -> (Set.Nonempty.{u1} X U) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) U) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align is_open.measure_ne_zero IsOpen.measure_ne_zeroₓ'. -/
theorem IsOpen.measure_ne_zero (hU : IsOpen U) (hne : U.Nonempty) : μ U ≠ 0 :=
  OpenPosMeasure.open_pos U hU hne
#align is_open.measure_ne_zero IsOpen.measure_ne_zero

/- warning: is_open.measure_pos -> IsOpen.measure_pos is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {U : Set.{u1} X}, (IsOpen.{u1} X _inst_1 U) -> (Set.Nonempty.{u1} X U) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ U))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {U : Set.{u1} X}, (IsOpen.{u1} X _inst_1 U) -> (Set.Nonempty.{u1} X U) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) U))
Case conversion may be inaccurate. Consider using '#align is_open.measure_pos IsOpen.measure_posₓ'. -/
theorem IsOpen.measure_pos (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U :=
  (hU.measure_ne_zero μ hne).bot_lt
#align is_open.measure_pos IsOpen.measure_pos

/- warning: is_open.measure_pos_iff -> IsOpen.measure_pos_iff is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {U : Set.{u1} X}, (IsOpen.{u1} X _inst_1 U) -> (Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ U)) (Set.Nonempty.{u1} X U))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {U : Set.{u1} X}, (IsOpen.{u1} X _inst_1 U) -> (Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) U)) (Set.Nonempty.{u1} X U))
Case conversion may be inaccurate. Consider using '#align is_open.measure_pos_iff IsOpen.measure_pos_iffₓ'. -/
theorem IsOpen.measure_pos_iff (hU : IsOpen U) : 0 < μ U ↔ U.Nonempty :=
  ⟨fun h => nonempty_iff_ne_empty.2 fun he => h.ne' <| he.symm ▸ measure_empty, hU.measure_pos μ⟩
#align is_open.measure_pos_iff IsOpen.measure_pos_iff

/- warning: is_open.measure_eq_zero_iff -> IsOpen.measure_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {U : Set.{u1} X}, (IsOpen.{u1} X _inst_1 U) -> (Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ U) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{succ u1} (Set.{u1} X) U (EmptyCollection.emptyCollection.{u1} (Set.{u1} X) (Set.hasEmptyc.{u1} X))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {U : Set.{u1} X}, (IsOpen.{u1} X _inst_1 U) -> (Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) U) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{succ u1} (Set.{u1} X) U (EmptyCollection.emptyCollection.{u1} (Set.{u1} X) (Set.instEmptyCollectionSet.{u1} X))))
Case conversion may be inaccurate. Consider using '#align is_open.measure_eq_zero_iff IsOpen.measure_eq_zero_iffₓ'. -/
theorem IsOpen.measure_eq_zero_iff (hU : IsOpen U) : μ U = 0 ↔ U = ∅ := by
  simpa only [not_lt, nonpos_iff_eq_zero, not_nonempty_iff_eq_empty] using
    not_congr (hU.measure_pos_iff μ)
#align is_open.measure_eq_zero_iff IsOpen.measure_eq_zero_iff

/- warning: measure_theory.measure.measure_pos_of_nonempty_interior -> MeasureTheory.Measure.measure_pos_of_nonempty_interior is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {s : Set.{u1} X}, (Set.Nonempty.{u1} X (interior.{u1} X _inst_1 s)) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ s))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {s : Set.{u1} X}, (Set.Nonempty.{u1} X (interior.{u1} X _inst_1 s)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) s))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.measure_pos_of_nonempty_interior MeasureTheory.Measure.measure_pos_of_nonempty_interiorₓ'. -/
theorem measure_pos_of_nonempty_interior (h : (interior s).Nonempty) : 0 < μ s :=
  (isOpen_interior.measure_pos μ h).trans_le (measure_mono interior_subset)
#align measure_theory.measure.measure_pos_of_nonempty_interior MeasureTheory.Measure.measure_pos_of_nonempty_interior

/- warning: measure_theory.measure.measure_pos_of_mem_nhds -> MeasureTheory.Measure.measure_pos_of_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {s : Set.{u1} X} {x : X}, (Membership.Mem.{u1, u1} (Set.{u1} X) (Filter.{u1} X) (Filter.hasMem.{u1} X) s (nhds.{u1} X _inst_1 x)) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ s))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {s : Set.{u1} X} {x : X}, (Membership.mem.{u1, u1} (Set.{u1} X) (Filter.{u1} X) (instMembershipSetFilter.{u1} X) s (nhds.{u1} X _inst_1 x)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) s))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.measure_pos_of_mem_nhds MeasureTheory.Measure.measure_pos_of_mem_nhdsₓ'. -/
theorem measure_pos_of_mem_nhds (h : s ∈ 𝓝 x) : 0 < μ s :=
  measure_pos_of_nonempty_interior _ ⟨x, mem_interior_iff_mem_nhds.2 h⟩
#align measure_theory.measure.measure_pos_of_mem_nhds MeasureTheory.Measure.measure_pos_of_mem_nhds

/- warning: measure_theory.measure.is_open_pos_measure_smul -> MeasureTheory.Measure.openPosMeasure_smul is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {c : ENNReal}, (Ne.{1} ENNReal c (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m (SMul.smul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} X m) (MeasureTheory.Measure.instSMul.{u1, 0} X ENNReal (SMulZeroClass.toHasSmul.{0, 0} ENNReal ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (SMulWithZero.toSmulZeroClass.{0, 0} ENNReal ENNReal (MulZeroClass.toHasZero.{0} ENNReal (MulZeroOneClass.toMulZeroClass.{0} ENNReal (MonoidWithZero.toMulZeroOneClass.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (MulActionWithZero.toSMulWithZero.{0, 0} ENNReal ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (Module.toMulActionWithZero.{0, 0} ENNReal ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Algebra.toModule.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) m) c μ))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {c : ENNReal}, (Ne.{1} ENNReal c (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m (HSMul.hSMul.{0, u1, u1} ENNReal (MeasureTheory.Measure.{u1} X m) (MeasureTheory.Measure.{u1} X m) (instHSMul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} X m) (MeasureTheory.Measure.instSMul.{u1, 0} X ENNReal (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) m)) c μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.is_open_pos_measure_smul MeasureTheory.Measure.openPosMeasure_smulₓ'. -/
theorem openPosMeasure_smul {c : ℝ≥0∞} (h : c ≠ 0) : OpenPosMeasure (c • μ) :=
  ⟨fun U Uo Une => mul_ne_zero h (Uo.measure_ne_zero μ Une)⟩
#align measure_theory.measure.is_open_pos_measure_smul MeasureTheory.Measure.openPosMeasure_smul

variable {μ ν}

#print MeasureTheory.Measure.AbsolutelyContinuous.openPosMeasure /-
protected theorem AbsolutelyContinuous.openPosMeasure (h : μ ≪ ν) : OpenPosMeasure ν :=
  ⟨fun U ho hne h₀ => ho.measure_ne_zero μ hne (h h₀)⟩
#align measure_theory.measure.absolutely_continuous.is_open_pos_measure MeasureTheory.Measure.AbsolutelyContinuous.openPosMeasure
-/

/- warning: has_le.le.is_open_pos_measure -> LE.le.isOpenPosMeasure is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} {μ : MeasureTheory.Measure.{u1} X m} {ν : MeasureTheory.Measure.{u1} X m} [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ], (LE.le.{u1} (MeasureTheory.Measure.{u1} X m) (Preorder.toHasLe.{u1} (MeasureTheory.Measure.{u1} X m) (PartialOrder.toPreorder.{u1} (MeasureTheory.Measure.{u1} X m) (MeasureTheory.Measure.instPartialOrder.{u1} X m))) μ ν) -> (MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m ν)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} {μ : MeasureTheory.Measure.{u1} X m} {ν : MeasureTheory.Measure.{u1} X m} [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ], (LE.le.{u1} (MeasureTheory.Measure.{u1} X m) (Preorder.toLE.{u1} (MeasureTheory.Measure.{u1} X m) (PartialOrder.toPreorder.{u1} (MeasureTheory.Measure.{u1} X m) (MeasureTheory.Measure.instPartialOrder.{u1} X m))) μ ν) -> (MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m ν)
Case conversion may be inaccurate. Consider using '#align has_le.le.is_open_pos_measure LE.le.isOpenPosMeasureₓ'. -/
theorem LE.le.isOpenPosMeasure (h : μ ≤ ν) : OpenPosMeasure ν :=
  h.AbsolutelyContinuous.OpenPosMeasure
#align has_le.le.is_open_pos_measure LE.le.isOpenPosMeasure

/- warning: is_open.eq_empty_of_measure_zero -> IsOpen.eq_empty_of_measure_zero is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} {μ : MeasureTheory.Measure.{u1} X m} [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {U : Set.{u1} X}, (IsOpen.{u1} X _inst_1 U) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ U) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{succ u1} (Set.{u1} X) U (EmptyCollection.emptyCollection.{u1} (Set.{u1} X) (Set.hasEmptyc.{u1} X)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} {μ : MeasureTheory.Measure.{u1} X m} [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {U : Set.{u1} X}, (IsOpen.{u1} X _inst_1 U) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) U) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{succ u1} (Set.{u1} X) U (EmptyCollection.emptyCollection.{u1} (Set.{u1} X) (Set.instEmptyCollectionSet.{u1} X)))
Case conversion may be inaccurate. Consider using '#align is_open.eq_empty_of_measure_zero IsOpen.eq_empty_of_measure_zeroₓ'. -/
theorem IsOpen.eq_empty_of_measure_zero (hU : IsOpen U) (h₀ : μ U = 0) : U = ∅ :=
  (hU.measure_eq_zero_iff μ).mp h₀
#align is_open.eq_empty_of_measure_zero IsOpen.eq_empty_of_measure_zero

/- warning: measure_theory.measure.interior_eq_empty_of_null -> MeasureTheory.Measure.interior_eq_empty_of_null is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} {μ : MeasureTheory.Measure.{u1} X m} [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {s : Set.{u1} X}, (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{succ u1} (Set.{u1} X) (interior.{u1} X _inst_1 s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} X) (Set.hasEmptyc.{u1} X)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} {μ : MeasureTheory.Measure.{u1} X m} [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {s : Set.{u1} X}, (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{succ u1} (Set.{u1} X) (interior.{u1} X _inst_1 s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} X) (Set.instEmptyCollectionSet.{u1} X)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.interior_eq_empty_of_null MeasureTheory.Measure.interior_eq_empty_of_nullₓ'. -/
theorem interior_eq_empty_of_null (hs : μ s = 0) : interior s = ∅ :=
  isOpen_interior.eq_empty_of_measure_zero <| measure_mono_null interior_subset hs
#align measure_theory.measure.interior_eq_empty_of_null MeasureTheory.Measure.interior_eq_empty_of_null

/- warning: measure_theory.measure.eq_on_open_of_ae_eq -> MeasureTheory.Measure.eqOn_open_of_ae_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : T2Space.{u2} Y _inst_2] {μ : MeasureTheory.Measure.{u1} X m} [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {U : Set.{u1} X} {f : X -> Y} {g : X -> Y}, (Filter.EventuallyEq.{u1, u2} X Y (MeasureTheory.Measure.ae.{u1} X m (MeasureTheory.Measure.restrict.{u1} X m μ U)) f g) -> (IsOpen.{u1} X _inst_1 U) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_2 f U) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_2 g U) -> (Set.EqOn.{u1, u2} X Y f g U)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {m : MeasurableSpace.{u2} X} [_inst_2 : TopologicalSpace.{u1} Y] [_inst_3 : T2Space.{u1} Y _inst_2] {μ : MeasureTheory.Measure.{u2} X m} [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u2} X _inst_1 m μ] {U : Set.{u2} X} {f : X -> Y} {g : X -> Y}, (Filter.EventuallyEq.{u2, u1} X Y (MeasureTheory.Measure.ae.{u2} X m (MeasureTheory.Measure.restrict.{u2} X m μ U)) f g) -> (IsOpen.{u2} X _inst_1 U) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 f U) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 g U) -> (Set.EqOn.{u2, u1} X Y f g U)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.eq_on_open_of_ae_eq MeasureTheory.Measure.eqOn_open_of_ae_eqₓ'. -/
/-- If two functions are a.e. equal on an open set and are continuous on this set, then they are
equal on this set. -/
theorem eqOn_open_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ.restrict U] g) (hU : IsOpen U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) : EqOn f g U :=
  by
  replace h := ae_imp_of_ae_restrict h
  simp only [eventually_eq, ae_iff, not_imp] at h
  have : IsOpen (U ∩ { a | f a ≠ g a }) :=
    by
    refine' is_open_iff_mem_nhds.mpr fun a ha => inter_mem (hU.mem_nhds ha.1) _
    rcases ha with ⟨ha : a ∈ U, ha' : (f a, g a) ∈ diagonal Yᶜ⟩
    exact
      (hf.continuous_at (hU.mem_nhds ha)).prod_mk_nhds (hg.continuous_at (hU.mem_nhds ha))
        (is_closed_diagonal.is_open_compl.mem_nhds ha')
  replace := (this.eq_empty_of_measure_zero h).le
  exact fun x hx => Classical.not_not.1 fun h => this ⟨hx, h⟩
#align measure_theory.measure.eq_on_open_of_ae_eq MeasureTheory.Measure.eqOn_open_of_ae_eq

/- warning: measure_theory.measure.eq_of_ae_eq -> MeasureTheory.Measure.eq_of_ae_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : T2Space.{u2} Y _inst_2] {μ : MeasureTheory.Measure.{u1} X m} [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {f : X -> Y} {g : X -> Y}, (Filter.EventuallyEq.{u1, u2} X Y (MeasureTheory.Measure.ae.{u1} X m μ) f g) -> (Continuous.{u1, u2} X Y _inst_1 _inst_2 f) -> (Continuous.{u1, u2} X Y _inst_1 _inst_2 g) -> (Eq.{max (succ u1) (succ u2)} (X -> Y) f g)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {m : MeasurableSpace.{u2} X} [_inst_2 : TopologicalSpace.{u1} Y] [_inst_3 : T2Space.{u1} Y _inst_2] {μ : MeasureTheory.Measure.{u2} X m} [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u2} X _inst_1 m μ] {f : X -> Y} {g : X -> Y}, (Filter.EventuallyEq.{u2, u1} X Y (MeasureTheory.Measure.ae.{u2} X m μ) f g) -> (Continuous.{u2, u1} X Y _inst_1 _inst_2 f) -> (Continuous.{u2, u1} X Y _inst_1 _inst_2 g) -> (Eq.{max (succ u2) (succ u1)} (X -> Y) f g)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.eq_of_ae_eq MeasureTheory.Measure.eq_of_ae_eqₓ'. -/
/-- If two continuous functions are a.e. equal, then they are equal. -/
theorem eq_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ] g) (hf : Continuous f) (hg : Continuous g) : f = g :=
  suffices EqOn f g univ from funext fun x => this trivial
  eqOn_open_of_ae_eq (ae_restrict_of_ae h) isOpen_univ hf.ContinuousOn hg.ContinuousOn
#align measure_theory.measure.eq_of_ae_eq MeasureTheory.Measure.eq_of_ae_eq

/- warning: measure_theory.measure.eq_on_of_ae_eq -> MeasureTheory.Measure.eqOn_of_ae_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : T2Space.{u2} Y _inst_2] {μ : MeasureTheory.Measure.{u1} X m} [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {s : Set.{u1} X} {f : X -> Y} {g : X -> Y}, (Filter.EventuallyEq.{u1, u2} X Y (MeasureTheory.Measure.ae.{u1} X m (MeasureTheory.Measure.restrict.{u1} X m μ s)) f g) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_2 f s) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_2 g s) -> (HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) s (closure.{u1} X _inst_1 (interior.{u1} X _inst_1 s))) -> (Set.EqOn.{u1, u2} X Y f g s)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {m : MeasurableSpace.{u2} X} [_inst_2 : TopologicalSpace.{u1} Y] [_inst_3 : T2Space.{u1} Y _inst_2] {μ : MeasureTheory.Measure.{u2} X m} [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u2} X _inst_1 m μ] {s : Set.{u2} X} {f : X -> Y} {g : X -> Y}, (Filter.EventuallyEq.{u2, u1} X Y (MeasureTheory.Measure.ae.{u2} X m (MeasureTheory.Measure.restrict.{u2} X m μ s)) f g) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 f s) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 g s) -> (HasSubset.Subset.{u2} (Set.{u2} X) (Set.instHasSubsetSet.{u2} X) s (closure.{u2} X _inst_1 (interior.{u2} X _inst_1 s))) -> (Set.EqOn.{u2, u1} X Y f g s)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.eq_on_of_ae_eq MeasureTheory.Measure.eqOn_of_ae_eqₓ'. -/
theorem eqOn_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ.restrict s] g) (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) (hU : s ⊆ closure (interior s)) : EqOn f g s :=
  have : interior s ⊆ s := interior_subset
  (eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset this h) isOpen_interior (hf.mono this)
        (hg.mono this)).of_subset_closure
    hf hg this hU
#align measure_theory.measure.eq_on_of_ae_eq MeasureTheory.Measure.eqOn_of_ae_eq

variable (μ)

/- warning: continuous.ae_eq_iff_eq -> Continuous.ae_eq_iff_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {m : MeasurableSpace.{u1} X} [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : T2Space.{u2} Y _inst_2] (μ : MeasureTheory.Measure.{u1} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {f : X -> Y} {g : X -> Y}, (Continuous.{u1, u2} X Y _inst_1 _inst_2 f) -> (Continuous.{u1, u2} X Y _inst_1 _inst_2 g) -> (Iff (Filter.EventuallyEq.{u1, u2} X Y (MeasureTheory.Measure.ae.{u1} X m μ) f g) (Eq.{max (succ u1) (succ u2)} (X -> Y) f g))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {m : MeasurableSpace.{u2} X} [_inst_2 : TopologicalSpace.{u1} Y] [_inst_3 : T2Space.{u1} Y _inst_2] (μ : MeasureTheory.Measure.{u2} X m) [_inst_4 : MeasureTheory.Measure.OpenPosMeasure.{u2} X _inst_1 m μ] {f : X -> Y} {g : X -> Y}, (Continuous.{u2, u1} X Y _inst_1 _inst_2 f) -> (Continuous.{u2, u1} X Y _inst_1 _inst_2 g) -> (Iff (Filter.EventuallyEq.{u2, u1} X Y (MeasureTheory.Measure.ae.{u2} X m μ) f g) (Eq.{max (succ u2) (succ u1)} (X -> Y) f g))
Case conversion may be inaccurate. Consider using '#align continuous.ae_eq_iff_eq Continuous.ae_eq_iff_eqₓ'. -/
theorem Continuous.ae_eq_iff_eq {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
    f =ᵐ[μ] g ↔ f = g :=
  ⟨fun h => eq_of_ae_eq h hf hg, fun h => h ▸ EventuallyEq.rfl⟩
#align continuous.ae_eq_iff_eq Continuous.ae_eq_iff_eq

end Basic

section LinearOrder

variable {X Y : Type _} [TopologicalSpace X] [LinearOrder X] [OrderTopology X]
  {m : MeasurableSpace X} [TopologicalSpace Y] [T2Space Y] (μ : Measure X) [OpenPosMeasure μ]

/- warning: measure_theory.measure.measure_Ioi_pos -> MeasureTheory.Measure.measure_Ioi_pos is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : LinearOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2))))] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] [_inst_7 : NoMaxOrder.{u1} X (Preorder.toHasLt.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))))] (a : X), LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ (Set.Ioi.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : LinearOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2)))))] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] [_inst_7 : NoMaxOrder.{u1} X (Preorder.toLT.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2))))))] (a : X), LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) (Set.Ioi.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2))))) a))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.measure_Ioi_pos MeasureTheory.Measure.measure_Ioi_posₓ'. -/
theorem measure_Ioi_pos [NoMaxOrder X] (a : X) : 0 < μ (Ioi a) :=
  isOpen_Ioi.measure_pos μ nonempty_Ioi
#align measure_theory.measure.measure_Ioi_pos MeasureTheory.Measure.measure_Ioi_pos

/- warning: measure_theory.measure.measure_Iio_pos -> MeasureTheory.Measure.measure_Iio_pos is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : LinearOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2))))] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] [_inst_7 : NoMinOrder.{u1} X (Preorder.toHasLt.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))))] (a : X), LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ (Set.Iio.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : LinearOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2)))))] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] [_inst_7 : NoMinOrder.{u1} X (Preorder.toLT.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2))))))] (a : X), LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) (Set.Iio.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2))))) a))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.measure_Iio_pos MeasureTheory.Measure.measure_Iio_posₓ'. -/
theorem measure_Iio_pos [NoMinOrder X] (a : X) : 0 < μ (Iio a) :=
  isOpen_Iio.measure_pos μ nonempty_Iio
#align measure_theory.measure.measure_Iio_pos MeasureTheory.Measure.measure_Iio_pos

/- warning: measure_theory.measure.measure_Ioo_pos -> MeasureTheory.Measure.measure_Ioo_pos is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : LinearOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2))))] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] [_inst_7 : DenselyOrdered.{u1} X (Preorder.toHasLt.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))))] {a : X} {b : X}, Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ (Set.Ioo.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b))) (LT.lt.{u1} X (Preorder.toHasLt.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2))))) a b)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : LinearOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2)))))] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] [_inst_7 : DenselyOrdered.{u1} X (Preorder.toLT.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2))))))] {a : X} {b : X}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) (Set.Ioo.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2))))) a b))) (LT.lt.{u1} X (Preorder.toLT.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2)))))) a b)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.measure_Ioo_pos MeasureTheory.Measure.measure_Ioo_posₓ'. -/
theorem measure_Ioo_pos [DenselyOrdered X] {a b : X} : 0 < μ (Ioo a b) ↔ a < b :=
  (isOpen_Ioo.measure_pos_iff μ).trans nonempty_Ioo
#align measure_theory.measure.measure_Ioo_pos MeasureTheory.Measure.measure_Ioo_pos

/- warning: measure_theory.measure.measure_Ioo_eq_zero -> MeasureTheory.Measure.measure_Ioo_eq_zero is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : LinearOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2))))] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] [_inst_7 : DenselyOrdered.{u1} X (Preorder.toHasLt.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))))] {a : X} {b : X}, Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ (Set.Ioo.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (LE.le.{u1} X (Preorder.toHasLe.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2))))) b a)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : LinearOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2)))))] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] [_inst_7 : DenselyOrdered.{u1} X (Preorder.toLT.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2))))))] {a : X} {b : X}, Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) (Set.Ioo.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2))))) a b)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (LE.le.{u1} X (Preorder.toLE.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (DistribLattice.toLattice.{u1} X (instDistribLattice.{u1} X _inst_2)))))) b a)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.measure_Ioo_eq_zero MeasureTheory.Measure.measure_Ioo_eq_zeroₓ'. -/
theorem measure_Ioo_eq_zero [DenselyOrdered X] {a b : X} : μ (Ioo a b) = 0 ↔ b ≤ a :=
  (isOpen_Ioo.measure_eq_zero_iff μ).trans (Ioo_eq_empty_iff.trans not_lt)
#align measure_theory.measure.measure_Ioo_eq_zero MeasureTheory.Measure.measure_Ioo_eq_zero

/- warning: measure_theory.measure.eq_on_Ioo_of_ae_eq -> MeasureTheory.Measure.eqOn_Ioo_of_ae_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : LinearOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2))))] {m : MeasurableSpace.{u1} X} [_inst_4 : TopologicalSpace.{u2} Y] [_inst_5 : T2Space.{u2} Y _inst_4] (μ : MeasureTheory.Measure.{u1} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] {a : X} {b : X} {f : X -> Y} {g : X -> Y}, (Filter.EventuallyEq.{u1, u2} X Y (MeasureTheory.Measure.ae.{u1} X m (MeasureTheory.Measure.restrict.{u1} X m μ (Set.Ioo.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b))) f g) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_4 f (Set.Ioo.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b)) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_4 g (Set.Ioo.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b)) -> (Set.EqOn.{u1, u2} X Y f g (Set.Ioo.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : LinearOrder.{u2} X] [_inst_3 : OrderTopology.{u2} X _inst_1 (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2)))))] {m : MeasurableSpace.{u2} X} [_inst_4 : TopologicalSpace.{u1} Y] [_inst_5 : T2Space.{u1} Y _inst_4] (μ : MeasureTheory.Measure.{u2} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u2} X _inst_1 m μ] {a : X} {b : X} {f : X -> Y} {g : X -> Y}, (Filter.EventuallyEq.{u2, u1} X Y (MeasureTheory.Measure.ae.{u2} X m (MeasureTheory.Measure.restrict.{u2} X m μ (Set.Ioo.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))) a b))) f g) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_4 f (Set.Ioo.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))) a b)) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_4 g (Set.Ioo.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))) a b)) -> (Set.EqOn.{u2, u1} X Y f g (Set.Ioo.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))) a b))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.eq_on_Ioo_of_ae_eq MeasureTheory.Measure.eqOn_Ioo_of_ae_eqₓ'. -/
theorem eqOn_Ioo_of_ae_eq {a b : X} {f g : X → Y} (hfg : f =ᵐ[μ.restrict (Ioo a b)] g)
    (hf : ContinuousOn f (Ioo a b)) (hg : ContinuousOn g (Ioo a b)) : EqOn f g (Ioo a b) :=
  eqOn_of_ae_eq hfg hf hg Ioo_subset_closure_interior
#align measure_theory.measure.eq_on_Ioo_of_ae_eq MeasureTheory.Measure.eqOn_Ioo_of_ae_eq

/- warning: measure_theory.measure.eq_on_Ioc_of_ae_eq -> MeasureTheory.Measure.eqOn_Ioc_of_ae_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : LinearOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2))))] {m : MeasurableSpace.{u1} X} [_inst_4 : TopologicalSpace.{u2} Y] [_inst_5 : T2Space.{u2} Y _inst_4] (μ : MeasureTheory.Measure.{u1} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] [_inst_7 : DenselyOrdered.{u1} X (Preorder.toHasLt.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))))] {a : X} {b : X} {f : X -> Y} {g : X -> Y}, (Filter.EventuallyEq.{u1, u2} X Y (MeasureTheory.Measure.ae.{u1} X m (MeasureTheory.Measure.restrict.{u1} X m μ (Set.Ioc.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b))) f g) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_4 f (Set.Ioc.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b)) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_4 g (Set.Ioc.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b)) -> (Set.EqOn.{u1, u2} X Y f g (Set.Ioc.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : LinearOrder.{u2} X] [_inst_3 : OrderTopology.{u2} X _inst_1 (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2)))))] {m : MeasurableSpace.{u2} X} [_inst_4 : TopologicalSpace.{u1} Y] [_inst_5 : T2Space.{u1} Y _inst_4] (μ : MeasureTheory.Measure.{u2} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u2} X _inst_1 m μ] [_inst_7 : DenselyOrdered.{u2} X (Preorder.toLT.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))))] {a : X} {b : X} {f : X -> Y} {g : X -> Y}, (Filter.EventuallyEq.{u2, u1} X Y (MeasureTheory.Measure.ae.{u2} X m (MeasureTheory.Measure.restrict.{u2} X m μ (Set.Ioc.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))) a b))) f g) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_4 f (Set.Ioc.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))) a b)) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_4 g (Set.Ioc.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))) a b)) -> (Set.EqOn.{u2, u1} X Y f g (Set.Ioc.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))) a b))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.eq_on_Ioc_of_ae_eq MeasureTheory.Measure.eqOn_Ioc_of_ae_eqₓ'. -/
theorem eqOn_Ioc_of_ae_eq [DenselyOrdered X] {a b : X} {f g : X → Y}
    (hfg : f =ᵐ[μ.restrict (Ioc a b)] g) (hf : ContinuousOn f (Ioc a b))
    (hg : ContinuousOn g (Ioc a b)) : EqOn f g (Ioc a b) :=
  eqOn_of_ae_eq hfg hf hg (Ioc_subset_closure_interior _ _)
#align measure_theory.measure.eq_on_Ioc_of_ae_eq MeasureTheory.Measure.eqOn_Ioc_of_ae_eq

/- warning: measure_theory.measure.eq_on_Ico_of_ae_eq -> MeasureTheory.Measure.eqOn_Ico_of_ae_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : LinearOrder.{u1} X] [_inst_3 : OrderTopology.{u1} X _inst_1 (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2))))] {m : MeasurableSpace.{u1} X} [_inst_4 : TopologicalSpace.{u2} Y] [_inst_5 : T2Space.{u2} Y _inst_4] (μ : MeasureTheory.Measure.{u1} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u1} X _inst_1 m μ] [_inst_7 : DenselyOrdered.{u1} X (Preorder.toHasLt.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))))] {a : X} {b : X} {f : X -> Y} {g : X -> Y}, (Filter.EventuallyEq.{u1, u2} X Y (MeasureTheory.Measure.ae.{u1} X m (MeasureTheory.Measure.restrict.{u1} X m μ (Set.Ico.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b))) f g) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_4 f (Set.Ico.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b)) -> (ContinuousOn.{u1, u2} X Y _inst_1 _inst_4 g (Set.Ico.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b)) -> (Set.EqOn.{u1, u2} X Y f g (Set.Ico.{u1} X (PartialOrder.toPreorder.{u1} X (SemilatticeInf.toPartialOrder.{u1} X (Lattice.toSemilatticeInf.{u1} X (LinearOrder.toLattice.{u1} X _inst_2)))) a b))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : LinearOrder.{u2} X] [_inst_3 : OrderTopology.{u2} X _inst_1 (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2)))))] {m : MeasurableSpace.{u2} X} [_inst_4 : TopologicalSpace.{u1} Y] [_inst_5 : T2Space.{u1} Y _inst_4] (μ : MeasureTheory.Measure.{u2} X m) [_inst_6 : MeasureTheory.Measure.OpenPosMeasure.{u2} X _inst_1 m μ] [_inst_7 : DenselyOrdered.{u2} X (Preorder.toLT.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))))] {a : X} {b : X} {f : X -> Y} {g : X -> Y}, (Filter.EventuallyEq.{u2, u1} X Y (MeasureTheory.Measure.ae.{u2} X m (MeasureTheory.Measure.restrict.{u2} X m μ (Set.Ico.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))) a b))) f g) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_4 f (Set.Ico.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))) a b)) -> (ContinuousOn.{u2, u1} X Y _inst_1 _inst_4 g (Set.Ico.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))) a b)) -> (Set.EqOn.{u2, u1} X Y f g (Set.Ico.{u2} X (PartialOrder.toPreorder.{u2} X (SemilatticeInf.toPartialOrder.{u2} X (Lattice.toSemilatticeInf.{u2} X (DistribLattice.toLattice.{u2} X (instDistribLattice.{u2} X _inst_2))))) a b))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.eq_on_Ico_of_ae_eq MeasureTheory.Measure.eqOn_Ico_of_ae_eqₓ'. -/
theorem eqOn_Ico_of_ae_eq [DenselyOrdered X] {a b : X} {f g : X → Y}
    (hfg : f =ᵐ[μ.restrict (Ico a b)] g) (hf : ContinuousOn f (Ico a b))
    (hg : ContinuousOn g (Ico a b)) : EqOn f g (Ico a b) :=
  eqOn_of_ae_eq hfg hf hg (Ico_subset_closure_interior _ _)
#align measure_theory.measure.eq_on_Ico_of_ae_eq MeasureTheory.Measure.eqOn_Ico_of_ae_eq

/- warning: measure_theory.measure.eq_on_Icc_of_ae_eq -> MeasureTheory.Measure.eqOn_Icc_of_ae_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.eq_on_Icc_of_ae_eq MeasureTheory.Measure.eqOn_Icc_of_ae_eqₓ'. -/
theorem eqOn_Icc_of_ae_eq [DenselyOrdered X] {a b : X} (hne : a ≠ b) {f g : X → Y}
    (hfg : f =ᵐ[μ.restrict (Icc a b)] g) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) : EqOn f g (Icc a b) :=
  eqOn_of_ae_eq hfg hf hg (closure_interior_Icc hne).symm.Subset
#align measure_theory.measure.eq_on_Icc_of_ae_eq MeasureTheory.Measure.eqOn_Icc_of_ae_eq

end LinearOrder

end Measure

end MeasureTheory

open MeasureTheory MeasureTheory.Measure

namespace Metric

variable {X : Type _} [PseudoMetricSpace X] {m : MeasurableSpace X} (μ : Measure X)
  [OpenPosMeasure μ]

/- warning: metric.measure_ball_pos -> Metric.measure_ball_pos is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_2 : MeasureTheory.Measure.OpenPosMeasure.{u1} X (UniformSpace.toTopologicalSpace.{u1} X (PseudoMetricSpace.toUniformSpace.{u1} X _inst_1)) m μ] (x : X) {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ (Metric.ball.{u1} X _inst_1 x r)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_2 : MeasureTheory.Measure.OpenPosMeasure.{u1} X (UniformSpace.toTopologicalSpace.{u1} X (PseudoMetricSpace.toUniformSpace.{u1} X _inst_1)) m μ] (x : X) {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) (Metric.ball.{u1} X _inst_1 x r)))
Case conversion may be inaccurate. Consider using '#align metric.measure_ball_pos Metric.measure_ball_posₓ'. -/
theorem measure_ball_pos (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ (ball x r) :=
  isOpen_ball.measure_pos μ (nonempty_ball.2 hr)
#align metric.measure_ball_pos Metric.measure_ball_pos

/- warning: metric.measure_closed_ball_pos -> Metric.measure_closedBall_pos is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_2 : MeasureTheory.Measure.OpenPosMeasure.{u1} X (UniformSpace.toTopologicalSpace.{u1} X (PseudoMetricSpace.toUniformSpace.{u1} X _inst_1)) m μ] (x : X) {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ (Metric.closedBall.{u1} X _inst_1 x r)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_2 : MeasureTheory.Measure.OpenPosMeasure.{u1} X (UniformSpace.toTopologicalSpace.{u1} X (PseudoMetricSpace.toUniformSpace.{u1} X _inst_1)) m μ] (x : X) {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) (Metric.closedBall.{u1} X _inst_1 x r)))
Case conversion may be inaccurate. Consider using '#align metric.measure_closed_ball_pos Metric.measure_closedBall_posₓ'. -/
theorem measure_closedBall_pos (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ (closedBall x r) :=
  (measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closedBall)
#align metric.measure_closed_ball_pos Metric.measure_closedBall_pos

end Metric

namespace Emetric

variable {X : Type _} [PseudoEMetricSpace X] {m : MeasurableSpace X} (μ : Measure X)
  [OpenPosMeasure μ]

/- warning: emetric.measure_ball_pos -> EMetric.measure_ball_pos is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_2 : MeasureTheory.Measure.OpenPosMeasure.{u1} X (UniformSpace.toTopologicalSpace.{u1} X (PseudoEMetricSpace.toUniformSpace.{u1} X _inst_1)) m μ] (x : X) {r : ENNReal}, (Ne.{1} ENNReal r (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ (EMetric.ball.{u1} X _inst_1 x r)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_2 : MeasureTheory.Measure.OpenPosMeasure.{u1} X (UniformSpace.toTopologicalSpace.{u1} X (PseudoEMetricSpace.toUniformSpace.{u1} X _inst_1)) m μ] (x : X) {r : ENNReal}, (Ne.{1} ENNReal r (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) (EMetric.ball.{u1} X _inst_1 x r)))
Case conversion may be inaccurate. Consider using '#align emetric.measure_ball_pos EMetric.measure_ball_posₓ'. -/
theorem measure_ball_pos (x : X) {r : ℝ≥0∞} (hr : r ≠ 0) : 0 < μ (ball x r) :=
  isOpen_ball.measure_pos μ ⟨x, mem_ball_self hr.bot_lt⟩
#align emetric.measure_ball_pos EMetric.measure_ball_pos

/- warning: emetric.measure_closed_ball_pos -> EMetric.measure_closedBall_pos is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_2 : MeasureTheory.Measure.OpenPosMeasure.{u1} X (UniformSpace.toTopologicalSpace.{u1} X (PseudoEMetricSpace.toUniformSpace.{u1} X _inst_1)) m μ] (x : X) {r : ENNReal}, (Ne.{1} ENNReal r (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} X m) (fun (_x : MeasureTheory.Measure.{u1} X m) => (Set.{u1} X) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} X m) μ (EMetric.closedBall.{u1} X _inst_1 x r)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} X] {m : MeasurableSpace.{u1} X} (μ : MeasureTheory.Measure.{u1} X m) [_inst_2 : MeasureTheory.Measure.OpenPosMeasure.{u1} X (UniformSpace.toTopologicalSpace.{u1} X (PseudoEMetricSpace.toUniformSpace.{u1} X _inst_1)) m μ] (x : X) {r : ENNReal}, (Ne.{1} ENNReal r (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} X (MeasureTheory.Measure.toOuterMeasure.{u1} X m μ) (EMetric.closedBall.{u1} X _inst_1 x r)))
Case conversion may be inaccurate. Consider using '#align emetric.measure_closed_ball_pos EMetric.measure_closedBall_posₓ'. -/
theorem measure_closedBall_pos (x : X) {r : ℝ≥0∞} (hr : r ≠ 0) : 0 < μ (closedBall x r) :=
  (measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closedBall)
#align emetric.measure_closed_ball_pos EMetric.measure_closedBall_pos

end Emetric

