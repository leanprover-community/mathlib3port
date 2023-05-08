/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.measure.ae_disjoint
! leanprover-community/mathlib commit b5ad141426bb005414324f89719c77c0aa3ec612
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Almost everywhere disjoint sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that sets `s` and `t` are `μ`-a.e. disjoint (see `measure_theory.ae_disjoint`) if their
intersection has measure zero. This assumption can be used instead of `disjoint` in most theorems in
measure theory.
-/


open Set Function

namespace MeasureTheory

variable {ι α : Type _} {m : MeasurableSpace α} (μ : Measure α)

#print MeasureTheory.AEDisjoint /-
/-- Two sets are said to be `μ`-a.e. disjoint if their intersection has measure zero. -/
def AEDisjoint (s t : Set α) :=
  μ (s ∩ t) = 0
#align measure_theory.ae_disjoint MeasureTheory.AEDisjoint
-/

variable {μ} {s t u v : Set α}

/- warning: measure_theory.exists_null_pairwise_disjoint_diff -> MeasureTheory.exists_null_pairwise_disjoint_diff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_1 : Countable.{succ u1} ι] {s : ι -> (Set.{u2} α)}, (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (MeasureTheory.AEDisjoint.{u2} α m μ) s)) -> (Exists.{max (succ u1) (succ u2)} (ι -> (Set.{u2} α)) (fun (t : ι -> (Set.{u2} α)) => And (forall (i : ι), MeasurableSet.{u2} α m (t i)) (And (forall (i : ι), Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} α m) (fun (_x : MeasureTheory.Measure.{u2} α m) => (Set.{u2} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} α m) μ (t i)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α)))) (fun (i : ι) => SDiff.sdiff.{u2} (Set.{u2} α) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α)) (s i) (t i)))))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u2} ι] {s : ι -> (Set.{u1} α)}, (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (MeasureTheory.AEDisjoint.{u1} α m μ) s)) -> (Exists.{max (succ u2) (succ u1)} (ι -> (Set.{u1} α)) (fun (t : ι -> (Set.{u1} α)) => And (forall (i : ι), MeasurableSet.{u1} α m (t i)) (And (forall (i : ι), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (t i)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (fun (i : ι) => SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (s i) (t i)))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.exists_null_pairwise_disjoint_diff MeasureTheory.exists_null_pairwise_disjoint_diffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (j «expr ≠ » i) -/
/-- If `s : ι → set α` is a countable family of pairwise a.e. disjoint sets, then there exists a
family of measurable null sets `t i` such that `s i \ t i` are pairwise disjoint. -/
theorem exists_null_pairwise_disjoint_diff [Countable ι] {s : ι → Set α}
    (hd : Pairwise (AEDisjoint μ on s)) :
    ∃ t : ι → Set α,
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, μ (t i) = 0) ∧ Pairwise (Disjoint on fun i => s i \ t i) :=
  by
  refine'
    ⟨fun i => to_measurable μ (s i ∩ ⋃ j ∈ ({i}ᶜ : Set ι), s j), fun i =>
      measurable_set_to_measurable _ _, fun i => _, _⟩
  · simp only [measure_to_measurable, inter_Union]
    exact (measure_bUnion_null_iff <| to_countable _).2 fun j hj => hd (Ne.symm hj)
  · simp only [Pairwise, disjoint_left, on_fun, mem_diff, not_and, and_imp, Classical.not_not]
    intro i j hne x hi hU hj
    replace hU : x ∉ s i ∩ ⋃ (j) (_ : j ≠ i), s j := fun h => hU (subset_to_measurable _ _ h)
    simp only [mem_inter_iff, mem_Union, not_and, not_exists] at hU
    exact (hU hi j hne.symm hj).elim
#align measure_theory.exists_null_pairwise_disjoint_diff MeasureTheory.exists_null_pairwise_disjoint_diff

namespace AeDisjoint

/- warning: measure_theory.ae_disjoint.eq -> MeasureTheory.AEDisjoint.eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.eq MeasureTheory.AEDisjoint.eqₓ'. -/
protected theorem eq (h : AEDisjoint μ s t) : μ (s ∩ t) = 0 :=
  h
#align measure_theory.ae_disjoint.eq MeasureTheory.AEDisjoint.eq

#print MeasureTheory.AEDisjoint.symm /-
@[symm]
protected theorem symm (h : AEDisjoint μ s t) : AEDisjoint μ t s := by rwa [ae_disjoint, inter_comm]
#align measure_theory.ae_disjoint.symm MeasureTheory.AEDisjoint.symm
-/

#print MeasureTheory.AEDisjoint.symmetric /-
protected theorem symmetric : Symmetric (AEDisjoint μ) := fun s t h => h.symm
#align measure_theory.ae_disjoint.symmetric MeasureTheory.AEDisjoint.symmetric
-/

#print MeasureTheory.AEDisjoint.comm /-
protected theorem comm : AEDisjoint μ s t ↔ AEDisjoint μ t s :=
  ⟨fun h => h.symm, fun h => h.symm⟩
#align measure_theory.ae_disjoint.comm MeasureTheory.AEDisjoint.comm
-/

/- warning: disjoint.ae_disjoint -> Disjoint.aedisjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (MeasureTheory.AEDisjoint.{u1} α m μ s t)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t) -> (MeasureTheory.AEDisjoint.{u1} α m μ s t)
Case conversion may be inaccurate. Consider using '#align disjoint.ae_disjoint Disjoint.aedisjointₓ'. -/
protected theorem Disjoint.aedisjoint (h : Disjoint s t) : AEDisjoint μ s t := by
  rw [ae_disjoint, disjoint_iff_inter_eq_empty.1 h, measure_empty]
#align disjoint.ae_disjoint Disjoint.aedisjoint

/- warning: pairwise.ae_disjoint -> Pairwise.aedisjoint is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {f : ι -> (Set.{u2} α)}, (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α)))) f)) -> (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (MeasureTheory.AEDisjoint.{u2} α m μ) f))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {f : ι -> (Set.{u2} α)}, (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (Disjoint.{u2} (Set.{u2} α) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) f)) -> (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (MeasureTheory.AEDisjoint.{u2} α m μ) f))
Case conversion may be inaccurate. Consider using '#align pairwise.ae_disjoint Pairwise.aedisjointₓ'. -/
protected theorem Pairwise.aedisjoint {f : ι → Set α} (hf : Pairwise (Disjoint on f)) :
    Pairwise (AEDisjoint μ on f) :=
  hf.mono fun i j h => h.AEDisjoint
#align pairwise.ae_disjoint Pairwise.aedisjoint

/- warning: set.pairwise_disjoint.ae_disjoint -> Set.PairwiseDisjoint.aedisjoint is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {f : ι -> (Set.{u2} α)} {s : Set.{u1} ι}, (Set.PairwiseDisjoint.{u2, u1} (Set.{u2} α) ι (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α))) s f) -> (Set.Pairwise.{u1} ι s (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (MeasureTheory.AEDisjoint.{u2} α m μ) f))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {f : ι -> (Set.{u2} α)} {s : Set.{u1} ι}, (Set.PairwiseDisjoint.{u2, u1} (Set.{u2} α) ι (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) s f) -> (Set.Pairwise.{u1} ι s (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (MeasureTheory.AEDisjoint.{u2} α m μ) f))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint.ae_disjoint Set.PairwiseDisjoint.aedisjointₓ'. -/
protected theorem Set.PairwiseDisjoint.aedisjoint {f : ι → Set α} {s : Set ι}
    (hf : s.PairwiseDisjoint f) : s.Pairwise (AEDisjoint μ on f) :=
  hf.mono' fun i j h => h.AEDisjoint
#align set.pairwise_disjoint.ae_disjoint Set.PairwiseDisjoint.aedisjoint

#print MeasureTheory.AEDisjoint.mono_ae /-
theorem mono_ae (h : AEDisjoint μ s t) (hu : u ≤ᵐ[μ] s) (hv : v ≤ᵐ[μ] t) : AEDisjoint μ u v :=
  measure_mono_null_ae (hu.inter hv) h
#align measure_theory.ae_disjoint.mono_ae MeasureTheory.AEDisjoint.mono_ae
-/

#print MeasureTheory.AEDisjoint.mono /-
protected theorem mono (h : AEDisjoint μ s t) (hu : u ⊆ s) (hv : v ⊆ t) : AEDisjoint μ u v :=
  h.mono_ae hu.EventuallyLE hv.EventuallyLE
#align measure_theory.ae_disjoint.mono MeasureTheory.AEDisjoint.mono
-/

#print MeasureTheory.AEDisjoint.congr /-
protected theorem congr (h : AEDisjoint μ s t) (hu : u =ᵐ[μ] s) (hv : v =ᵐ[μ] t) :
    AEDisjoint μ u v :=
  h.mono_ae (Filter.EventuallyEq.le hu) (Filter.EventuallyEq.le hv)
#align measure_theory.ae_disjoint.congr MeasureTheory.AEDisjoint.congr
-/

/- warning: measure_theory.ae_disjoint.Union_left_iff -> MeasureTheory.AEDisjoint.unionᵢ_left_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {t : Set.{u2} α} [_inst_1 : Countable.{succ u1} ι] {s : ι -> (Set.{u2} α)}, Iff (MeasureTheory.AEDisjoint.{u2} α m μ (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => s i)) t) (forall (i : ι), MeasureTheory.AEDisjoint.{u2} α m μ (s i) t)
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {t : Set.{u1} α} [_inst_1 : Countable.{succ u2} ι] {s : ι -> (Set.{u1} α)}, Iff (MeasureTheory.AEDisjoint.{u1} α m μ (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => s i)) t) (forall (i : ι), MeasureTheory.AEDisjoint.{u1} α m μ (s i) t)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.Union_left_iff MeasureTheory.AEDisjoint.unionᵢ_left_iffₓ'. -/
@[simp]
theorem unionᵢ_left_iff [Countable ι] {s : ι → Set α} :
    AEDisjoint μ (⋃ i, s i) t ↔ ∀ i, AEDisjoint μ (s i) t := by
  simp only [ae_disjoint, Union_inter, measure_Union_null_iff]
#align measure_theory.ae_disjoint.Union_left_iff MeasureTheory.AEDisjoint.unionᵢ_left_iff

/- warning: measure_theory.ae_disjoint.Union_right_iff -> MeasureTheory.AEDisjoint.unionᵢ_right_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {s : Set.{u2} α} [_inst_1 : Countable.{succ u1} ι] {t : ι -> (Set.{u2} α)}, Iff (MeasureTheory.AEDisjoint.{u2} α m μ s (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => t i))) (forall (i : ι), MeasureTheory.AEDisjoint.{u2} α m μ s (t i))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} [_inst_1 : Countable.{succ u2} ι] {t : ι -> (Set.{u1} α)}, Iff (MeasureTheory.AEDisjoint.{u1} α m μ s (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => t i))) (forall (i : ι), MeasureTheory.AEDisjoint.{u1} α m μ s (t i))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.Union_right_iff MeasureTheory.AEDisjoint.unionᵢ_right_iffₓ'. -/
@[simp]
theorem unionᵢ_right_iff [Countable ι] {t : ι → Set α} :
    AEDisjoint μ s (⋃ i, t i) ↔ ∀ i, AEDisjoint μ s (t i) := by
  simp only [ae_disjoint, inter_Union, measure_Union_null_iff]
#align measure_theory.ae_disjoint.Union_right_iff MeasureTheory.AEDisjoint.unionᵢ_right_iff

/- warning: measure_theory.ae_disjoint.union_left_iff -> MeasureTheory.AEDisjoint.union_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (MeasureTheory.AEDisjoint.{u1} α m μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) u) (And (MeasureTheory.AEDisjoint.{u1} α m μ s u) (MeasureTheory.AEDisjoint.{u1} α m μ t u))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (MeasureTheory.AEDisjoint.{u1} α m μ (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) u) (And (MeasureTheory.AEDisjoint.{u1} α m μ s u) (MeasureTheory.AEDisjoint.{u1} α m μ t u))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.union_left_iff MeasureTheory.AEDisjoint.union_left_iffₓ'. -/
@[simp]
theorem union_left_iff : AEDisjoint μ (s ∪ t) u ↔ AEDisjoint μ s u ∧ AEDisjoint μ t u := by
  simp [union_eq_Union, and_comm]
#align measure_theory.ae_disjoint.union_left_iff MeasureTheory.AEDisjoint.union_left_iff

/- warning: measure_theory.ae_disjoint.union_right_iff -> MeasureTheory.AEDisjoint.union_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (MeasureTheory.AEDisjoint.{u1} α m μ s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u)) (And (MeasureTheory.AEDisjoint.{u1} α m μ s t) (MeasureTheory.AEDisjoint.{u1} α m μ s u))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (MeasureTheory.AEDisjoint.{u1} α m μ s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u)) (And (MeasureTheory.AEDisjoint.{u1} α m μ s t) (MeasureTheory.AEDisjoint.{u1} α m μ s u))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.union_right_iff MeasureTheory.AEDisjoint.union_right_iffₓ'. -/
@[simp]
theorem union_right_iff : AEDisjoint μ s (t ∪ u) ↔ AEDisjoint μ s t ∧ AEDisjoint μ s u := by
  simp [union_eq_Union, and_comm]
#align measure_theory.ae_disjoint.union_right_iff MeasureTheory.AEDisjoint.union_right_iff

/- warning: measure_theory.ae_disjoint.union_left -> MeasureTheory.AEDisjoint.union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s u) -> (MeasureTheory.AEDisjoint.{u1} α m μ t u) -> (MeasureTheory.AEDisjoint.{u1} α m μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) u)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s u) -> (MeasureTheory.AEDisjoint.{u1} α m μ t u) -> (MeasureTheory.AEDisjoint.{u1} α m μ (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) u)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.union_left MeasureTheory.AEDisjoint.union_leftₓ'. -/
theorem union_left (hs : AEDisjoint μ s u) (ht : AEDisjoint μ t u) : AEDisjoint μ (s ∪ t) u :=
  union_left_iff.mpr ⟨hs, ht⟩
#align measure_theory.ae_disjoint.union_left MeasureTheory.AEDisjoint.union_left

/- warning: measure_theory.ae_disjoint.union_right -> MeasureTheory.AEDisjoint.union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (MeasureTheory.AEDisjoint.{u1} α m μ s u) -> (MeasureTheory.AEDisjoint.{u1} α m μ s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (MeasureTheory.AEDisjoint.{u1} α m μ s u) -> (MeasureTheory.AEDisjoint.{u1} α m μ s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.union_right MeasureTheory.AEDisjoint.union_rightₓ'. -/
theorem union_right (ht : AEDisjoint μ s t) (hu : AEDisjoint μ s u) : AEDisjoint μ s (t ∪ u) :=
  union_right_iff.2 ⟨ht, hu⟩
#align measure_theory.ae_disjoint.union_right MeasureTheory.AEDisjoint.union_right

/- warning: measure_theory.ae_disjoint.diff_ae_eq_left -> MeasureTheory.AEDisjoint.diff_ae_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) s)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) s)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.diff_ae_eq_left MeasureTheory.AEDisjoint.diff_ae_eq_leftₓ'. -/
theorem diff_ae_eq_left (h : AEDisjoint μ s t) : (s \ t : Set α) =ᵐ[μ] s :=
  @diff_self_inter _ s t ▸ diff_null_ae_eq_self h
#align measure_theory.ae_disjoint.diff_ae_eq_left MeasureTheory.AEDisjoint.diff_ae_eq_left

/- warning: measure_theory.ae_disjoint.diff_ae_eq_right -> MeasureTheory.AEDisjoint.diff_ae_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s) t)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s) t)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.diff_ae_eq_right MeasureTheory.AEDisjoint.diff_ae_eq_rightₓ'. -/
theorem diff_ae_eq_right (h : AEDisjoint μ s t) : (t \ s : Set α) =ᵐ[μ] t :=
  h.symm.diff_ae_eq_left
#align measure_theory.ae_disjoint.diff_ae_eq_right MeasureTheory.AEDisjoint.diff_ae_eq_right

/- warning: measure_theory.ae_disjoint.measure_diff_left -> MeasureTheory.AEDisjoint.measure_diff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.measure_diff_left MeasureTheory.AEDisjoint.measure_diff_leftₓ'. -/
theorem measure_diff_left (h : AEDisjoint μ s t) : μ (s \ t) = μ s :=
  measure_congr h.diff_ae_eq_left
#align measure_theory.ae_disjoint.measure_diff_left MeasureTheory.AEDisjoint.measure_diff_left

/- warning: measure_theory.ae_disjoint.measure_diff_right -> MeasureTheory.AEDisjoint.measure_diff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s)) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ t))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) t))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.measure_diff_right MeasureTheory.AEDisjoint.measure_diff_rightₓ'. -/
theorem measure_diff_right (h : AEDisjoint μ s t) : μ (t \ s) = μ t :=
  measure_congr h.diff_ae_eq_right
#align measure_theory.ae_disjoint.measure_diff_right MeasureTheory.AEDisjoint.measure_diff_right

/- warning: measure_theory.ae_disjoint.exists_disjoint_diff -> MeasureTheory.AEDisjoint.exists_disjoint_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (MeasurableSet.{u1} α m u) (And (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ u) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s u) t))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.AEDisjoint.{u1} α m μ s t) -> (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (MeasurableSet.{u1} α m u) (And (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) u) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s u) t))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.exists_disjoint_diff MeasureTheory.AEDisjoint.exists_disjoint_diffₓ'. -/
/-- If `s` and `t` are `μ`-a.e. disjoint, then `s \ u` and `t` are disjoint for some measurable null
set `u`. -/
theorem exists_disjoint_diff (h : AEDisjoint μ s t) :
    ∃ u, MeasurableSet u ∧ μ u = 0 ∧ Disjoint (s \ u) t :=
  ⟨toMeasurable μ (s ∩ t), measurableSet_toMeasurable _ _, (measure_toMeasurable _).trans h,
    disjoint_sdiff_self_left.mono_left fun x hx =>
      ⟨hx.1, fun hxt => hx.2 <| subset_toMeasurable _ _ ⟨hx.1, hxt⟩⟩⟩
#align measure_theory.ae_disjoint.exists_disjoint_diff MeasureTheory.AEDisjoint.exists_disjoint_diff

/- warning: measure_theory.ae_disjoint.of_null_right -> MeasureTheory.AEDisjoint.of_null_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (MeasureTheory.AEDisjoint.{u1} α m μ s t)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (MeasureTheory.AEDisjoint.{u1} α m μ s t)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.of_null_right MeasureTheory.AEDisjoint.of_null_rightₓ'. -/
theorem of_null_right (h : μ t = 0) : AEDisjoint μ s t :=
  measure_mono_null (inter_subset_right _ _) h
#align measure_theory.ae_disjoint.of_null_right MeasureTheory.AEDisjoint.of_null_right

/- warning: measure_theory.ae_disjoint.of_null_left -> MeasureTheory.AEDisjoint.of_null_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (MeasureTheory.AEDisjoint.{u1} α m μ s t)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {t : Set.{u1} α}, (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (MeasureTheory.AEDisjoint.{u1} α m μ s t)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint.of_null_left MeasureTheory.AEDisjoint.of_null_leftₓ'. -/
theorem of_null_left (h : μ s = 0) : AEDisjoint μ s t :=
  (of_null_right h).symm
#align measure_theory.ae_disjoint.of_null_left MeasureTheory.AEDisjoint.of_null_left

end AeDisjoint

/- warning: measure_theory.ae_disjoint_compl_left -> MeasureTheory.aedisjoint_compl_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α}, MeasureTheory.AEDisjoint.{u1} α m μ (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) s
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α}, MeasureTheory.AEDisjoint.{u1} α m μ (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) s
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint_compl_left MeasureTheory.aedisjoint_compl_leftₓ'. -/
theorem aedisjoint_compl_left : AEDisjoint μ (sᶜ) s :=
  (@disjoint_compl_left _ _ s).AEDisjoint
#align measure_theory.ae_disjoint_compl_left MeasureTheory.aedisjoint_compl_left

/- warning: measure_theory.ae_disjoint_compl_right -> MeasureTheory.aedisjoint_compl_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α}, MeasureTheory.AEDisjoint.{u1} α m μ s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α}, MeasureTheory.AEDisjoint.{u1} α m μ s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_disjoint_compl_right MeasureTheory.aedisjoint_compl_rightₓ'. -/
theorem aedisjoint_compl_right : AEDisjoint μ s (sᶜ) :=
  (@disjoint_compl_right _ _ s).AEDisjoint
#align measure_theory.ae_disjoint_compl_right MeasureTheory.aedisjoint_compl_right

end MeasureTheory

