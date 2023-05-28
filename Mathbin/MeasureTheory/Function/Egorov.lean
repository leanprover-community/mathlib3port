/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

! This file was ported from Lean 3 source module measure_theory.function.egorov
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Egorov theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the Egorov theorem which states that an almost everywhere convergent
sequence on a finite measure space converges uniformly except on an arbitrarily small set.
This theorem is useful for the Vitali convergence theorem as well as theorems regarding
convergence in measure.

## Main results

* `measure_theory.egorov`: Egorov's theorem which shows that a sequence of almost everywhere
  convergent functions converges uniformly except on an arbitrarily small set.

-/


noncomputable section

open Classical MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type _} {m : MeasurableSpace α} [MetricSpace β] {μ : Measure α}

namespace Egorov

#print MeasureTheory.Egorov.notConvergentSeq /-
/-- Given a sequence of functions `f` and a function `g`, `not_convergent_seq f g n j` is the
set of elements such that `f k x` and `g x` are separated by at least `1 / (n + 1)` for some
`k ≥ j`.

This definition is useful for Egorov's theorem. -/
def notConvergentSeq [Preorder ι] (f : ι → α → β) (g : α → β) (n : ℕ) (j : ι) : Set α :=
  ⋃ (k) (hk : j ≤ k), { x | 1 / (n + 1 : ℝ) < dist (f k x) (g x) }
#align measure_theory.egorov.not_convergent_seq MeasureTheory.Egorov.notConvergentSeq
-/

variable {n : ℕ} {i j : ι} {s : Set α} {ε : ℝ} {f : ι → α → β} {g : α → β}

/- warning: measure_theory.egorov.mem_not_convergent_seq_iff -> MeasureTheory.Egorov.mem_notConvergentSeq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : MetricSpace.{u2} β] {n : Nat} {j : ι} {f : ι -> α -> β} {g : α -> β} [_inst_2 : Preorder.{u3} ι] {x : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (MeasureTheory.Egorov.notConvergentSeq.{u1, u2, u3} α β ι _inst_1 _inst_2 f g n j)) (Exists.{succ u3} ι (fun (k : ι) => Exists.{0} (LE.le.{u3} ι (Preorder.toHasLe.{u3} ι _inst_2) j k) (fun (hk : LE.le.{u3} ι (Preorder.toHasLe.{u3} ι _inst_2) j k) => LT.lt.{0} Real Real.hasLt (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1)) (f k x) (g x)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Type.{u3}} [_inst_1 : MetricSpace.{u1} β] {n : Nat} {j : ι} {f : ι -> α -> β} {g : α -> β} [_inst_2 : Preorder.{u3} ι] {x : α}, Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (MeasureTheory.Egorov.notConvergentSeq.{u2, u1, u3} α β ι _inst_1 _inst_2 f g n j)) (Exists.{succ u3} ι (fun (k : ι) => Exists.{0} (LE.le.{u3} ι (Preorder.toLE.{u3} ι _inst_2) j k) (fun (hk : LE.le.{u3} ι (Preorder.toLE.{u3} ι _inst_2) j k) => LT.lt.{0} Real Real.instLTReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast n) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Dist.dist.{u1} β (PseudoMetricSpace.toDist.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_1)) (f k x) (g x)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.egorov.mem_not_convergent_seq_iff MeasureTheory.Egorov.mem_notConvergentSeq_iffₓ'. -/
theorem mem_notConvergentSeq_iff [Preorder ι] {x : α} :
    x ∈ notConvergentSeq f g n j ↔ ∃ (k : _)(hk : j ≤ k), 1 / (n + 1 : ℝ) < dist (f k x) (g x) :=
  by
  simp_rw [not_convergent_seq, mem_Union]
  rfl
#align measure_theory.egorov.mem_not_convergent_seq_iff MeasureTheory.Egorov.mem_notConvergentSeq_iff

/- warning: measure_theory.egorov.not_convergent_seq_antitone -> MeasureTheory.Egorov.notConvergentSeq_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : MetricSpace.{u2} β] {n : Nat} {f : ι -> α -> β} {g : α -> β} [_inst_2 : Preorder.{u3} ι], Antitone.{u3, u1} ι (Set.{u1} α) _inst_2 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (MeasureTheory.Egorov.notConvergentSeq.{u1, u2, u3} α β ι _inst_1 _inst_2 f g n)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Type.{u3}} [_inst_1 : MetricSpace.{u1} β] {n : Nat} {f : ι -> α -> β} {g : α -> β} [_inst_2 : Preorder.{u3} ι], Antitone.{u3, u2} ι (Set.{u2} α) _inst_2 (PartialOrder.toPreorder.{u2} (Set.{u2} α) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (MeasureTheory.Egorov.notConvergentSeq.{u2, u1, u3} α β ι _inst_1 _inst_2 f g n)
Case conversion may be inaccurate. Consider using '#align measure_theory.egorov.not_convergent_seq_antitone MeasureTheory.Egorov.notConvergentSeq_antitoneₓ'. -/
theorem notConvergentSeq_antitone [Preorder ι] : Antitone (notConvergentSeq f g n) := fun j k hjk =>
  iUnion₂_mono' fun l hl => ⟨l, le_trans hjk hl, Subset.rfl⟩
#align measure_theory.egorov.not_convergent_seq_antitone MeasureTheory.Egorov.notConvergentSeq_antitone

/- warning: measure_theory.egorov.measure_inter_not_convergent_seq_eq_zero -> MeasureTheory.Egorov.measure_inter_notConvergentSeq_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} {m : MeasurableSpace.{u1} α} [_inst_1 : MetricSpace.{u2} β] {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {f : ι -> α -> β} {g : α -> β} [_inst_2 : SemilatticeSup.{u3} ι] [_inst_3 : Nonempty.{succ u3} ι], (Filter.Eventually.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Filter.Tendsto.{u3, u2} ι β (fun (n : ι) => f n x) (Filter.atTop.{u3} ι (PartialOrder.toPreorder.{u3} ι (SemilatticeSup.toPartialOrder.{u3} ι _inst_2))) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) (g x)))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (forall (n : Nat), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.iInter.{u1, succ u3} α ι (fun (j : ι) => MeasureTheory.Egorov.notConvergentSeq.{u1, u2, u3} α β ι _inst_1 (PartialOrder.toPreorder.{u3} ι (SemilatticeSup.toPartialOrder.{u3} ι _inst_2)) f g n j)))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Type.{u3}} {m : MeasurableSpace.{u2} α} [_inst_1 : MetricSpace.{u1} β] {μ : MeasureTheory.Measure.{u2} α m} {s : Set.{u2} α} {f : ι -> α -> β} {g : α -> β} [_inst_2 : SemilatticeSup.{u3} ι] [_inst_3 : Nonempty.{succ u3} ι], (Filter.Eventually.{u2} α (fun (x : α) => (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Filter.Tendsto.{u3, u1} ι β (fun (n : ι) => f n x) (Filter.atTop.{u3} ι (PartialOrder.toPreorder.{u3} ι (SemilatticeSup.toPartialOrder.{u3} ι _inst_2))) (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_1))) (g x)))) (MeasureTheory.Measure.ae.{u2} α m μ)) -> (forall (n : Nat), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α m μ) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Set.iInter.{u2, succ u3} α ι (fun (j : ι) => MeasureTheory.Egorov.notConvergentSeq.{u2, u1, u3} α β ι _inst_1 (PartialOrder.toPreorder.{u3} ι (SemilatticeSup.toPartialOrder.{u3} ι _inst_2)) f g n j)))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.egorov.measure_inter_not_convergent_seq_eq_zero MeasureTheory.Egorov.measure_inter_notConvergentSeq_eq_zeroₓ'. -/
theorem measure_inter_notConvergentSeq_eq_zero [SemilatticeSup ι] [Nonempty ι]
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    μ (s ∩ ⋂ j, notConvergentSeq f g n j) = 0 :=
  by
  simp_rw [Metric.tendsto_atTop, ae_iff] at hfg
  rw [← nonpos_iff_eq_zero, ← hfg]
  refine' measure_mono fun x => _
  simp only [mem_inter_iff, mem_Inter, ge_iff_le, mem_not_convergent_seq_iff]
  push_neg
  rintro ⟨hmem, hx⟩
  refine' ⟨hmem, 1 / (n + 1 : ℝ), Nat.one_div_pos_of_nat, fun N => _⟩
  obtain ⟨n, hn₁, hn₂⟩ := hx N
  exact ⟨n, hn₁, hn₂.le⟩
#align measure_theory.egorov.measure_inter_not_convergent_seq_eq_zero MeasureTheory.Egorov.measure_inter_notConvergentSeq_eq_zero

/- warning: measure_theory.egorov.not_convergent_seq_measurable_set -> MeasureTheory.Egorov.notConvergentSeq_measurableSet is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} {m : MeasurableSpace.{u1} α} [_inst_1 : MetricSpace.{u2} β] {n : Nat} {j : ι} {f : ι -> α -> β} {g : α -> β} [_inst_2 : Preorder.{u3} ι] [_inst_3 : Countable.{succ u3} ι], (forall (n : ι), MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) m (f n)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) m g) -> (MeasurableSet.{u1} α m (MeasureTheory.Egorov.notConvergentSeq.{u1, u2, u3} α β ι _inst_1 _inst_2 f g n j))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Type.{u3}} {m : MeasurableSpace.{u2} α} [_inst_1 : MetricSpace.{u1} β] {n : Nat} {j : ι} {f : ι -> α -> β} {g : α -> β} [_inst_2 : Preorder.{u3} ι] [_inst_3 : Countable.{succ u3} ι], (forall (n : ι), MeasureTheory.StronglyMeasurable.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_1))) m (f n)) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_1))) m g) -> (MeasurableSet.{u2} α m (MeasureTheory.Egorov.notConvergentSeq.{u2, u1, u3} α β ι _inst_1 _inst_2 f g n j))
Case conversion may be inaccurate. Consider using '#align measure_theory.egorov.not_convergent_seq_measurable_set MeasureTheory.Egorov.notConvergentSeq_measurableSetₓ'. -/
theorem notConvergentSeq_measurableSet [Preorder ι] [Countable ι]
    (hf : ∀ n, strongly_measurable[m] (f n)) (hg : StronglyMeasurable g) :
    MeasurableSet (notConvergentSeq f g n j) :=
  MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun hk =>
      StronglyMeasurable.measurableSet_lt stronglyMeasurable_const <| (hf k).dist hg
#align measure_theory.egorov.not_convergent_seq_measurable_set MeasureTheory.Egorov.notConvergentSeq_measurableSet

/- warning: measure_theory.egorov.measure_not_convergent_seq_tendsto_zero -> MeasureTheory.Egorov.measure_notConvergentSeq_tendsto_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.egorov.measure_not_convergent_seq_tendsto_zero MeasureTheory.Egorov.measure_notConvergentSeq_tendsto_zeroₓ'. -/
theorem measure_notConvergentSeq_tendsto_zero [SemilatticeSup ι] [Countable ι]
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g) (hsm : MeasurableSet s)
    (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    Tendsto (fun j => μ (s ∩ notConvergentSeq f g n j)) atTop (𝓝 0) :=
  by
  cases isEmpty_or_nonempty ι
  · have : (fun j => μ (s ∩ not_convergent_seq f g n j)) = fun j => 0 := by
      simp only [eq_iff_true_of_subsingleton]
    rw [this]
    exact tendsto_const_nhds
  rw [← measure_inter_not_convergent_seq_eq_zero hfg n, inter_Inter]
  refine'
    tendsto_measure_Inter (fun n => hsm.inter <| not_convergent_seq_measurable_set hf hg)
      (fun k l hkl => inter_subset_inter_right _ <| not_convergent_seq_antitone hkl)
      ⟨h.some, (lt_of_le_of_lt (measure_mono <| inter_subset_left _ _) (lt_top_iff_ne_top.2 hs)).Ne⟩
#align measure_theory.egorov.measure_not_convergent_seq_tendsto_zero MeasureTheory.Egorov.measure_notConvergentSeq_tendsto_zero

variable [SemilatticeSup ι] [Nonempty ι] [Countable ι]

/- warning: measure_theory.egorov.exists_not_convergent_seq_lt -> MeasureTheory.Egorov.exists_notConvergentSeq_lt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.egorov.exists_not_convergent_seq_lt MeasureTheory.Egorov.exists_notConvergentSeq_ltₓ'. -/
theorem exists_notConvergentSeq_lt (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    ∃ j : ι, μ (s ∩ notConvergentSeq f g n j) ≤ ENNReal.ofReal (ε * 2⁻¹ ^ n) :=
  by
  obtain ⟨N, hN⟩ :=
    (ENNReal.tendsto_atTop ENNReal.zero_ne_top).1
      (measure_not_convergent_seq_tendsto_zero hf hg hsm hs hfg n) (ENNReal.ofReal (ε * 2⁻¹ ^ n)) _
  · rw [zero_add] at hN
    exact ⟨N, (hN N le_rfl).2⟩
  · rw [gt_iff_lt, ENNReal.ofReal_pos]
    exact mul_pos hε (pow_pos (by norm_num) n)
#align measure_theory.egorov.exists_not_convergent_seq_lt MeasureTheory.Egorov.exists_notConvergentSeq_lt

/- warning: measure_theory.egorov.not_convergent_seq_lt_index -> MeasureTheory.Egorov.notConvergentSeqLtIndex is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} {m : MeasurableSpace.{u1} α} [_inst_1 : MetricSpace.{u2} β] {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {ε : Real} {f : ι -> α -> β} {g : α -> β} [_inst_2 : SemilatticeSup.{u3} ι] [_inst_3 : Nonempty.{succ u3} ι] [_inst_4 : Countable.{succ u3} ι], (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (forall (n : ι), MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) m (f n)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) m g) -> (MeasurableSet.{u1} α m s) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Eventually.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Filter.Tendsto.{u3, u2} ι β (fun (n : ι) => f n x) (Filter.atTop.{u3} ι (PartialOrder.toPreorder.{u3} ι (SemilatticeSup.toPartialOrder.{u3} ι _inst_2))) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) (g x)))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> Nat -> ι
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} {m : MeasurableSpace.{u1} α} [_inst_1 : MetricSpace.{u2} β] {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {ε : Real} {f : ι -> α -> β} {g : α -> β} [_inst_2 : SemilatticeSup.{u3} ι] [_inst_3 : Nonempty.{succ u3} ι] [_inst_4 : Countable.{succ u3} ι], (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (forall (n : ι), MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) m (f n)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) m g) -> (MeasurableSet.{u1} α m s) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Eventually.{u1} α (fun (x : α) => (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Filter.Tendsto.{u3, u2} ι β (fun (n : ι) => f n x) (Filter.atTop.{u3} ι (PartialOrder.toPreorder.{u3} ι (SemilatticeSup.toPartialOrder.{u3} ι _inst_2))) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) (g x)))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> Nat -> ι
Case conversion may be inaccurate. Consider using '#align measure_theory.egorov.not_convergent_seq_lt_index MeasureTheory.Egorov.notConvergentSeqLtIndexₓ'. -/
/-- Given some `ε > 0`, `not_convergent_seq_lt_index` provides the index such that
`not_convergent_seq` (intersected with a set of finite measure) has measure less than
`ε * 2⁻¹ ^ n`.

This definition is useful for Egorov's theorem. -/
def notConvergentSeqLtIndex (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) : ι :=
  Classical.choose <| exists_notConvergentSeq_lt hε hf hg hsm hs hfg n
#align measure_theory.egorov.not_convergent_seq_lt_index MeasureTheory.Egorov.notConvergentSeqLtIndex

/- warning: measure_theory.egorov.not_convergent_seq_lt_index_spec -> MeasureTheory.Egorov.notConvergentSeqLtIndex_spec is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.egorov.not_convergent_seq_lt_index_spec MeasureTheory.Egorov.notConvergentSeqLtIndex_specₓ'. -/
theorem notConvergentSeqLtIndex_spec (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    μ (s ∩ notConvergentSeq f g n (notConvergentSeqLtIndex hε hf hg hsm hs hfg n)) ≤
      ENNReal.ofReal (ε * 2⁻¹ ^ n) :=
  Classical.choose_spec <| exists_notConvergentSeq_lt hε hf hg hsm hs hfg n
#align measure_theory.egorov.not_convergent_seq_lt_index_spec MeasureTheory.Egorov.notConvergentSeqLtIndex_spec

/- warning: measure_theory.egorov.Union_not_convergent_seq -> MeasureTheory.Egorov.iUnionNotConvergentSeq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} {m : MeasurableSpace.{u1} α} [_inst_1 : MetricSpace.{u2} β] {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {ε : Real} {f : ι -> α -> β} {g : α -> β} [_inst_2 : SemilatticeSup.{u3} ι] [_inst_3 : Nonempty.{succ u3} ι] [_inst_4 : Countable.{succ u3} ι], (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (forall (n : ι), MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) m (f n)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) m g) -> (MeasurableSet.{u1} α m s) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Eventually.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Filter.Tendsto.{u3, u2} ι β (fun (n : ι) => f n x) (Filter.atTop.{u3} ι (PartialOrder.toPreorder.{u3} ι (SemilatticeSup.toPartialOrder.{u3} ι _inst_2))) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) (g x)))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Set.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} {m : MeasurableSpace.{u1} α} [_inst_1 : MetricSpace.{u2} β] {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {ε : Real} {f : ι -> α -> β} {g : α -> β} [_inst_2 : SemilatticeSup.{u3} ι] [_inst_3 : Nonempty.{succ u3} ι] [_inst_4 : Countable.{succ u3} ι], (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (forall (n : ι), MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) m (f n)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) m g) -> (MeasurableSet.{u1} α m s) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Eventually.{u1} α (fun (x : α) => (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Filter.Tendsto.{u3, u2} ι β (fun (n : ι) => f n x) (Filter.atTop.{u3} ι (PartialOrder.toPreorder.{u3} ι (SemilatticeSup.toPartialOrder.{u3} ι _inst_2))) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (MetricSpace.toPseudoMetricSpace.{u2} β _inst_1))) (g x)))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Set.{u1} α)
Case conversion may be inaccurate. Consider using '#align measure_theory.egorov.Union_not_convergent_seq MeasureTheory.Egorov.iUnionNotConvergentSeqₓ'. -/
/-- Given some `ε > 0`, `Union_not_convergent_seq` is the union of `not_convergent_seq` with
specific indicies such that `Union_not_convergent_seq` has measure less equal than `ε`.

This definition is useful for Egorov's theorem. -/
def iUnionNotConvergentSeq (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Set α :=
  ⋃ n, s ∩ notConvergentSeq f g n (notConvergentSeqLtIndex (half_pos hε) hf hg hsm hs hfg n)
#align measure_theory.egorov.Union_not_convergent_seq MeasureTheory.Egorov.iUnionNotConvergentSeq

/- warning: measure_theory.egorov.Union_not_convergent_seq_measurable_set -> MeasureTheory.Egorov.iUnionNotConvergentSeq_measurableSet is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.egorov.Union_not_convergent_seq_measurable_set MeasureTheory.Egorov.iUnionNotConvergentSeq_measurableSetₓ'. -/
theorem iUnionNotConvergentSeq_measurableSet (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MeasurableSet <| iUnionNotConvergentSeq hε hf hg hsm hs hfg :=
  MeasurableSet.iUnion fun n => hsm.inter <| notConvergentSeq_measurableSet hf hg
#align measure_theory.egorov.Union_not_convergent_seq_measurable_set MeasureTheory.Egorov.iUnionNotConvergentSeq_measurableSet

/- warning: measure_theory.egorov.measure_Union_not_convergent_seq -> MeasureTheory.Egorov.measure_iUnionNotConvergentSeq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.egorov.measure_Union_not_convergent_seq MeasureTheory.Egorov.measure_iUnionNotConvergentSeqₓ'. -/
theorem measure_iUnionNotConvergentSeq (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    μ (iUnionNotConvergentSeq hε hf hg hsm hs hfg) ≤ ENNReal.ofReal ε :=
  by
  refine'
    le_trans (measure_Union_le _)
      (le_trans
        (ENNReal.tsum_le_tsum <| not_convergent_seq_lt_index_spec (half_pos hε) hf hg hsm hs hfg) _)
  simp_rw [ENNReal.ofReal_mul (half_pos hε).le]
  rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg, inv_eq_one_div, tsum_geometric_two, ←
    ENNReal.ofReal_mul (half_pos hε).le, div_mul_cancel ε two_ne_zero]
  · exact le_rfl
  · exact fun n => pow_nonneg (by norm_num) _
  · rw [inv_eq_one_div]
    exact summable_geometric_two
#align measure_theory.egorov.measure_Union_not_convergent_seq MeasureTheory.Egorov.measure_iUnionNotConvergentSeq

/- warning: measure_theory.egorov.Union_not_convergent_seq_subset -> MeasureTheory.Egorov.iUnionNotConvergentSeq_subset is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.egorov.Union_not_convergent_seq_subset MeasureTheory.Egorov.iUnionNotConvergentSeq_subsetₓ'. -/
theorem iUnionNotConvergentSeq_subset (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    iUnionNotConvergentSeq hε hf hg hsm hs hfg ⊆ s :=
  by
  rw [Union_not_convergent_seq, ← inter_Union]
  exact inter_subset_left _ _
#align measure_theory.egorov.Union_not_convergent_seq_subset MeasureTheory.Egorov.iUnionNotConvergentSeq_subset

/- warning: measure_theory.egorov.tendsto_uniformly_on_diff_Union_not_convergent_seq -> MeasureTheory.Egorov.tendstoUniformlyOn_diff_iUnionNotConvergentSeq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.egorov.tendsto_uniformly_on_diff_Union_not_convergent_seq MeasureTheory.Egorov.tendstoUniformlyOn_diff_iUnionNotConvergentSeqₓ'. -/
theorem tendstoUniformlyOn_diff_iUnionNotConvergentSeq (hε : 0 < ε)
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g) (hsm : MeasurableSet s)
    (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop (s \ Egorov.iUnionNotConvergentSeq hε hf hg hsm hs hfg) :=
  by
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  rw [eventually_at_top]
  refine' ⟨egorov.not_convergent_seq_lt_index (half_pos hε) hf hg hsm hs hfg N, fun n hn x hx => _⟩
  simp only [mem_diff, egorov.Union_not_convergent_seq, not_exists, mem_Union, mem_inter_iff,
    not_and, exists_and_left] at hx
  obtain ⟨hxs, hx⟩ := hx
  specialize hx hxs N
  rw [egorov.mem_not_convergent_seq_iff] at hx
  push_neg  at hx
  rw [dist_comm]
  exact lt_of_le_of_lt (hx n hn) hN
#align measure_theory.egorov.tendsto_uniformly_on_diff_Union_not_convergent_seq MeasureTheory.Egorov.tendstoUniformlyOn_diff_iUnionNotConvergentSeq

end Egorov

variable [SemilatticeSup ι] [Nonempty ι] [Countable ι] {γ : Type _} [TopologicalSpace γ]
  {f : ι → α → β} {g : α → β} {s : Set α}

/- warning: measure_theory.tendsto_uniformly_on_of_ae_tendsto -> MeasureTheory.tendstoUniformlyOn_of_ae_tendsto is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.tendsto_uniformly_on_of_ae_tendsto MeasureTheory.tendstoUniformlyOn_of_ae_tendstoₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/-- **Egorov's theorem**: If `f : ι → α → β` is a sequence of strongly measurable functions that
converges to `g : α → β` almost everywhere on a measurable set `s` of finite measure,
then for all `ε > 0`, there exists a subset `t ⊆ s` such that `μ t ≤ ε` and `f` converges to `g`
uniformly on `s \ t`. We require the index type `ι` to be countable, and usually `ι = ℕ`.

In other words, a sequence of almost everywhere convergent functions converges uniformly except on
an arbitrarily small set. -/
theorem tendstoUniformlyOn_of_ae_tendsto (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
    ∃ (t : _)(_ : t ⊆ s),
      MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop (s \ t) :=
  ⟨Egorov.iUnionNotConvergentSeq hε hf hg hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_subset hε hf hg hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_measurableSet hε hf hg hsm hs hfg,
    Egorov.measure_iUnionNotConvergentSeq hε hf hg hsm hs hfg,
    Egorov.tendstoUniformlyOn_diff_iUnionNotConvergentSeq hε hf hg hsm hs hfg⟩
#align measure_theory.tendsto_uniformly_on_of_ae_tendsto MeasureTheory.tendstoUniformlyOn_of_ae_tendsto

/- warning: measure_theory.tendsto_uniformly_on_of_ae_tendsto' -> MeasureTheory.tendstoUniformlyOn_of_ae_tendsto' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.tendsto_uniformly_on_of_ae_tendsto' MeasureTheory.tendstoUniformlyOn_of_ae_tendsto'ₓ'. -/
/-- Egorov's theorem for finite measure spaces. -/
theorem tendstoUniformlyOn_of_ae_tendsto' [FiniteMeasure μ] (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ t, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop (tᶜ) :=
  by
  obtain ⟨t, _, ht, htendsto⟩ :=
    tendsto_uniformly_on_of_ae_tendsto hf hg MeasurableSet.univ (measure_ne_top μ univ) _ hε
  · refine' ⟨_, ht, _⟩
    rwa [compl_eq_univ_diff]
  · filter_upwards [hfg]with _ htendsto _ using htendsto
#align measure_theory.tendsto_uniformly_on_of_ae_tendsto' MeasureTheory.tendstoUniformlyOn_of_ae_tendsto'

end MeasureTheory

