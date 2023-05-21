/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.function.ae_measurable_order
! leanprover-community/mathlib commit bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability criterion for ennreal-valued functions

Consider a function `f : α → ℝ≥0∞`. If the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p` and `q` are finite numbers satisfying
`p < q`, then `f` is almost-everywhere measurable. This is proved in
`ennreal.ae_measurable_of_exist_almost_disjoint_supersets`, and deduced from an analogous statement
for any target space which is a complete linear dense order, called
`measure_theory.ae_measurable_of_exist_almost_disjoint_supersets`.

Note that it should be enough to assume that the space is a conditionally complete linear order,
but the proof would be more painful. Since our only use for now is for `ℝ≥0∞`, we keep it as simple
as possible.
-/


open MeasureTheory Set TopologicalSpace

open Classical ENNReal NNReal

/- warning: measure_theory.ae_measurable_of_exist_almost_disjoint_supersets -> MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) {β : Type.{u2}} [_inst_1 : CompleteLinearOrder.{u2} β] [_inst_2 : DenselyOrdered.{u2} β (Preorder.toHasLt.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (CompleteLinearOrder.toCompleteLattice.{u2} β _inst_1)))))] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : OrderTopology.{u2} β _inst_3 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (CompleteLinearOrder.toCompleteLattice.{u2} β _inst_1))))] [_inst_5 : TopologicalSpace.SecondCountableTopology.{u2} β _inst_3] [_inst_6 : MeasurableSpace.{u2} β] [_inst_7 : BorelSpace.{u2} β _inst_3 _inst_6] (s : Set.{u2} β), (Set.Countable.{u2} β s) -> (Dense.{u2} β _inst_3 s) -> (forall (f : α -> β), (forall (p : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) p s) -> (forall (q : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) q s) -> (LT.lt.{u2} β (Preorder.toHasLt.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (CompleteLinearOrder.toCompleteLattice.{u2} β _inst_1))))) p q) -> (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{succ u1} (Set.{u1} α) (fun (v : Set.{u1} α) => And (MeasurableSet.{u1} α m u) (And (MeasurableSet.{u1} α m v) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (setOf.{u1} α (fun (x : α) => LT.lt.{u2} β (Preorder.toHasLt.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (CompleteLinearOrder.toCompleteLattice.{u2} β _inst_1))))) (f x) p)) u) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (setOf.{u1} α (fun (x : α) => LT.lt.{u2} β (Preorder.toHasLt.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (CompleteLinearOrder.toCompleteLattice.{u2} β _inst_1))))) q (f x))) v) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u v)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))))))))) -> (AEMeasurable.{u1, u2} α β _inst_6 m f μ))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} (μ : MeasureTheory.Measure.{u2} α m) {β : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} β] [_inst_2 : DenselyOrdered.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (OmegaCompletePartialOrder.toPartialOrder.{u1} β (CompleteLattice.instOmegaCompletePartialOrder.{u1} β (CompleteLinearOrder.toCompleteLattice.{u1} β _inst_1)))))] [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : OrderTopology.{u1} β _inst_3 (PartialOrder.toPreorder.{u1} β (OmegaCompletePartialOrder.toPartialOrder.{u1} β (CompleteLattice.instOmegaCompletePartialOrder.{u1} β (CompleteLinearOrder.toCompleteLattice.{u1} β _inst_1))))] [_inst_5 : TopologicalSpace.SecondCountableTopology.{u1} β _inst_3] [_inst_6 : MeasurableSpace.{u1} β] [_inst_7 : BorelSpace.{u1} β _inst_3 _inst_6] (s : Set.{u1} β), (Set.Countable.{u1} β s) -> (Dense.{u1} β _inst_3 s) -> (forall (f : α -> β), (forall (p : β), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) p s) -> (forall (q : β), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) q s) -> (LT.lt.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (OmegaCompletePartialOrder.toPartialOrder.{u1} β (CompleteLattice.instOmegaCompletePartialOrder.{u1} β (CompleteLinearOrder.toCompleteLattice.{u1} β _inst_1))))) p q) -> (Exists.{succ u2} (Set.{u2} α) (fun (u : Set.{u2} α) => Exists.{succ u2} (Set.{u2} α) (fun (v : Set.{u2} α) => And (MeasurableSet.{u2} α m u) (And (MeasurableSet.{u2} α m v) (And (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (setOf.{u2} α (fun (x : α) => LT.lt.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (OmegaCompletePartialOrder.toPartialOrder.{u1} β (CompleteLattice.instOmegaCompletePartialOrder.{u1} β (CompleteLinearOrder.toCompleteLattice.{u1} β _inst_1))))) (f x) p)) u) (And (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (setOf.{u2} α (fun (x : α) => LT.lt.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (OmegaCompletePartialOrder.toPartialOrder.{u1} β (CompleteLattice.instOmegaCompletePartialOrder.{u1} β (CompleteLinearOrder.toCompleteLattice.{u1} β _inst_1))))) q (f x))) v) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α m μ) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) u v)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))))))))) -> (AEMeasurable.{u2, u1} α β _inst_6 m f μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_measurable_of_exist_almost_disjoint_supersets MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersetsₓ'. -/
/-- If a function `f : α → β` is such that the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p < q`, then `f` is almost-everywhere
measurable. It is even enough to have this for `p` and `q` in a countable dense set. -/
theorem MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets {α : Type _}
    {m : MeasurableSpace α} (μ : Measure α) {β : Type _} [CompleteLinearOrder β] [DenselyOrdered β]
    [TopologicalSpace β] [OrderTopology β] [SecondCountableTopology β] [MeasurableSpace β]
    [BorelSpace β] (s : Set β) (s_count : s.Countable) (s_dense : Dense s) (f : α → β)
    (h :
      ∀ p ∈ s,
        ∀ q ∈ s,
          p < q →
            ∃ u v,
              MeasurableSet u ∧
                MeasurableSet v ∧ { x | f x < p } ⊆ u ∧ { x | q < f x } ⊆ v ∧ μ (u ∩ v) = 0) :
    AEMeasurable f μ := by
  haveI : Encodable s := s_count.to_encodable
  have h' :
    ∀ p q,
      ∃ u v,
        MeasurableSet u ∧
          MeasurableSet v ∧
            { x | f x < p } ⊆ u ∧ { x | q < f x } ⊆ v ∧ (p ∈ s → q ∈ s → p < q → μ (u ∩ v) = 0) :=
    by
    intro p q
    by_cases H : p ∈ s ∧ q ∈ s ∧ p < q
    · rcases h p H.1 q H.2.1 H.2.2 with ⟨u, v, hu, hv, h'u, h'v, hμ⟩
      exact ⟨u, v, hu, hv, h'u, h'v, fun ps qs pq => hμ⟩
    · refine'
        ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, subset_univ _, subset_univ _,
          fun ps qs pq => _⟩
      simp only [not_and] at H
      exact (H ps qs pq).elim
  choose! u v huv using h'
  let u' : β → Set α := fun p => ⋂ q ∈ s ∩ Ioi p, u p q
  have u'_meas : ∀ i, MeasurableSet (u' i) := by
    intro i
    exact MeasurableSet.biInter (s_count.mono (inter_subset_left _ _)) fun b hb => (huv i b).1
  let f' : α → β := fun x => ⨅ i : s, piecewise (u' i) (fun x => (i : β)) (fun x => (⊤ : β)) x
  have f'_meas : Measurable f' := by
    apply measurable_iInf
    exact fun i => Measurable.piecewise (u'_meas i) measurable_const measurable_const
  let t := ⋃ (p : s) (q : s ∩ Ioi p), u' p ∩ v p q
  have μt : μ t ≤ 0 :=
    calc
      μ t ≤ ∑' (p : s) (q : s ∩ Ioi p), μ (u' p ∩ v p q) :=
        by
        refine' (measure_Union_le _).trans _
        apply ENNReal.tsum_le_tsum fun p => _
        apply measure_Union_le _
        exact (s_count.mono (inter_subset_left _ _)).to_subtype
      _ ≤ ∑' (p : s) (q : s ∩ Ioi p), μ (u p q ∩ v p q) :=
        by
        apply ENNReal.tsum_le_tsum fun p => _
        refine' ENNReal.tsum_le_tsum fun q => measure_mono _
        exact inter_subset_inter_left _ (bInter_subset_of_mem q.2)
      _ = ∑' (p : s) (q : s ∩ Ioi p), (0 : ℝ≥0∞) :=
        by
        congr
        ext1 p
        congr
        ext1 q
        exact (huv p q).2.2.2.2 p.2 q.2.1 q.2.2
      _ = 0 := by simp only [tsum_zero]
      
  have ff' : ∀ᵐ x ∂μ, f x = f' x :=
    by
    have : ∀ᵐ x ∂μ, x ∉ t := by
      have : μ t = 0 := le_antisymm μt bot_le
      change μ _ = 0
      convert this
      ext y
      simp only [not_exists, exists_prop, mem_set_of_eq, mem_compl_iff, not_not_mem]
    filter_upwards [this]with x hx
    apply (iInf_eq_of_forall_ge_of_forall_gt_exists_lt _ _).symm
    · intro i
      by_cases H : x ∈ u' i
      swap
      · simp only [H, le_top, not_false_iff, piecewise_eq_of_not_mem]
      simp only [H, piecewise_eq_of_mem]
      contrapose! hx
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : ∃ r, r ∈ Ioo (i : β) (f x) ∩ s :=
        dense_iff_inter_open.1 s_dense (Ioo i (f x)) isOpen_Ioo (nonempty_Ioo.2 hx)
      have A : x ∈ v i r := (huv i r).2.2.2.1 rq
      apply mem_Union.2 ⟨i, _⟩
      refine' mem_Union.2 ⟨⟨r, ⟨rs, xr⟩⟩, _⟩
      exact ⟨H, A⟩
    · intro q hq
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : ∃ r, r ∈ Ioo (f x) q ∩ s :=
        dense_iff_inter_open.1 s_dense (Ioo (f x) q) isOpen_Ioo (nonempty_Ioo.2 hq)
      refine' ⟨⟨r, rs⟩, _⟩
      have A : x ∈ u' r := mem_bInter fun i hi => (huv r i).2.2.1 xr
      simp only [A, rq, piecewise_eq_of_mem, Subtype.coe_mk]
  exact ⟨f', f'_meas, ff'⟩
#align measure_theory.ae_measurable_of_exist_almost_disjoint_supersets MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets

/- warning: ennreal.ae_measurable_of_exist_almost_disjoint_supersets -> ENNReal.aemeasurable_of_exist_almost_disjoint_supersets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) (f : α -> ENNReal), (forall (p : NNReal) (q : NNReal), (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) p q) -> (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{succ u1} (Set.{u1} α) (fun (v : Set.{u1} α) => And (MeasurableSet.{u1} α m u) (And (MeasurableSet.{u1} α m v) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (setOf.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) p))) u) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (setOf.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) q) (f x))) v) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u v)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))))))))) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) (f : α -> ENNReal), (forall (p : NNReal) (q : NNReal), (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) p q) -> (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{succ u1} (Set.{u1} α) (fun (v : Set.{u1} α) => And (MeasurableSet.{u1} α m u) (And (MeasurableSet.{u1} α m v) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (setOf.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (ENNReal.some p))) u) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (setOf.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (ENNReal.some q) (f x))) v) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u v)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))))))))) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ)
Case conversion may be inaccurate. Consider using '#align ennreal.ae_measurable_of_exist_almost_disjoint_supersets ENNReal.aemeasurable_of_exist_almost_disjoint_supersetsₓ'. -/
/-- If a function `f : α → ℝ≥0∞` is such that the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p` and `q` are finite numbers satisfying
`p < q`, then `f` is almost-everywhere measurable. -/
theorem ENNReal.aemeasurable_of_exist_almost_disjoint_supersets {α : Type _} {m : MeasurableSpace α}
    (μ : Measure α) (f : α → ℝ≥0∞)
    (h :
      ∀ (p : ℝ≥0) (q : ℝ≥0),
        p < q →
          ∃ u v,
            MeasurableSet u ∧
              MeasurableSet v ∧
                { x | f x < p } ⊆ u ∧ { x | (q : ℝ≥0∞) < f x } ⊆ v ∧ μ (u ∩ v) = 0) :
    AEMeasurable f μ :=
  by
  obtain ⟨s, s_count, s_dense, s_zero, s_top⟩ :
    ∃ s : Set ℝ≥0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s :=
    ENNReal.exists_countable_dense_no_zero_top
  have I : ∀ x ∈ s, x ≠ ∞ := fun x xs hx => s_top (hx ▸ xs)
  apply MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets μ s s_count s_dense _
  rintro p hp q hq hpq
  lift p to ℝ≥0 using I p hp
  lift q to ℝ≥0 using I q hq
  exact h p q (ENNReal.coe_lt_coe.1 hpq)
#align ennreal.ae_measurable_of_exist_almost_disjoint_supersets ENNReal.aemeasurable_of_exist_almost_disjoint_supersets

