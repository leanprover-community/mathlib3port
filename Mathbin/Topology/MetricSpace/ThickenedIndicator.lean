/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä

! This file was ported from Lean 3 source module topology.metric_space.thickened_indicator
! leanprover-community/mathlib commit 38df578a6450a8c5142b3727e3ae894c2300cae0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Ennreal
import Mathbin.Topology.ContinuousFunction.Bounded
import Mathbin.Topology.MetricSpace.HausdorffDistance

/-!
# Thickened indicators

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is about thickened indicators of sets in (pseudo e)metric spaces. For a decreasing
sequence of thickening radii tending to 0, the thickened indicators of a closed set form a
decreasing pointwise converging approximation of the indicator function of the set, where the
members of the approximating sequence are nonnegative bounded continuous functions.

## Main definitions

 * `thickened_indicator_aux δ E`: The `δ`-thickened indicator of a set `E` as an
   unbundled `ℝ≥0∞`-valued function.
 * `thickened_indicator δ E`: The `δ`-thickened indicator of a set `E` as a bundled
   bounded continuous `ℝ≥0`-valued function.

## Main results

 * For a sequence of thickening radii tending to 0, the `δ`-thickened indicators of a set `E` tend
   pointwise to the indicator of `closure E`.
   - `thickened_indicator_aux_tendsto_indicator_closure`: The version is for the
     unbundled `ℝ≥0∞`-valued functions.
   - `thickened_indicator_tendsto_indicator_closure`: The version is for the bundled `ℝ≥0`-valued
     bounded continuous functions.

-/


noncomputable section

open Classical NNReal ENNReal Topology BoundedContinuousFunction

open NNReal ENNReal Set Metric Emetric Filter

section thickenedIndicator

variable {α : Type _} [PseudoEMetricSpace α]

#print thickenedIndicatorAux /-
/-- The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `inf_edist _ E`.

`thickened_indicator_aux` is the unbundled `ℝ≥0∞`-valued function. See `thickened_indicator`
for the (bundled) bounded continuous function with `ℝ≥0`-values. -/
def thickenedIndicatorAux (δ : ℝ) (E : Set α) : α → ℝ≥0∞ := fun x : α =>
  (1 : ℝ≥0∞) - infEdist x E / ENNReal.ofReal δ
#align thickened_indicator_aux thickenedIndicatorAux
-/

/- warning: continuous_thickened_indicator_aux -> continuous_thickenedIndicatorAux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (forall (E : Set.{u1} α), Continuous.{u1, 0} α ENNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) ENNReal.topologicalSpace (thickenedIndicatorAux.{u1} α _inst_1 δ E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (forall (E : Set.{u1} α), Continuous.{u1, 0} α ENNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) ENNReal.instTopologicalSpaceENNReal (thickenedIndicatorAux.{u1} α _inst_1 δ E))
Case conversion may be inaccurate. Consider using '#align continuous_thickened_indicator_aux continuous_thickenedIndicatorAuxₓ'. -/
theorem continuous_thickenedIndicatorAux {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    Continuous (thickenedIndicatorAux δ E) :=
  by
  unfold thickenedIndicatorAux
  let f := fun x : α => (⟨1, inf_edist x E / ENNReal.ofReal δ⟩ : ℝ≥0 × ℝ≥0∞)
  let sub := fun p : ℝ≥0 × ℝ≥0∞ => (p.1 : ℝ≥0∞) - p.2
  rw [show (fun x : α => (1 : ℝ≥0∞) - inf_edist x E / ENNReal.ofReal δ) = sub ∘ f by rfl]
  apply (@ENNReal.continuous_nnreal_sub 1).comp
  apply (ENNReal.continuous_div_const (ENNReal.ofReal δ) _).comp continuous_inf_edist
  norm_num [δ_pos]
#align continuous_thickened_indicator_aux continuous_thickenedIndicatorAux

/- warning: thickened_indicator_aux_le_one -> thickenedIndicatorAux_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) (E : Set.{u1} α) (x : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (thickenedIndicatorAux.{u1} α _inst_1 δ E x) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) (E : Set.{u1} α) (x : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (thickenedIndicatorAux.{u1} α _inst_1 δ E x) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))
Case conversion may be inaccurate. Consider using '#align thickened_indicator_aux_le_one thickenedIndicatorAux_le_oneₓ'. -/
theorem thickenedIndicatorAux_le_one (δ : ℝ) (E : Set α) (x : α) :
    thickenedIndicatorAux δ E x ≤ 1 := by apply @tsub_le_self _ _ _ _ (1 : ℝ≥0∞)
#align thickened_indicator_aux_le_one thickenedIndicatorAux_le_one

/- warning: thickened_indicator_aux_lt_top -> thickenedIndicatorAux_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} {E : Set.{u1} α} {x : α}, LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (thickenedIndicatorAux.{u1} α _inst_1 δ E x) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} {E : Set.{u1} α} {x : α}, LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (thickenedIndicatorAux.{u1} α _inst_1 δ E x) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align thickened_indicator_aux_lt_top thickenedIndicatorAux_lt_topₓ'. -/
theorem thickenedIndicatorAux_lt_top {δ : ℝ} {E : Set α} {x : α} :
    thickenedIndicatorAux δ E x < ∞ :=
  lt_of_le_of_lt (thickenedIndicatorAux_le_one _ _ _) one_lt_top
#align thickened_indicator_aux_lt_top thickenedIndicatorAux_lt_top

#print thickenedIndicatorAux_closure_eq /-
theorem thickenedIndicatorAux_closure_eq (δ : ℝ) (E : Set α) :
    thickenedIndicatorAux δ (closure E) = thickenedIndicatorAux δ E := by
  simp_rw [thickenedIndicatorAux, inf_edist_closure]
#align thickened_indicator_aux_closure_eq thickenedIndicatorAux_closure_eq
-/

#print thickenedIndicatorAux_one /-
theorem thickenedIndicatorAux_one (δ : ℝ) (E : Set α) {x : α} (x_in_E : x ∈ E) :
    thickenedIndicatorAux δ E x = 1 := by
  simp [thickenedIndicatorAux, inf_edist_zero_of_mem x_in_E, tsub_zero]
#align thickened_indicator_aux_one thickenedIndicatorAux_one
-/

#print thickenedIndicatorAux_one_of_mem_closure /-
theorem thickenedIndicatorAux_one_of_mem_closure (δ : ℝ) (E : Set α) {x : α}
    (x_mem : x ∈ closure E) : thickenedIndicatorAux δ E x = 1 := by
  rw [← thickenedIndicatorAux_closure_eq, thickenedIndicatorAux_one δ (closure E) x_mem]
#align thickened_indicator_aux_one_of_mem_closure thickenedIndicatorAux_one_of_mem_closure
-/

/- warning: thickened_indicator_aux_zero -> thickenedIndicatorAux_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (forall (E : Set.{u1} α) {x : α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Metric.thickening.{u1} α _inst_1 δ E))) -> (Eq.{1} ENNReal (thickenedIndicatorAux.{u1} α _inst_1 δ E x) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (forall (E : Set.{u1} α) {x : α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Metric.thickening.{u1} α _inst_1 δ E))) -> (Eq.{1} ENNReal (thickenedIndicatorAux.{u1} α _inst_1 δ E x) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align thickened_indicator_aux_zero thickenedIndicatorAux_zeroₓ'. -/
theorem thickenedIndicatorAux_zero {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_out : x ∉ thickening δ E) : thickenedIndicatorAux δ E x = 0 :=
  by
  rw [thickening, mem_set_of_eq, not_lt] at x_out
  unfold thickenedIndicatorAux
  apply le_antisymm _ bot_le
  have key := tsub_le_tsub (@rfl _ (1 : ℝ≥0∞)).le (ENNReal.div_le_div x_out rfl.le)
  rw [ENNReal.div_self (ne_of_gt (ennreal.of_real_pos.mpr δ_pos)) of_real_ne_top] at key
  simpa using key
#align thickened_indicator_aux_zero thickenedIndicatorAux_zero

/- warning: thickened_indicator_aux_mono -> thickenedIndicatorAux_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : Real} {δ₂ : Real}, (LE.le.{0} Real Real.hasLe δ₁ δ₂) -> (forall (E : Set.{u1} α), LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) (thickenedIndicatorAux.{u1} α _inst_1 δ₁ E) (thickenedIndicatorAux.{u1} α _inst_1 δ₂ E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : Real} {δ₂ : Real}, (LE.le.{0} Real Real.instLEReal δ₁ δ₂) -> (forall (E : Set.{u1} α), LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) (thickenedIndicatorAux.{u1} α _inst_1 δ₁ E) (thickenedIndicatorAux.{u1} α _inst_1 δ₂ E))
Case conversion may be inaccurate. Consider using '#align thickened_indicator_aux_mono thickenedIndicatorAux_monoₓ'. -/
theorem thickenedIndicatorAux_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    thickenedIndicatorAux δ₁ E ≤ thickenedIndicatorAux δ₂ E := fun _ =>
  tsub_le_tsub (@rfl ℝ≥0∞ 1).le (ENNReal.div_le_div rfl.le (ofReal_le_ofReal hle))
#align thickened_indicator_aux_mono thickenedIndicatorAux_mono

/- warning: indicator_le_thickened_indicator_aux -> indicator_le_thickenedIndicatorAux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) (E : Set.{u1} α), LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) (Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero E (fun (_x : α) => OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (thickenedIndicatorAux.{u1} α _inst_1 δ E)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) (E : Set.{u1} α), LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) (Set.indicator.{u1, 0} α ENNReal instENNRealZero E (fun (_x : α) => OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (thickenedIndicatorAux.{u1} α _inst_1 δ E)
Case conversion may be inaccurate. Consider using '#align indicator_le_thickened_indicator_aux indicator_le_thickenedIndicatorAuxₓ'. -/
theorem indicator_le_thickenedIndicatorAux (δ : ℝ) (E : Set α) :
    (E.indicator fun _ => (1 : ℝ≥0∞)) ≤ thickenedIndicatorAux δ E :=
  by
  intro a
  by_cases a ∈ E
  · simp only [h, indicator_of_mem, thickenedIndicatorAux_one δ E h, le_refl]
  · simp only [h, indicator_of_not_mem, not_false_iff, zero_le]
#align indicator_le_thickened_indicator_aux indicator_le_thickenedIndicatorAux

/- warning: thickened_indicator_aux_subset -> thickenedIndicatorAux_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) {E₁ : Set.{u1} α} {E₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) E₁ E₂) -> (LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) (thickenedIndicatorAux.{u1} α _inst_1 δ E₁) (thickenedIndicatorAux.{u1} α _inst_1 δ E₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (δ : Real) {E₁ : Set.{u1} α} {E₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) E₁ E₂) -> (LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) (thickenedIndicatorAux.{u1} α _inst_1 δ E₁) (thickenedIndicatorAux.{u1} α _inst_1 δ E₂))
Case conversion may be inaccurate. Consider using '#align thickened_indicator_aux_subset thickenedIndicatorAux_subsetₓ'. -/
theorem thickenedIndicatorAux_subset (δ : ℝ) {E₁ E₂ : Set α} (subset : E₁ ⊆ E₂) :
    thickenedIndicatorAux δ E₁ ≤ thickenedIndicatorAux δ E₂ := fun _ =>
  tsub_le_tsub (@rfl ℝ≥0∞ 1).le (ENNReal.div_le_div (infEdist_anti subset) rfl.le)
#align thickened_indicator_aux_subset thickenedIndicatorAux_subset

/- warning: thickened_indicator_aux_tendsto_indicator_closure -> thickenedIndicatorAux_tendsto_indicator_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δseq : Nat -> Real}, (Filter.Tendsto.{0, 0} Nat Real δseq (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (forall (E : Set.{u1} α), Filter.Tendsto.{0, u1} Nat (α -> ENNReal) (fun (n : Nat) => thickenedIndicatorAux.{u1} α _inst_1 (δseq n) E) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} (α -> ENNReal) (Pi.topologicalSpace.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (a : α) => ENNReal.topologicalSpace)) (Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (fun (x : α) => OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δseq : Nat -> Real}, (Filter.Tendsto.{0, 0} Nat Real δseq (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (forall (E : Set.{u1} α), Filter.Tendsto.{0, u1} Nat (α -> ENNReal) (fun (n : Nat) => thickenedIndicatorAux.{u1} α _inst_1 (δseq n) E) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} (α -> ENNReal) (Pi.topologicalSpace.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (a : α) => ENNReal.instTopologicalSpaceENNReal)) (Set.indicator.{u1, 0} α ENNReal instENNRealZero (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (fun (x : α) => OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))
Case conversion may be inaccurate. Consider using '#align thickened_indicator_aux_tendsto_indicator_closure thickenedIndicatorAux_tendsto_indicator_closureₓ'. -/
/-- As the thickening radius δ tends to 0, the δ-thickened indicator of a set E (in α) tends
pointwise (i.e., w.r.t. the product topology on `α → ℝ≥0∞`) to the indicator function of the
closure of E.

This statement is for the unbundled `ℝ≥0∞`-valued functions `thickened_indicator_aux δ E`, see
`thickened_indicator_tendsto_indicator_closure` for the version for bundled `ℝ≥0`-valued
bounded continuous functions. -/
theorem thickenedIndicatorAux_tendsto_indicator_closure {δseq : ℕ → ℝ}
    (δseq_lim : Tendsto δseq atTop (𝓝 0)) (E : Set α) :
    Tendsto (fun n => thickenedIndicatorAux (δseq n) E) atTop
      (𝓝 (indicator (closure E) fun x => (1 : ℝ≥0∞))) :=
  by
  rw [tendsto_pi_nhds]
  intro x
  by_cases x_mem_closure : x ∈ closure E
  · simp_rw [thickenedIndicatorAux_one_of_mem_closure _ E x_mem_closure]
    rw [show (indicator (closure E) fun _ => (1 : ℝ≥0∞)) x = 1 by
        simp only [x_mem_closure, indicator_of_mem]]
    exact tendsto_const_nhds
  · rw [show (closure E).indicator (fun _ => (1 : ℝ≥0∞)) x = 0 by
        simp only [x_mem_closure, indicator_of_not_mem, not_false_iff]]
    rcases exists_real_pos_lt_inf_edist_of_not_mem_closure x_mem_closure with ⟨ε, ⟨ε_pos, ε_lt⟩⟩
    rw [Metric.tendsto_nhds] at δseq_lim
    specialize δseq_lim ε ε_pos
    simp only [dist_zero_right, Real.norm_eq_abs, eventually_at_top, ge_iff_le] at δseq_lim
    rcases δseq_lim with ⟨N, hN⟩
    apply @tendsto_atTop_of_eventually_const _ _ _ _ _ _ _ N
    intro n n_large
    have key : x ∉ thickening ε E := by simpa only [thickening, mem_set_of_eq, not_lt] using ε_lt.le
    refine' le_antisymm _ bot_le
    apply (thickenedIndicatorAux_mono (lt_of_abs_lt (hN n n_large)).le E x).trans
    exact (thickenedIndicatorAux_zero ε_pos E key).le
#align thickened_indicator_aux_tendsto_indicator_closure thickenedIndicatorAux_tendsto_indicator_closure

/- warning: thickened_indicator -> thickenedIndicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (Set.{u1} α) -> (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (Set.{u1} α) -> (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal)
Case conversion may be inaccurate. Consider using '#align thickened_indicator thickenedIndicatorₓ'. -/
/-- The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `inf_edist _ E`.

`thickened_indicator` is the (bundled) bounded continuous function with `ℝ≥0`-values.
See `thickened_indicator_aux` for the unbundled `ℝ≥0∞`-valued function. -/
@[simps]
def thickenedIndicator {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) : α →ᵇ ℝ≥0
    where
  toFun := fun x : α => (thickenedIndicatorAux δ E x).toNNReal
  continuous_toFun :=
    by
    apply
      ContinuousOn.comp_continuous continuous_on_to_nnreal
        (continuous_thickenedIndicatorAux δ_pos E)
    intro x
    exact (lt_of_le_of_lt (@thickenedIndicatorAux_le_one _ _ δ E x) one_lt_top).Ne
  map_bounded' := by
    use 2
    intro x y
    rw [NNReal.dist_eq]
    apply (abs_sub _ _).trans
    rw [NNReal.abs_eq, NNReal.abs_eq, ← one_add_one_eq_two]
    have key := @thickenedIndicatorAux_le_one _ _ δ E
    apply add_le_add <;>
      · norm_cast
        refine'
          (to_nnreal_le_to_nnreal (lt_of_le_of_lt (key _) one_lt_top).Ne one_ne_top).mpr (key _)
#align thickened_indicator thickenedIndicator

/- warning: thickened_indicator.coe_fn_eq_comp -> thickenedIndicator.coeFn_eq_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (E : Set.{u1} α), Eq.{succ u1} (α -> NNReal) (coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (fun (_x : BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) => α -> NNReal) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E)) (Function.comp.{succ u1, 1, 1} α ENNReal NNReal ENNReal.toNNReal (thickenedIndicatorAux.{u1} α _inst_1 δ E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (E : Set.{u1} α), Eq.{succ u1} (forall (ᾰ : α), (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) ᾰ) (FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α (fun (_x : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal))) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E)) (Function.comp.{succ u1, 1, 1} α ENNReal NNReal ENNReal.toNNReal (thickenedIndicatorAux.{u1} α _inst_1 δ E))
Case conversion may be inaccurate. Consider using '#align thickened_indicator.coe_fn_eq_comp thickenedIndicator.coeFn_eq_compₓ'. -/
theorem thickenedIndicator.coeFn_eq_comp {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    ⇑(thickenedIndicator δ_pos E) = ENNReal.toNNReal ∘ thickenedIndicatorAux δ E :=
  rfl
#align thickened_indicator.coe_fn_eq_comp thickenedIndicator.coeFn_eq_comp

/- warning: thickened_indicator_le_one -> thickenedIndicator_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (E : Set.{u1} α) (x : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (fun (_x : BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) => α -> NNReal) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E) x) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (E : Set.{u1} α) (x : α), LE.le.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) (Preorder.toLE.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) (PartialOrder.toPreorder.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) (StrictOrderedSemiring.toPartialOrder.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) instNNRealStrictOrderedSemiring))) (FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α (fun (_x : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal))) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E) x) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) 1 (One.toOfNat1.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) instNNRealOne))
Case conversion may be inaccurate. Consider using '#align thickened_indicator_le_one thickenedIndicator_le_oneₓ'. -/
theorem thickenedIndicator_le_one {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) (x : α) :
    thickenedIndicator δ_pos E x ≤ 1 :=
  by
  rw [thickenedIndicator.coeFn_eq_comp]
  simpa using
    (to_nnreal_le_to_nnreal thickened_indicator_aux_lt_top.ne one_ne_top).mpr
      (thickenedIndicatorAux_le_one δ E x)
#align thickened_indicator_le_one thickenedIndicator_le_one

/- warning: thickened_indicator_one_of_mem_closure -> thickenedIndicator_one_of_mem_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (E : Set.{u1} α) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E)) -> (Eq.{1} NNReal (coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (fun (_x : BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) => α -> NNReal) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E) x) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (E : Set.{u1} α) {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E)) -> (Eq.{1} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) (FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α (fun (_x : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal))) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E) x) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) 1 (One.toOfNat1.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) instNNRealOne)))
Case conversion may be inaccurate. Consider using '#align thickened_indicator_one_of_mem_closure thickenedIndicator_one_of_mem_closureₓ'. -/
theorem thickenedIndicator_one_of_mem_closure {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_mem : x ∈ closure E) : thickenedIndicator δ_pos E x = 1 := by
  rw [thickenedIndicator_apply, thickenedIndicatorAux_one_of_mem_closure δ E x_mem, one_to_nnreal]
#align thickened_indicator_one_of_mem_closure thickenedIndicator_one_of_mem_closure

/- warning: thickened_indicator_one -> thickenedIndicator_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (E : Set.{u1} α) {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x E) -> (Eq.{1} NNReal (coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (fun (_x : BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) => α -> NNReal) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E) x) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (E : Set.{u1} α) {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x E) -> (Eq.{1} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) (FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α (fun (_x : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal))) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E) x) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) 1 (One.toOfNat1.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) instNNRealOne)))
Case conversion may be inaccurate. Consider using '#align thickened_indicator_one thickenedIndicator_oneₓ'. -/
theorem thickenedIndicator_one {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_in_E : x ∈ E) :
    thickenedIndicator δ_pos E x = 1 :=
  thickenedIndicator_one_of_mem_closure _ _ (subset_closure x_in_E)
#align thickened_indicator_one thickenedIndicator_one

/- warning: thickened_indicator_zero -> thickenedIndicator_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (E : Set.{u1} α) {x : α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Metric.thickening.{u1} α _inst_1 δ E))) -> (Eq.{1} NNReal (coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (fun (_x : BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) => α -> NNReal) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E) x) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (E : Set.{u1} α) {x : α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Metric.thickening.{u1} α _inst_1 δ E))) -> (Eq.{1} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) (FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α (fun (_x : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal))) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E) x) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) 0 (Zero.toOfNat0.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) x) instNNRealZero)))
Case conversion may be inaccurate. Consider using '#align thickened_indicator_zero thickenedIndicator_zeroₓ'. -/
theorem thickenedIndicator_zero {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_out : x ∉ thickening δ E) : thickenedIndicator δ_pos E x = 0 := by
  rw [thickenedIndicator_apply, thickenedIndicatorAux_zero δ_pos E x_out, zero_to_nnreal]
#align thickened_indicator_zero thickenedIndicator_zero

/- warning: indicator_le_thickened_indicator -> indicator_le_thickenedIndicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) (E : Set.{u1} α), LE.le.{u1} (α -> NNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => NNReal) (fun (i : α) => Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (Set.indicator.{u1, 0} α NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) E (fun (_x : α) => OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (fun (_x : BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) => α -> NNReal) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) (E : Set.{u1} α), LE.le.{u1} (α -> NNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => NNReal) (fun (i : α) => Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)))) (Set.indicator.{u1, 0} α NNReal instNNRealZero E (fun (_x : α) => OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) (FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α (fun (_x : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal))) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E))
Case conversion may be inaccurate. Consider using '#align indicator_le_thickened_indicator indicator_le_thickenedIndicatorₓ'. -/
theorem indicator_le_thickenedIndicator {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    (E.indicator fun _ => (1 : ℝ≥0)) ≤ thickenedIndicator δ_pos E :=
  by
  intro a
  by_cases a ∈ E
  · simp only [h, indicator_of_mem, thickenedIndicator_one δ_pos E h, le_refl]
  · simp only [h, indicator_of_not_mem, not_false_iff, zero_le]
#align indicator_le_thickened_indicator indicator_le_thickenedIndicator

/- warning: thickened_indicator_mono -> thickenedIndicator_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : Real} {δ₂ : Real} (δ₁_pos : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ₁) (δ₂_pos : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ₂), (LE.le.{0} Real Real.hasLe δ₁ δ₂) -> (forall (E : Set.{u1} α), LE.le.{u1} (α -> NNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => NNReal) (fun (i : α) => Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (fun (_x : BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) => α -> NNReal) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (thickenedIndicator.{u1} α _inst_1 δ₁ δ₁_pos E)) (coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (fun (_x : BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) => α -> NNReal) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (thickenedIndicator.{u1} α _inst_1 δ₂ δ₂_pos E)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ₁ : Real} {δ₂ : Real} (δ₁_pos : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ₁) (δ₂_pos : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ₂), (LE.le.{0} Real Real.instLEReal δ₁ δ₂) -> (forall (E : Set.{u1} α), LE.le.{u1} (forall (ᾰ : α), (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) ᾰ) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) ᾰ) (fun (i : α) => Preorder.toLE.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) i) (PartialOrder.toPreorder.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) i) (StrictOrderedSemiring.toPartialOrder.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) i) instNNRealStrictOrderedSemiring)))) (FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α (fun (_x : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal))) (thickenedIndicator.{u1} α _inst_1 δ₁ δ₁_pos E)) (FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α (fun (_x : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal))) (thickenedIndicator.{u1} α _inst_1 δ₂ δ₂_pos E)))
Case conversion may be inaccurate. Consider using '#align thickened_indicator_mono thickenedIndicator_monoₓ'. -/
theorem thickenedIndicator_mono {δ₁ δ₂ : ℝ} (δ₁_pos : 0 < δ₁) (δ₂_pos : 0 < δ₂) (hle : δ₁ ≤ δ₂)
    (E : Set α) : ⇑(thickenedIndicator δ₁_pos E) ≤ thickenedIndicator δ₂_pos E :=
  by
  intro x
  apply
    (to_nnreal_le_to_nnreal thickened_indicator_aux_lt_top.ne thickened_indicator_aux_lt_top.ne).mpr
  apply thickenedIndicatorAux_mono hle
#align thickened_indicator_mono thickenedIndicator_mono

/- warning: thickened_indicator_subset -> thickenedIndicator_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) {E₁ : Set.{u1} α} {E₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) E₁ E₂) -> (LE.le.{u1} (α -> NNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => NNReal) (fun (i : α) => Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (fun (_x : BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) => α -> NNReal) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E₁)) (coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (fun (_x : BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) => α -> NNReal) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E₂)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δ : Real} (δ_pos : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) {E₁ : Set.{u1} α} {E₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) E₁ E₂) -> (LE.le.{u1} (forall (ᾰ : α), (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) ᾰ) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) ᾰ) (fun (i : α) => Preorder.toLE.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) i) (PartialOrder.toPreorder.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) i) (StrictOrderedSemiring.toPartialOrder.{0} ((fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) i) instNNRealStrictOrderedSemiring)))) (FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α (fun (_x : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal))) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E₁)) (FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α (fun (_x : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) _x) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal))) (thickenedIndicator.{u1} α _inst_1 δ δ_pos E₂)))
Case conversion may be inaccurate. Consider using '#align thickened_indicator_subset thickenedIndicator_subsetₓ'. -/
theorem thickenedIndicator_subset {δ : ℝ} (δ_pos : 0 < δ) {E₁ E₂ : Set α} (subset : E₁ ⊆ E₂) :
    ⇑(thickenedIndicator δ_pos E₁) ≤ thickenedIndicator δ_pos E₂ := fun x =>
  (toNNReal_le_toNNReal thickenedIndicatorAux_lt_top.Ne thickenedIndicatorAux_lt_top.Ne).mpr
    (thickenedIndicatorAux_subset δ subset x)
#align thickened_indicator_subset thickenedIndicator_subset

/- warning: thickened_indicator_tendsto_indicator_closure -> thickenedIndicator_tendsto_indicator_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δseq : Nat -> Real} (δseq_pos : forall (n : Nat), LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (δseq n)), (Filter.Tendsto.{0, 0} Nat Real δseq (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (forall (E : Set.{u1} α), Filter.Tendsto.{0, u1} Nat (α -> NNReal) (fun (n : Nat) => coeFn.{succ u1, succ u1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (fun (ᾰ : BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) => α -> NNReal) (BoundedContinuousFunction.hasCoeToFun.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) NNReal.pseudoMetricSpace) (thickenedIndicator.{u1} α _inst_1 (δseq n) (δseq_pos n) E)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} (α -> NNReal) (Pi.topologicalSpace.{u1, 0} α (fun (ᾰ : α) => NNReal) (fun (a : α) => NNReal.topologicalSpace)) (Set.indicator.{u1, 0} α NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (fun (x : α) => OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {δseq : Nat -> Real} (δseq_pos : forall (n : Nat), LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (δseq n)), (Filter.Tendsto.{0, 0} Nat Real δseq (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (forall (E : Set.{u1} α), Filter.Tendsto.{0, u1} Nat (forall (ᾰ : α), (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) ᾰ) (fun (n : Nat) => FunLike.coe.{succ u1, succ u1, 1} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α (fun (ᾰ : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) ᾰ) (ContinuousMapClass.toFunLike.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (BoundedContinuousMapClass.toContinuousMapClass.{u1, u1, 0} (BoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal) α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal (BoundedContinuousFunction.instBoundedContinuousMapClassBoundedContinuousFunction.{u1, 0} α NNReal (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) instPseudoMetricSpaceNNReal))) (thickenedIndicator.{u1} α _inst_1 (δseq n) (δseq_pos n) E)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} (forall (ᾰ : α), (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) ᾰ) (Pi.topologicalSpace.{u1, 0} α (fun (ᾰ : α) => (fun (a._@.Mathlib.Topology.ContinuousFunction.Bounded._hyg.904 : α) => NNReal) ᾰ) (fun (a : α) => NNReal.instTopologicalSpaceNNReal)) (Set.indicator.{u1, 0} α NNReal instNNRealZero (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) E) (fun (x : α) => OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)))))
Case conversion may be inaccurate. Consider using '#align thickened_indicator_tendsto_indicator_closure thickenedIndicator_tendsto_indicator_closureₓ'. -/
/-- As the thickening radius δ tends to 0, the δ-thickened indicator of a set E (in α) tends
pointwise to the indicator function of the closure of E.

Note: This version is for the bundled bounded continuous functions, but the topology is not
the topology on `α →ᵇ ℝ≥0`. Coercions to functions `α → ℝ≥0` are done first, so the topology
instance is the product topology (the topology of pointwise convergence). -/
theorem thickenedIndicator_tendsto_indicator_closure {δseq : ℕ → ℝ} (δseq_pos : ∀ n, 0 < δseq n)
    (δseq_lim : Tendsto δseq atTop (𝓝 0)) (E : Set α) :
    Tendsto (fun n : ℕ => (coeFn : (α →ᵇ ℝ≥0) → α → ℝ≥0) (thickenedIndicator (δseq_pos n) E)) atTop
      (𝓝 (indicator (closure E) fun x => (1 : ℝ≥0))) :=
  by
  have key := thickenedIndicatorAux_tendsto_indicator_closure δseq_lim E
  rw [tendsto_pi_nhds] at *
  intro x
  rw [show
      indicator (closure E) (fun x => (1 : ℝ≥0)) x =
        (indicator (closure E) (fun x => (1 : ℝ≥0∞)) x).toNNReal
      by refine' (congr_fun (comp_indicator_const 1 ENNReal.toNNReal zero_to_nnreal) x).symm]
  refine' tendsto.comp (tendsto_to_nnreal _) (key x)
  by_cases x_mem : x ∈ closure E <;> simp [x_mem]
#align thickened_indicator_tendsto_indicator_closure thickenedIndicator_tendsto_indicator_closure

end thickenedIndicator

-- section
